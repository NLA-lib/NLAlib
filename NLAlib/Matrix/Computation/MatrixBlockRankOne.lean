/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.MatrixBlockUpdate
public import NLAlib.Computation.BLAS.MatrixKernels

/-!
# Packed rank-one updates of rectangular matrix views

Gather a matrix rectangle, apply the existing packed `ger` kernel, and scatter its result.
The packed workspace is scoped; the original matrix is the sole net output. Panel LU uses
this operation twice with disjoint column intervals and saved original vector operands.

## Main definitions

* `NLAlib.Computation.gerMatrixBlock`: gather, rank-one update and scatter a rectangle.

## Main results

* `NLAlib.Computation.executionComposable_gerMatrixBlock`: scoped-workspace composition.
* `NLAlib.Computation.exec_gerMatrixBlock`: actual exact update and full matrix write.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Update a rectangular matrix view by a packed `ger` call, with exact gather and scatter
copies. Its physical leading dimension remains `size`. Factor inputs may overlap the target
matrix because all numerical factor reads precede the final scatter. [GolubVanLoan2013, §1.1]. -/
def gerMatrixBlock {P ι VB VI : Type} (p : P) (size m n : IExp VI) (a : Cell VB VI)
    (x : VB) (xo : IExp VI) (y : VB) (yo : IExp VI) (R : VB)
    (off row col : IExp VI) : Builder P ι VB VI Unit := scope do
  let packed ← alloc p (m * n)
  gatherMatrixBlock p m n size R off row col packed 0
  ger p m n a x xo y yo packed 0
  scatterMatrixBlock p m n size packed 0 R off row col

variable {P ι 𝕜 : Type} [DecidableEq P] [RCLike 𝕜]

/-- The packed rectangle workspace is released before the continuation. -/
theorem executionComposable_gerMatrixBlock {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (p : P) (size m n : IExp ℕ) (a : Cell ℕ ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ) (R : ℕ) (off row col : IExp ℕ) :
    ExecutionComposable I (gerMatrixBlock p size m n a x xo y yo R off row col) :=
  executionComposable_single I (fun _ => rfl)

private def matrixView {N m n : ℕ} (M : Matrix (Fin N) (Fin N) 𝕜)
    (row col : ℕ) (hr : row + m ≤ N) (hc : col + n ≤ N) : Matrix (Fin m) (Fin n) 𝕜 :=
  M.submatrix (fun i => Fin.castLE hr (Fin.natAdd row i))
    (fun j => Fin.castLE hc (Fin.natAdd col j))

private theorem exec_gatherGer (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (initial : Store P 𝕜) (st : St P 𝕜 (OpCount P ι)) (size m n : IExp ℕ)
    (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ) (R : ℕ)
    (off row col : IExp ℕ) (av : 𝕜) (xv : Fin m.eval → 𝕜) (yv : Fin n.eval → 𝕜)
    (M : Matrix (Fin size.eval) (Fin size.eval) 𝕜)
    (hr : row.eval + m.eval ≤ size.eval) (hcol : col.eval + n.eval ≤ size.eval)
    (hM : Holds initial p R off.eval M) (ha : initial.read p a.buf a.idx.eval = some av)
    (hx : ∀ i : Fin m.eval, initial.read p x (xo.eval + i) = some (xv i))
    (hy : ∀ j : Fin n.eval, initial.read p y (yo.eval + j) = some (yv j))
    (hst : st.store = initial.push (p, Array.replicate (m.eval * n.eval) none)) :
    let B := matrixView M row.eval col.eval hr hcol
    let B' := B + av • Matrix.vecMulVec xv (star yv)
    ∃ out, exec I (do
      gatherMatrixBlock p m n size R off row col initial.size 0
      ger p m n a x xo y yo initial.size 0).run st = some out ∧
      st.store.writeBlock p initial.size 0 (flatten B') = some out.store ∧
      Holds out.store p initial.size 0 B' := by
  dsimp only
  let B := matrixView M row.eval col.eval hr hcol
  let B' := B + av • Matrix.vecMulVec xv (star yv)
  have hsep : 0 < m.eval * n.eval → R ≠ initial.size := by
    intro hmn
    have hn : 0 < n.eval := Nat.pos_of_mul_pos_left hmn
    have hN : 0 < size.eval := by omega
    exact Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩))
  have hcap : Writable st.store p initial.size 0 (m.eval * n.eval) := by
    rw [hst]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial p
      (m.eval * n.eval)) (by omega)
  have hMp : Holds st.store p R off.eval M := fun i j => by
    rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hM i j))]
    exact hM i j
  obtain ⟨gathered, W, hW, hr₁, hw₁, hB⟩ := exec_gatherMatrixBlock I p st m n size R off
    row col initial.size 0 B hsep (fun i j => by
      simpa only [B, matrixView, Matrix.submatrix_apply, Fin.val_castLE, Fin.val_natAdd,
        Nat.add_assoc] using hMp (Fin.castLE hr (Fin.natAdd row.eval i))
          (Fin.castLE hcol (Fin.natAdd col.eval j))) hcap
  have ha' : gathered.store.read p a.buf a.idx.eval = some av := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₁
      (Or.inl (Nat.ne_of_lt (Store.lt_size_of_read_eq_some ha))), hst,
      Store.read_push_of_lt (Store.lt_size_of_read_eq_some ha)]
    exact ha
  have hx' (i : Fin m.eval) : gathered.store.read p x (xo.eval + i) = some (xv i) := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₁
      (Or.inl (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hx i)))), hst,
      Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hx i))]
    exact hx i
  have hy' (j : Fin n.eval) : gathered.store.read p y (yo.eval + j) = some (yv j) := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₁
      (Or.inl (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hy j)))), hst,
      Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hy j))]
    exact hy j
  have htarget : Writable gathered.store p initial.size 0 (flatten B').size := by
    simpa only [size_flatten, IExp.eval_zero] using hB.writable
  obtain ⟨target, hw₂⟩ := htarget.exists_writeBlock
  obtain ⟨out, hr₂, hout, _⟩ := exec_ger I hI hc p gathered m n a x xo y yo initial.size 0
    av xv yv B hB ha' hx' hy'
    (fun he => (Nat.ne_of_lt (Store.lt_size_of_read_eq_some ha) he).elim)
    (fun he => by
      by_cases hm : 0 < m.eval
      · exact (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hx ⟨0, hm⟩)) he).elim
      · have hm0 : m.eval = 0 := by omega
        exact Or.inr (by simp only [IExp.eval_zero, hm0, zero_mul, zero_add]; exact Nat.zero_le _))
    (fun he => by
      by_cases hn : 0 < n.eval
      · exact (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hy ⟨0, hn⟩)) he).elim
      · have hn0 : n.eval = 0 := by omega
        exact Or.inr (by simp only [IExp.eval_zero, hn0, mul_zero, zero_add]; exact Nat.zero_le _))
    target hw₂
  have hwOut : gathered.store.writeBlock p initial.size 0 (flatten B') = some out.store :=
    hout.symm ▸ hw₂
  have hB' : Holds out.store p initial.size 0 B' := fun i j => by
    have ht : i.val + m.eval * j.val < (flatten B').size := by
      rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt
    simpa only [Nat.add_assoc, getElem?_flatten, IExp.eval_zero] using
      Store.read_of_writeBlock_eq_some_of_lt hwOut ht
  refine ⟨out, ?_, ?_, hB'⟩
  · rw [exec_run_bind I (b := gatherMatrixBlock p m n size R off row col initial.size 0)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · apply Store.writeBlock_eq_some_of_read
      ((Store.shape_of_writeBlock_eq_some hwOut).trans (Store.shape_of_writeBlock_eq_some hw₁))
    · intro t ht
      exact hB'.read_flatten t (by simpa only [size_flatten] using ht)
    · intro q b t ht
      rw [Store.read_of_writeBlock_eq_some_of_ne hwOut ht,
        Store.read_of_writeBlock_eq_some_of_ne hw₁
          (by simpa only [hW, size_flatten, IExp.eval_zero] using ht)]

private theorem frame_of_rectangle_writes {K : Type} {initial mid final : Store P K} {p : P}
    {T R off N : ℕ} {B : Array K} {W : Array K}
    (hwB : initial.writeBlock p T 0 B = some mid)
    (hwR : mid.writeBlock p R off W = some final) (hW : W.size = N * N) :
    Store.BlockFrame initial p T R off (N * N) final
      (fun t => final.read p R (off + t)) := by
  have hf : Store.BlockFrame initial p T R off (N * N) mid
      (fun t => mid.read p R (off + t)) :=
    ⟨Store.shape_of_writeBlock_eq_some hwB,
      fun _ _ _ hbT _ => Store.read_of_writeBlock_eq_some_of_ne hwB (Or.inl hbT),
      fun _ _ => rfl⟩
  have hf' := hf.writeBlock (off := 0) (by simpa only [Nat.add_zero] using hwR)
    (by rw [hW]; omega)
  exact hf'.congr (fun t ht => (hf'.2.2 t ht).symm)

private theorem exec_rectangleBody (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (initial : Store P 𝕜) (st : St P 𝕜 (OpCount P ι)) (size m n : IExp ℕ)
    (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ) (R : ℕ)
    (off row col : IExp ℕ) (av : 𝕜) (xv : Fin m.eval → 𝕜) (yv : Fin n.eval → 𝕜)
    (M : Matrix (Fin size.eval) (Fin size.eval) 𝕜)
    (hr : row.eval + m.eval ≤ size.eval) (hcol : col.eval + n.eval ≤ size.eval)
    (hM : Holds initial p R off.eval M) (ha : initial.read p a.buf a.idx.eval = some av)
    (hx : ∀ i : Fin m.eval, initial.read p x (xo.eval + i) = some (xv i))
    (hy : ∀ j : Fin n.eval, initial.read p y (yo.eval + j) = some (yv j))
    (hst : st.store = initial.push (p, Array.replicate (m.eval * n.eval) none)) :
    ∃ (out : St P 𝕜 (OpCount P ι)) (M' : Matrix (Fin size.eval) (Fin size.eval) 𝕜),
      exec I (do
        gatherMatrixBlock p m n size R off row col initial.size 0
        ger p m n a x xo y yo initial.size 0
        scatterMatrixBlock p m n size initial.size 0 R off row col).run st = some out ∧
      initial.writeBlock p R off.eval (flatten M') = some out.store.pop ∧
      Holds out.store.pop p R off.eval M' ∧
      (∀ i j, M' (Fin.castLE hr (Fin.natAdd row.eval i))
        (Fin.castLE hcol (Fin.natAdd col.eval j)) =
          M (Fin.castLE hr (Fin.natAdd row.eval i)) (Fin.castLE hcol (Fin.natAdd col.eval j)) +
            av * xv i * star (yv j)) ∧
      ∀ i j, (i.val < row.eval ∨ row.eval + m.eval ≤ i.val ∨
        j.val < col.eval ∨ col.eval + n.eval ≤ j.val) → M' i j = M i j := by
  let B := matrixView M row.eval col.eval hr hcol
  let B' := B + av • Matrix.vecMulVec xv (star yv)
  obtain ⟨mid, hex₁, hw₁, hB'⟩ := exec_gatherGer I hI hc p initial st size m n a x xo y yo
    R off row col av xv yv M hr hcol hM ha hx hy hst
  have hMp : Holds mid.store p R off.eval M := fun i j => by
    have hRb := Store.lt_size_of_read_eq_some (hM i j)
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl (Nat.ne_of_lt hRb)),
      hst, Store.read_push_of_lt hRb]
    exact hM i j
  obtain ⟨out, W, M', hW, hex₂, hw₂, hM', hcoords, houtside⟩ :=
    exec_scatterMatrixBlock_into_matrix I p mid size m n initial.size 0 R off row col
      M B' hr hcol hMp hB' (fun hmn => by
        have hn : 0 < n.eval := Nat.pos_of_mul_pos_left hmn
        have hN : 0 < size.eval := by omega
        exact Nat.ne_of_gt (Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)))
  have hFrame := frame_of_rectangle_writes hw₁ hw₂ hW
  have hFrame' : Store.BlockFrame (initial.push (p, Array.replicate (m.eval * n.eval) none))
      p initial.size R off.eval (size.eval * size.eval) out.store
      (fun t => out.store.read p R (off.eval + t)) := hst ▸ hFrame
  have hcap : Writable initial p R off.eval (flatten M').size := by
    simpa only [size_flatten] using hM.writable
  obtain ⟨target, htarget⟩ := hcap.exists_writeBlock
  have hpop := hFrame'.pop_eq htarget (size_flatten M') (fun t ht => hM'.read_flatten t ht)
  have hsize : out.store.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hFrame'.1
  refine ⟨out, M', ?_, hpop ▸ htarget, ?_, ?_, houtside⟩
  · have hcomp : ExecutionComposable I (do
        gatherMatrixBlock p m n size R off row col initial.size 0
        ger p m n a x xo y yo initial.size 0) :=
      (executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl))
    change exec I ((do
      gatherMatrixBlock p m n size R off row col initial.size 0
      ger p m n a x xo y yo initial.size 0) >>= fun _ =>
      scatterMatrixBlock p m n size initial.size 0 R off row col).run st = some out
    rw [hcomp, hex₁, Option.bind_some]
    exact hex₂
  · intro i j
    rw [Store.read_pop_of_lt (by have := Store.lt_size_of_read_eq_some (hM i j); omega)]
    exact hM' i j
  · intro i j
    rw [hcoords]
    simp only [B', B, matrixView, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.vecMulVec_apply, Pi.star_apply]
    ring

/-- The actual gather/`ger`/scatter sequence succeeds and changes exactly one full original
matrix block. Its rectangular entries receive the stated rank-one update, every other matrix
entry is retained, and the packed workspace is released. Input factors may overlap the matrix:
their words are read before the final scatter. Empty dimensions are supported. -/
theorem exec_gerMatrixBlock (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (st : St P 𝕜 (OpCount P ι)) (size m n : IExp ℕ) (a : Cell ℕ ℕ)
    (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ) (R : ℕ) (off row col : IExp ℕ)
    (av : 𝕜) (xv : Fin m.eval → 𝕜) (yv : Fin n.eval → 𝕜)
    (M : Matrix (Fin size.eval) (Fin size.eval) 𝕜)
    (hr : row.eval + m.eval ≤ size.eval) (hcol : col.eval + n.eval ≤ size.eval)
    (hM : Holds st.store p R off.eval M) (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i : Fin m.eval, st.store.read p x (xo.eval + i) = some (xv i))
    (hy : ∀ j : Fin n.eval, st.store.read p y (yo.eval + j) = some (yv j)) :
    ∃ (out : St P 𝕜 (OpCount P ι)) (M' : Matrix (Fin size.eval) (Fin size.eval) 𝕜),
      exec I (gerMatrixBlock p size m n a x xo y yo R off row col).run st = some out ∧
      st.store.writeBlock p R off.eval (flatten M') = some out.store ∧
      Holds out.store p R off.eval M' ∧
      (∀ i j, M' (Fin.castLE hr (Fin.natAdd row.eval i))
        (Fin.castLE hcol (Fin.natAdd col.eval j)) =
          M (Fin.castLE hr (Fin.natAdd row.eval i)) (Fin.castLE hcol (Fin.natAdd col.eval j)) +
            av * xv i * star (yv j)) ∧
      ∀ i j, (i.val < row.eval ∨ row.eval + m.eval ≤ i.val ∨
        j.val < col.eval ∨ col.eval + n.eval ≤ j.val) → M' i j = M i j := by
  let Q := fun s => ∃ M' : Matrix (Fin size.eval) (Fin size.eval) 𝕜,
    st.store.writeBlock p R off.eval (flatten M') = some s ∧ Holds s p R off.eval M' ∧
    (∀ i j, M' (Fin.castLE hr (Fin.natAdd row.eval i))
      (Fin.castLE hcol (Fin.natAdd col.eval j)) =
        M (Fin.castLE hr (Fin.natAdd row.eval i)) (Fin.castLE hcol (Fin.natAdd col.eval j)) +
          av * xv i * star (yv j)) ∧
    ∀ i j, (i.val < row.eval ∨ row.eval + m.eval ≤ i.val ∨
      j.val < col.eval ∨ col.eval + n.eval ≤ j.val) → M' i j = M i j
  obtain ⟨out, hex, M', hw, hM', hcoords, houtside⟩ := exists_exec_alloc I p (m * n)
    (fun packed => ((do
      gatherMatrixBlock p m n size R off row col packed 0
      ger p m n a x xo y yo packed 0
      scatterMatrixBlock p m n size packed 0 R off row col) : Builder P ι ℕ ℕ Unit).run)
    st Q (by
      intro σ hσ
      obtain ⟨out, M', he, hw, hM', hc', ho⟩ := exec_rectangleBody I hI hc p st.store σ
        size m n a x xo y yo R off row col av xv yv M hr hcol hM ha hx hy
        (by simpa only [IExp.eval_mul] using hσ)
      exact ⟨out, he, M', hw, hM', hc', ho⟩)
  refine ⟨out, M', ?_, hw, hM', hcoords, houtside⟩
  change exec I (.seq (.alloc p (m * n) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hex

end NLAlib.Computation
