/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SchurUpdate
public import NLAlib.Matrix.Computation.MatrixBlockRankOne
public import NLAlib.Matrix.Factorizations.LUBlocked

/-!
# Panel-only Schur updates for blocked LU

A saved pivot row and column feed two packed rank-one updates. The rectangles comprise the
remaining panel columns and its trailing block rows. The bottom-right square is left for one
GEMM-backed update after the panel is complete.

## Main definitions

* `NLAlib.Computation.panelSchurStep`: the actual two-rectangle panel update.

## Main results

* `NLAlib.Computation.executionComposable_panelSchurStep`: scoped-workspace composition.
* `NLAlib.Computation.exec_panelSchurStep`: actual exact two-rectangle update and full frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Eliminate one nonzero panel pivot using two packed `ger` calls and exact rectangular
copies. Save the pivot row and column before either matrix write. The trailing square
beginning at `stop` is deferred to the block update. [GolubVanLoan2013, §3.2]. -/
def panelSchurStep {P ι VB VI : Type} (p : P) (n k stop : IExp VI) (R : VB)
    (off : IExp VI) : Builder P ι VB VI Unit := scope do
  let work ← alloc p (2 * n + 1)
  prepareSchur p n R work off k
  gerMatrixBlock p n (n - k) (stop - k) ⟨work, 2 * n⟩ work k work (n + k) R off k k
  gerMatrixBlock p n (stop - k) (n - stop) ⟨work, 2 * n⟩ work k work (n + stop) R off k stop

variable {P ι : Type} [DecidableEq P]

/-- The packed rectangle buffers and saved pivot workspace are released before the
continuation, independently of arithmetic interpretation. -/
theorem executionComposable_panelSchurStep {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (p : P) (n k stop : IExp ℕ) (R : ℕ) (off : IExp ℕ) :
    ExecutionComposable I (panelSchurStep p n k stop R off) :=
  executionComposable_single I (fun _ => rfl)

private theorem exec_panelRectangle
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hcharge : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (size m n : IExp ℕ) (R work : ℕ)
    (off row col : IExp ℕ) (source current : Matrix (Fin size.eval) (Fin size.eval) ℝ)
    (pivot : Fin size.eval) (hr : row.eval + m.eval ≤ size.eval)
    (hc : col.eval + n.eval ≤ size.eval) (hcur : Holds st.store p R off.eval current)
    (hcol : ∀ i : Fin size.eval, st.store.read p work i = some (source i pivot))
    (hrow : ∀ j : Fin size.eval, st.store.read p work (size.eval + j) = some (source pivot j))
    (hcoeff : st.store.read p work (2 * size.eval) = some ((-1) / source pivot pivot)) :
    ∃ out, exec I (gerMatrixBlock p size m n ⟨work, 2 * size⟩ work row work (size + col)
      R off row col).run st = some out ∧
      st.store.writeBlock p R off.eval
        (flatten (luPanelRectangle source current pivot row.eval col.eval m.eval n.eval)) =
        some out.store ∧
      Holds out.store p R off.eval
        (luPanelRectangle source current pivot row.eval col.eval m.eval n.eval) := by
  let xv := fun i : Fin m.eval => source (Fin.castLE hr (Fin.natAdd row.eval i)) pivot
  let yv := fun j : Fin n.eval => source pivot (Fin.castLE hc (Fin.natAdd col.eval j))
  obtain ⟨out, M', hex, hw, hM', hcoords, houtside⟩ := exec_gerMatrixBlock I hI hcharge p st
    size m n ⟨work, 2 * size⟩ work row work (size + col) R off row col
    ((-1) / source pivot pivot) xv yv current hr hc hcur
    (by simpa only [IExp.eval_mul, IExp.eval_ofNat] using hcoeff)
    (fun i => by
      simpa only [Fin.val_castLE, Fin.val_natAdd] using
        (hcol (Fin.castLE hr (Fin.natAdd row.eval i))))
    (fun j => by
      simpa only [IExp.eval_add, Fin.val_castLE, Fin.val_natAdd, Nat.add_assoc] using
        (hrow (Fin.castLE hc (Fin.natAdd col.eval j))))
  have heq : M' = luPanelRectangle source current pivot row.eval col.eval m.eval n.eval := by
    apply eq_luPanelRectangle_of_coordinates source current M' pivot
      row.eval col.eval m.eval n.eval hr hc ?_ houtside
    intro i j
    rw [hcoords]
    dsimp only [xv, yv]
    simp only [star_trivial]
    ring
  exact ⟨out, hex, by simpa only [heq] using hw, by simpa only [heq] using hM'⟩

private theorem exec_panelBody
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n k stop : IExp ℕ)
    (R : ℕ) (off : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hks : k.eval ≤ stop.eval) (hs : stop.eval ≤ n.eval)
    (hM : Holds initial p R off.eval M) (hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ ≠ 0)
    (hst : st.store = initial.push (p, Array.replicate (2 * n.eval + 1) none)) :
    ∃ out, exec I (do
      prepareSchur p n R initial.size off k
      gerMatrixBlock p n (n - k) (stop - k) ⟨initial.size, 2 * n⟩
        initial.size k initial.size (n + k) R off k k
      gerMatrixBlock p n (stop - k) (n - stop) ⟨initial.size, 2 * n⟩
        initial.size k initial.size (n + stop) R off k stop).run st = some out ∧
      initial.writeBlock p R off.eval (flatten (luPanelStep M ⟨k.eval, hk⟩ stop.eval)) =
        some out.store.pop ∧
      Holds out.store.pop p R off.eval (luPanelStep M ⟨k.eval, hk⟩ stop.eval) := by
  let r : Fin n.eval := ⟨k.eval, hk⟩
  have hRb : R < initial.size := Store.lt_size_of_read_eq_some (hM r r)
  have hMp : Holds st.store p R off.eval M := fun i j => by
    rw [hst, Store.read_push_of_lt hRb]; exact hM i j
  obtain ⟨prepared, hex₀, hprep⟩ := exec_prepareSchur I hI p st n R initial.size off k
    M hk hMp (Nat.ne_of_lt hRb) (hst ▸ Store.getElem?_shape_push_size initial p _) hp
  let M₁ := luPanelRectangle M M r k.eval k.eval (n.eval - k.eval) (stop.eval - k.eval)
  obtain ⟨first, hex₁, hw₁, hM₁⟩ := exec_panelRectangle I hI hc p prepared n (n - k) (stop - k)
    R initial.size off k k M M r (by simp only [IExp.eval_sub]; omega)
    (by simp only [IExp.eval_sub]; omega)
    (fun i j => (hprep.frame p R _ (Nat.ne_of_lt hRb)).trans (hMp i j))
    hprep.col hprep.row hprep.coeff
  obtain ⟨out, hex₂, hw₂, hM₂⟩ := exec_panelRectangle I hI hc p first n (stop - k) (n - stop)
    R initial.size off k stop M M₁ r (by simp only [IExp.eval_sub]; omega)
    (by simp only [IExp.eval_sub]; omega) hM₁
    (fun i => (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl (Nat.ne_of_gt hRb))).trans
      (hprep.col i))
    (fun j => (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl (Nat.ne_of_gt hRb))).trans
      (hprep.row j))
    ((Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl (Nat.ne_of_gt hRb))).trans hprep.coeff)
  have heq : luPanelRectangle M M₁ r k.eval stop.eval (stop.eval - k.eval)
      (n.eval - stop.eval) = luPanelStep M r stop.eval :=
    luPanelRectangle_twice M r stop.eval hks hs
  have hMfinal : Holds out.store p R off.eval (luPanelStep M r stop.eval) := by
    simpa only [IExp.eval_sub, heq] using hM₂
  have hf : Store.BlockFrame st.store p initial.size R off.eval (n.eval * n.eval)
      prepared.store (fun t => prepared.store.read p R (off.eval + t)) :=
    ⟨hprep.shape, fun q b t hb _ => hprep.frame q b t hb, fun _ _ => rfl⟩
  have hf₁ := hf.writeBlock (off := 0) (by simpa only [Nat.add_zero] using hw₁)
    (by simp only [size_flatten, Nat.zero_add]; exact le_rfl)
  have hf₂ := hf₁.writeBlock (off := 0) (by simpa only [Nat.add_zero] using hw₂)
    (by simp only [size_flatten, Nat.zero_add]; exact le_rfl)
  have hframe := (hst ▸ hf₂).congr (fun t ht => (hf₂.2.2 t ht).symm)
  have hcap : Writable initial p R off.eval (flatten (luPanelStep M r stop.eval)).size := by
    simpa only [size_flatten] using hM.writable
  obtain ⟨target, htarget⟩ := hcap.exists_writeBlock
  have hpop := hframe.pop_eq htarget (size_flatten _) (fun t ht => hMfinal.read_flatten t ht)
  have hsize : out.store.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hframe.1
  refine ⟨out, ?_, hpop ▸ htarget, ?_⟩
  · rw [executionComposable_prepareSchur I p n R initial.size off k,
      hex₀, Option.bind_some, exec_run_bind I
        (b := gerMatrixBlock p n (n - k) (stop - k) ⟨initial.size, 2 * n⟩
          initial.size k initial.size (n + k) R off k k) (fun _ => rfl),
      hex₁, Option.bind_some]
    exact hex₂
  · intro i j
    rw [Store.read_pop_of_lt (by omega)]
    exact hMfinal i j

/-- The actual panel pivot succeeds under exact semantics and a nonzero diagonal, updates
precisely its two panel rectangles, retains the trailing square, and releases every workspace.
Its sole net store effect is one packed full-matrix write. [GolubVanLoan2013, §3.2]. -/
theorem exec_panelSchurStep (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n k stop : IExp ℕ) (R : ℕ) (off : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hks : k.eval ≤ stop.eval) (hs : stop.eval ≤ n.eval) (hM : Holds st.store p R off.eval M)
    (hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ ≠ 0) :
    ∃ out, exec I (panelSchurStep p n k stop R off).run st = some out ∧
      st.store.writeBlock p R off.eval (flatten (luPanelStep M ⟨k.eval, hk⟩ stop.eval)) =
        some out.store ∧
      Holds out.store p R off.eval (luPanelStep M ⟨k.eval, hk⟩ stop.eval) := by
  let Q := fun s => st.store.writeBlock p R off.eval
      (flatten (luPanelStep M ⟨k.eval, hk⟩ stop.eval)) = some s ∧
    Holds s p R off.eval (luPanelStep M ⟨k.eval, hk⟩ stop.eval)
  obtain ⟨out, hex, hw, hout⟩ := exists_exec_alloc I p (2 * n + 1)
    (fun work => ((do
      prepareSchur p n R work off k
      gerMatrixBlock p n (n - k) (stop - k) ⟨work, 2 * n⟩ work k work (n + k) R off k k
      gerMatrixBlock p n (stop - k) (n - stop) ⟨work, 2 * n⟩
        work k work (n + stop) R off k stop) : Builder P ι ℕ ℕ Unit).run) st Q (by
      intro σ hσ
      exact exec_panelBody I hI hc p st.store σ n k stop R off M hk hks hs hM hp
        (by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat] using hσ))
  refine ⟨out, ?_, hw, hout⟩
  change exec I (.seq (.alloc p (2 * n + 1) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hex

end NLAlib.Computation
