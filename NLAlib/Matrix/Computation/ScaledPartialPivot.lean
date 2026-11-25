/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Fin.Embedding
public import NLAlib.Matrix.Computation.ScaledPivot
public import NLAlib.Matrix.Computation.RowSwap
public import NLAlib.Computation.MatrixStorage

/-!
# Stored scaled partial pivoting

The selected row maximizes the absolute active-column entry divided by its stored scale.
The same row exchange acts on the matrix and the scale vector, so fixed initial row scales
follow the rows. The stored relative scan index is consumed by a bounded binder and replaced
with the absolute chosen row. The first-maximum policy refers to the input before this swap.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.Computation.scaledPartialPivot`: choose and exchange an active row and its scale.

## Main results

* `NLAlib.Computation.exec_scaledPartialPivot`: exact execution, first ratio maximum, matching
  row exchanges and the complete three-block write frame.
* `NLAlib.Computation.executionComposable_scaledPartialPivot`: composition with following code.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Scan the active column relative to its stored scales, consume the relative choice, swap
full matrix rows and the matching scale entries, and record the absolute selected row. A zero
scale has zero score when its active-column entry is zero. No division instruction is used.
[Higham2002, §9.3]. -/
def scaledPartialPivot {P ι VB VI : Type} (tag : P) (n k : IExp VI) (R : VB)
    (off : IExp VI) (scales : VB) (so : IExp VI) (index : Cell VB VI) :
    Builder P ι VB VI Unit := scope do
  argmaxScaledAbs tag (n - k) R (off + k + n * k) scales (so + k) index
  bindIdx tag index (n - k) fun rel => do
    swapRows tag n n R off k (k + .var rel)
    swapRows tag n 1 scales so k (k + .var rel)
    ins (.litIdx tag index (k + .var rel))

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- The scoped scaled pivot operation composes with every following builder. -/
theorem executionComposable_scaledPartialPivot {K : Type} (I : Interp P ι K C) (tag : P)
    (n k : IExp ℕ) (R : ℕ) (off : IExp ℕ) (scales : ℕ) (so : IExp ℕ)
    (index : Cell ℕ ℕ) :
    ExecutionComposable I (scaledPartialPivot tag n k R off scales so index) :=
  executionComposable_single I (fun _ => rfl)

private theorem writeBlocks_pivot {N : ℕ} (tag : P) (initial final : Store P ℝ)
    (R S : ℕ) (off so : ℕ) (index : Cell ℕ ℕ)
    (M : Matrix (Fin N) (Fin N) ℝ) (s : Fin N → ℝ) (r : Fin N)
    (hdis : blockDisjoint (R, off, N * N) (S, so, N) = true)
    (hRI : R ≠ index.buf) (hSI : S ≠ index.buf)
    (hshape : final.shape = initial.shape) (hM : Holds final tag R off M)
    (hs : ∀ i : Fin N, final.read tag S (so + i) = some (s i))
    (hi : final.read tag index.buf index.idx.eval = some (r.val : ℝ))
    (hframe : ∀ q b j, (b ≠ R ∨ j < off ∨ off + N * N ≤ j) →
      (b ≠ S ∨ j < so ∨ so + N ≤ j) →
      (b ≠ index.buf ∨ j < index.idx.eval ∨ index.idx.eval + 1 ≤ j) →
      final.read q b j = initial.read q b j) :
    initial.writeBlocks tag [(R, off, N * N), (S, so, N), (index.buf, index.idx.eval, 1)]
      [flatten M, Array.ofFn s, #[(r.val : ℝ)]] = some final := by
  refine Store.writeBlocks_eq_some_of_read
    (.cons (size_flatten M) (.cons (by simp) (.cons (by simp) .nil))) ?_ hshape ?_ ?_
  · have hd := blockDisjoint_iff.mp hdis
    simp only [Nat.mul_eq_zero, or_self] at hd
    simp [List.pairwise_cons, blockDisjoint, hRI, hSI]
    omega
  · intro k x y hx hy j hj
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst x; subst y
      exact hM.read_flatten j hj
    · rcases k with _ | k
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
        subst x; subst y
        simpa only [Array.getElem?_ofFn, hj, ↓reduceDIte] using hs ⟨j, hj⟩
      · rcases k with _ | k
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst x; subst y
          have hj0 : j = 0 := by simpa using hj
          subst j
          simpa using hi
        · simp at hx
  · intro q b j hj
    exact hframe q b j (hj _ List.mem_cons_self)
      (hj _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hj _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

private theorem holds_scales_column {N : ℕ} {st : Store P ℝ} {tag : P} {S so : ℕ}
    {s : Fin N → ℝ} (hs : ReadsDecoded st (fun _ a => a) tag S so s) :
    Holds st tag S so (fun i (_ : Fin 1) => s i) := by
  intro i j
  obtain ⟨w, hr, hd⟩ := hs i
  have hj : j.val = 0 := by omega
  simpa only [hj, Nat.mul_zero, Nat.add_zero, hd] using hr

private theorem read_scales_column {N : ℕ} {st : Store P ℝ} {tag : P} {S so : ℕ}
    {s : Fin N → ℝ} (hs : Holds st tag S so (fun i (_ : Fin 1) => s i)) (i : Fin N) :
    st.read tag S (so + i) = some (s i) := by
  have hr := hs i (0 : Fin 1)
  simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using hr

private theorem holds_matrix_of_scales_write {N : ℕ} {before after : Store P ℝ}
    {tag : P} {R S off so : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {W : Array ℝ}
    (hA : Holds before tag R off A) (hw : before.writeBlock tag S so W = some after)
    (hsize : W.size = N)
    (hdis : blockDisjoint (R, off, N * N) (S, so, N) = true) :
    Holds after tag R off A := by
  have hd : HoldsDecoded before (fun _ a => a) tag R off A := fun i j => ⟨_, hA i j, rfl⟩
  have hfinal := hd.of_writeBlock hw (fun _ _ => by simpa only [hsize] using hdis)
  intro i j
  obtain ⟨w, hr, he⟩ := hfinal i j
  simpa only [he] using hr

private theorem exec_scaledSwapRecord (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (R : ℕ) (off : IExp ℕ)
    (S : ℕ) (so : IExp ℕ) (index : Cell ℕ ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (s : Fin n.eval → ℝ)
    (hk : k.eval < n.eval) (hA : Holds st.store tag R off.eval A)
    (hs : ReadsDecoded st.store (fun _ a => a) tag S so.eval s)
    (hw : Writable st.store tag index.buf index.idx.eval 1)
    (hdis : blockDisjoint (R, off.eval, n.eval * n.eval) (S, so.eval, n.eval) = true)
    (hRI : R ≠ index.buf) (hSI : S ≠ index.buf)
    (r : Fin (n.eval - k.eval))
    (hread : st.store.read tag index.buf index.idx.eval = some (r.val : ℝ)) :
    let chosen := (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) r
    let τ := Equiv.swap ⟨k.eval, hk⟩ chosen
    ∃ out, exec I (bindIdx tag index (n - k) fun rel => do
        swapRows tag n n R off k (k + .var rel)
        swapRows tag n 1 S so k (k + .var rel)
        ins (.litIdx tag index (k + .var rel))).run st = some out ∧
      out.store.shape = st.store.shape ∧
      Holds out.store tag R off.eval (A.submatrix τ id) ∧
      (∀ i : Fin n.eval, out.store.read tag S (so.eval + i) = some (s (τ i))) ∧
      out.store.read tag index.buf index.idx.eval = some (chosen.val : ℝ) ∧
      ∀ q b j, (b ≠ R ∨ j < off.eval ∨ off.eval + n.eval * n.eval ≤ j) →
        (b ≠ S ∨ j < so.eval ∨ so.eval + n.eval ≤ j) →
        (b ≠ index.buf ∨ j < index.idx.eval ∨ index.idx.eval + 1 ≤ j) →
        out.store.read q b j = st.store.read q b j := by
  let chosen := (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) r
  have hchosenVal : chosen.val = k.eval + r.val :=
    Fin.val_natAdd_castLEEmb_sub k.eval (Nat.sub_le n.eval k.eval) r
  let τ := Equiv.swap ⟨k.eval, hk⟩ chosen
  have hto : I.sem.toNat tag (r.val : ℝ) = some r.val := by
    rw [hI, isExactToNat_exactSem tag r.val]
    simp
  let ready : St P ℝ C := { st with cnt := st.cnt + I.charge (.toNat tag) }
  have hkr : (k + IExp.var r.val).eval < n.eval := by
    simpa only [IExp.eval_add, IExp.eval_var, hchosenVal] using
      chosen.isLt
  have hrFin : (⟨(k + IExp.var r.val).eval, hkr⟩ : Fin n.eval) = chosen := by
    apply Fin.ext
    simp only [IExp.eval_add, IExp.eval_var, hchosenVal]
  obtain ⟨matSwap, W₁, hr₂, hw₂, hA₂⟩ := exec_swapRows I tag ready n n R off k
    (k + IExp.var r.val) A hk hkr hA
  rw [hrFin] at hA₂
  have hs₂ : ReadsDecoded matSwap.store (fun _ a => a) tag S so.eval s :=
    hs.of_writeBlock hw₂ (fun _ _ => by
      simp only [Array.size_ofFn, blockDisjoint_iff]
      have hd := blockDisjoint_iff.mp hdis
      dsimp only at hd ⊢
      omega)
  let scaleMatrix : Matrix (Fin n.eval) (Fin 1) ℝ := fun i _ => s i
  have hSM : Holds matSwap.store tag S so.eval scaleMatrix := holds_scales_column hs₂
  obtain ⟨scaleSwap, W₂, hr₃, hw₃, hSM₃⟩ := exec_swapRows I tag matSwap n 1 S so k
    (k + IExp.var r.val) scaleMatrix hk hkr hSM
  rw [hrFin] at hSM₃
  change Holds scaleSwap.store tag S so.eval (scaleMatrix.submatrix τ id) at hSM₃
  have hW₂size : (Array.ofFn W₂).size = n.eval := by
    have he : (Array.ofFn W₂).size = n.eval * (1 : IExp ℕ).eval := Array.size_ofFn
    change (Array.ofFn W₂).size = n.eval * 1 at he
    simpa only [Nat.mul_one] using he
  have hA₃ := holds_matrix_of_scales_write hA₂ hw₃ hW₂size hdis
  have hshape : scaleSwap.store.shape = st.store.shape :=
    (Store.shape_of_writeBlock_eq_some hw₃).trans
      (Store.shape_of_writeBlock_eq_some hw₂)
  obtain ⟨len, hlen, hlt⟩ := hw 0 (by omega)
  obtain ⟨finalStore, hf⟩ := Store.exists_write_eq_some_of_getElem?_shape (chosen.val : ℝ)
    (hshape.symm ▸ hlen) (by simpa using hlt)
  let out : St P ℝ C := { scaleSwap with
    store := finalStore
    cnt := scaleSwap.cnt + I.charge (.lit tag) }
  have hAout : Holds out.store tag R off.eval (A.submatrix τ id) :=
    hA₃.write hf (fun he => (hRI he.symm).elim)
  have hsout (i : Fin n.eval) : out.store.read tag S (so.eval + i) = some (s (τ i)) :=
    (Store.read_of_write_eq_some_of_ne hf (Or.inl hSI)).trans (read_scales_column hSM₃ i)
  have hiout : out.store.read tag index.buf index.idx.eval = some (chosen.val : ℝ) :=
    Store.read_of_write_eq_some hf
  refine ⟨out, ?_, (Store.shape_of_write_eq_some hf).trans hshape, hAout, hsout, hiout, ?_⟩
  · change exec I (.seq (.bindIdx tag index (n - k) _) .skip) st = some out
    rw [exec_seq_skip, exec_bindIdx_of_read I hread hto (by
      change r.val ≤ n.eval - k.eval; exact Nat.le_of_lt r.isLt)]
    rw [exec_run_bind I (b := swapRows tag n n R off k (k + IExp.var r.val))
      (fun _ => rfl), hr₂, Option.bind_some,
      exec_run_bind I (b := swapRows tag n 1 S so k (k + IExp.var r.val))
      (fun _ => rfl), hr₃, Option.bind_some]
    change exec I (.seq (.instr (.litIdx tag index (k + IExp.var r.val))) .skip) scaleSwap = _
    rw [exec_seq_instr_litIdx I
      (by simp [hI, exactSem, hchosenVal, IExp.eval]) hf,
      exec_skip]
  · intro q b j hR hS hIdx
    rw [Store.read_of_write_eq_some_of_ne hf (by omega),
      Store.read_of_writeBlock_eq_some_of_ne hw₃ (by simpa only [hW₂size] using hS),
      Store.read_of_writeBlock_eq_some_of_ne hw₂ (by simpa only [Array.size_ofFn] using hR)]

private theorem scaled_suffix_policy {N k : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (s : Fin N → ℝ) (hk : k < N)
    (htail : N - k ≤ N) (r : Fin (N - k))
    (hmax : ∀ j : Fin (N - k),
      |A (Fin.natAdd_castLEEmb (htail) j) ⟨k, hk⟩| /
          s (Fin.natAdd_castLEEmb (htail) j) ≤
        |A (Fin.natAdd_castLEEmb (htail) r) ⟨k, hk⟩| /
          s (Fin.natAdd_castLEEmb (htail) r))
    (hfirst : ∀ j : Fin (N - k), j < r →
      |A (Fin.natAdd_castLEEmb (htail) j) ⟨k, hk⟩| /
          s (Fin.natAdd_castLEEmb (htail) j) <
        |A (Fin.natAdd_castLEEmb (htail) r) ⟨k, hk⟩| /
          s (Fin.natAdd_castLEEmb (htail) r)) :
    (∀ i, k ≤ i.val → |A i ⟨k, hk⟩| / s i ≤
      |A (Fin.natAdd_castLEEmb (htail) r) ⟨k, hk⟩| /
        s (Fin.natAdd_castLEEmb (htail) r)) ∧
    (∀ i, k ≤ i.val → i < Fin.natAdd_castLEEmb (htail) r →
      |A i ⟨k, hk⟩| / s i <
        |A (Fin.natAdd_castLEEmb (htail) r) ⟨k, hk⟩| /
          s (Fin.natAdd_castLEEmb (htail) r)) := by
  constructor
  · intro i hi
    let j : Fin (N - k) := ⟨i.val - k, by have := i.isLt; omega⟩
    have hj : Fin.natAdd_castLEEmb (htail) j = i := by
      apply Fin.ext
      rw [Fin.val_natAdd_castLEEmb_sub]
      exact Nat.add_sub_of_le hi
    simpa only [hj] using hmax j
  · intro i hi hir
    let j : Fin (N - k) := ⟨i.val - k, by have := i.isLt; omega⟩
    have hj : Fin.natAdd_castLEEmb (htail) j = i := by
      apply Fin.ext
      rw [Fin.val_natAdd_castLEEmb_sub]
      exact Nat.add_sub_of_le hi
    have hjr : j < r := by
      change i.val - k < r.val
      change i.val < (Fin.natAdd_castLEEmb (htail) r).val at hir
      rw [Fin.val_natAdd_castLEEmb_sub] at hir
      omega
    simpa only [hj] using hfirst j hjr

/-- Exact scaled partial pivoting succeeds for every nonempty active suffix whose scales are
nonnegative and whose zero-scale active entries vanish. It exchanges the same matrix and scale
rows and records the absolute chosen index. The chosen row is the first largest ratio in the
input suffix; the final active column retains zero-scale compatibility. The matrix and scale
windows may share a buffer when disjoint; the index occupies a separate buffer. The three
specified output blocks are the entire net store change. No nonsingularity or bound on
unweighted elimination multipliers is asserted. [Higham2002, §9.3]. -/
theorem exec_scaledPartialPivot (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (R : ℕ) (off : IExp ℕ)
    (S : ℕ) (so : IExp ℕ) (index : Cell ℕ ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (s : Fin n.eval → ℝ)
    (hk : k.eval < n.eval) (hA : Holds st.store tag R off.eval A)
    (hs : ReadsDecoded st.store (fun _ a => a) tag S so.eval s)
    (hscale : ∀ i, 0 ≤ s i)
    (hcompat : ∀ i, k.eval ≤ i.val → s i = 0 → A i ⟨k.eval, hk⟩ = 0)
    (hw : Writable st.store tag index.buf index.idx.eval 1)
    (hdis : blockDisjoint (R, off.eval, n.eval * n.eval) (S, so.eval, n.eval) = true)
    (hRI : R ≠ index.buf) (hSI : S ≠ index.buf) :
    ∃ (out : St P ℝ C) (chosen : Fin n.eval),
      let τ := Equiv.swap ⟨k.eval, hk⟩ chosen
      exec I (scaledPartialPivot tag n k R off S so index).run st = some out ∧
      k.eval ≤ chosen.val ∧
      st.store.writeBlocks tag
        [(R, off.eval, n.eval * n.eval), (S, so.eval, n.eval), (index.buf, index.idx.eval, 1)]
        [flatten (A.submatrix τ id), Array.ofFn (fun i => s (τ i)), #[(chosen.val : ℝ)]] =
          some out.store ∧
      Holds out.store tag R off.eval (A.submatrix τ id) ∧
      ReadsDecoded out.store (fun _ a => a) tag S so.eval (fun i => s (τ i)) ∧
      out.store.read tag index.buf index.idx.eval = some (chosen.val : ℝ) ∧
      (∀ i, k.eval ≤ i.val → |A i ⟨k.eval, hk⟩| / s i ≤
        |A chosen ⟨k.eval, hk⟩| / s chosen) ∧
      (∀ i, k.eval ≤ i.val → i < chosen → |A i ⟨k.eval, hk⟩| / s i <
        |A chosen ⟨k.eval, hk⟩| / s chosen) ∧
      ∀ i, k.eval ≤ i.val → s (τ i) = 0 → (A.submatrix τ id) i ⟨k.eval, hk⟩ = 0 := by
  let x : Fin (n.eval - k.eval) → ℝ := fun j =>
    A ((Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) j) ⟨k.eval, hk⟩
  let ss : Fin (n.eval - k.eval) → ℝ := fun j =>
    s ((Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) j)
  have hx : ReadsDecoded st.store (fun _ a => a) tag R (off + k + n * k).eval x := by
    intro j
    refine ⟨_, ?_, rfl⟩
    simpa only [x, Fin.val_natAdd_castLEEmb_sub, IExp.eval_add, IExp.eval_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
        hA ((Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) j) ⟨k.eval, hk⟩
  have hss : ReadsDecoded st.store (fun _ a => a) tag S (so + k).eval ss := by
    intro j
    obtain ⟨w, hr, hd⟩ := hs ((Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) j)
    exact ⟨w, by simpa only [Fin.val_natAdd_castLEEmb_sub, IExp.eval_add, Nat.add_assoc] using
      hr, hd⟩
  obtain ⟨scanned, r, hr₁, hw₁, hmax, hfirst⟩ := exec_argmaxScaledAbs I hI tag st (n - k)
    (Nat.sub_pos_of_lt hk) x ss R S (off + k + n * k) (so + k) index hx hss
    (fun j => hscale _) (fun j => by
      change Fin (n.eval - k.eval) at j
      exact hcompat _ (by rw [Fin.val_natAdd_castLEEmb_sub]; omega)) hw hRI hSI
  change Fin (n.eval - k.eval) at r
  let chosen := (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) r
  have hchosenVal : chosen.val = k.eval + r.val :=
    Fin.val_natAdd_castLEEmb_sub k.eval (Nat.sub_le n.eval k.eval) r
  let τ := Equiv.swap ⟨k.eval, hk⟩ chosen
  have hchosen : k.eval ≤ chosen.val := by
    rw [hchosenVal]
    exact Nat.le_add_right _ _
  have hA₁ : Holds scanned.store tag R off.eval A := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hRI)).trans (hA i j)
  have hs₁ : ReadsDecoded scanned.store (fun _ a => a) tag S so.eval s :=
    hs.of_writeBlock hw₁ (fun _ _ => by simp [blockDisjoint, hSI])
  have hread : scanned.store.read tag index.buf index.idx.eval = some (r.val : ℝ) := by
    simpa using Store.read_of_writeBlock_eq_some_of_lt (j := 0) hw₁ (by simp)
  obtain ⟨out, hrSwap, hshape, hAout, hsout, hiout, hframe⟩ := exec_scaledSwapRecord I hI
    tag scanned n k R off S so index A s hk hA₁ hs₁
    (hw.of_shape_eq (Store.shape_of_writeBlock_eq_some hw₁)) hdis hRI hSI r hread
  have hwrite := writeBlocks_pivot tag st.store out.store R S off.eval so.eval index
    (A.submatrix τ id) (fun i => s (τ i)) chosen hdis hRI hSI
    (hshape.trans (Store.shape_of_writeBlock_eq_some hw₁)) hAout hsout hiout (by
      intro q b j hR hS hIdx
      rw [hframe q b j hR hS hIdx,
        Store.read_of_writeBlock_eq_some_of_ne hw₁ (by simp only [Array.size_singleton]; omega)])
  obtain ⟨hmaxAbs, hfirstAbs⟩ := scaled_suffix_policy A s hk (Nat.sub_le _ _) r
    (fun j => hmax j) (fun j hj => hfirst j hj)
  refine ⟨out, chosen, ?_, hchosen, hwrite, hAout,
    fun i => ⟨_, hsout i, rfl⟩, hiout, hmaxAbs, hfirstAbs, ?_⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip, exec_run_bind I
      (b := argmaxScaledAbs tag (n - k) R (off + k + n * k) S (so + k) index)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hrSwap
  · intro i hi hz
    apply hcompat (τ i) ?_ hz
    by_cases hik : i = ⟨k.eval, hk⟩
    · subst i; simpa only [τ, Equiv.swap_apply_left] using hchosen
    · by_cases hir : i = chosen
      · subst i; simp only [τ, Equiv.swap_apply_right]; exact le_rfl
      · simpa only [τ, Equiv.swap_apply_of_ne_of_ne hik hir] using hi

end NLAlib.Computation
