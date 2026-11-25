/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.StridedPivotScan

/-!
# Stored diagonal pivot selection

The active diagonal is a strided vector with stride one greater than the matrix order.
Its first magnitude maximum is recorded as an absolute matrix index.

## Main results

* `NLAlib.Computation.exec_diagonalPivotChoice`: actual stable diagonal selection and frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Record the first largest-magnitude active diagonal entry. The index is absolute, and
the input matrix remains unchanged when the index occupies another buffer. -/
def diagonalPivotChoice {P ι VB VI : Type} (tag : P) (n k : IExp VI) (A : VB)
    (off : IExp VI) (index : Cell VB VI) : Builder P ι VB VI Unit := scope do
  argmaxStridedAbs tag (n - k) A (off + (n + 1) * k) (n + 1) index
  bindIdx tag index (n - k) fun rel => ins (.litIdx tag index (k + .var rel))

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- Diagonal selection releases every temporary before the following builder. -/
theorem executionComposable_diagonalPivotChoice (I : Interp P ι ℝ C) (tag : P)
    (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ) (index : Cell ℕ ℕ) :
    ExecutionComposable I (diagonalPivotChoice tag n k A off index) :=
  executionComposable_single I (fun _ => rfl)

private theorem exec_record (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (index : Cell ℕ ℕ)
    (rel : Fin (n.eval - k.eval))
    (hread : st.store.read tag index.buf index.idx.eval = some (rel.val : ℝ)) :
    ∃ out, exec I (bindIdx tag index (n - k) fun r =>
      ins (.litIdx tag index (k + .var r))).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[(k.eval + rel.val : ℕ)] =
        some out.store := by
  obtain ⟨s, hs⟩ := Store.exists_write_eq_some_of_read_eq_some
    (v := ((k.eval + rel.val : ℕ) : ℝ)) hread
  let ready : St P ℝ C := { st with cnt := st.cnt + I.charge (.toNat tag) }
  let out : St P ℝ C :=
    { ready with store := s, cnt := ready.cnt + I.charge (.lit tag) }
  refine ⟨out, ?_, ?_⟩
  · change exec I (.seq (.bindIdx tag index (n - k) _) .skip) st = _
    rw [exec_seq_skip, exec_bindIdx_of_read I hread
      (by simp [hI, exactSem]) rel.isLt.le]
    change exec I (.seq (.instr (.litIdx tag index (k + .var rel.val))) .skip) ready = _
    rw [exec_seq_instr_litIdx I (st := ready) (e := k + .var rel.val)
      (by simp [hI, exactSem]) hs, exec_skip]
  · simpa [Store.writeBlock, out] using hs

/-- Exact diagonal selection succeeds on every nonempty active suffix. The sole net write
is the absolute selected index, the matrix is retained, and ties choose the earliest row.
No division, square root or nonzero-pivot premise is used. -/
theorem exec_diagonalPivotChoice (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ)
    (index : Cell ℕ ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : Holds st.store tag A off.eval M)
    (hw : Writable st.store tag index.buf index.idx.eval 1) (hAI : A ≠ index.buf) :
    ∃ (out : St P ℝ C) (r : Fin n.eval),
      exec I (diagonalPivotChoice tag n k A off index).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[(r.val : ℝ)] = some out.store ∧
      k.eval ≤ r.val ∧ Holds out.store tag A off.eval M ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → |M i i| ≤ |M r r|) ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → i < r → |M i i| < |M r r|) := by
  let emb := Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)
  let x : Fin (n.eval - k.eval) → ℝ := fun i => M (emb i) (emb i)
  have hemb (i : Fin (n.eval - k.eval)) : (emb i).val = k.eval + i.val :=
    Fin.val_natAdd_castLEEmb_sub _ _ _
  have h := hI ▸ (isRelErrSem_exactSem (P := P))
  obtain ⟨mid, w, rel, hr₁, hw₁, hd, hm, hf⟩ := h.exec_argmaxStridedAbs I (.const (n.eval - k.eval))
    (hI ▸ isIndexExactSem_exactSem _) (Nat.sub_pos_of_lt hk) tag st x A
    (off + (n + 1) * k) (n + 1) index (by
      intro i
      change Fin (n.eval - k.eval) at i
      refine ⟨x i, ?_, rfl⟩
      simpa only [x, hemb, IExp.eval_add, IExp.eval_mul,
        IExp.eval_one, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hM (emb i) (emb i)) hw
  change Fin (n.eval - k.eval) at rel
  have hr₁' : exec I (argmaxStridedAbs tag (n - k) A
      (off + (n + 1) * k) (n + 1) index).run st = some mid :=
    (exec_eq_of_normIdx_eq I
      (s := (argmaxStridedAbs tag (n - k) A (off + (n + 1) * k) (n + 1) index).run)
      (s' := (argmaxStridedAbs tag (.const (n.eval - k.eval)) A
        (off + (n + 1) * k) (n + 1) index).run) rfl st).trans hr₁
  have hrd : mid.store.read tag index.buf index.idx.eval = some (rel.val : ℝ) := by
    simpa [hd] using
      (Store.read_of_writeBlock_eq_some_of_lt hw₁ (j := 0) (by simp))
  obtain ⟨out, hr₂, hw₂⟩ := exec_record I hI tag mid n k index rel hrd
  change mid.store.writeBlock tag index.buf index.idx.eval
    #[((k.eval + rel.val : ℕ) : ℝ)] = some out.store at hw₂
  have hs : st.store.writeBlock tag index.buf index.idx.eval #[((emb rel).val : ℝ)] =
      some out.store := by
    rw [hemb]
    exact Store.writeBlock_writeBlock_self hw₁ hw₂ (by simp)
  refine ⟨out, emb rel, ?_, hs, ?_, ?_, ?_, ?_⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip, exec_run_bind I
      (b := argmaxStridedAbs tag (n - k) A (off + (n + 1) * k) (n + 1) index)
      (fun _ => rfl), hr₁', Option.bind_some]
    exact hr₂
  · rw [hemb]; omega
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl hAI)]
    exact hM i j
  · intro i hi
    let j : Fin (n.eval - k.eval) := ⟨i.val - k.eval, by omega⟩
    have he : emb j = i := by
      apply Fin.ext
      rw [hemb]
      dsimp only [j]
      omega
    simpa only [x, he] using hm j
  · intro i hi hir
    let j : Fin (n.eval - k.eval) := ⟨i.val - k.eval, by omega⟩
    have he : emb j = i := by
      apply Fin.ext
      rw [hemb]
      dsimp only [j]
      omega
    have hj : j < rel := by
      have hir' := Fin.lt_def.mp hir
      rw [hemb] at hir'
      change i.val - k.eval < rel.val
      omega
    simpa only [x, he] using hf j hj

end NLAlib.Computation
