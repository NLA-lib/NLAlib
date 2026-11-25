/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Computation.MatrixStorage
public import NLAlib.Computation.IndexBinder
public import NLAlib.Computation.BLAS.Frames
public import NLAlib.Matrix.Computation.SchurUpdate
public import NLAlib.Matrix.Factorizations.LUEntries

/-!
# Stored unpivoted LU factorization

The executable factorization copies the input into a scoped Schur matrix, materializes each
column of the unit lower factor and row of the upper factor, then invokes stored elimination.
Every nonzero pivot of the mathematical elimination sequence suffices for exact execution.
The two output blocks may be uninitialized, the offsets are arbitrary, and empty matrices are
valid. Exact index literals in two scoped control cells select the triangular cases; this adds
quadratic control work and makes no claim of optimal operation counts.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.Computation.luColumnEntry`: materialize a single lower-column and upper-row entry.
* `NLAlib.Computation.luColumn`: materialize the pivot column and row.
* `NLAlib.Computation.luFactor`: the complete stored unpivoted factorization.
* `NLAlib.Computation.LUColumn.replaceEntry`: one coordinate replacement.
* `NLAlib.Computation.LUColumn.columnPrefix`, `NLAlib.Computation.LUColumn.rowPrefix`:
  shared intermediate matrices while materializing a pivot column and row.

## Main results

* `NLAlib.Computation.run_luColumnEntry`: shared instruction form of one column entry.
* `NLAlib.Computation.exec_luColumn`: exact execution and the two factor block writes.
* `NLAlib.Computation.exec_luFactor`: exact execution, factorization and retained input.
* `NLAlib.Computation.executionComposable_luColumn`,
  `NLAlib.Computation.executionComposable_luFactor`: composition with following routines.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Materialize one entry of the lower pivot column and upper pivot row, using control cell
one for the pivot index and cell zero for the current index. The Schur matrix is read only. -/
def luColumnEntry {P ι VB VI : Type} (p : P) (n k i : IExp VI)
    (S L U ctrl : VB) (so lo uo : IExp VI) : Builder P ι VB VI Unit := do
  ins (.litIdx p ⟨ctrl, 0⟩ i)
  ifThenElse p .lt ⟨ctrl, 0⟩ ⟨ctrl, 1⟩
    (do
      ins (.lit p ⟨L, lo + i + n * k⟩ 0)
      ins (.lit p ⟨U, uo + k + n * i⟩ 0))
    (do
      ifThenElse p .eq ⟨ctrl, 0⟩ ⟨ctrl, 1⟩
        (ins (.lit p ⟨L, lo + i + n * k⟩ 1))
        (ins (.bin p .div ⟨L, lo + i + n * k⟩
          ⟨S, so + i + n * k⟩ ⟨S, so + k + n * k⟩))
      ins (.copy p ⟨U, uo + k + n * i⟩ ⟨S, so + k + n * i⟩))

/-- The instruction form of a single LU column entry, shared by exact and rounded execution
proofs. This equation is independent of scalar arithmetic and both variable carriers. -/
theorem run_luColumnEntry {P ι VB VI : Type} (p : P) (n k i : IExp VI)
    (S L U ctrl : VB) (so lo uo : IExp VI) :
    (luColumnEntry (ι := ι) p n k i S L U ctrl so lo uo).run =
      .seq (.instr (.litIdx p ⟨ctrl, 0⟩ i))
        (.seq (.ite p .lt ⟨ctrl, 0⟩ ⟨ctrl, 1⟩
          (.seq (.instr (.lit p ⟨L, lo + i + n * k⟩ 0))
            (.seq (.instr (.lit p ⟨U, uo + k + n * i⟩ 0)) .skip))
          (.seq (.ite p .eq ⟨ctrl, 0⟩ ⟨ctrl, 1⟩
            (.seq (.instr (.lit p ⟨L, lo + i + n * k⟩ 1)) .skip)
            (.seq (.instr (.bin p .div ⟨L, lo + i + n * k⟩
              ⟨S, so + i + n * k⟩ ⟨S, so + k + n * k⟩)) .skip))
            (.seq (.instr (.copy p ⟨U, uo + k + n * i⟩ ⟨S, so + k + n * i⟩)) .skip)))
          .skip) := rfl

/-- Materialize the lower factor's pivot column and the upper factor's pivot row from a stored
Schur matrix. Above the lower diagonal and left of the upper diagonal the entries are zero;
the lower diagonal is one. Two scoped exact index words select these cases. No Schur update
is performed. [GolubVanLoan2013, §3.2]. -/
def luColumn {P ι VB VI : Type} (p : P) (n k : IExp VI) (S L U : VB)
    (so lo uo : IExp VI) : Builder P ι VB VI Unit := scope do
  let ctrl ← alloc p 2
  ins (.litIdx p ⟨ctrl, 1⟩ k)
  forRange n fun i => luColumnEntry p n k (.var i) S L U ctrl so lo uo

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The scoped LU column materialization composes with a following program. -/
theorem executionComposable_luColumn (I : Interp P ι K C) (p : P) (n k : IExp ℕ)
    (S L U : ℕ) (so lo uo : IExp ℕ) :
    ExecutionComposable I (luColumn p n k S L U so lo uo) :=
  executionComposable_single I (fun _ => rfl)

private noncomputable def lowerEntry {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (k i : Fin N) : ℝ :=
  if i < k then 0 else if i = k then 1 else M i k / M k k

private def upperEntry {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (k i : Fin N) : ℝ :=
  if i < k then 0 else M k i

namespace LUColumn

/-- Replace one entry of a square matrix by a word of the same arbitrary carrier. -/
def replaceEntry {N : ℕ} (M : Matrix (Fin N) (Fin N) K) (r c : Fin N) (v : K) :
    Matrix (Fin N) (Fin N) K := fun i j => if i = r ∧ j = c then v else M i j

/-- One successful coordinate write preserves the packed matrix predicate
with that entry replaced. -/
theorem holds_replaceEntry {N : ℕ} {s s' : Store P K} {p : P} {buf off : ℕ}
    {M : Matrix (Fin N) (Fin N) K} {r c : Fin N} {v : K}
    (hM : Holds s p buf off M)
    (hw : s.write p buf (off + r + N * c) v = some s') :
    Holds s' p buf off (replaceEntry M r c v) := by
  intro i j
  have heq : off + i + N * j = off + r + N * c ↔ i = r ∧ j = c := by
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_cancel_iff,
      Nat.add_mul_eq_add_mul_iff_of_lt i.isLt r.isLt]
    simp only [Fin.ext_iff]
  by_cases h : i = r ∧ j = c
  · rw [heq.mpr h, Store.read_of_write_eq_some hw]
    simp [replaceEntry, h.1, h.2]
  · rw [Store.read_of_write_eq_some_of_ne hw (Or.inr (mt heq.mp h)), hM]
    simp only [replaceEntry, h, if_false]

/-- Materialize the first `t` entries of column `k`, retaining every other matrix entry. -/
def columnPrefix {N : ℕ} (B : Matrix (Fin N) (Fin N) K) (k : Fin N)
    (v : Fin N → K) (t : ℕ) : Matrix (Fin N) (Fin N) K :=
  fun i j => if j = k ∧ (i : ℕ) < t then v i else B i j

/-- Materialize the first `t` entries of row `k`, retaining every other matrix entry. -/
def rowPrefix {N : ℕ} (B : Matrix (Fin N) (Fin N) K) (k : Fin N)
    (v : Fin N → K) (t : ℕ) : Matrix (Fin N) (Fin N) K :=
  fun i j => if i = k ∧ (j : ℕ) < t then v j else B i j

/-- Writing the next column entry advances its materialized prefix by one. -/
theorem replaceEntry_columnPrefix {N : ℕ} (B : Matrix (Fin N) (Fin N) K)
    (k i : Fin N) (v : Fin N → K) :
    replaceEntry (columnPrefix B k v i) i k (v i) = columnPrefix B k v (i + 1) := by
  ext a b
  by_cases hb : b = k
  · subst b
    by_cases ha : a = i
    · subst a
      simp [replaceEntry, columnPrefix]
    · have hne : (a : ℕ) ≠ (i : ℕ) := fun h => ha (Fin.ext h)
      have hiff : (a : ℕ) < (i : ℕ) + 1 ↔ (a : ℕ) < (i : ℕ) := by omega
      simp only [replaceEntry, ha, false_and, if_false, columnPrefix, true_and, hiff]
  · simp only [replaceEntry, hb, and_false, if_false, columnPrefix, false_and]

/-- Writing the next row entry advances its materialized prefix by one. -/
theorem replaceEntry_rowPrefix {N : ℕ} (B : Matrix (Fin N) (Fin N) K)
    (k i : Fin N) (v : Fin N → K) :
    replaceEntry (rowPrefix B k v i) k i (v i) = rowPrefix B k v (i + 1) := by
  ext a b
  by_cases ha : a = k
  · subst a
    by_cases hb : b = i
    · subst b
      simp [replaceEntry, rowPrefix]
    · have hne : (b : ℕ) ≠ (i : ℕ) := fun h => hb (Fin.ext h)
      have hiff : (b : ℕ) < (i : ℕ) + 1 ↔ (b : ℕ) < (i : ℕ) := by omega
      simp only [replaceEntry, hb, and_false, if_false, rowPrefix, true_and, hiff]
  · simp only [replaceEntry, ha, false_and, if_false, rowPrefix]

end LUColumn

open LUColumn

private theorem exec_luEntry {P ι : Type} [DecidableEq P] {C : Type} [AddMonoid C]
    (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (p : P) (st : St P ℝ C)
    (n k i : IExp ℕ) (S L U ctrl : ℕ) (so lo uo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval) (hi : i.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ ≠ 0)
    (hc : st.store.read p ctrl 1 = some (k.eval : ℝ))
    (hctrl : st.store.shape[ctrl]? = some (p, 2))
    (hL : Writable st.store p L lo.eval (n.eval * n.eval))
    (hU : Writable st.store p U uo.eval (n.eval * n.eval))
    (hSC : S ≠ ctrl) (hSL : S ≠ L) :
    ∃ (out : St P ℝ C) (s₁ s₂ : Store P ℝ),
      exec I (luColumnEntry p n k i S L U ctrl so lo uo).run st = some out ∧
      st.store.write p ctrl 0 (i.eval : ℝ) = some s₁ ∧
      s₁.write p L (lo.eval + i.eval + n.eval * k.eval)
        (lowerEntry M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩) = some s₂ ∧
      s₂.write p U (uo.eval + k.eval + n.eval * i.eval)
        (upperEntry M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩) = some out.store := by
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_getElem?_shape (i.eval : ℝ) hctrl
    (by omega : 0 < 2)
  obtain ⟨lenL, hlenL, hltL⟩ := hL (i.eval + n.eval * k.eval)
    (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape
    (i := lo.eval + i.eval + n.eval * k.eval)
    (lowerEntry M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩)
    ((Store.shape_of_write_eq_some hs₁).symm ▸ hlenL) (by simpa [Nat.add_assoc] using hltL)
  obtain ⟨lenU, hlenU, hltU⟩ := hU (k.eval + n.eval * i.eval)
    (Nat.add_mul_lt_mul_of_lt_of_lt hk hi)
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape
    (i := uo.eval + k.eval + n.eval * i.eval)
    (upperEntry M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩)
    (((Store.shape_of_write_eq_some hs₂).trans (Store.shape_of_write_eq_some hs₁)).symm ▸ hlenU)
    (by simpa [Nat.add_assoc] using hltU)
  have hc₁ : s₁.read p ctrl 1 = some (k.eval : ℝ) :=
    (Store.read_of_write_eq_some_of_ne hs₁ (Or.inr (by omega : 1 ≠ 0))).trans hc
  have hr₁ := Store.read_of_write_eq_some hs₁
  have hM₁ : Holds s₁ p S so.eval M := hM.write hs₁ (fun h => (hSC h.symm).elim)
  have hM₂ : Holds s₂ p S so.eval M := hM₁.write hs₂ (fun h => (hSL h.symm).elim)
  have hSrc := hM₁ ⟨i.eval, hi⟩ ⟨k.eval, hk⟩
  have hPiv := hM₁ ⟨k.eval, hk⟩ ⟨k.eval, hk⟩
  have hUpper := hM₂ ⟨k.eval, hk⟩ ⟨i.eval, hi⟩
  have hll : s₁.write p L (lo.eval + i.eval + n.eval * k.eval)
      (lowerEntry M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩) = some s₂ := hs₂
  have huu : s₂.write p U (uo.eval + k.eval + n.eval * i.eval)
      (upperEntry M ⟨k.eval, hk⟩ ⟨i.eval, hi⟩) = some s₃ := hs₃
  by_cases hik : i.eval < k.eval
  · let count := st.cnt + I.charge (.lit p) + I.charge (.cmp p) +
      I.charge (.lit p) + I.charge (.lit p)
    refine ⟨{ st with store := s₃, cnt := count }, s₁, s₂, ?_, hs₁, hs₂, hs₃⟩
    simp only [lowerEntry, upperEntry, Fin.lt_def, hik, if_true] at hll huu
    simp [run_luColumnEntry, exec, Instr.run, Instr.kind, IExp.eval, hI, exactSem,
      hs₁, hll, huu, hr₁, hc₁, cmpStep, hik, count]
  · by_cases heq : i.eval = k.eval
    · let count := st.cnt + I.charge (.lit p) + I.charge (.cmp p) +
        I.charge (.cmp p) + I.charge (.lit p) + I.charge (.copy p)
      refine ⟨{ st with store := s₃, cnt := count }, s₁, s₂,
        ?_, hs₁, hs₂, hs₃⟩
      simp [lowerEntry, upperEntry, heq] at hll huu
      simp only [heq] at hs₁ hr₁ hUpper
      simp [run_luColumnEntry, exec, Instr.run, Instr.kind,
        IExp.eval, hI, exactSem, hs₁, hll, huu, hr₁, hc₁, cmpStep, heq, hUpper, count]
    · let count := st.cnt + I.charge (.lit p) + I.charge (.cmp p) +
        I.charge (.cmp p) + I.charge (.bin p .div) + I.charge (.copy p)
      refine ⟨{ st with store := s₃, cnt := count }, s₁, s₂,
        ?_, hs₁, hs₂, hs₃⟩
      simp only [lowerEntry, upperEntry, Fin.lt_def, Fin.ext_iff, hik, heq, if_false] at hll huu
      simp [run_luColumnEntry, exec, Instr.run, Instr.kind,
        IExp.eval, hI, exactSem, hs₁, hll, huu, hr₁, hc₁, cmpStep, hik, heq,
        hSrc, hPiv, hUpper, hp, count]

private theorem exists_exec_luColumn_loop {P ι : Type} [DecidableEq P]
    {C : Type} [AddMonoid C] (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ C) (n k : IExp ℕ) (S L U ctrl : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ ≠ 0)
    (hB : Holds st.store p L lo.eval B) (hD : Holds st.store p U uo.eval D)
    (hc : st.store.read p ctrl 1 = some (k.eval : ℝ))
    (hctrl : st.store.shape[ctrl]? = some (p, 2))
    (hSC : S ≠ ctrl) (hLC : L ≠ ctrl) (hUC : U ≠ ctrl)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (.loop n fun i =>
        (luColumnEntry p n k (.var i) S L U ctrl so lo uo).run) st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b idx, b ≠ ctrl →
        (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
        (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
        out.store.read q b idx = st.store.read q b idx) ∧
      Holds out.store p L lo.eval (B.updateCol ⟨k.eval, hk⟩ (lowerEntry M ⟨k.eval, hk⟩)) ∧
      Holds out.store p U uo.eval (D.updateRow ⟨k.eval, hk⟩ (upperEntry M ⟨k.eval, hk⟩)) := by
  let r : Fin n.eval := ⟨k.eval, hk⟩
  let R := fun t (σ : St P ℝ C) => σ.store.shape = st.store.shape ∧
    (∀ q b idx, b ≠ ctrl →
      (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
      (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
      σ.store.read q b idx = st.store.read q b idx) ∧
    σ.store.read p ctrl 1 = some (k.eval : ℝ) ∧
    Holds σ.store p L lo.eval (columnPrefix B r (lowerEntry M r) t) ∧
    Holds σ.store p U uo.eval (rowPrefix D r (upperEntry M r) t)
  have h0 : R 0 st := ⟨rfl, fun _ _ _ _ _ _ => rfl, hc,
    fun i j => by simpa only [columnPrefix, Nat.not_lt_zero, and_false, if_false] using hB i j,
    fun i j => by simpa only [rowPrefix, Nat.not_lt_zero, and_false, if_false] using hD i j⟩
  obtain ⟨out, hr, hsh, hfr, -, hBL, hDU⟩ := exists_exec_loop_eq_some_of_forall I R h0
    (fun t ht σ hR => by
      obtain ⟨hsh, hfr, hc, hBL, hDU⟩ := hR
      have hMσ : Holds σ.store p S so.eval M := fun i j =>
        (hfr p S _ hSC (Or.inl hSL) (Or.inl hSU)).trans (hM i j)
      obtain ⟨out, s₁, s₂, hr, h₁, h₂, h₃⟩ := exec_luEntry I hI p σ n k (.var t)
        S L U ctrl so lo uo M hk ht hMσ hp hc (hsh ▸ hctrl) hBL.writable hDU.writable hSC hSL
      have hB₁ := hBL.write h₁ (fun h => (hLC h.symm).elim)
      have hD₁ := hDU.write h₁ (fun h => (hUC h.symm).elim)
      have hB₂ := holds_replaceEntry (r := ⟨t, ht⟩) (c := r) hB₁ h₂
      have hD₂ := hD₁.write h₂ (fun h => (hLU h).elim)
      refine ⟨out, hr,
        (Store.shape_of_write_eq_some h₃).trans ((Store.shape_of_write_eq_some h₂).trans
          ((Store.shape_of_write_eq_some h₁).trans hsh)), ?_, ?_, ?_, ?_⟩
      · intro q b idx hbC hbL hbU
        have htL := Nat.add_mul_lt_mul_of_lt_of_lt ht hk
        have htU := Nat.add_mul_lt_mul_of_lt_of_lt hk ht
        rw [Store.read_of_write_eq_some_of_ne h₃ (by
            rcases hbU with hbU | hbU | hbU
            · exact Or.inl hbU
            · exact Or.inr (by dsimp; omega)
            · exact Or.inr (by dsimp; omega)),
          Store.read_of_write_eq_some_of_ne h₂ (by
            rcases hbL with hbL | hbL | hbL
            · exact Or.inl hbL
            · exact Or.inr (by dsimp; omega)
            · exact Or.inr (by dsimp; omega)),
          Store.read_of_write_eq_some_of_ne h₁ (Or.inl hbC)]
        exact hfr q b idx hbC hbL hbU
      · rw [Store.read_of_write_eq_some_of_ne h₃ (Or.inl hUC.symm),
          Store.read_of_write_eq_some_of_ne h₂ (Or.inl hLC.symm),
          Store.read_of_write_eq_some_of_ne h₁ (Or.inr (by omega : 1 ≠ 0))]
        exact hc
      · have hB₃ := hB₂.write h₃ (fun h => (hLU h.symm).elim)
        change Holds out.store p L lo.eval
          (replaceEntry (columnPrefix B r (lowerEntry M r) t) ⟨t, ht⟩ r
            ((lowerEntry M r) ⟨t, ht⟩)) at hB₃
        rw [replaceEntry_columnPrefix B r ⟨t, ht⟩ (lowerEntry M r)] at hB₃
        exact hB₃
      · have hD₃ := holds_replaceEntry (r := r) (c := ⟨t, ht⟩) hD₂ h₃
        change Holds out.store p U uo.eval
          (replaceEntry (rowPrefix D r (upperEntry M r) t) r ⟨t, ht⟩
            ((upperEntry M r) ⟨t, ht⟩)) at hD₃
        rw [replaceEntry_rowPrefix D r ⟨t, ht⟩ (upperEntry M r)] at hD₃
        exact hD₃)
  refine ⟨out, hr, hsh, hfr, fun i j => ?_, fun i j => ?_⟩
  · simpa only [columnPrefix, i.isLt, and_true, Matrix.updateCol_apply] using hBL i j
  · simpa only [rowPrefix, j.isLt, and_true, Matrix.updateRow_apply] using hDU i j

private theorem exists_exec_luColumn_body {P ι : Type} [DecidableEq P]
    {C : Type} [AddMonoid C] (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ C) (n k : IExp ℕ) (S L U ctrl : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ ≠ 0)
    (hB : Holds st.store p L lo.eval B) (hD : Holds st.store p U uo.eval D)
    (hctrl : st.store.shape[ctrl]? = some (p, 2))
    (hSC : S ≠ ctrl) (hLC : L ≠ ctrl) (hUC : U ≠ ctrl)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (do
        ins (.litIdx p ⟨ctrl, 1⟩ k)
        forRange n fun i => luColumnEntry p n k (.var i) S L U ctrl so lo uo).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b idx, b ≠ ctrl →
        (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
        (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
        out.store.read q b idx = st.store.read q b idx) ∧
      Holds out.store p L lo.eval (B.updateCol ⟨k.eval, hk⟩ (lowerEntry M ⟨k.eval, hk⟩)) ∧
      Holds out.store p U uo.eval (D.updateRow ⟨k.eval, hk⟩ (upperEntry M ⟨k.eval, hk⟩)) := by
  obtain ⟨s₁, h₁⟩ := Store.exists_write_eq_some_of_getElem?_shape (k.eval : ℝ) hctrl
    (by omega : 1 < 2)
  let start : St P ℝ C := { st with store := s₁, cnt := st.cnt + I.charge (.lit p) }
  obtain ⟨out, hr, hsh, hfr, hBL, hDU⟩ := exists_exec_luColumn_loop I hI p start n k S L U ctrl
    so lo uo M B D hk (hM.write h₁ (fun h => (hSC h.symm).elim)) hp
    (hB.write h₁ (fun h => (hLC h.symm).elim)) (hD.write h₁ (fun h => (hUC h.symm).elim))
    (Store.read_of_write_eq_some h₁) ((Store.shape_of_write_eq_some h₁).symm ▸ hctrl)
    hSC hLC hUC hSL hSU hLU
  refine ⟨out, ?_, hsh.trans (Store.shape_of_write_eq_some h₁), ?_, hBL, hDU⟩
  · change exec I (.seq (.instr (.litIdx p ⟨ctrl, 1⟩ k)) (.seq (.loop n _) .skip)) st = some out
    rw [exec_seq_instr_litIdx I (by rw [hI]; simp [exactSem]) h₁, exec_seq_skip]
    exact hr
  · intro q b idx hbC hbL hbU
    exact (hfr q b idx hbC hbL hbU).trans
      (Store.read_of_write_eq_some_of_ne h₁ (Or.inl hbC))

/-- Under exact arithmetic, materializing a pivot column and row succeeds and writes precisely
the two factor blocks with their new column and row. The Schur matrix and unrelated cells are
retained. The pivot must be nonzero, all three matrix buffers are distinct, and factor blocks
are initialized matrices. The complete LU routine initializes them before its pivot loop. -/
theorem exec_luColumn {P ι : Type} [DecidableEq P] {C : Type} [AddMonoid C]
    (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (p : P) (st : St P ℝ C)
    (n k : IExp ℕ) (S L U : ℕ) (so lo uo : IExp ℕ)
    (M B D : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store p S so.eval M) (hp : M ⟨k.eval, hk⟩ ⟨k.eval, hk⟩ ≠ 0)
    (hB : Holds st.store p L lo.eval B) (hD : Holds st.store p U uo.eval D)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    let B' := B.updateCol r (fun i => if i < r then 0 else if i = r then 1 else M i r / M r r)
    let D' := D.updateRow r (fun j => if j < r then 0 else M r j)
    ∃ out, exec I (luColumn p n k S L U so lo uo).run st = some out ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [flatten B', flatten D'] = some out.store ∧
      Holds out.store p L lo.eval B' ∧ Holds out.store p U uo.eval D' := by
  dsimp only
  let r : Fin n.eval := ⟨k.eval, hk⟩
  let B' := B.updateCol r (lowerEntry M r)
  let D' := D.updateRow r (upperEntry M r)
  have hSsize := Store.lt_size_of_read_eq_some (hM r r)
  have hLsize := Store.lt_size_of_read_eq_some (hB r r)
  have hUsize := Store.lt_size_of_read_eq_some (hD r r)
  have halloc := exists_exec_alloc I p 2 (fun ctrl => ((do
      ins (.litIdx p ⟨ctrl, 1⟩ k)
      forRange n fun i => luColumnEntry p n k (.var i) S L U ctrl so lo uo) :
        Builder P ι ℕ ℕ Unit).run) st
    (fun store => st.store.writeBlocks p
      [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)] [flatten B', flatten D'] =
        some store ∧ Holds store p L lo.eval B' ∧ Holds store p U uo.eval D') (by
      intro σ hσ
      have pushH {buf off : ℕ} {A : Matrix (Fin n.eval) (Fin n.eval) ℝ}
          (h : Holds st.store p buf off A) (hb : buf < st.store.size) :
          Holds σ.store p buf off A := fun i j => by
        rw [hσ, Store.read_push_of_lt hb]; exact h i j
      obtain ⟨out, hr, hsh, hfr, hBL, hDU⟩ := exists_exec_luColumn_body I hI p σ n k S L U
        st.store.size so lo uo M B D hk (pushH hM hSsize) hp (pushH hB hLsize)
        (pushH hD hUsize) (hσ ▸ Store.getElem?_shape_push_size st.store p 2)
        (Nat.ne_of_lt hSsize) (Nat.ne_of_lt hLsize) (Nat.ne_of_lt hUsize) hSL hSU hLU
      have hsize : out.store.size = st.store.size + 1 := by
        simpa only [Store.size_shape, hσ, Array.size_push] using congrArg Array.size hsh
      have hBLpop : Holds out.store.pop p L lo.eval B' := fun i j => by
        rw [Store.read_pop_of_lt (by omega)]; exact hBL i j
      have hDUpop : Holds out.store.pop p U uo.eval D' := fun i j => by
        rw [Store.read_pop_of_lt (by omega)]; exact hDU i j
      refine ⟨out, hr, writeBlocks_factors hLU ?_ hBLpop hDUpop ?_, hBLpop, hDUpop⟩
      · rw [Store.shape_pop, hsh, hσ]
        simp only [Store.shape, Array.map_push, Array.pop_push]
      · intro q b idx hbL hbU
        by_cases hb : b < st.store.size
        · rw [Store.read_pop_of_lt (by omega), hfr q b idx (by omega) hbL hbU,
            hσ, Store.read_push_of_lt hb]
        · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
            Store.read_eq_none_of_size_le (by omega)])
  obtain ⟨out, hr, hw, hBL, hDU⟩ := halloc
  refine ⟨out, ?_, hw, hBL, hDU⟩
  change exec I (.seq (.alloc p 2 _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- Unpivoted LU factorization on separate input and factor buffers. A scoped matrix stores
the elimination state. Factor buffers are first zero-filled; each iteration materializes one
lower column and upper row and then performs a full Schur elimination step. All scalar data
operations are instructions or calls to the existing stored kernels. [GolubVanLoan2013, §3.2]. -/
def luFactor {P ι VB VI : Type} (p : P) (n : IExp VI) (A L U : VB)
    (ao lo uo : IExp VI) : Builder P ι VB VI Unit := scope do
  let S ← alloc p (n * n)
  copyv p A ao S 0 (n * n)
  forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
  forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)
  forRange n fun k => do
    luColumn p n (.var k) S L U 0 lo uo
    schurStep p n S 0 (.var k)

/-- The scoped unpivoted LU factorization composes with a following routine. -/
theorem executionComposable_luFactor (I : Interp P ι K C) (p : P) (n : IExp ℕ)
    (A L U : ℕ) (ao lo uo : IExp ℕ) :
    ExecutionComposable I (luFactor p n A L U ao lo uo) :=
  executionComposable_single I (fun _ => rfl)

private theorem materializedLower_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (k i : Fin N) :
    lowerEntry (gaussState A k) k i = luLower A i k := by
  simpa only [lowerEntry] using (luLower_apply_eq_ite A i k).symm

private theorem materializedUpper_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (k j : Fin N) :
    upperEntry (gaussState A k) k j = luUpper A k j := by
  simpa only [upperEntry] using (luUpper_apply_eq_ite A k j).symm

private theorem exec_luFactor_loop {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (S L U : ℕ) (so lo uo : IExp ℕ)
    (A B D : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : Holds st.store p S so.eval A) (hB : Holds st.store p L lo.eval B)
    (hD : Holds st.store p U uo.eval D)
    (hp : ∀ k : Fin n.eval, gaussState A k k k ≠ 0)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (.loop n fun k => (do
        luColumn p n (.var k) S L U so lo uo
        schurStep p n S so (.var k)).run) st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b idx, (b ≠ S ∨ idx < so.eval ∨ so.eval + n.eval * n.eval ≤ idx) →
        (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
        (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
        out.store.read q b idx = st.store.read q b idx) ∧
      Holds out.store p L lo.eval (luLower A) ∧ Holds out.store p U uo.eval (luUpper A) := by
  let R := fun k (σ : St P ℝ (OpCount P ι)) =>
    σ.store.shape = st.store.shape ∧
    (∀ q b idx, (b ≠ S ∨ idx < so.eval ∨ so.eval + n.eval * n.eval ≤ idx) →
      (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
      (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
      σ.store.read q b idx = st.store.read q b idx) ∧
    Holds σ.store p S so.eval (gaussState A k) ∧
    ∃ B D : Matrix (Fin n.eval) (Fin n.eval) ℝ,
      Holds σ.store p L lo.eval B ∧ Holds σ.store p U uo.eval D ∧
      (∀ i j : Fin n.eval, (j : ℕ) < k → B i j = luLower A i j) ∧
      (∀ i j : Fin n.eval, (i : ℕ) < k → D i j = luUpper A i j)
  have h0 : R 0 st := ⟨rfl, fun _ _ _ _ _ _ => rfl, hA, B, D, hB, hD,
    fun _ _ h => (Nat.not_lt_zero _ h).elim, fun _ _ h => (Nat.not_lt_zero _ h).elim⟩
  obtain ⟨out, hr, hsh, hfr, -, Bf, Df, hBL, hDU, hLB, hUD⟩ :=
    exists_exec_loop_eq_some_of_forall I
      (body := fun k => (do
        luColumn p n (.var k) S L U so lo uo
        schurStep p n S so (.var k)).run) R h0 (fun k hk σ hR => by
      obtain ⟨hsh, hfr, hS, B, D, hBL, hDU, hLB, hUD⟩ := hR
      let r : Fin n.eval := ⟨k, hk⟩
      obtain ⟨mid, hr₁, hw₁, hBL', hDU'⟩ := exec_luColumn I hI p σ n (.var k) S L U so lo uo
        (gaussState A k) B D hk hS (hp r) hBL hDU hSL hSU hLU
      have hS' : Holds mid.store p S so.eval (gaussState A k) := fun i j =>
        (Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun x hx => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact Or.inl hSL
          · exact Or.inl hSU)).trans (hS i j)
      obtain ⟨final, hr₂, hw₂, hS''⟩ := exec_schurStep I hI hc p mid n S so (.var k)
        (gaussState A k) hk hS' (hp r)
      have hBL'' := fun i j => (Store.read_of_writeBlock_eq_some_of_ne hw₂
        (Or.inl hSL.symm)).trans (hBL' i j)
      have hDU'' := fun i j => (Store.read_of_writeBlock_eq_some_of_ne hw₂
        (Or.inl hSU.symm)).trans (hDU' i j)
      refine ⟨final, ?_, (Store.shape_of_writeBlock_eq_some hw₂).trans
        ((Store.shape_of_writeBlocks_eq_some hw₁).trans hsh), ?_, ?_, _, _, hBL'', hDU'', ?_, ?_⟩
      · rw [exec_run_bind I (b := luColumn p n (.var k) S L U so lo uo) (fun _ => rfl),
          hr₁, Option.bind_some]
        exact hr₂
      · intro q b idx hbS hbL hbU
        rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (by simpa only [size_flatten] using hbS),
          Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun x hx => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · exact hbL
            · exact hbU)]
        exact hfr q b idx hbS hbL hbU
      · simpa only [IExp.eval_var, gaussState_succ A hk] using hS''
      · intro i j hj
        by_cases heq : j = r
        · subst j
          change (B.updateCol r (lowerEntry (gaussState A k) r)) i r = luLower A i r
          rw [Matrix.updateCol_self]
          exact materializedLower_eq A r i
        · have hjk : (j : ℕ) < k := by have hne : (j : ℕ) ≠ k := fun h => heq (Fin.ext h); omega
          change (B.updateCol r (lowerEntry (gaussState A k) r)) i j = luLower A i j
          rw [Matrix.updateCol_ne heq]
          exact hLB i j hjk
      · intro i j hi
        by_cases heq : i = r
        · subst i
          change (D.updateRow r (upperEntry (gaussState A k) r)) r j = luUpper A r j
          rw [Matrix.updateRow_self]
          exact materializedUpper_eq A r j
        · have hik : (i : ℕ) < k := by have hne : (i : ℕ) ≠ k := fun h => heq (Fin.ext h); omega
          change (D.updateRow r (upperEntry (gaussState A k) r)) i j = luUpper A i j
          rw [Matrix.updateRow_ne heq]
          exact hUD i j hik)
  exact ⟨out, hr, hsh, hfr, fun i j => (hBL i j).trans (congrArg some (hLB i j j.isLt)),
    fun i j => (hDU i j).trans (congrArg some (hUD i j i.isLt))⟩

/-- Copy a stored matrix into separate residual storage and initialize both factor blocks
to zero. Writable output capacity suffices; all three complete blocks and their outside-cell
frame are retained for subsequent elimination loops. [GolubVanLoan2013, §3.2]. -/
theorem exec_luInitialize {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A S L U : ℕ) (ao lo uo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store p A ao.eval M)
    (hS : Writable st.store p S 0 (n.eval * n.eval))
    (hL : Writable st.store p L lo.eval (n.eval * n.eval))
    (hU : Writable st.store p U uo.eval (n.eval * n.eval))
    (hAS : A ≠ S) (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (do
        copyv p A ao S 0 (n * n)
        forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
        forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b idx, (b ≠ S ∨ idx < 0 ∨ n.eval * n.eval ≤ idx) →
        (b ≠ L ∨ idx < lo.eval ∨ lo.eval + n.eval * n.eval ≤ idx) →
        (b ≠ U ∨ idx < uo.eval ∨ uo.eval + n.eval * n.eval ≤ idx) →
        out.store.read q b idx = st.store.read q b idx) ∧
      Holds out.store p S 0 M ∧
      Holds out.store p L lo.eval (0 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ∧
      Holds out.store p U uo.eval (0 : Matrix (Fin n.eval) (Fin n.eval) ℝ) := by
  let xs := fun t => (flatten M).getD t 0
  have hxs : ∀ t < (n * n).eval, st.store.read p A (ao.eval + t) = some (xs t) := by
    intro t ht
    have ht' : t < (flatten M).size := by simpa only [size_flatten, IExp.eval_mul] using ht
    have hread := hM.read_flatten t (by simpa only [IExp.eval_mul] using ht)
    rw [hread, Array.getElem?_eq_getElem ht']
    simp only [xs, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht', Option.getD_some]
  obtain ⟨copied, hcopy, hcsh, hcread, hcfr, -⟩ := exec_copyv_frame I hc p st (n * n) A S ao 0
    xs hxs hAS (by simpa only [Writable, IExp.eval_mul, IExp.eval_zero] using hS)
  have hCM : Holds copied.store p S 0 M := fun i j => by
    have hr := hcread (i + n.eval * j) (by
      simpa only [IExp.eval_mul] using Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)
    simpa only [IExp.eval_zero, Nat.zero_add, xs, Array.getD_eq_getD_getElem?,
      getElem?_flatten, Option.getD_some] using hr
  obtain ⟨sl, hlrun, hlsh, hlread, hlfr⟩ := exec_forRange_literal_zero I p 0
    (by rw [hI]; simp [exactSem]) copied (n * n) L lo
    (by simpa only [Writable, IExp.eval_mul] using hL.of_shape_eq hcsh)
  let lower : St P ℝ (OpCount P ι) :=
    { copied with store := sl, cnt := copied.cnt + (n * n).eval • I.charge (.lit p) }
  obtain ⟨su, hurun, hush, huread, hufr⟩ := exec_forRange_literal_zero I p 0
    (by rw [hI]; simp [exactSem]) lower (n * n) U uo
    (by simpa only [Writable, IExp.eval_mul, lower] using hU.of_shape_eq (hlsh.trans hcsh))
  let out : St P ℝ (OpCount P ι) :=
    { lower with store := su, cnt := lower.cnt + (n * n).eval • I.charge (.lit p) }
  refine ⟨out, ?_, hush.trans (hlsh.trans hcsh), ?_, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := copyv p A ao S 0 (n * n)) (fun _ => rfl), hcopy,
      Option.bind_some, exec_run_bind I
        (b := forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)) (fun _ => rfl),
      hlrun, Option.bind_some]
    exact hurun
  · intro q b idx hbS hbL hbU
    rw [hufr q b idx (Or.inr (by simpa only [IExp.eval_mul] using hbU)),
      hlfr q b idx (Or.inr (by simpa only [IExp.eval_mul] using hbL)),
      hcfr q b idx (by simpa only [IExp.eval_zero, IExp.eval_mul, Nat.zero_add] using hbS)]
  · intro i j
    rw [hufr p S _ (Or.inr (Or.inl hSU)), hlfr p S _ (Or.inr (Or.inl hSL))]
    exact hCM i j
  · intro i j
    rw [hufr p L _ (Or.inr (Or.inl hLU))]
    simpa only [lower, Nat.add_assoc, Matrix.zero_apply] using hlread (i + n.eval * j) (by
      simpa only [IExp.eval_mul] using Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)
  · intro i j
    simpa only [out, Nat.add_assoc, Matrix.zero_apply] using huread (i + n.eval * j) (by
      simpa only [IExp.eval_mul] using Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)

private theorem exec_luBody_empty {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    (I : Interp P ι K C) (p : P) (st : St P K C) (n : IExp ℕ) (A S L U : ℕ)
    (ao lo uo : IExp ℕ) (hn : n.eval = 0) :
    exec I (do
      copyv p A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        luColumn p n (.var k) S L U 0 lo uo
        schurStep p n S 0 (.var k)).run st = some st := by
  change exec I (.seq (.named "copy" _ (.seq (.loop (n * n) _) .skip))
    (.seq (.loop (n * n) _) (.seq (.loop (n * n) _) (.seq (.loop n _) .skip)))) st = some st
  simp only [exec_seq, exec_named, exec_loop, IExp.eval_mul, hn, zero_mul,
    List.range_zero, List.foldlM_nil, Option.pure_def, Option.bind_some, exec_skip]

/-- Exact unpivoted LU factorization succeeds when every elimination pivot is nonzero. The
input and two output buffers are distinct, factor windows need only be writable, and the
input matrix may be empty. The only net effect is the two packed factor writes; the output
factors are the existing `luLower` and `luUpper` and satisfy `IsLU`. Standard unit operation
charges are used because the stored Schur kernel's execution theorem fixes those charges.
This asserts exact arithmetic only, with no rounded nonbreakdown or cost-optimality claim.
[GolubVanLoan2013, §3.2]. -/
private theorem exec_luFactor_outputs {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U : ℕ) (ao lo uo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store p A ao.eval M)
    (hp : ∀ k : Fin n.eval, gaussState M k k k ≠ 0)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval))
    (hU : Writable st.store p U uo.eval (n.eval * n.eval))
    (hLU : L ≠ U) :
    ∃ out, exec I (luFactor p n A L U ao lo uo).run st = some out ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [flatten (luLower M), flatten (luUpper M)] = some out.store ∧
      Holds out.store p L lo.eval (luLower M) ∧ Holds out.store p U uo.eval (luUpper M) := by
  have halloc := exists_exec_alloc I p (n * n) (fun S => ((do
      copyv p A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        luColumn p n (.var k) S L U 0 lo uo
        schurStep p n S 0 (.var k)) : Builder P ι ℕ ℕ Unit).run) st
    (fun store => st.store.writeBlocks p
      [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
      [flatten (luLower M), flatten (luUpper M)] = some store ∧
      Holds store p L lo.eval (luLower M) ∧ Holds store p U uo.eval (luUpper M)) (by
      intro σ hσ
      by_cases hn : n.eval = 0
      · refine ⟨σ, exec_luBody_empty I p σ n A st.store.size L U ao lo uo hn, ?_⟩
        have hpop : σ.store.pop = st.store := by rw [hσ]; exact Array.pop_push
        rw [hpop]
        have hBL : Holds st.store p L lo.eval (luLower M) := fun i _ => by have := i.isLt; omega
        have hDU : Holds st.store p U uo.eval (luUpper M) := fun i _ => by have := i.isLt; omega
        exact ⟨writeBlocks_factors hLU rfl hBL hDU (fun _ _ _ _ _ => rfl), hBL, hDU⟩
      · have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
        have hAsize := Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
        have hLsize := hL.lt_size (Nat.mul_pos hN hN)
        have hUsize := hU.lt_size (Nat.mul_pos hN hN)
        have hMp : Holds σ.store p A ao.eval M := fun i j => by
          rw [hσ, Store.read_push_of_lt hAsize]; exact hM i j
        have hSp : Writable σ.store p st.store.size 0 (n.eval * n.eval) := fun t ht =>
          ⟨n.eval * n.eval, hσ ▸ Store.getElem?_shape_push_size st.store p (n.eval * n.eval),
            by omega⟩
        obtain ⟨mid, hr₁, hsh₁, hfr₁, hS, hBL, hDU⟩ := exec_luInitialize I hI hc p σ n A
          st.store.size L U ao lo uo M hMp hSp (hσ ▸ hL.push _) (hσ ▸ hU.push _)
          (Nat.ne_of_lt hAsize) (Nat.ne_of_gt hLsize) (Nat.ne_of_gt hUsize) hLU
        obtain ⟨final, hr₂, hsh₂, hfr₂, hBL', hDU'⟩ := exec_luFactor_loop I hI hc p mid n
          st.store.size L U 0 lo uo M 0 0 hS hBL hDU hp
          (Nat.ne_of_gt hLsize) (Nat.ne_of_gt hUsize) hLU
        have hsize : final.store.size = st.store.size + 1 := by
          simpa only [Store.size_shape, hσ, Array.size_push] using
            congrArg Array.size (hsh₂.trans hsh₁)
        have hBLpop : Holds final.store.pop p L lo.eval (luLower M) := fun i j => by
          rw [Store.read_pop_of_lt (by omega)]; exact hBL' i j
        have hDUpop : Holds final.store.pop p U uo.eval (luUpper M) := fun i j => by
          rw [Store.read_pop_of_lt (by omega)]; exact hDU' i j
        refine ⟨final, ?_, writeBlocks_factors hLU ?_ hBLpop hDUpop ?_, hBLpop, hDUpop⟩
        · change exec I ((do
              copyv p A ao st.store.size 0 (n * n)
              forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
              forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)) >>= fun _ =>
                forRange n fun k => do
                  luColumn p n (.var k) st.store.size L U 0 lo uo
                  schurStep p n st.store.size 0 (.var k)).run σ = some final
          have hcomp : ExecutionComposable I (do
              copyv p A ao st.store.size 0 (n * n)
              forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
              forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)) :=
            (executionComposable_single I (b := copyv p A ao st.store.size 0 (n * n))
              (fun _ => rfl)).bind
                ((executionComposable_single I
                  (b := forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0))
                  (fun _ => rfl)).bind (executionComposable_single I (fun _ => rfl)))
          rw [hcomp, hr₁, Option.bind_some]
          change exec I (.seq (.loop n _) .skip) mid = some final
          rw [exec_seq_skip]; exact hr₂
        · rw [Store.shape_pop, hsh₂, hsh₁, hσ]
          simp only [Store.shape, Array.map_push, Array.pop_push]
        · intro q b idx hbL hbU
          by_cases hb : b < st.store.size
          · rw [Store.read_pop_of_lt (by omega),
              hfr₂ q b idx (Or.inl (by omega)) hbL hbU,
              hfr₁ q b idx (Or.inl (by omega)) hbL hbU, hσ, Store.read_push_of_lt hb]
          · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
              Store.read_eq_none_of_size_le (by omega)])
  obtain ⟨out, hr, hw, hBL, hDU⟩ := halloc
  refine ⟨out, ?_, hw, hBL, hDU⟩
  change exec I (.seq (.alloc p (n * n) _) .skip) st = some out
  rw [exec_seq_skip]; exact hr

/-- Exact unpivoted LU factorization succeeds when every elimination pivot is nonzero. The
input and output buffers are distinct for nonempty matrices, the factor buffers are distinct,
and factor windows need only be writable. The output factors are the elimination factors and form
an exact LU factorization. The two packed factor writes are the only net store effect, and
the input matrix is retained. Standard unit charges are required by the stored Schur kernel.
This is an exact-arithmetic theorem, with no rounded nonbreakdown or optimal-cost claim.
[GolubVanLoan2013, §3.2]. -/
theorem exec_luFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U : ℕ) (ao lo uo : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store p A ao.eval M)
    (hp : ∀ k : Fin n.eval, gaussState M k k k ≠ 0)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval))
    (hU : Writable st.store p U uo.eval (n.eval * n.eval))
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (luFactor p n A L U ao lo uo).run st = some out ∧
      st.store.writeBlocks p [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval)]
        [flatten (luLower M), flatten (luUpper M)] = some out.store ∧
      Holds out.store p L lo.eval (luLower M) ∧ Holds out.store p U uo.eval (luUpper M) ∧
      IsLU M (luLower M) (luUpper M) ∧ Holds out.store p A ao.eval M := by
  obtain ⟨out, hr, hw, hBL, hDU⟩ := exec_luFactor_outputs I hI hc p st n A L U ao lo uo
    M hM hp hL hU hLU
  refine ⟨out, hr, hw, hBL, hDU, isLU_luLower_luUpper (fun i _ => ?_), fun i j => ?_⟩
  · rw [luUpper_apply_self]; exact hp i
  · exact (Store.read_of_writeBlocks_eq_some_of_forall hw (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inl (hAL (Nat.zero_lt_of_lt i.isLt))
      · exact Or.inl (hAU (Nat.zero_lt_of_lt i.isLt)))).trans (hM i j)

end NLAlib.Computation
