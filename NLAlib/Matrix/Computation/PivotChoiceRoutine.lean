/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CompletePivot
public import NLAlib.Matrix.Computation.RookPivot
public import NLAlib.Matrix.Computation.ThresholdPivot

/-!
# Executable pivot-choice contracts

The shared exact LU driver needs an active row and column, exact stored index words, a
readonly source and quantitative quality in the selected column. Complete and rook selection
provide quality one; threshold selection provides its positive rational threshold. A policy
flag also records the actual fixed-column behavior needed to scope away an identity column log.

## Main definitions

* `NLAlib.Computation.PivotChoice`: an actual two-index chooser builder.
* `NLAlib.Computation.IsPivotChoiceRoutine`: success, frame, column quality and policy behavior.

## Main results

* `NLAlib.Computation.isPivotChoiceRoutine_completePivotChoice`: complete selection instance.
* `NLAlib.Computation.isPivotChoiceRoutine_rookPivotChoice`: rook selection instance.
* `NLAlib.Computation.isPivotChoiceRoutine_thresholdPivotChoice`: fixed-column threshold instance.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- An actual pivot selector, with the scalar tag captured by the builder. The two output
cells store absolute row and column coordinates in the source's active square. -/
abbrev PivotChoice (P ι VB VI : Type) :=
  IExp VI → IExp VI → VB → IExp VI → Cell VB VI → Cell VB VI → Builder P ι VB VI Unit

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- An executable two-index chooser contract. Positive column quality suffices for total LU,
while the fixed-column flag supports a row-only factorization consumer. Its guarantees include
actual execution, exact stored words and the two ordered singleton writes. -/
structure IsPivotChoiceRoutine (I : Interp P ι ℝ C) (tag : P) (α : ℝ)
    (fixedColumns : Bool) (choose : PivotChoice P ι ℕ ℕ) : Prop where
  /-- The quality fraction is positive. -/
  pos : 0 < α
  /-- The quality fraction also covers the unit lower diagonal. -/
  le_one : α ≤ 1
  /-- The actual chooser composes after releasing its workspace. -/
  composable : ∀ n k A off rowIndex colIndex,
    ExecutionComposable I (choose n k A off rowIndex colIndex)
  /-- Every nonempty active square can be selected without a pivot nonzero premise. -/
  success : ∀ (st : St P ℝ C) (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ)
    (rowIndex colIndex : Cell ℕ ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval), Holds st.store tag A off.eval M →
    Writable st.store tag rowIndex.buf rowIndex.idx.eval 1 →
    Writable st.store tag colIndex.buf colIndex.idx.eval 1 →
    A ≠ rowIndex.buf → A ≠ colIndex.buf →
    (rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval) →
    ∃ (out : St P ℝ C) (r c : Fin n.eval) (mid : Store P ℝ),
      exec I (choose n k A off rowIndex colIndex).run st = some out ∧
      st.store.writeBlock tag rowIndex.buf rowIndex.idx.eval #[(r.val : ℝ)] = some mid ∧
      mid.writeBlock tag colIndex.buf colIndex.idx.eval #[(c.val : ℝ)] = some out.store ∧
      k.eval ≤ r.val ∧ k.eval ≤ c.val ∧ Holds out.store tag A off.eval M ∧
      out.store.read tag rowIndex.buf rowIndex.idx.eval = some (r.val : ℝ) ∧
      out.store.read tag colIndex.buf colIndex.idx.eval = some (c.val : ℝ) ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → α * |M i c| ≤ |M r c|) ∧
      (fixedColumns = true → c = ⟨k.eval, hk⟩)

/-- Exact complete selection supplies a unit-quality actual chooser. Both selected indices
and the full source/frame guarantee come from execution of the existing complete scan. -/
theorem isPivotChoiceRoutine_completePivotChoice (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) : IsPivotChoiceRoutine I tag 1 false (completePivotChoice tag) where
  pos := zero_lt_one
  le_one := le_rfl
  composable := executionComposable_completePivotChoice I tag
  success := by
    intro st n k A off rowIndex colIndex M hk hM hwR hwC hAR hAC hRC
    have h := hI ▸ (isRelErrSem_exactSem (P := P))
    obtain ⟨out, r, c, rw, cw, mid, he, hw₁, hw₂, hdr, hdc, hkr, hkc, hMS, hm, -⟩ :=
      h.exec_completePivotChoice I n k (hI ▸ isIndexExactSem_exactSem n.eval) tag st
        A off rowIndex colIndex M hk (fun i j => ⟨M i j, hM i j, rfl⟩)
        hwR hwC hAR hAC hRC
    have hw₁' : st.store.writeBlock tag rowIndex.buf rowIndex.idx.eval #[(r.val : ℝ)] =
        some mid := by simpa only [hdr] using hw₁
    have hw₂' : mid.writeBlock tag colIndex.buf colIndex.idx.eval #[(c.val : ℝ)] =
        some out.store := by simpa only [hdc] using hw₂
    refine ⟨out, r, c, mid, he, hw₁', hw₂', hkr, hkc, ?_, ?_, ?_, ?_, by simp⟩
    · intro i j
      obtain ⟨v, hv, hd⟩ := hMS i j
      simpa only [hd] using hv
    · rw [Store.read_of_writeBlock_eq_some_of_ne hw₂' (by
        rcases hRC with hb | hi
        · exact Or.inl hb
        · right; simp only [Array.size_singleton]; omega)]
      simpa using Store.read_of_writeBlock_eq_some_of_lt hw₁' (by simp : 0 < #[(r.val : ℝ)].size)
    · simpa using Store.read_of_writeBlock_eq_some_of_lt hw₂' (by simp : 0 < #[(c.val : ℝ)].size)
    · intro i hi
      simpa only [one_mul] using hm i c hi hkc

/-- Exact rook selection supplies a unit-quality actual chooser. Its stronger row maximality
is retained by the selector theorem; the common factorization consumer needs column quality. -/
theorem isPivotChoiceRoutine_rookPivotChoice (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) : IsPivotChoiceRoutine I tag 1 false (rookPivotChoice tag) where
  pos := zero_lt_one
  le_one := le_rfl
  composable := executionComposable_rookPivotChoice I tag
  success := by
    intro st n k A off rowIndex colIndex M hk hM hwR hwC hAR hAC hRC
    obtain ⟨out, r, c, mid, he, hw₁, hw₂, hkr, hkc, hMS, hr, hc, hm, -, -, -⟩ :=
      exec_rookPivotChoice I hI tag st n k A off rowIndex colIndex M hk hM
        hwR hwC hAR hAC hRC
    exact ⟨out, r, c, mid, he, hw₁, hw₂, hkr, hkc, hMS, hr, hc,
      fun i hi => by simpa only [one_mul] using hm i hi, by simp⟩

/-- The actual threshold selector followed by the exact current-column literal supplies a
fixed-column chooser. Equality accepts the diagonal, and the quality fraction is the exact
positive rational threshold. The two output cells may share a buffer at distinct offsets. -/
theorem isPivotChoiceRoutine_thresholdPivotChoice (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (τ : ℚ) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1) :
    IsPivotChoiceRoutine I tag (τ : ℝ) true (fun n k A off rowIndex colIndex => do
      thresholdPivotChoice tag n k A off τ rowIndex
      ins (.litIdx tag colIndex k)) where
  pos := Rat.cast_pos.mpr hτ₀
  le_one := by exact_mod_cast hτ₁
  composable := by
    intro n k A off rowIndex colIndex
    exact (executionComposable_thresholdPivotChoice I tag n k A off τ rowIndex).bind
      (executionComposable_single I (fun _ => rfl))
  success := by
    intro st n k A off rowIndex colIndex M hk hM hwR hwC hAR hAC hRC
    obtain ⟨chosen, r, he₁, hw₁, hkr, hMS, hm, -, -, -⟩ :=
      exec_thresholdPivotChoice I hI tag st n k A off τ rowIndex M hk hτ₀ hτ₁ hM hwR hAR
    obtain ⟨len, hlen, hlt⟩ := hwC 0 (by omega)
    obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape (k.eval : ℝ)
      ((Store.shape_of_writeBlock_eq_some hw₁).symm ▸ hlen) (by simpa using hlt)
    let out : St P ℝ C := { chosen with store := s₂, cnt := chosen.cnt + I.charge (.lit tag) }
    have hw₂ : chosen.store.writeBlock tag colIndex.buf colIndex.idx.eval #[(k.eval : ℝ)] =
        some out.store := by simpa [Store.writeBlock, List.range_succ] using hs₂
    refine ⟨out, r, ⟨k.eval, hk⟩, chosen.store, ?_, hw₁, hw₂, hkr, le_rfl,
      ?_, ?_, Store.read_of_write_eq_some hs₂, hm, fun _ => rfl⟩
    · rw [executionComposable_thresholdPivotChoice I tag n k A off τ rowIndex,
        he₁, Option.bind_some]
      exact (exec_seq_instr_litIdx I (by simp [hI, exactSem]) hs₂).trans (exec_skip I _)
    · intro i j
      rw [Store.read_of_write_eq_some_of_ne hs₂ (Or.inl hAC)]
      exact hMS i j
    · rw [Store.read_of_write_eq_some_of_ne hs₂ hRC]
      simpa using Store.read_of_writeBlock_eq_some_of_lt hw₁ (by simp : 0 < #[(r.val : ℝ)].size)

end NLAlib.Computation
