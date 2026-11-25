/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.CompleteChoice
public import NLAlib.Matrix.Factorizations.LU.PivotedRoutine

/-!
# Scalar complete-pivot LU

The actual first column-major active-square maximum selector drives the shared total
elimination loop. Independent stored row and column logs determine the final permutations.
Every matrix is admitted, including singular matrices and order zero. The outer dimension
guard preserves empty execution without touching caller handles or entering a frame.

## Main results

* `NLAlib.LU.factorComplete_meets`: exact canonical PLUQ and both actual pivot logs.
* `NLAlib.LU.eval_factorComplete_zero`: handle-free empty execution of the actual tree.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Actual complete-pivot LU with separate row and column histories. Empty order skips all
framed calls; nonempty inputs use the stored active-square selector and total Schur steps. -/
def factorComplete : Routine Op Tst :=
  routine% [n] (A : n * n) → (L : n * n, U : n * n, H : n, Q : n) {
    ifPos n {
      run (factorPivoted (completeChoice (Op := Op) (Tst := Tst)).body false)
        [n] (A, L, U, H, Q)
    }
  }

/-- The actual empty tree returns the original memory without a handle, capacity, separation,
model or arithmetic premise, including missing operands and fresh-scratch coincidences. -/
theorem eval_factorComplete_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (factorComplete (Op := Op) (Tst := Tst)).body
      (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- Both actual current-position logs decode to active indices. Their independent row and
column permutations give the canonical lower and upper factors and exact LU identity.
All lower multipliers have magnitude at most one, including singular inputs. -/
def factorCompleteSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls, us, hs, qs) ensures
    ∃ p q : Fin n → Fin n,
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) ∧
      (∀ i : Fin n, dec (vec qs i.val) = (q i).val) ∧
      (∀ i : Fin n, i ≤ p i) ∧ (∀ i : Fin n, i ≤ q i) ∧
      let B := (decodeMatrix dec n n as).submatrix
        (luPivotPermutation p n) (luPivotPermutation q n)
      decodeMatrix dec n n ls = luLower B ∧ decodeMatrix dec n n us = luUpper B ∧
        IsLU B (decodeMatrix dec n n ls) (decodeMatrix dec n n us) ∧
        ∀ i j : Fin n, |decodeMatrix dec n n ls i j| ≤ 1

/-- Unit-quality independent-log engine outputs have the concrete complete-pivot shape. -/
theorem factorCompleteSpec_of_pivoted {dec : K → ℝ} {n : ℕ} {τ : Tape K}
    {as ls us hs qs : List K}
    (h : (factorPivotedSpec dec 1 false).post [n] τ [as] [ls, us, hs, qs]) :
    (factorCompleteSpec dec).post [n] τ [as] [ls, us, hs, qs] := by
  obtain ⟨p, q, hp, hq, _, hpr, hqr, _, hlo, hup, hLU, hbound⟩ := h
  exact ⟨p, q, hp, hq rfl, hpr, hqr, hlo, hup, hLU, by simpa only [inv_one] using hbound⟩

/-- The concrete active-square selector supplies unit column quality to the shared engine.
The stronger square-maximum and first-tie result remains in `completeChoiceSpec`. -/
theorem completeChoice_meets_choice {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (completeChoice (Op := Op) (Tst := Tst)).Meets I (choiceSpec dec 1 bound false) := by
  routine_intro [n, k] (R, p) reads (rs)
  have hraw := (completeChoice_meets hI hcmp hlit hQ hM hNat)
    [n, k] [R, p] τ m [rs] rfl rfl hlive hsep hr hpre hrooms
  refine hraw.mono le_rfl ?_
  rintro m' hfr ⟨hp, ys, hys, hpost⟩
  change m'.readBlocks [p] [2] = some ys at hys
  obtain ⟨ws, rest, hws, hrest, rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys
  have he : rest = [] := by simpa only [Mem.readBlocks_nil, Option.some.injEq] using hrest.symm
  subst rest
  obtain ⟨r, c, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hws)
  exact ⟨hp, [[r, c]], Mem.readBlocks_of_cons hws rfl, completeChoiceSpec_choiceSpec hpost⟩

/-- Complete pivoting executes on every input matrix. Every pivot comes from the actual
stored scan outputs and both permutations are decoded from its reported histories. Zero
pivots use the total elimination step rather than imposing nonsingularity. -/
theorem factorComplete_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (factorComplete (Op := Op) (Tst := Tst)).Meets I (factorCompleteSpec dec) := by
  routine_intro [n] (A, L, U, H, Q) reads (as)
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    call (factorPivoted_meets (quality := 1) (fixedColumns := false)
      hI hcmp hlit hQ hM (by norm_num) le_rfl
      (fun bound => completeChoice_meets_choice hI hcmp hlit hQ hM.toStdModel_zero
        (hM.isExactNatLit bound))) [n] (A, L, U, H, Q)
      as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hout
    routine_exit
    exact factorCompleteSpec_of_pivoted hout
  · rw [if_neg hn]
    have he : n = 0 := by omega
    subst n
    have heas : as = [] := List.eq_nil_of_length_eq_zero (Store.length_of_readBlock has)
    subst as
    exact ⟨rfl, [[], [], [], []], by simp [Mem.readBlocks, Store.readBlock_zero],
      factorCompleteSpec_of_pivoted (factorPivotedSpec_zero dec 1 false (τ.shift m.pos))⟩

end NLAlib.LU
