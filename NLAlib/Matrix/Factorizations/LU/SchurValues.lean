/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RankOne
public import NLAlib.Matrix.Factorizations.Elimination

/-!
# Saved-pivot elimination on machine words

The saved pivot row, pivot column and negative reciprocal determine the functional result
of a full Schur update. Its exact decoded result is the library's Gaussian elimination step.
The word formula also records the actual arithmetic order for rounded analyses.

## Main results

* `NLAlib.LU.schurValues_dec`: exact arithmetic gives the elimination-entry formula.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type}

/-- The saved-pivot full residual update: form the negative reciprocal, multiply it by
the saved row entry, then multiply by the saved column entry and add to the old entry. -/
def schurValues (M : Machine K) (A : ℕ → ℕ → K) (k : ℕ) : ℕ → ℕ → K :=
  rankOneValues M (M.div (M.lit (-1)) (A k k)) (fun i => A i k) (A k) A

/-- Exact decoding of the actual scalar word formula, at a nonzero pivot. The expression
is the entry of `eliminationStep`; no memory or execution premise is involved. -/
theorem schurValues_dec {dec : K → ℝ} {M : Machine K} (hM : ExactModel dec M)
    (A : ℕ → ℕ → K) (k i j : ℕ) (hk : dec (A k k) ≠ 0) :
    dec (schurValues M A k i j) =
      dec (A i j) - (dec (A k k))⁻¹ * (dec (A i k) * dec (A k j)) := by
  simp only [schurValues, rankOneValues, hM.add, hM.mul, hM.div _ _ hk, hM.lit]
  norm_num only [Rat.cast_neg, Rat.cast_one]
  ring

/-- The negative-reciprocal update on a finite matrix is the existing exact elimination
step, including all retired rows and columns. -/
theorem schurValues_eq_eliminationStep {dec : K → ℝ} {M : Machine K}
    (hM : ExactModel dec M) {N : ℕ} (A : ℕ → ℕ → K) (k : Fin N)
    (hk : dec (A k k) ≠ 0) :
    (fun i j : Fin N => dec (schurValues M A k i j)) =
      eliminationStep (fun i j : Fin N => dec (A i j)) k := by
  funext i j
  exact schurValues_dec hM A k i j hk

end NLAlib.LU
