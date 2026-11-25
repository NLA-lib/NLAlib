/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.SchurValues
public import NLAlib.Matrix.Perturbation.SchurRelative

/-!
# Relative error of the actual Schur words

The five scalar roundings in the actual saved-pivot word recurrence give the original-entry
term and the five-factor rank-one term. This is a numerical consequence of the words written
by the shared Schur routine, independent of a particular representation or execution witness.

## Main results

* `NLAlib.LU.abs_sub_schurValues_le`: local relative defect of the actual word recurrence.
-/

@[expose] public section

namespace NLAlib.LU

open Ops Computation

variable {K : Type}

/-- The actual five rounded saved-pivot operations give the local componentwise defect.
The multiplication order on words is retained; commutation is only used on decoded reals. -/
theorem abs_sub_schurValues_le {M : Machine K} {dec : K → ℝ} {u : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hu1 : u < 1)
    (A : ℕ → ℕ → K) (k : ℕ) (hp : dec (A k k) ≠ 0) (i j : ℕ) :
    |dec (schurValues M A k i j) -
      (dec (A i j) - dec (A i k) * dec (A k j) / dec (A k k))| ≤
      u * |dec (A i j)| + roundingFactor 5 u *
        |dec (A i k) * dec (A k j) / dec (A k k)| := by
  let c := M.div (M.lit (-1)) (A k k)
  let t := M.mul c (A k j)
  let q := M.mul t (A i k)
  have hell : RelErr u (-1) (dec (M.lit (-1))) := by
    apply relErr_of_abs_sub_le hu
    simpa only [Rat.cast_neg, Rat.cast_one, abs_neg, abs_one, mul_one] using hM.lit (-1)
  have hc : RelErr u (dec (M.lit (-1)) / dec (A k k)) (dec c) :=
    relErr_of_abs_sub_le hu (hM.div _ _ hp)
  have ht : RelErr u (dec c * dec (A k j)) (dec t) := relErr_of_abs_sub_le hu (hM.mul _ _)
  have hq : RelErr u (dec (A i k) * dec t) (dec q) := by
    simpa only [mul_comm] using relErr_of_abs_sub_le hu (hM.mul t (A i k))
  have hz : RelErr u (dec (A i j) + dec q) (dec (M.add (A i j) q)) :=
    relErr_of_abs_sub_le hu (hM.add _ _)
  exact abs_sub_schurUpdate_le_of_relErr hu1 hell hc ht hq hz

end NLAlib.LU
