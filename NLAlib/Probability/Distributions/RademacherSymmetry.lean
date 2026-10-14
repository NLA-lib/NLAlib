/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.Rademacher

/-!
# Sign-flip symmetry of the Rademacher laws

The Rademacher law is symmetric, and flipping one coordinate of a vector of independent random
signs preserves its law. These are the symmetries behind the Rademacher moment recursion of the
noncommutative Khintchine inequality
(`NLAlib/Probability/MatrixConcentration/Khintchine.lean`). Statements with
`HasLaw ε (rademacherVector n) μ` transport through `integral_map`; no random-variable twin is
stated.

This skeleton file is to be merged into `Rademacher.lean`, which owns the subject (P5c §8).

## Main results

* `NLAlib.measurePreserving_neg_rademacherMeasure`.
* `NLAlib.measurePreserving_update_neg_rademacherVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- The Rademacher law is symmetric: `x ↦ -x` preserves it. -/
theorem measurePreserving_neg_rademacherMeasure :
    MeasurePreserving (fun x : ℝ => -x) rademacherMeasure rademacherMeasure := by
  refine ⟨measurable_neg, ?_⟩
  rw [rademacherMeasure, Measure.map_smul, Measure.map_add _ _ measurable_neg,
    Measure.map_dirac' measurable_neg, Measure.map_dirac' measurable_neg, neg_neg, add_comm]

/-- Flipping the sign of one coordinate of a vector of independent random signs preserves its
law. Proof: Mathlib's `measurePreserving_pi`, with `-·` in coordinate `i` and `id` elsewhere. -/
theorem measurePreserving_update_neg_rademacherVector [DecidableEq n] (i : n) :
    MeasurePreserving (fun x : n → ℝ => Function.update x i (-x i))
      (rademacherVector n) (rademacherVector n) := by
  have h := measurePreserving_pi (fun _ : n => rademacherMeasure) (fun _ => rademacherMeasure)
    (f := fun j (x : ℝ) => if j = i then -x else x) fun j => by
      by_cases hj : j = i
      · simp only [hj, if_true]
        exact measurePreserving_neg_rademacherMeasure
      · simp only [hj, if_false]
        exact MeasurePreserving.id _
  convert h using 1
  funext x j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

end NLAlib
