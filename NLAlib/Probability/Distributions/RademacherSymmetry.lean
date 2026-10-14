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
  sorry

/-- Flipping the sign of one coordinate of a vector of independent random signs preserves its
law. Proof: Mathlib's `measurePreserving_pi`, with `-·` in coordinate `i` and `id` elsewhere. -/
theorem measurePreserving_update_neg_rademacherVector [DecidableEq n] (i : n) :
    MeasurePreserving (fun x : n → ℝ => Function.update x i (-x i))
      (rademacherVector n) (rademacherVector n) := by
  sorry

end NLAlib
