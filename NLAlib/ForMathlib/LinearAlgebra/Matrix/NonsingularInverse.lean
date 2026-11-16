/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The inverse of a negated matrix

A fact about `Matrix.inv` that Mathlib does not yet have. Upstream candidate for
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`.

## Main results

* `Matrix.inv_neg`: $(-\mathbf{A})^{-1} = -\mathbf{A}^{-1}$, with no invertibility hypothesis.
-/

@[expose] public section

namespace Matrix

variable {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]

/-- The inverse of $-\mathbf{A}$ is $-\mathbf{A}^{-1}$, for every square matrix: both sides are
$0$ when $\mathbf{A}$ is singular. -/
theorem inv_neg (A : Matrix n n α) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · refine inv_eq_left_inv ?_
    rw [neg_mul_neg, nonsing_inv_mul A h]
  · have h' : ¬ IsUnit (-A).det := by
      rwa [det_neg, IsUnit.mul_iff, and_iff_right ((isUnit_one.neg).pow _)]
    rw [nonsing_inv_apply_not_isUnit A h, nonsing_inv_apply_not_isUnit _ h', neg_zero]

end Matrix
