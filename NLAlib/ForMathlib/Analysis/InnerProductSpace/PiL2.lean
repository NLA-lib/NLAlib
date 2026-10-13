/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Euclidean norm of a coordinate vector as a dot product

Bridges between the Euclidean norm `‖WithLp.toLp 2 x‖` of a vector `x : n → 𝕜` and the pairing
`star x ⬝ᵥ x`. Upstream candidates for `Mathlib.Analysis.InnerProductSpace.PiL2`.

## Main results

* `EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct`: the inner product is `star x ⬝ᵥ y`.
* `EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct`: `‖x‖ ^ 2 = re (star x ⬝ᵥ x)`.
* `EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq`: `star x ⬝ᵥ x = ‖x‖ ^ 2` in `𝕜`.
-/

@[expose] public section

namespace EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The inner product of two coordinate vectors in Euclidean space is `star x ⬝ᵥ y`. -/
theorem inner_toLp_toLp_eq_star_dotProduct (x y : n → 𝕜) :
    inner 𝕜 (WithLp.toLp 2 x) (WithLp.toLp 2 y) = star x ⬝ᵥ y := by
  rw [inner_toLp_toLp, dotProduct_comm]

/-- The squared Euclidean norm of a coordinate vector is the real part of `star x ⬝ᵥ x`.
Port of `NLAlib.norm_toLp_sq_eq_re_star_dotProduct`. -/
theorem norm_toLp_sq_eq_re_star_dotProduct (x : n → 𝕜) :
    ‖WithLp.toLp 2 x‖ ^ 2 = RCLike.re (star x ⬝ᵥ x) := by
  rw [← inner_toLp_toLp_eq_star_dotProduct, inner_self_eq_norm_sq]

/-- The pairing of a coordinate vector with itself is its squared Euclidean norm, as an element
of `𝕜`. -/
theorem star_dotProduct_self_eq_coe_norm_sq (x : n → 𝕜) :
    star x ⬝ᵥ x = ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_toLp_toLp_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

/-- Over `ℝ`, the squared Euclidean norm of a coordinate vector is `x ⬝ᵥ x`.
Port of `NLAlib.norm_toLp_sq_eq_dotProduct_self`. -/
theorem norm_toLp_sq_eq_dotProduct_self (x : n → ℝ) : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
  rw [norm_toLp_sq_eq_re_star_dotProduct, star_trivial, RCLike.re_to_real]

end EuclideanSpace
