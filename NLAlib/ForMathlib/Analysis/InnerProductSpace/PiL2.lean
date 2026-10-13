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
`star x ⬝ᵥ x`, and the behaviour of that norm under conjugation, reindexing, extension by zero
and concatenation. Upstream candidates for `Mathlib.Analysis.InnerProductSpace.PiL2`.

## Main results

* `EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct`: the inner product is `star x ⬝ᵥ y`.
* `EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct`: `‖x‖ ^ 2 = re (star x ⬝ᵥ x)`.
* `EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq`: `star x ⬝ᵥ x = ‖x‖ ^ 2` in `𝕜`.
* `EuclideanSpace.norm_toLp_star`: `‖star x‖ = ‖x‖`.
* `EuclideanSpace.norm_toLp_comp_equiv`: `‖x ∘ e‖ = ‖x‖` for a bijection `e`.
* `EuclideanSpace.norm_toLp_comp_le_of_injective`: `‖y ∘ e‖ ≤ ‖y‖` for an injection `e`.
* `EuclideanSpace.norm_toLp_extend_zero`: extending by zero along an injection keeps the norm.
* `EuclideanSpace.norm_toLp_sumElim_sq`: `‖Sum.elim x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2`.
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

/-! ### Conjugation, reindexing, extension by zero and concatenation -/

/-- Entrywise conjugation does not change the Euclidean norm of a coordinate vector. -/
theorem norm_toLp_star (x : n → 𝕜) : ‖WithLp.toLp 2 (star x)‖ = ‖WithLp.toLp 2 x‖ := by
  simp [EuclideanSpace.norm_eq]

/-- Relabelling the coordinates by a bijection does not change the Euclidean norm. -/
theorem norm_toLp_comp_equiv {p : Type*} [Fintype p] (x : n → 𝕜) (e : p ≃ n) :
    ‖WithLp.toLp 2 (x ∘ e)‖ = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt (e.sum_comp fun i => ‖x i‖ ^ 2)

/-- Selecting coordinates along an injection does not increase the Euclidean norm. -/
theorem norm_toLp_comp_le_of_injective {p : Type*} [Fintype p] {e : p → n}
    (he : Function.Injective e) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (y ∘ e)‖ ≤ ‖WithLp.toLp 2 y‖ := by
  classical
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Function.comp_apply]
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := fun k => ‖y k‖ ^ 2) he.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => sq_nonneg _

/-- Extending a coordinate vector by zero along an injection does not change its Euclidean
norm. -/
theorem norm_toLp_extend_zero {p : Type*} [Fintype p] {e : p → n} (he : Function.Injective e)
    (x : p → 𝕜) : ‖WithLp.toLp 2 (Function.extend e x 0)‖ = ‖WithLp.toLp 2 x‖ := by
  have h : ∑ i, ‖x i‖ ^ 2 = ∑ k, ‖Function.extend e x 0 k‖ ^ 2 := by
    refine Fintype.sum_of_injective e he _ _ (fun k hk => ?_) fun i => ?_
    · rw [Function.extend_apply' _ _ _ hk, Pi.zero_apply, norm_zero, zero_pow two_ne_zero]
    · rw [he.extend_apply]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt h.symm

/-- **Pythagoras for concatenated coordinate vectors**: the squared Euclidean norm of
`Sum.elim x y` is the sum of the squared Euclidean norms of `x` and `y`. -/
theorem norm_toLp_sumElim_sq {m : Type*} [Fintype m] (x : m → 𝕜) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (Sum.elim x y)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 + ‖WithLp.toLp 2 y‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

end EuclideanSpace
