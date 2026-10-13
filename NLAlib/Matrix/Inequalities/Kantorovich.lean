/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# The Kantorovich and Wielandt inequalities

For a positive definite matrix `A` with spectrum in `[a, b]`, the product of the quadratic forms
of `A` and `A⁻¹` at a unit vector is at most `(a + b)² / (4 a b)`, and the bilinear form at two
orthogonal vectors is controlled by `(b - a) / (b + a)`. These constants govern the convergence of
steepest descent and of the conjugate gradient method.

## Main results

* `NLAlib.add_smul_inv_le_smul_one`: the operator form `A + (a b) A⁻¹ ≤ (a + b) • 1`.
* `NLAlib.re_quadForm_mul_re_quadForm_inv_le`: the Kantorovich inequality.
* `Matrix.PosDef.re_quadForm_mul_re_quadForm_inv_le_conditionNumber`: with the condition number.
* `NLAlib.norm_sq_star_dotProduct_mulVec_le_of_dotProduct_eq_zero`: the Wielandt inequality.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Kantorovich inequality, operator form.** If `a • 1 ≤ A ≤ b • 1` with `0 < a`, then
`A + (a b) A⁻¹ ≤ (a + b) • 1`.
[HornJohnson2013, §7.4.12].
Port of `NLAlib.add_smul_inv_le_smul_one_of_sandwich`, there over `ℝ`. -/
theorem add_smul_inv_le_smul_one {A : Matrix n n 𝕜} {a b : ℝ} (ha : 0 < a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) :
    A + (a * b) • A⁻¹ ≤ (a + b) • (1 : Matrix n n 𝕜) := by
  sorry

/-- **The Kantorovich inequality.** If `a • 1 ≤ A ≤ b • 1` with `0 < a`, then for every vector
`x`, `(xᴴ A x) (xᴴ A⁻¹ x) ≤ (a + b)² / (4 a b) · ‖x‖⁴`.
[HornJohnson2013, Theorem 7.4.41].
Port of `NLAlib.quadForm_mul_quadForm_inv_le_of_sandwich`, there over `ℝ`.
Result: kantorovich-inequality -/
theorem re_quadForm_mul_re_quadForm_inv_le {A : Matrix n n 𝕜} {a b : ℝ} (ha : 0 < a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) (x : n → 𝕜) :
    RCLike.re (quadForm A x) * RCLike.re (quadForm A⁻¹ x) ≤
      (a + b) ^ 2 / (4 * a * b) * ‖WithLp.toLp 2 x‖ ^ 4 := by
  sorry

/-- **The Kantorovich inequality with the condition number**: for positive definite `A`,
`(xᴴ A x) (xᴴ A⁻¹ x) ≤ (κ + 1)² / (4 κ) · ‖x‖⁴` with `κ = conditionNumber A`.
[HornJohnson2013, Theorem 7.4.41].
Port of `NLAlib.quadForm_mul_quadForm_inv_le_moorePenroseConditionNumber_sqrt`, there over `ℝ`.
Result: kantorovich-inequality -/
theorem _root_.Matrix.PosDef.re_quadForm_mul_re_quadForm_inv_le_conditionNumber
    {A : Matrix n n 𝕜} (hA : A.PosDef) (x : n → 𝕜) :
    RCLike.re (quadForm A x) * RCLike.re (quadForm A⁻¹ x) ≤
      (conditionNumber A + 1) ^ 2 / (4 * conditionNumber A) * ‖WithLp.toLp 2 x‖ ^ 4 := by
  sorry

/-- **The Wielandt inequality.** If `a • 1 ≤ A ≤ b • 1` with `0 < a` and `x`, `y` are
orthogonal, then `|xᴴ A y|² ≤ ((b - a) / (b + a))² (xᴴ A x) (yᴴ A y)`.
[HornJohnson2013, Theorem 7.4.34].
Port of `NLAlib.sq_bilinear_le_sq_ratio_mul_quadForm_of_sandwich`, there over `ℝ`.
Result: wielandt-inequality -/
theorem norm_sq_star_dotProduct_mulVec_le_of_dotProduct_eq_zero {A : Matrix n n 𝕜} {a b : ℝ}
    (ha : 0 < a) (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜))
    {x y : n → 𝕜} (hxy : star x ⬝ᵥ y = 0) :
    ‖star x ⬝ᵥ A *ᵥ y‖ ^ 2 ≤
      ((b - a) / (b + a)) ^ 2 * RCLike.re (quadForm A x) * RCLike.re (quadForm A y) := by
  sorry

end NLAlib
