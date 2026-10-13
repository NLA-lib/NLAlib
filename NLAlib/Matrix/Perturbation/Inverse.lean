/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Perturbation of the inverse and of linear systems

The Neumann series for `(1 - F)⁻¹` when `‖F‖₂ < 1`, the resulting bounds for the inverse of a
perturbed matrix `A + E`, and the classical forward error bounds for the solution of a linear
system in terms of the condition number.

## Main results

* `NLAlib.isUnit_one_sub_of_specNorm_lt_one`, `NLAlib.hasSum_pow_inv_one_sub`: the Neumann series.
* `NLAlib.isUnit_add_of_specNorm_inv_mul_lt_one`, `NLAlib.specNorm_inv_add_le`,
  `NLAlib.specNorm_inv_add_sub_inv_le`: perturbation of the inverse.
* `NLAlib.norm_sub_le_specNorm_inv_mul_norm_sub_mulVec`: forward error from the residual.
* `NLAlib.norm_sub_le_of_add_mulVec_eq`, `NLAlib.norm_sub_le_conditionNumber_mul_of_add_mulVec_eq`:
  perturbation of a linear system.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The Neumann series -/

/-- If `‖F‖₂ < 1` then `1 - F` is invertible.
[HornJohnson2013, Corollary 5.6.16]. Port of `NLAlib.isUnit_one_sub_of_specNorm_lt_one`. -/
theorem isUnit_one_sub_of_specNorm_lt_one {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    IsUnit (1 - F) := by
  sorry

/-- **The Neumann series**: if `‖F‖₂ < 1` then `(1 - F)⁻¹ = ∑ F ^ k`.
[HornJohnson2013, Corollary 5.6.16]. Port of `NLAlib.hasSum_pow_inv_one_sub`, there over `ℝ`.
Result: neumann-series -/
theorem hasSum_pow_inv_one_sub {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    HasSum (fun k : ℕ => F ^ k) (1 - F)⁻¹ := by
  sorry

/-- `‖(1 - F)⁻¹‖₂ ≤ 1 / (1 - ‖F‖₂)` when `‖F‖₂ < 1`.
Port of `NLAlib.specNorm_inv_one_sub_le`. -/
theorem specNorm_inv_one_sub_le {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    specNorm (1 - F)⁻¹ ≤ (1 - specNorm F)⁻¹ := by
  sorry

/-- `‖(1 - F)⁻¹ - 1‖₂ ≤ ‖F‖₂ / (1 - ‖F‖₂)` when `‖F‖₂ < 1`.
Port of `NLAlib.specNorm_inv_one_sub_sub_one_le`. -/
theorem specNorm_inv_one_sub_sub_one_le {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    specNorm ((1 - F)⁻¹ - 1) ≤ specNorm F / (1 - specNorm F) := by
  sorry

/-! ### The inverse of a perturbed matrix -/

/-- A perturbation `E` with `‖A⁻¹ E‖₂ < 1` keeps `A + E` invertible.
[GolubVanLoan2013, Theorem 2.3.4]. Port of `NLAlib.isUnit_add_of_specNorm_inv_mul_lt_one`. -/
theorem isUnit_add_of_specNorm_inv_mul_lt_one {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) : IsUnit (A + E) := by
  sorry

/-- A perturbation `E` with `‖A⁻¹‖₂ ‖E‖₂ < 1` keeps `A + E` invertible. -/
theorem isUnit_add_of_specNorm_inv_mul_specNorm_lt_one {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm A⁻¹ * specNorm E < 1) : IsUnit (A + E) := by
  sorry

/-- A perturbation smaller than the smallest singular value keeps `A + E` invertible. -/
theorem isUnit_add_of_specNorm_lt_singularValues {A E : Matrix n n 𝕜} {k : ℕ}
    (hk : k + 1 = Fintype.card n) (hE : specNorm E < singularValues A k) : IsUnit (A + E) := by
  sorry

/-- The difference of two inverses: `(A + E)⁻¹ - A⁻¹ = -(A + E)⁻¹ E A⁻¹`. -/
theorem inv_add_sub_inv {A E : Matrix n n 𝕜} (hA : IsUnit A) (hAE : IsUnit (A + E)) :
    (A + E)⁻¹ - A⁻¹ = -((A + E)⁻¹ * E * A⁻¹) := by
  sorry

/-- `‖(A + E)⁻¹‖₂ ≤ ‖A⁻¹‖₂ / (1 - ‖A⁻¹ E‖₂)`.
[GolubVanLoan2013, Theorem 2.3.4]. Port of `NLAlib.specNorm_inv_add_le`. -/
theorem specNorm_inv_add_le {A E : Matrix n n 𝕜} (hA : IsUnit A) (hE : specNorm (A⁻¹ * E) < 1) :
    specNorm (A + E)⁻¹ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) := by
  sorry

/-- **Perturbation of the inverse**:
`‖(A + E)⁻¹ - A⁻¹‖₂ ≤ ‖A⁻¹‖₂² ‖E‖₂ / (1 - ‖A⁻¹ E‖₂)`.
[GolubVanLoan2013, Theorem 2.3.4]. Port of `NLAlib.specNorm_inv_add_sub_inv_le`.
Result: inverse-perturbation -/
theorem specNorm_inv_add_sub_inv_le {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) :
    specNorm ((A + E)⁻¹ - A⁻¹) ≤ specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E)) := by
  sorry

/-- Perturbation of the inverse in any unitarily invariant norm:
`‖(A + E)⁻¹ - A⁻¹‖ ≤ ‖(A + E)⁻¹‖₂ ‖E‖ ‖A⁻¹‖₂`.
Port of `NLAlib.frobNorm_inv_add_sub_inv_le`, there for the Frobenius norm. -/
theorem SymmetricGauge.matrixNorm_inv_add_sub_inv_le (Φ : SymmetricGauge) {A E : Matrix n n 𝕜}
    (hA : IsUnit A) (hAE : IsUnit (A + E)) :
    Φ.matrixNorm ((A + E)⁻¹ - A⁻¹) ≤ specNorm (A + E)⁻¹ * Φ.matrixNorm E * specNorm A⁻¹ := by
  sorry

/-- **Relative perturbation of the inverse through the condition number.** If
`‖E‖₂ ≤ ε ‖A‖₂` and `κ(A) ε < 1`, then
`‖(A + E)⁻¹ - A⁻¹‖₂ ≤ κ ε / (1 - κ ε) · ‖A⁻¹‖₂`.
[GolubVanLoan2013, §2.6.2]; [Higham2002, §6.2]. -/
theorem specNorm_inv_add_sub_inv_le_conditionNumber_mul {A E : Matrix n n 𝕜} (hA : IsUnit A)
    {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A) (hε : conditionNumber A * ε < 1) :
    specNorm ((A + E)⁻¹ - A⁻¹) ≤
      conditionNumber A * ε / (1 - conditionNumber A * ε) * specNorm A⁻¹ := by
  sorry

/-! ### Linear systems -/

/-- **Forward error from the residual.** If `A x = b` with `A` invertible, then for any `y`,
`‖x - y‖ ≤ ‖A⁻¹‖₂ ‖b - A y‖`. -/
theorem norm_sub_le_specNorm_inv_mul_norm_sub_mulVec {A : Matrix n n 𝕜} (hA : IsUnit A)
    {x b : n → 𝕜} (hx : A *ᵥ x = b) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (x - y)‖ ≤ specNorm A⁻¹ * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ := by
  sorry

/-- **Relative forward error from the relative residual**, without divisions:
`‖x - y‖ ‖b‖ ≤ κ(A) ‖b - A y‖ ‖x‖`.
[GolubVanLoan2013, §2.6.4]. Port of `NLAlib.norm_sub_div_le_conditionNumber_mul`. -/
theorem norm_sub_mul_norm_le_conditionNumber_mul {A : Matrix n n 𝕜} (hA : IsUnit A)
    {x b : n → 𝕜} (hx : A *ᵥ x = b) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (x - y)‖ * ‖WithLp.toLp 2 b‖ ≤
      conditionNumber A * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ * ‖WithLp.toLp 2 x‖ := by
  sorry

/-- **Perturbation of a linear system.** If `A x = b`, `(A + E) y = b + f` and `‖A⁻¹ E‖₂ < 1`,
then `‖y - x‖ ≤ ‖A⁻¹‖₂ / (1 - ‖A⁻¹ E‖₂) · (‖f‖ + ‖E‖₂ ‖x‖)`.
[GolubVanLoan2013, Theorem 2.6.2]; [Higham2002, Theorem 7.2].
Port of `NLAlib.norm_div_le_of_add_mulVec_add`. -/
theorem norm_sub_le_of_add_mulVec_eq {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) {x y b f : n → 𝕜} (hx : A *ᵥ x = b)
    (hy : (A + E) *ᵥ y = b + f) :
    ‖WithLp.toLp 2 (y - x)‖ ≤
      specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) *
        (‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖) := by
  sorry

/-- **Relative perturbation of a linear system through the condition number.** If `A x = b`,
`(A + E) y = b + f`, `‖E‖₂ ≤ ε ‖A‖₂`, `‖f‖ ≤ ε ‖b‖` and `κ(A) ε < 1`, then
`‖y - x‖ ≤ 2 ε κ / (1 - κ ε) · ‖x‖`.
[GolubVanLoan2013, Theorem 2.6.2].
Port of `NLAlib.norm_div_le_of_add_mulVec_add`.
Result: linear-system-perturbation -/
theorem norm_sub_le_conditionNumber_mul_of_add_mulVec_eq {A E : Matrix n n 𝕜} (hA : IsUnit A)
    {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A) (hε : conditionNumber A * ε < 1)
    {x y b f : n → 𝕜} (hx : A *ᵥ x = b) (hy : (A + E) *ᵥ y = b + f)
    (hf : ‖WithLp.toLp 2 f‖ ≤ ε * ‖WithLp.toLp 2 b‖) :
    ‖WithLp.toLp 2 (y - x)‖ ≤
      2 * ε * conditionNumber A / (1 - conditionNumber A * ε) * ‖WithLp.toLp 2 x‖ := by
  sorry

end NLAlib
