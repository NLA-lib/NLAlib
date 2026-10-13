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

private theorem mul_inv_of_isUnit {A : Matrix n n 𝕜} (hA : IsUnit A) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA)

private theorem inv_mul_of_isUnit {A : Matrix n n 𝕜} (hA : IsUnit A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)

/-- If `‖F‖₂ < 1` then `1 - F` is invertible.
[HornJohnson2013, Corollary 5.6.16]. Port of `NLAlib.isUnit_one_sub_of_specNorm_lt_one`. -/
theorem isUnit_one_sub_of_specNorm_lt_one {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    IsUnit (1 - F) := by
  open scoped Matrix.Norms.L2Operator in
  exact isUnit_one_sub_of_norm_lt_one (R := Matrix n n 𝕜) h

/-- **The Neumann series**: if `‖F‖₂ < 1` then `(1 - F)⁻¹ = ∑ F ^ k`.
[HornJohnson2013, Corollary 5.6.16]. Port of `NLAlib.hasSum_pow_inv_one_sub`, there over `ℝ`.
Result: neumann-series -/
theorem hasSum_pow_inv_one_sub {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    HasSum (fun k : ℕ => F ^ k) (1 - F)⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  open scoped Matrix.Norms.L2Operator in
  exact hasSum_geom_series_inverse (R := Matrix n n 𝕜) F h

private theorem inv_one_sub_eq_one_add_mul {F : Matrix n n 𝕜} (h : IsUnit (1 - F)) :
    (1 - F)⁻¹ = 1 + F * (1 - F)⁻¹ := by
  have h1 := mul_inv_of_isUnit h
  rw [Matrix.sub_mul, Matrix.one_mul] at h1
  exact eq_add_of_sub_eq h1

/-- `‖(1 - F)⁻¹‖₂ ≤ 1 / (1 - ‖F‖₂)` when `‖F‖₂ < 1`.
Port of `NLAlib.specNorm_inv_one_sub_le`. -/
theorem specNorm_inv_one_sub_le {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    specNorm (1 - F)⁻¹ ≤ (1 - specNorm F)⁻¹ := by
  have hle : specNorm (1 - F)⁻¹ ≤ 1 + specNorm F * specNorm (1 - F)⁻¹ := by
    calc specNorm (1 - F)⁻¹ = specNorm (1 + F * (1 - F)⁻¹) := by
          rw [← inv_one_sub_eq_one_add_mul (isUnit_one_sub_of_specNorm_lt_one h)]
      _ ≤ specNorm (1 : Matrix n n 𝕜) + specNorm (F * (1 - F)⁻¹) := specNorm_add_le _ _
      _ ≤ 1 + specNorm F * specNorm (1 - F)⁻¹ := add_le_add specNorm_one_le (specNorm_mul_le _ _)
  rw [← one_div (1 - specNorm F), le_div_iff₀ (by linarith)]
  linarith

/-- `‖(1 - F)⁻¹ - 1‖₂ ≤ ‖F‖₂ / (1 - ‖F‖₂)` when `‖F‖₂ < 1`.
Port of `NLAlib.specNorm_inv_one_sub_sub_one_le`. -/
theorem specNorm_inv_one_sub_sub_one_le {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    specNorm ((1 - F)⁻¹ - 1) ≤ specNorm F / (1 - specNorm F) := by
  have he : (1 - F)⁻¹ - 1 = F * (1 - F)⁻¹ :=
    sub_eq_of_eq_add' (inv_one_sub_eq_one_add_mul (isUnit_one_sub_of_specNorm_lt_one h))
  rw [he, div_eq_mul_inv]
  exact (specNorm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (specNorm_inv_one_sub_le h) (specNorm_nonneg F))

/-! ### The inverse of a perturbed matrix -/

private theorem add_eq_mul_one_sub_neg {A : Matrix n n 𝕜} (hA : IsUnit A) (E : Matrix n n 𝕜) :
    A + E = A * (1 - -(A⁻¹ * E)) := by
  rw [sub_neg_eq_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, mul_inv_of_isUnit hA,
    Matrix.one_mul]

/-- A perturbation `E` with `‖A⁻¹ E‖₂ < 1` keeps `A + E` invertible.
[GolubVanLoan2013, Theorem 2.3.4]. Port of `NLAlib.isUnit_add_of_specNorm_inv_mul_lt_one`. -/
theorem isUnit_add_of_specNorm_inv_mul_lt_one {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) : IsUnit (A + E) := by
  rw [add_eq_mul_one_sub_neg hA E]
  exact hA.mul (isUnit_one_sub_of_specNorm_lt_one (by rwa [specNorm_neg]))

/-- A perturbation `E` with `‖A⁻¹‖₂ ‖E‖₂ < 1` keeps `A + E` invertible. -/
theorem isUnit_add_of_specNorm_inv_mul_specNorm_lt_one {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm A⁻¹ * specNorm E < 1) : IsUnit (A + E) := by
  exact isUnit_add_of_specNorm_inv_mul_lt_one hA ((specNorm_mul_le _ _).trans_lt hE)

/-- A perturbation smaller than the smallest singular value keeps `A + E` invertible. -/
theorem isUnit_add_of_specNorm_lt_singularValues {A E : Matrix n n 𝕜} {k : ℕ}
    (hk : k + 1 = Fintype.card n) (hE : specNorm E < singularValues A k) : IsUnit (A + E) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  by_contra h
  exact absurd (singularValues_last_le_specNorm_of_not_injective_add A hk h) (not_le.mpr hE)

/-- The difference of two inverses: `(A + E)⁻¹ - A⁻¹ = -(A + E)⁻¹ E A⁻¹`. -/
theorem inv_add_sub_inv {A E : Matrix n n 𝕜} (hA : IsUnit A) (hAE : IsUnit (A + E)) :
    (A + E)⁻¹ - A⁻¹ = -((A + E)⁻¹ * E * A⁻¹) := by
  rw [Matrix.inv_sub_inv (iff_of_true hAE hA), sub_add_cancel_left, Matrix.mul_neg,
    Matrix.neg_mul]

/-- `‖(A + E)⁻¹‖₂ ≤ ‖A⁻¹‖₂ / (1 - ‖A⁻¹ E‖₂)`.
[GolubVanLoan2013, Theorem 2.3.4]. Port of `NLAlib.specNorm_inv_add_le`. -/
theorem specNorm_inv_add_le {A E : Matrix n n 𝕜} (hA : IsUnit A) (hE : specNorm (A⁻¹ * E) < 1) :
    specNorm (A + E)⁻¹ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) := by
  have hF : specNorm (-(A⁻¹ * E)) < 1 := by rwa [specNorm_neg]
  have h := specNorm_inv_one_sub_le hF
  rw [specNorm_neg] at h
  rw [add_eq_mul_one_sub_neg hA E, Matrix.mul_inv_rev, div_eq_inv_mul]
  exact (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h (specNorm_nonneg _))

/-- **Perturbation of the inverse**:
`‖(A + E)⁻¹ - A⁻¹‖₂ ≤ ‖A⁻¹‖₂² ‖E‖₂ / (1 - ‖A⁻¹ E‖₂)`.
[GolubVanLoan2013, Theorem 2.3.4]. Port of `NLAlib.specNorm_inv_add_sub_inv_le`.
Result: inverse-perturbation -/
theorem specNorm_inv_add_sub_inv_le {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) :
    specNorm ((A + E)⁻¹ - A⁻¹) ≤ specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E)) := by
  rw [inv_add_sub_inv hA (isUnit_add_of_specNorm_inv_mul_lt_one hA hE), specNorm_neg]
  calc specNorm ((A + E)⁻¹ * E * A⁻¹)
      ≤ specNorm (A + E)⁻¹ * specNorm E * specNorm A⁻¹ :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) * specNorm E * specNorm A⁻¹ := by
        gcongr
        exact specNorm_inv_add_le hA hE
    _ = specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E)) := by ring

/-- Perturbation of the inverse in any unitarily invariant norm:
`‖(A + E)⁻¹ - A⁻¹‖ ≤ ‖(A + E)⁻¹‖₂ ‖E‖ ‖A⁻¹‖₂`.
Port of `NLAlib.frobNorm_inv_add_sub_inv_le`, there for the Frobenius norm. -/
theorem SymmetricGauge.matrixNorm_inv_add_sub_inv_le (Φ : SymmetricGauge) {A E : Matrix n n 𝕜}
    (hA : IsUnit A) (hAE : IsUnit (A + E)) :
    Φ.matrixNorm ((A + E)⁻¹ - A⁻¹) ≤ specNorm (A + E)⁻¹ * Φ.matrixNorm E * specNorm A⁻¹ := by
  rw [inv_add_sub_inv hA hAE, SymmetricGauge.matrixNorm_neg]
  exact (Φ.matrixNorm_mul_le_mul_specNorm _ _).trans
    (mul_le_mul_of_nonneg_right (Φ.matrixNorm_mul_le_specNorm_mul _ _) (specNorm_nonneg _))

private theorem specNorm_inv_mul_specNorm_le_conditionNumber_mul {A E : Matrix n n 𝕜}
    (hA : IsUnit A) {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A) :
    specNorm A⁻¹ * specNorm E ≤ conditionNumber A * ε := by
  rw [conditionNumber_of_isUnit hA]
  calc specNorm A⁻¹ * specNorm E ≤ specNorm A⁻¹ * (ε * specNorm A) :=
        mul_le_mul_of_nonneg_left hE (specNorm_nonneg _)
    _ = specNorm A * specNorm A⁻¹ * ε := by ring

/-- **Relative perturbation of the inverse through the condition number.** If
`‖E‖₂ ≤ ε ‖A‖₂` and `κ(A) ε < 1`, then
`‖(A + E)⁻¹ - A⁻¹‖₂ ≤ κ ε / (1 - κ ε) · ‖A⁻¹‖₂`.
[GolubVanLoan2013, §2.6.2]; [Higham2002, §6.2]. -/
theorem specNorm_inv_add_sub_inv_le_conditionNumber_mul {A E : Matrix n n 𝕜} (hA : IsUnit A)
    {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A) (hε : conditionNumber A * ε < 1) :
    specNorm ((A + E)⁻¹ - A⁻¹) ≤
      conditionNumber A * ε / (1 - conditionNumber A * ε) * specNorm A⁻¹ := by
  have hκ := specNorm_inv_mul_specNorm_le_conditionNumber_mul hA hE
  have ht : specNorm (A⁻¹ * E) ≤ conditionNumber A * ε := (specNorm_mul_le _ _).trans hκ
  calc specNorm ((A + E)⁻¹ - A⁻¹)
      ≤ specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E)) :=
        specNorm_inv_add_sub_inv_le hA (ht.trans_lt hε)
    _ = specNorm A⁻¹ * specNorm E / (1 - specNorm (A⁻¹ * E)) * specNorm A⁻¹ := by ring
    _ ≤ conditionNumber A * ε / (1 - conditionNumber A * ε) * specNorm A⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg _)
        exact div_le_div₀ ((mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)).trans hκ) hκ
          (by linarith) (by linarith)

/-! ### Linear systems -/

/-- **Forward error from the residual.** If `A x = b` with `A` invertible, then for any `y`,
`‖x - y‖ ≤ ‖A⁻¹‖₂ ‖b - A y‖`. -/
theorem norm_sub_le_specNorm_inv_mul_norm_sub_mulVec {A : Matrix n n 𝕜} (hA : IsUnit A)
    {x b : n → 𝕜} (hx : A *ᵥ x = b) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (x - y)‖ ≤ specNorm A⁻¹ * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ := by
  have h : x - y = A⁻¹ *ᵥ (b - A *ᵥ y) := by
    rw [← hx, ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, inv_mul_of_isUnit hA,
      Matrix.one_mulVec]
  nth_rewrite 1 [h]
  exact norm_toLp_mulVec_le _ _

/-- **Relative forward error from the relative residual**, without divisions:
`‖x - y‖ ‖b‖ ≤ κ(A) ‖b - A y‖ ‖x‖`.
[GolubVanLoan2013, §2.6.4]. Port of `NLAlib.norm_sub_div_le_conditionNumber_mul`. -/
theorem norm_sub_mul_norm_le_conditionNumber_mul {A : Matrix n n 𝕜} (hA : IsUnit A)
    {x b : n → 𝕜} (hx : A *ᵥ x = b) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (x - y)‖ * ‖WithLp.toLp 2 b‖ ≤
      conditionNumber A * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ * ‖WithLp.toLp 2 x‖ := by
  have h₁ := norm_sub_le_specNorm_inv_mul_norm_sub_mulVec hA hx y
  have h₂ : ‖WithLp.toLp 2 b‖ ≤ specNorm A * ‖WithLp.toLp 2 x‖ := by
    rw [← hx]
    exact norm_toLp_mulVec_le A x
  rw [conditionNumber_of_isUnit hA]
  calc ‖WithLp.toLp 2 (x - y)‖ * ‖WithLp.toLp 2 b‖
      ≤ specNorm A⁻¹ * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ * (specNorm A * ‖WithLp.toLp 2 x‖) :=
        mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
    _ = specNorm A * specNorm A⁻¹ * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ * ‖WithLp.toLp 2 x‖ := by ring

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
  have hAE := isUnit_add_of_specNorm_inv_mul_lt_one hA hE
  have h : y - x = (A + E)⁻¹ *ᵥ (f - E *ᵥ x) := by
    have h' : (A + E) *ᵥ (y - x) = f - E *ᵥ x := by
      rw [Matrix.mulVec_sub, hy, Matrix.add_mulVec, hx, add_sub_add_left_eq_sub]
    rw [← h', Matrix.mulVec_mulVec, inv_mul_of_isUnit hAE, Matrix.one_mulVec]
  have hres : ‖WithLp.toLp 2 (f - E *ᵥ x)‖ ≤
      ‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖ := by
    rw [WithLp.toLp_sub]
    exact (norm_sub_le _ _).trans (add_le_add_right (norm_toLp_mulVec_le E x) _)
  have hden : 0 < 1 - specNorm (A⁻¹ * E) := by linarith
  rw [h]
  calc ‖WithLp.toLp 2 ((A + E)⁻¹ *ᵥ (f - E *ᵥ x))‖
      ≤ specNorm (A + E)⁻¹ * ‖WithLp.toLp 2 (f - E *ᵥ x)‖ := norm_toLp_mulVec_le _ _
    _ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) *
          (‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖) :=
        mul_le_mul (specNorm_inv_add_le hA hE) hres (norm_nonneg _) (by positivity)

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
  have hκ := specNorm_inv_mul_specNorm_le_conditionNumber_mul hA hE
  have ht : specNorm (A⁻¹ * E) ≤ conditionNumber A * ε := (specNorm_mul_le _ _).trans hκ
  have hb : ‖WithLp.toLp 2 b‖ ≤ specNorm A * ‖WithLp.toLp 2 x‖ := by
    rw [← hx]
    exact norm_toLp_mulVec_le A x
  have hεb : ε * ‖WithLp.toLp 2 b‖ ≤ ε * (specNorm A * ‖WithLp.toLp 2 x‖) := by
    rcases le_or_gt 0 ε with h0 | h0
    · exact mul_le_mul_of_nonneg_left hb h0
    · have hA0 : specNorm A = 0 := by
        nlinarith [specNorm_nonneg A, specNorm_nonneg E]
      have hb0 : ‖WithLp.toLp 2 b‖ = 0 := by
        rw [hA0, zero_mul] at hb
        exact le_antisymm hb (norm_nonneg _)
      rw [hb0, hA0, zero_mul]
  have hsum : ‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖ ≤
      2 * ε * specNorm A * ‖WithLp.toLp 2 x‖ := by
    have h := mul_le_mul_of_nonneg_right hE (norm_nonneg (WithLp.toLp 2 x))
    linarith
  have hden : 0 < 1 - conditionNumber A * ε := by linarith
  calc ‖WithLp.toLp 2 (y - x)‖
      ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) *
          (‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖) :=
        norm_sub_le_of_add_mulVec_eq hA (ht.trans_lt hε) hx hy
    _ ≤ specNorm A⁻¹ / (1 - conditionNumber A * ε) *
          (2 * ε * specNorm A * ‖WithLp.toLp 2 x‖) :=
        mul_le_mul (div_le_div_of_nonneg_left (specNorm_nonneg _) hden (by linarith)) hsum
          (by positivity) (div_nonneg (specNorm_nonneg _) hden.le)
    _ = 2 * ε * conditionNumber A / (1 - conditionNumber A * ε) * ‖WithLp.toLp 2 x‖ := by
        rw [conditionNumber_of_isUnit hA]
        ring

end NLAlib
