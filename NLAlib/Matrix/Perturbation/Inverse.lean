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

The Neumann series for $(\mathbf{I} - \mathbf{F})^{-1}$ when $\|\mathbf{F}\|_2 < 1$, the resulting
bounds for the inverse of a perturbed matrix $\mathbf{A} + \mathbf{E}$, and the classical forward
error bounds for the solution of a linear system in terms of the condition number.

## Main results

* `NLAlib.isUnit_one_sub_of_specNorm_lt_one`, `NLAlib.hasSum_pow_inv_one_sub`: the Neumann series.
* `NLAlib.isUnit_one_add_of_specNorm_lt_one`, `NLAlib.pseudoConditionNumber_one_add_le`: a
  perturbed identity and its condition number.
* `NLAlib.isUnit_add_of_specNorm_inv_mul_lt_one`, `NLAlib.specNorm_inv_add_le`,
  `NLAlib.specNorm_inv_add_sub_inv_le`: perturbation of the inverse.
* `NLAlib.norm_sub_le_specNorm_inv_mul_norm_sub_mulVec`: forward error from the residual.
* `NLAlib.norm_sub_le_of_add_mulVec_eq`,
  `NLAlib.norm_sub_le_pseudoConditionNumber_mul_of_add_mulVec_eq`: perturbation of a linear system.
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

/-- If $\|\mathbf{F}\|_2 < 1$ then $\mathbf{I} - \mathbf{F}$ is invertible.
[HornJohnson2013, Corollary 5.6.16]. -/
theorem isUnit_one_sub_of_specNorm_lt_one {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    IsUnit (1 - F) := by
  open scoped Matrix.Norms.L2Operator in
  exact isUnit_one_sub_of_norm_lt_one (R := Matrix n n 𝕜) h

/-- **The Neumann series**: if $\|\mathbf{F}\|_2 < 1$ then the series $\sum_{k \ge 0} \mathbf{F}^k$
converges to $(\mathbf{I} - \mathbf{F})^{-1}$.
[HornJohnson2013, Corollary 5.6.16].
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

/-- $\|(\mathbf{I} - \mathbf{F})^{-1}\|_2 \le 1 / (1 - \|\mathbf{F}\|_2)$ when
$\|\mathbf{F}\|_2 < 1$. -/
theorem specNorm_inv_one_sub_le {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    specNorm (1 - F)⁻¹ ≤ (1 - specNorm F)⁻¹ := by
  have hle : specNorm (1 - F)⁻¹ ≤ 1 + specNorm F * specNorm (1 - F)⁻¹ := by
    calc specNorm (1 - F)⁻¹ = specNorm (1 + F * (1 - F)⁻¹) := by
          rw [← inv_one_sub_eq_one_add_mul (isUnit_one_sub_of_specNorm_lt_one h)]
      _ ≤ specNorm (1 : Matrix n n 𝕜) + specNorm (F * (1 - F)⁻¹) := specNorm_add_le _ _
      _ ≤ 1 + specNorm F * specNorm (1 - F)⁻¹ := add_le_add specNorm_one_le (specNorm_mul_le _ _)
  rw [← one_div (1 - specNorm F), le_div_iff₀ (by linarith)]
  linarith

/-- $\|(\mathbf{I} - \mathbf{F})^{-1} - \mathbf{I}\|_2
\le \|\mathbf{F}\|_2 / (1 - \|\mathbf{F}\|_2)$ when $\|\mathbf{F}\|_2 < 1$. -/
theorem specNorm_inv_one_sub_sub_one_le {F : Matrix n n 𝕜} (h : specNorm F < 1) :
    specNorm ((1 - F)⁻¹ - 1) ≤ specNorm F / (1 - specNorm F) := by
  have he : (1 - F)⁻¹ - 1 = F * (1 - F)⁻¹ :=
    sub_eq_of_eq_add' (inv_one_sub_eq_one_add_mul (isUnit_one_sub_of_specNorm_lt_one h))
  rw [he, div_eq_mul_inv]
  exact (specNorm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (specNorm_inv_one_sub_le h) (specNorm_nonneg F))

/-- If $\|\mathbf{Z}\|_2 < 1$ then $\mathbf{I} + \mathbf{Z}$ is invertible.
[HornJohnson2013, Corollary 5.6.16]. -/
theorem isUnit_one_add_of_specNorm_lt_one {Z : Matrix n n 𝕜} (h : specNorm Z < 1) :
    IsUnit (1 + Z) := by
  simpa only [sub_neg_eq_add] using
    isUnit_one_sub_of_specNorm_lt_one (F := -Z) (by rwa [specNorm_neg])

/-- **The condition number of a perturbed identity**: if $\|\mathbf{Z}\|_2 < 1$ then
$\kappa(\mathbf{I} + \mathbf{Z}) \le (1 + \|\mathbf{Z}\|_2) / (1 - \|\mathbf{Z}\|_2)$.
[GolubVanLoan2013, Theorem 2.3.4]. -/
theorem pseudoConditionNumber_one_add_le {Z : Matrix n n 𝕜} (h : specNorm Z < 1) :
    pseudoConditionNumber (1 + Z) ≤ (1 + specNorm Z) / (1 - specNorm Z) := by
  rw [pseudoConditionNumber_of_isUnit (isUnit_one_add_of_specNorm_lt_one h), div_eq_mul_inv]
  have h1 : specNorm (1 + Z) ≤ 1 + specNorm Z :=
    (specNorm_add_le _ _).trans (add_le_add_left specNorm_one_le _)
  have h2 := specNorm_inv_one_sub_le (F := -Z) (by rwa [specNorm_neg])
  rw [sub_neg_eq_add, specNorm_neg] at h2
  exact mul_le_mul h1 h2 (specNorm_nonneg _) (by linarith [specNorm_nonneg Z])

/-! ### The inverse of a perturbed matrix -/

private theorem add_eq_mul_one_sub_neg {A : Matrix n n 𝕜} (hA : IsUnit A) (E : Matrix n n 𝕜) :
    A + E = A * (1 - -(A⁻¹ * E)) := by
  rw [sub_neg_eq_add, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, mul_inv_of_isUnit hA,
    Matrix.one_mul]

/-- For invertible $\mathbf{A}$, a perturbation $\mathbf{E}$ with
$\|\mathbf{A}^{-1}\mathbf{E}\|_2 < 1$ keeps $\mathbf{A} + \mathbf{E}$ invertible.
[GolubVanLoan2013, Theorem 2.3.4]. -/
theorem isUnit_add_of_specNorm_inv_mul_lt_one {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm (A⁻¹ * E) < 1) : IsUnit (A + E) := by
  rw [add_eq_mul_one_sub_neg hA E]
  exact hA.mul (isUnit_one_sub_of_specNorm_lt_one (by rwa [specNorm_neg]))

/-- For invertible $\mathbf{A}$, a perturbation $\mathbf{E}$ with
$\|\mathbf{A}^{-1}\|_2 \|\mathbf{E}\|_2 < 1$ keeps $\mathbf{A} + \mathbf{E}$ invertible. -/
theorem isUnit_add_of_specNorm_inv_mul_specNorm_lt_one {A E : Matrix n n 𝕜} (hA : IsUnit A)
    (hE : specNorm A⁻¹ * specNorm E < 1) : IsUnit (A + E) := by
  exact isUnit_add_of_specNorm_inv_mul_lt_one hA ((specNorm_mul_le _ _).trans_lt hE)

/-- A perturbation smaller than the smallest singular value keeps $\mathbf{A} + \mathbf{E}$
invertible: if $\|\mathbf{E}\|_2 < \sigma_k(\mathbf{A})$ with $k + 1 = \lvert n \rvert$, then
$\mathbf{A} + \mathbf{E}$ is invertible. -/
theorem isUnit_add_of_specNorm_lt_singularValues {A E : Matrix n n 𝕜} {k : ℕ}
    (hk : k + 1 = Fintype.card n) (hE : specNorm E < singularValues A k) : IsUnit (A + E) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  by_contra h
  exact absurd (singularValues_last_le_specNorm_of_not_injective_add A hk h) (not_le.mpr hE)

/-- The difference of two inverses:
$(\mathbf{A} + \mathbf{E})^{-1} - \mathbf{A}^{-1}
= -(\mathbf{A} + \mathbf{E})^{-1} \mathbf{E} \mathbf{A}^{-1}$ for invertible $\mathbf{A}$ and
$\mathbf{A} + \mathbf{E}$. -/
theorem inv_add_sub_inv {A E : Matrix n n 𝕜} (hA : IsUnit A) (hAE : IsUnit (A + E)) :
    (A + E)⁻¹ - A⁻¹ = -((A + E)⁻¹ * E * A⁻¹) := by
  rw [Matrix.inv_sub_inv (iff_of_true hAE hA), sub_add_cancel_left, Matrix.mul_neg,
    Matrix.neg_mul]

/-- For invertible $\mathbf{A}$ with $\|\mathbf{A}^{-1}\mathbf{E}\|_2 < 1$,
$\|(\mathbf{A} + \mathbf{E})^{-1}\|_2
\le \|\mathbf{A}^{-1}\|_2 / (1 - \|\mathbf{A}^{-1}\mathbf{E}\|_2)$.
[GolubVanLoan2013, Theorem 2.3.4]. -/
theorem specNorm_inv_add_le {A E : Matrix n n 𝕜} (hA : IsUnit A) (hE : specNorm (A⁻¹ * E) < 1) :
    specNorm (A + E)⁻¹ ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) := by
  have hF : specNorm (-(A⁻¹ * E)) < 1 := by rwa [specNorm_neg]
  have h := specNorm_inv_one_sub_le hF
  rw [specNorm_neg] at h
  rw [add_eq_mul_one_sub_neg hA E, Matrix.mul_inv_rev, div_eq_inv_mul]
  exact (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h (specNorm_nonneg _))

/-- **Perturbation of the inverse**: for invertible $\mathbf{A}$ with
$\|\mathbf{A}^{-1}\mathbf{E}\|_2 < 1$,
$$\|(\mathbf{A} + \mathbf{E})^{-1} - \mathbf{A}^{-1}\|_2
  \le \frac{\|\mathbf{A}^{-1}\|_2^2 \|\mathbf{E}\|_2}{1 - \|\mathbf{A}^{-1}\mathbf{E}\|_2}.$$
[GolubVanLoan2013, Theorem 2.3.4].
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

/-- Perturbation of the inverse in any unitarily invariant norm $\|\cdot\|_{\Phi}$: for invertible
$\mathbf{A}$ and $\mathbf{A} + \mathbf{E}$,
$\|(\mathbf{A} + \mathbf{E})^{-1} - \mathbf{A}^{-1}\|_{\Phi}
\le \|(\mathbf{A} + \mathbf{E})^{-1}\|_2 \|\mathbf{E}\|_{\Phi} \|\mathbf{A}^{-1}\|_2$. -/
theorem SymmetricGauge.matrixNorm_inv_add_sub_inv_le (Φ : SymmetricGauge) {A E : Matrix n n 𝕜}
    (hA : IsUnit A) (hAE : IsUnit (A + E)) :
    Φ.matrixNorm ((A + E)⁻¹ - A⁻¹) ≤ specNorm (A + E)⁻¹ * Φ.matrixNorm E * specNorm A⁻¹ := by
  rw [inv_add_sub_inv hA hAE, SymmetricGauge.matrixNorm_neg]
  exact (Φ.matrixNorm_mul_le_mul_specNorm _ _).trans
    (mul_le_mul_of_nonneg_right (Φ.matrixNorm_mul_le_specNorm_mul _ _) (specNorm_nonneg _))

private theorem specNorm_inv_mul_specNorm_le_pseudoConditionNumber_mul {A E : Matrix n n 𝕜}
    (hA : IsUnit A) {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A) :
    specNorm A⁻¹ * specNorm E ≤ pseudoConditionNumber A * ε := by
  rw [pseudoConditionNumber_of_isUnit hA]
  calc specNorm A⁻¹ * specNorm E ≤ specNorm A⁻¹ * (ε * specNorm A) :=
        mul_le_mul_of_nonneg_left hE (specNorm_nonneg _)
    _ = specNorm A * specNorm A⁻¹ * ε := by ring

/-- **Relative perturbation of the inverse through the condition number.** If $\mathbf{A}$ is
invertible, $\|\mathbf{E}\|_2 \le \varepsilon \|\mathbf{A}\|_2$ and
$\kappa(\mathbf{A}) \varepsilon < 1$, then
$$\|(\mathbf{A} + \mathbf{E})^{-1} - \mathbf{A}^{-1}\|_2
  \le \frac{\kappa(\mathbf{A}) \varepsilon}{1 - \kappa(\mathbf{A}) \varepsilon}
  \|\mathbf{A}^{-1}\|_2.$$
[GolubVanLoan2013, §2.6.2]; [Higham2002, §6.2]. -/
theorem specNorm_inv_add_sub_inv_le_pseudoConditionNumber_mul {A E : Matrix n n 𝕜} (hA : IsUnit A)
    {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A) (hε : pseudoConditionNumber A * ε < 1) :
    specNorm ((A + E)⁻¹ - A⁻¹) ≤
      pseudoConditionNumber A * ε / (1 - pseudoConditionNumber A * ε) * specNorm A⁻¹ := by
  have hκ := specNorm_inv_mul_specNorm_le_pseudoConditionNumber_mul hA hE
  have ht : specNorm (A⁻¹ * E) ≤ pseudoConditionNumber A * ε := (specNorm_mul_le _ _).trans hκ
  calc specNorm ((A + E)⁻¹ - A⁻¹)
      ≤ specNorm A⁻¹ ^ 2 * specNorm E / (1 - specNorm (A⁻¹ * E)) :=
        specNorm_inv_add_sub_inv_le hA (ht.trans_lt hε)
    _ = specNorm A⁻¹ * specNorm E / (1 - specNorm (A⁻¹ * E)) * specNorm A⁻¹ := by ring
    _ ≤ pseudoConditionNumber A * ε / (1 - pseudoConditionNumber A * ε) * specNorm A⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg _)
        exact div_le_div₀ ((mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)).trans hκ) hκ
          (by linarith) (by linarith)

/-! ### Linear systems -/

/-- Forward error from the residual: if $\mathbf{A}\mathbf{x} = \mathbf{b}$ with $\mathbf{A}$
invertible, then for any $\mathbf{y}$,
$\|\mathbf{x} - \mathbf{y}\| \le \|\mathbf{A}^{-1}\|_2 \|\mathbf{b} - \mathbf{A}\mathbf{y}\|$. -/
theorem norm_sub_le_specNorm_inv_mul_norm_sub_mulVec {A : Matrix n n 𝕜} (hA : IsUnit A)
    {x b : n → 𝕜} (hx : A *ᵥ x = b) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (x - y)‖ ≤ specNorm A⁻¹ * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ := by
  have h : x - y = A⁻¹ *ᵥ (b - A *ᵥ y) := by
    rw [← hx, ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, inv_mul_of_isUnit hA,
      Matrix.one_mulVec]
  nth_rewrite 1 [h]
  exact norm_toLp_mulVec_le _ _

/-- **Relative forward error from the relative residual**, without divisions: if
$\mathbf{A}\mathbf{x} = \mathbf{b}$ with $\mathbf{A}$ invertible, then for any $\mathbf{y}$,
$\|\mathbf{x} - \mathbf{y}\| \, \|\mathbf{b}\|
\le \kappa(\mathbf{A}) \, \|\mathbf{b} - \mathbf{A}\mathbf{y}\| \, \|\mathbf{x}\|$.
[GolubVanLoan2013, §2.6.4]. -/
theorem norm_sub_mul_norm_le_pseudoConditionNumber_mul {A : Matrix n n 𝕜} (hA : IsUnit A)
    {x b : n → 𝕜} (hx : A *ᵥ x = b) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (x - y)‖ * ‖WithLp.toLp 2 b‖ ≤
      pseudoConditionNumber A * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ * ‖WithLp.toLp 2 x‖ := by
  have h₁ := norm_sub_le_specNorm_inv_mul_norm_sub_mulVec hA hx y
  have h₂ : ‖WithLp.toLp 2 b‖ ≤ specNorm A * ‖WithLp.toLp 2 x‖ := by
    rw [← hx]
    exact norm_toLp_mulVec_le A x
  rw [pseudoConditionNumber_of_isUnit hA]
  calc ‖WithLp.toLp 2 (x - y)‖ * ‖WithLp.toLp 2 b‖
      ≤ specNorm A⁻¹ * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ * (specNorm A * ‖WithLp.toLp 2 x‖) :=
        mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
    _ = specNorm A * specNorm A⁻¹ * ‖WithLp.toLp 2 (b - A *ᵥ y)‖ * ‖WithLp.toLp 2 x‖ := by ring

/-- **Perturbation of a linear system.** If $\mathbf{A}$ is invertible,
$\mathbf{A}\mathbf{x} = \mathbf{b}$, $(\mathbf{A} + \mathbf{E})\mathbf{y} = \mathbf{b} + \mathbf{f}$
and $\|\mathbf{A}^{-1}\mathbf{E}\|_2 < 1$, then
$$\|\mathbf{y} - \mathbf{x}\| \le \frac{\|\mathbf{A}^{-1}\|_2}{1 - \|\mathbf{A}^{-1}\mathbf{E}\|_2}
  \bigl(\|\mathbf{f}\| + \|\mathbf{E}\|_2 \|\mathbf{x}\|\bigr).$$
[GolubVanLoan2013, Theorem 2.6.2]; [Higham2002, Theorem 7.2]. -/
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

/-- **Relative perturbation of a linear system through the condition number.** If $\mathbf{A}$ is
invertible, $\mathbf{A}\mathbf{x} = \mathbf{b}$,
$(\mathbf{A} + \mathbf{E})\mathbf{y} = \mathbf{b} + \mathbf{f}$,
$\|\mathbf{E}\|_2 \le \varepsilon \|\mathbf{A}\|_2$, $\|\mathbf{f}\| \le \varepsilon \|\mathbf{b}\|$
and $\kappa(\mathbf{A}) \varepsilon < 1$, then
$$\|\mathbf{y} - \mathbf{x}\|
  \le \frac{2 \varepsilon \kappa(\mathbf{A})}{1 - \kappa(\mathbf{A}) \varepsilon} \|\mathbf{x}\|.$$
[GolubVanLoan2013, Theorem 2.6.2].
Result: linear-system-perturbation -/
theorem norm_sub_le_pseudoConditionNumber_mul_of_add_mulVec_eq {A E : Matrix n n 𝕜} (hA : IsUnit A)
    {ε : ℝ} (hE : specNorm E ≤ ε * specNorm A) (hε : pseudoConditionNumber A * ε < 1)
    {x y b f : n → 𝕜} (hx : A *ᵥ x = b) (hy : (A + E) *ᵥ y = b + f)
    (hf : ‖WithLp.toLp 2 f‖ ≤ ε * ‖WithLp.toLp 2 b‖) :
    ‖WithLp.toLp 2 (y - x)‖ ≤
      2 * ε * pseudoConditionNumber A / (1 - pseudoConditionNumber A * ε) * ‖WithLp.toLp 2 x‖ := by
  have hκ := specNorm_inv_mul_specNorm_le_pseudoConditionNumber_mul hA hE
  have ht : specNorm (A⁻¹ * E) ≤ pseudoConditionNumber A * ε := (specNorm_mul_le _ _).trans hκ
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
  have hden : 0 < 1 - pseudoConditionNumber A * ε := by linarith
  calc ‖WithLp.toLp 2 (y - x)‖
      ≤ specNorm A⁻¹ / (1 - specNorm (A⁻¹ * E)) *
          (‖WithLp.toLp 2 f‖ + specNorm E * ‖WithLp.toLp 2 x‖) :=
        norm_sub_le_of_add_mulVec_eq hA (ht.trans_lt hε) hx hy
    _ ≤ specNorm A⁻¹ / (1 - pseudoConditionNumber A * ε) *
          (2 * ε * specNorm A * ‖WithLp.toLp 2 x‖) :=
        mul_le_mul (div_le_div_of_nonneg_left (specNorm_nonneg _) hden (by linarith)) hsum
          (by positivity) (div_nonneg (specNorm_nonneg _) hden.le)
    _ = 2 * ε * pseudoConditionNumber A / (1 - pseudoConditionNumber A * ε) *
          ‖WithLp.toLp 2 x‖ := by
        rw [pseudoConditionNumber_of_isUnit hA]
        ring

/-! ### Deprecated aliases -/

@[deprecated specNorm_inv_add_sub_inv_le_pseudoConditionNumber_mul (since := "2026-10-14")]
alias specNorm_inv_add_sub_inv_le_conditionNumber_mul :=
  specNorm_inv_add_sub_inv_le_pseudoConditionNumber_mul

@[deprecated norm_sub_mul_norm_le_pseudoConditionNumber_mul (since := "2026-10-14")]
alias norm_sub_mul_norm_le_conditionNumber_mul :=
  norm_sub_mul_norm_le_pseudoConditionNumber_mul

@[deprecated norm_sub_le_pseudoConditionNumber_mul_of_add_mulVec_eq (since := "2026-10-14")]
alias norm_sub_le_conditionNumber_mul_of_add_mulVec_eq :=
  norm_sub_le_pseudoConditionNumber_mul_of_add_mulVec_eq

end NLAlib
