/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.Chernoff

/-!
# The matrix Chernoff inequalities for sums of independent matrices

For independent random positive semidefinite matrices `0 ≤ X k ≤ L • 1`, with
`μmax = λ_max (∑ E X k)` and `μmin = λ_min (∑ E X k)`, the largest eigenvalue of the sum
exceeds `(1 + δ) μmax`, and the smallest falls below `(1 - δ) μmin`, with the Chernoff
probabilities (Tropp 2015, Theorem 5.1.1), and the means satisfy
`E λ_max ≤ (e - 1) μmax + L log d`, `E λ_min ≥ (1 - e⁻¹) μmin - L log d`. When the summands have
mean sum the identity, the sum is within `ε` of the identity in spectral norm outside probability
`2 d e^{-ε² / (3L)}`, the form row-sampling arguments use.

## Main results

* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_chernoff`,
  `NLAlib.measureReal_eigenvalue_sum_le_le_chernoff`: the source forms.
* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp`,
  `NLAlib.measureReal_eigenvalue_sum_le_le_card_mul_exp`: the simplified forms.
* `NLAlib.integral_eigenvalue_zero_sum_le_chernoff`, `NLAlib.le_integral_eigenvalue_sum_chernoff`.
* `NLAlib.measureReal_specNorm_sum_sub_one_ge_le`: the two-sided form around the identity.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι] {X : ι → Ω → Matrix n n 𝕜}
  {L : ℝ}

/-- **Matrix Chernoff, upper tail** ([Tropp2015], Theorem 5.1.1). -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff [Nonempty n] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue (∑ k, ∫ ω', X k ω' ∂μ) 0 ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^
        (eigenvalue (∑ k, ∫ ω, X k ω ∂μ) 0 / L) := by
  sorry

/-- **Matrix Chernoff, lower tail** ([Tropp2015], Theorem 5.1.1), for `0 ≤ δ < 1`. -/
theorem measureReal_eigenvalue_sum_le_le_chernoff (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {j : ℕ} (hj : j + 1 = Fintype.card n)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (∑ k, X k ω) j ≤ (1 - δ) * eigenvalue (∑ k, ∫ ω', X k ω' ∂μ) j} ≤
      Fintype.card n * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^
        (eigenvalue (∑ k, ∫ ω, X k ω ∂μ) j / L) := by
  sorry

/-- Matrix Chernoff, upper tail, simplified: `≤ d e^{-δ² μmax / (3L)}` for `0 ≤ δ ≤ 1`. -/
theorem measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp [Nonempty n] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | (1 + δ) * eigenvalue (∑ k, ∫ ω', X k ω' ∂μ) 0 ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * Real.exp (-δ ^ 2 * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) 0 / (3 * L)) := by
  sorry

/-- Matrix Chernoff, lower tail, simplified: `≤ d e^{-δ² μmin / (2L)}` for `0 ≤ δ < 1`. -/
theorem measureReal_eigenvalue_sum_le_le_card_mul_exp (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {j : ℕ} (hj : j + 1 = Fintype.card n)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (∑ k, X k ω) j ≤ (1 - δ) * eigenvalue (∑ k, ∫ ω', X k ω' ∂μ) j} ≤
      Fintype.card n * Real.exp (-δ ^ 2 * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) j / (2 * L)) := by
  sorry

/-- Matrix Chernoff for the mean of the largest eigenvalue ([Tropp2015], Theorem 5.1.1):
`E λ_max (∑ X k) ≤ (e - 1) μmax + L log d`. -/
theorem integral_eigenvalue_zero_sum_le_chernoff [Nonempty n] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      (Real.exp 1 - 1) * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) 0 + L * Real.log (Fintype.card n) := by
  sorry

/-- Matrix Chernoff for the mean of the smallest eigenvalue ([Tropp2015], Theorem 5.1.1):
`E λ_min (∑ X k) ≥ (1 - e⁻¹) μmin - L log d`. The summands are bounded, so the sum is
integrable and the integral is not a junk value. -/
theorem le_integral_eigenvalue_sum_chernoff (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {j : ℕ} (hj : j + 1 = Fintype.card n) :
    (1 - Real.exp (-1)) * eigenvalue (∑ k, ∫ ω, X k ω ∂μ) j - L * Real.log (Fintype.card n) ≤
      ∫ ω, eigenvalue (∑ k, X k ω) j ∂μ := by
  sorry

/-- **Spectral approximation of the identity by a sum of bounded positive semidefinite
matrices**: if `∑ E X k = 1`, then `P(ε ≤ ‖∑ X k - 1‖) ≤ 2 d e^{-ε² / (3L)}` for `0 ≤ ε < 1`; the
form row-sampling and subspace-embedding arguments use. -/
theorem measureReal_specNorm_sum_sub_one_ge_le [Nonempty n] (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜))
    (hmean : ∑ k, ∫ ω, X k ω ∂μ = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    μ.real {ω | ε ≤ specNorm (∑ k, X k ω - 1)} ≤
      2 * Fintype.card n * Real.exp (-ε ^ 2 / (3 * L)) := by
  sorry

end NLAlib
