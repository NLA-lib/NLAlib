/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Dilation
public import NLAlib.Probability.MatrixConcentration.MGFBound
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Matrix series with sub-Gaussian coefficients

For fixed Hermitian matrices `B k` and independent real coefficients `γ k` with
`HasSubgaussianMGF (γ k) (c k)`, the series `∑ γ k • B k` satisfies
`P(t ≤ λ_max) ≤ d exp (-t² / (2v))` with `v = ‖∑ c k B k²‖`, and
`E λ_max ≤ √(2 v log d)`. Rectangular coefficients go through the dilation. Gaussian and
Rademacher series are the case `c k = 1` (Tropp 2015, Theorem 4.1.1, which states the Gaussian and
Rademacher cases; the sub-Gaussian form is the same proof).

## Main results

* `NLAlib.hasMatrixMGFBound_smul_of_hasSubgaussianMGF`.
* `NLAlib.measureReal_eigenvalue_zero_sum_smul_ge_le`,
  `NLAlib.integral_eigenvalue_zero_sum_smul_le`.
* `NLAlib.measureReal_specNorm_sum_smul_ge_le`, `NLAlib.integral_specNorm_sum_smul_le`.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder NNReal
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- A sub-Gaussian coefficient times a fixed Hermitian matrix has a matrix MGF bound:
`E exp (θ γ B) ≤ exp (θ²/2 • c B²)`. -/
theorem hasMatrixMGFBound_smul_of_hasSubgaussianMGF {γ : Ω → ℝ} {c : ℝ≥0}
    (hγ : HasSubgaussianMGF γ c μ) {B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    HasMatrixMGFBound (fun ω => γ ω • B) (fun θ => θ ^ 2 / 2) ((c : ℝ) • B ^ 2) Set.univ μ := by
  sorry

variable {ι : Type*} [Fintype ι] {γ : ι → Ω → ℝ} {c : ι → ℝ≥0}

/-- **The matrix series tail**, Hermitian coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem measureReal_eigenvalue_zero_sum_smul_ge_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {B : ι → Matrix n n 𝕜}
    (hB : ∀ k, (B k).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, γ k ω • B k) 0} ≤
      Fintype.card n * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, (c k : ℝ) • B k ^ 2))) := by
  sorry

/-- The matrix series mean, Hermitian coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem integral_eigenvalue_zero_sum_smul_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {B : ι → Matrix n n 𝕜}
    (hB : ∀ k, (B k).IsHermitian) :
    ∫ ω, eigenvalue (∑ k, γ k ω • B k) 0 ∂μ ≤
      √(2 * specNorm (∑ k, (c k : ℝ) • B k ^ 2) * Real.log (Fintype.card n)) := by
  sorry

variable {m : Type*} [Fintype m] {B : ι → Matrix m n 𝕜}

/-- **The matrix series tail**, rectangular coefficients ([Tropp2015], Theorem 4.1.1), with
`v = max ‖∑ c k B k B kᴴ‖ ‖∑ c k B kᴴ B k‖`. -/
theorem measureReal_specNorm_sum_smul_ge_le [Nonempty m] [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, γ k ω • B k)} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-t ^ 2 /
        (2 * max (specNorm (∑ k, (c k : ℝ) • (B k * (B k)ᴴ)))
          (specNorm (∑ k, (c k : ℝ) • ((B k)ᴴ * B k))))) := by
  sorry

/-- The matrix series mean, rectangular coefficients ([Tropp2015], Theorem 4.1.1). -/
theorem integral_specNorm_sum_smul_le [Nonempty m] [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) (c k) μ) :
    ∫ ω, specNorm (∑ k, γ k ω • B k) ∂μ ≤
      √(2 * max (specNorm (∑ k, (c k : ℝ) • (B k * (B k)ᴴ)))
          (specNorm (∑ k, (c k : ℝ) • ((B k)ᴴ * B k))) *
        Real.log (Fintype.card m + Fintype.card n)) := by
  sorry

end NLAlib
