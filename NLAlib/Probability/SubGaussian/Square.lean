/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.SubExponential.Basic
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Squares of sub-Gaussian random variables

The exponential square moment `E exp (θ X²)` of a sub-Gaussian variable, and the fact that its
centred square `X² - E X²` is sub-exponential, which is what Bernstein's inequality and the
diagonal part of the Hanson–Wright inequality consume.

The two constants of the centred square are definitions (`CONTRIBUTING.md` §5.2, "Numerical
bounds"): a better proof changes their bodies and the comparison lemmas, no statement.

## Main definitions

* `NLAlib.centeredSqVarianceConstant`, `NLAlib.centeredSqScaleConstant`.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.integral_exp_mul_sq_le`:
  `E exp (θ X²) ≤ (1 - 2θc)^{-1/2}`.
* `ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral`: the centred square
  is sub-exponential with variance proxy `centeredSqVarianceConstant * c²` and scale
  `centeredSqScaleConstant * c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- `exp (θ X²)` is integrable for a sub-Gaussian `X` when `2 θ c < 1` (in particular for every
`θ ≤ 0`). -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integrable_exp_mul_sq
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ : 2 * θ * c < 1) :
    Integrable (fun ω => rexp (θ * X ω ^ 2)) μ := by
  sorry

/-- `E exp (θ X²) ≤ (1 - 2θc)^{-1/2}` for a sub-Gaussian `X` and `0 ≤ θ < 1 / (2c)`: the value
for a centred Gaussian of variance `c`, by Gaussian linearisation
`exp (θ x²) = E_g exp (√(2θ) g x)`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_exp_mul_sq_le
    (h : HasSubgaussianMGF X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ * c < 1) :
    ∫ ω, rexp (θ * X ω ^ 2) ∂μ ≤ 1 / √(1 - 2 * θ * c) := by
  sorry

/-- The variance-proxy constant of the centred square of a sub-Gaussian variable:
`X² - E X²` has variance proxy `centeredSqVarianceConstant * c²` when `X` has proxy `c`. The
literature has `32` (Honorio and Jaakkola, 2014); the value here, `4 e³ ≈ 80.3`, is what the
proof reaches. Use only `centeredSqVarianceConstant_pos` and `centeredSqVarianceConstant_le`. -/
noncomputable irreducible_def centeredSqVarianceConstant : ℝ≥0 := Real.toNNReal (4 * rexp 3)

/-- The scale constant of the centred square of a sub-Gaussian variable: `X² - E X²` has scale
`centeredSqScaleConstant * c` when `X` has proxy `c`. The literature has `4`; the value here,
`2 e ≈ 5.44`, is what the proof reaches. Use only `centeredSqScaleConstant_pos` and
`centeredSqScaleConstant_le`. -/
noncomputable irreducible_def centeredSqScaleConstant : ℝ≥0 := Real.toNNReal (2 * rexp 1)

theorem centeredSqVarianceConstant_pos : 0 < centeredSqVarianceConstant := by
  sorry

theorem centeredSqScaleConstant_pos : 0 < centeredSqScaleConstant := by
  sorry

/-- An explicit upper bound on `centeredSqVarianceConstant`. -/
theorem centeredSqVarianceConstant_le : (centeredSqVarianceConstant : ℝ) ≤ 4 * rexp 3 := by
  sorry

/-- An explicit upper bound on `centeredSqScaleConstant`. -/
theorem centeredSqScaleConstant_le : (centeredSqScaleConstant : ℝ) ≤ 2 * rexp 1 := by
  sorry

/-- The centred square of a sub-Gaussian variable is sub-exponential. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral
    [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) :
    HasSubexponentialMGF (fun ω => X ω ^ 2 - ∫ ω', X ω' ^ 2 ∂μ)
      (centeredSqVarianceConstant * c ^ 2) (centeredSqScaleConstant * c) μ := by
  sorry

end NLAlib
