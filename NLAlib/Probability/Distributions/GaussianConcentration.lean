/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.GaussianLogSobolev
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Gaussian concentration of Lipschitz functions

A Lipschitz function `f` of a standard Gaussian vector is sub-Gaussian about its mean with proxy
`L²`, where `L` is its Lipschitz constant for the Euclidean norm (Tsirelson, Ibragimov and
Sudakov); the constant is sharp. The general statement is for Mathlib's `stdGaussian E` on a
Euclidean space; for `f : (n → ℝ) → ℝ` and `X` with law `gaussianVector n`, the Lipschitz
hypothesis is stated on `EuclideanSpace ℝ n`, since `n → ℝ` carries the sup metric, and
`NLAlib.lipschitzWith_ofLp_iff` turns it into the explicit inequality.

## Main results

* `NLAlib.hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_stdGaussian`.
* `NLAlib.hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_gaussianVector`.
* `NLAlib.measureReal_integral_add_le_of_lipschitzWith_of_hasLaw_gaussianVector`: the upper tail.
* `NLAlib.lipschitzWith_ofLp_iff`.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Theorem 5.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Lipschitz for the Euclidean norm, as an inequality on `n → ℝ`. -/
theorem lipschitzWith_ofLp_iff {n : Type*} [Fintype n] {f : (n → ℝ) → ℝ} {L : ℝ≥0} :
    LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x)) ↔
      ∀ x y, |f x - f y| ≤ L * ‖WithLp.toLp 2 (x - y)‖ := by
  sorry

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {X : Ω → E} {f : E → ℝ} {L : ℝ≥0}

/-- A Lipschitz function of a standard Gaussian vector is integrable. -/
theorem integrable_comp_of_lipschitzWith_of_hasLaw_stdGaussian (hX : HasLaw X (stdGaussian E) μ)
    (hf : LipschitzWith L f) : Integrable (fun ω => f (X ω)) μ := by
  sorry

/-- **Gaussian concentration of Lipschitz functions** ([BoucheronLugosiMassart2013],
Theorem 5.6): `f (X) - E f (X)` is sub-Gaussian with proxy `L²`.
Result: gaussian-lipschitz-concentration -/
theorem hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_stdGaussian
    (hX : HasLaw X (stdGaussian E) μ) (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) (L ^ 2) μ := by
  sorry

end Euclidean

section Vector

variable {n : Type*} [Fintype n] {X : Ω → n → ℝ} {f : (n → ℝ) → ℝ} {L : ℝ≥0}

/-- Gaussian concentration for a standard Gaussian vector in `ℝⁿ`, with `f` Lipschitz for the
Euclidean norm. -/
theorem hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ)
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x))) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) (L ^ 2) μ := by
  sorry

/-- A Lipschitz function of a standard Gaussian vector in `ℝⁿ` is integrable. -/
theorem integrable_comp_of_lipschitzWith_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ)
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x))) :
    Integrable (fun ω => f (X ω)) μ := by
  sorry

/-- The upper tail of a Lipschitz function of a standard Gaussian vector,
`P(E f(X) + t ≤ f(X)) ≤ exp (-t² / (2L²))`, with the event in the form the random-matrix
consumers use. -/
theorem measureReal_integral_add_le_of_lipschitzWith_of_hasLaw_gaussianVector
    (hX : HasLaw X (gaussianVector n) μ)
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x))) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | ∫ ω', f (X ω') ∂μ + t ≤ f (X ω)} ≤ rexp (-t ^ 2 / (2 * L ^ 2)) := by
  sorry

end Vector

end NLAlib
