/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.EntropyTensorization
public import NLAlib.Probability.LogSobolev

/-!
# Gross's logarithmic Sobolev inequality

For the standard Gaussian, `Ent (g²) ≤ 2 E ‖∇g‖²` for every `C¹` function `g` with `g²` and
`‖∇g‖²` integrable; then `g² log g²` is integrable too, so the entropy is not a junk value. The
one-dimensional inequality is proved first and tensorized. The standard Gaussian on a Euclidean
space therefore satisfies `NLAlib.HasLogSobolev` with constant `1`.

## Main results

* `NLAlib.entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal`: Gross's inequality on `ℝ`.
* `NLAlib.entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian`: on a Euclidean space.
* `NLAlib.hasLogSobolev_stdGaussian`.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Theorem 5.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- `g² log g²` is integrable for the standard Gaussian on `ℝ` when `g` is `C¹` with `g²` and
`g'²` integrable. -/
theorem integrable_sq_mul_log_sq_gaussianReal {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (gaussianReal 0 1) := by
  sorry

/-- **Gross's logarithmic Sobolev inequality** on `ℝ`: `Ent (g²) ≤ 2 E g'²` for the standard
Gaussian. -/
theorem entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    entropy (gaussianReal 0 1) (fun x => g x ^ 2) ≤ 2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 := by
  sorry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `g² log g²` is integrable for the standard Gaussian on a Euclidean space when `g` is `C¹`
with `g²` and `‖∇g‖²` integrable. -/
theorem integrable_sq_mul_log_sq_stdGaussian {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (stdGaussian E) := by
  sorry

/-- **Gross's logarithmic Sobolev inequality** for the standard Gaussian on a Euclidean space:
`Ent (g²) ≤ 2 E ‖∇g‖²` ([BoucheronLugosiMassart2013], Theorem 5.4).
Result: gaussian-log-sobolev -/
theorem entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    entropy (stdGaussian E) (fun x => g x ^ 2) ≤
      2 * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂stdGaussian E := by
  sorry

/-- The standard Gaussian satisfies a logarithmic Sobolev inequality with constant `1`. -/
theorem hasLogSobolev_stdGaussian : HasLogSobolev (stdGaussian E) 1 := by
  sorry

end NLAlib
