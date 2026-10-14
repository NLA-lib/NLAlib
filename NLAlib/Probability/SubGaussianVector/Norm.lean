/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.SubExponential.Tail
public import NLAlib.Probability.SubGaussian.Square
public import NLAlib.Probability.SubGaussianVector.Basic

/-!
# The squared norm of a sub-Gaussian random vector

For a real sub-Gaussian vector `X` with proxy `c`, `E exp (θ ‖X‖²)` is at most the Laplace
transform of `c χ²_n`, and the upper tail of `‖X‖²` is the Laurent–Massart bound
`P(c (n + 2√(n t) + 2t) ≤ ‖X‖²) ≤ e^{-t}` (Hsu, Kakade and Zhang). For independent sub-Gaussian
coordinates, the two-sided tail of `‖X‖²` about its mean is Bernstein's inequality for the
centred squares.

The statements are over `ℝ`: the proofs linearise with a standard Gaussian vector of the same
dimension, which exists over `ℝ` only in this library for now; the complex versions are the real
ones in dimension `2 n`.

## Main results

* `NLAlib.IsSubgaussianVector.integral_exp_mul_norm_sq_le`: `E exp (θ‖X‖²) ≤ (1 - 2θc)^{-n/2}`.
* `NLAlib.IsSubgaussianVector.measureReal_norm_sq_ge_le`: the upper tail of `‖X‖²`.
* `NLAlib.measureReal_abs_norm_sq_sub_integral_ge_le`: the two-sided tail for independent
  coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ} {c : ℝ≥0}

namespace IsSubgaussianVector

/-- The mean squared norm of a sub-Gaussian vector is at most `c n`. -/
theorem integral_norm_sq_le [IsProbabilityMeasure μ] (h : IsSubgaussianVector X c μ) :
    ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ^ 2 ∂μ ≤ c * Fintype.card n := by
  sorry

/-- `exp (θ ‖X‖²)` is integrable for a sub-Gaussian vector when `2 θ c < 1`. -/
theorem integrable_exp_mul_norm_sq (h : IsSubgaussianVector X c μ) {θ : ℝ}
    (hθ : 2 * θ * c < 1) : Integrable (fun ω => rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ := by
  sorry

/-- `E exp (θ ‖X‖²) ≤ (1 - 2θc)^{-n/2}` for a sub-Gaussian vector and `0 ≤ θ < 1 / (2c)`: the
Laplace transform of `c χ²_n`, by Gaussian linearisation. -/
theorem integral_exp_mul_norm_sq_le (h : IsSubgaussianVector X c μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * c < 1) :
    ∫ ω, rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2) ∂μ ≤
      (1 - 2 * θ * c) ^ (-(Fintype.card n / 2 : ℝ)) := by
  sorry

/-- **The upper tail of `‖X‖²`** for a sub-Gaussian vector (Hsu, Kakade and Zhang 2012,
Theorem 2.1 with `A = 1`; for a standard Gaussian vector this is Laurent and Massart's bound).
`c ≠ 0` is needed for the non-strict event: with `c = 0` the vector is `0` almost surely and the
event is everything. -/
theorem measureReal_norm_sq_ge_le (h : IsSubgaussianVector X c μ) (hc : c ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | c * (Fintype.card n + 2 * √(Fintype.card n * t) + 2 * t) ≤
      ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤ rexp (-t) := by
  sorry

end IsSubgaussianVector

/-- The two-sided tail of `‖X‖²` about its mean for independent sub-Gaussian coordinates:
Bernstein's inequality for the centred squares, whose variance proxy and scale are `32 c²` and
`4 c`. -/
theorem measureReal_abs_norm_sq_sub_integral_ge_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |‖WithLp.toLp 2 (X ω)‖ ^ 2 - ∫ ω', ‖WithLp.toLp 2 (X ω')‖ ^ 2 ∂μ|} ≤
      2 * rexp (-min (t ^ 2 / (2 * (Fintype.card n * (32 * c ^ 2)))) (t / (2 * (4 * c)))) := by
  sorry

end NLAlib
