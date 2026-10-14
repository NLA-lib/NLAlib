/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.Gaussian

/-!
# The squared norm of a standard Gaussian vector

The squared norm of a standard Gaussian vector in `ℝⁿ` is `χ²_n`. This file gives its Laplace
transform and the Laurent–Massart lower tail. The upper tail is the sub-Gaussian-vector bound
`NLAlib.IsSubgaussianVector.measureReal_norm_sq_ge_le` at proxy `1`, which is Laurent and
Massart's exactly.

## Main results

* `NLAlib.integral_exp_mul_norm_sq_of_hasLaw_gaussianVector`: `E exp (θ‖X‖²) = (1 - 2θ)^{-n/2}`.
* `NLAlib.measureReal_norm_sq_le_of_hasLaw_gaussianVector`:
  `P(‖X‖² ≤ n - 2√(n t)) ≤ e^{-t}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ}

/-- The Laplace transform of `χ²_n`: `E exp (θ ‖X‖²) = (1 - 2θ)^{-n/2}` for `θ < 1/2`. -/
theorem integral_exp_mul_norm_sq_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {θ : ℝ} (hθ : 2 * θ < 1) :
    ∫ ω, rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2) ∂μ = (1 - 2 * θ) ^ (-(Fintype.card n / 2 : ℝ)) := by
  sorry

/-- **The lower tail of `χ²_n`** (Laurent and Massart 2000, Lemma 1):
`P(‖X‖² ≤ n - 2√(n t)) ≤ e^{-t}`. The dimension must be positive: for `n = 0` the event is
everything. -/
theorem measureReal_norm_sq_le_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    (hn : 0 < Fintype.card n) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ Fintype.card n - 2 * √(Fintype.card n * t)} ≤
      rexp (-t) := by
  sorry

end NLAlib
