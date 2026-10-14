/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Probability.Moments.Covariance
public import NLAlib.ForMathlib.MeasureTheory.Constructions.PiUpdate
public import NLAlib.Probability.Distributions.Gaussian

/-!
# Gaussian integration by parts

For a Gaussian vector `X` in `ℝ^ι` (any mean, any covariance, possibly singular) and a function
`f` of class `C¹` with bounded derivative, Stein's identity in covariance form:
`E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`. It is the tool behind the Gaussian
interpolation inequality and hence every Gaussian comparison theorem
(`NLAlib/Probability/Distributions/GaussianComparison.lean`).

The regularity class is the one the interpolation needs: it applies the identity to the partial
derivatives of a `C²` test function with bounded Hessian. A bounded derivative gives linear growth,
so both integrands are integrable and the identity is never between junk values.

## Main results

* `NLAlib.integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw`:
  Gaussian integration by parts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- **Gaussian integration by parts** (Stein's identity, covariance form): for a Gaussian vector
`X` and `f` of class `C¹` with derivative bounded by `C`,
`E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`.
[Vershynin2018, Lemma 7.2.5]; stated there for a standard Gaussian, `E [g f(g)] = E f'(g)`; here
any mean and any covariance, possibly singular, and no centring hypothesis (a centred consumer
rewrites with `sub_zero`).
Result: gaussian-integration-by-parts -/
theorem integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw
    {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (i : ι) :
    ∫ ω, (X ω i - ∫ ω', X ω' i ∂μ) * f (X ω) ∂μ =
      ∑ j, covariance (fun ω => X ω i) (fun ω => X ω j) μ *
        ∫ ω, fderiv ℝ f (X ω) (Pi.single j 1) ∂μ := by
  sorry

end NLAlib
