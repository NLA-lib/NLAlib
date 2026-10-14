/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.GaussianIntegrationByParts

/-!
# Gaussian integration by parts for derivatives of polynomial growth

Stein's identity in covariance form, `E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`,
for a Gaussian vector `X` and `f` of class `C¹` whose derivative grows at most polynomially,
`‖Df(x)‖ ≤ C (1 + ‖x‖)^k`. The bounded-derivative identity of
`NLAlib/Probability/Distributions/GaussianIntegrationByParts.lean` is the case `k = 0`. The
polynomial class is the one trace polynomials `x ↦ re tr (B (∑ x j • A j)^q)` belong to, as the
Gaussian moment recursion of the noncommutative Khintchine inequality needs
(`NLAlib/Probability/MatrixConcentration/Khintchine.lean`).

This skeleton file is to be merged into `GaussianIntegrationByParts.lean`, which owns the
subject; the bounded version is then reproved from this one at `k = 0` and keeps its name
(P5c D4 and §8).

## Main results

* Stein's identity for derivatives of polynomial growth:
  `integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw_of_le_pow`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- **Gaussian integration by parts** (Stein's identity, covariance form) for `f` of class `C¹`
whose derivative grows at most polynomially, `‖Df(x)‖ ≤ C (1 + ‖x‖)^k`:
`E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`.
[Vershynin2018, Lemma 7.2.5]; stated there for a standard Gaussian, here any mean and any
covariance, possibly singular. `‖x‖` is the sup norm of `ι → ℝ`; any norm gives the same class.
Both integrands are integrable (Gaussian moments of every order), so the identity is never
between junk values. Proof: the route of
`integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw`, whose
one-dimensional step `integral_mul_eq_integral_deriv_gaussianReal_one` takes only integrability;
the bounded derivative is used there only for the growth and `L²` bounds, which polynomial growth
replaces through `memLp_id_gaussianReal` and `HasGaussianLaw.memLp`.
Result: gaussian-integration-by-parts -/
theorem integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw_of_le_pow
    {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} {k : ℕ} (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) (i : ι) :
    ∫ ω, (X ω i - ∫ ω', X ω' i ∂μ) * f (X ω) ∂μ =
      ∑ j, covariance (fun ω => X ω i) (fun ω => X ω j) μ *
        ∫ ω, fderiv ℝ f (X ω) (Pi.single j 1) ∂μ := by
  sorry

end NLAlib
