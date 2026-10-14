/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.GaussianIntegrationByParts

/-!
# Gaussian interpolation and comparison

Kahane's Gaussian interpolation inequality and the two expectation comparisons proved from it:
the Sudakov–Fernique inequality `E max X ≤ E max Y` and Gordon's min-max inequality
`E min max X ≤ E min max Y`, each for centred finite Gaussian families whose increments compare.

A finite Gaussian family is `X : T → Ω → ℝ` with `HasGaussianLaw (fun ω t => X t ω) μ`, the
process form of Mathlib's `IsGaussianProcess` (for finite `T` the two are equivalent; the bridge
is added when a consumer holds an `IsGaussianProcess`). Gordon's two-index family is
`X : U → T → Ω → ℝ` with `HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ`. The two families
of a comparison live on different probability spaces: only their laws matter, and a comparison
process need not be built on the space of the process it bounds. Second moments of increments are
written as integrals, the form a consumer computes from isotropy. No equal-variance hypothesis is
needed in the expectation forms (unlike Slepian's tail comparison, which is not stated).

Over an empty index set the suprema and infima are `0` (`Real.iSup_of_isEmpty`), and both sides
of each comparison vanish.

## Main results

* `NLAlib.integral_comp_le_integral_comp_of_hasGaussianLaw`: Gaussian interpolation (Kahane).
* `NLAlib.integral_iSup_le_integral_iSup_of_hasGaussianLaw`: the Sudakov–Fernique inequality.
* `NLAlib.integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw`: Gordon's min-max
  inequality.
* Integrability companions: `NLAlib.integrable_comp_of_hasGaussianLaw_of_contDiff_two`,
  `NLAlib.integrable_iSup_of_hasGaussianLaw`, `NLAlib.integrable_iInf_iSup_of_hasGaussianLaw`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω}
  {ν : Measure Ω'}

section Interpolation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A function of class `C²` with Hessian bounded by `C` of a Gaussian vector is integrable: it
has quadratic growth and a Gaussian vector has every moment. -/
theorem integrable_comp_of_hasGaussianLaw_of_contDiff_two {X : Ω → ι → ℝ}
    (hX : HasGaussianLaw X μ) {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {C : ℝ}
    (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) : Integrable (fun ω => F (X ω)) μ := by
  sorry

/-- **Gaussian interpolation** (Kahane's inequality): for centred Gaussian vectors `X`, `Y` and
`F` of class `C²` with Hessian bounded by `C`, if
`∑ i j, (E Yᵢ Yⱼ - E Xᵢ Xⱼ) ∂ᵢⱼF(x) ≥ 0` for every `x`, then `E F(X) ≤ E F(Y)`.
[Vershynin2018, Lemma 7.2.7 and the proof of Theorem 7.2.1]; [Kahane1986]; there as an identity
along the interpolating path `√t X + √(1 - t) Y`, here the inequality it gives, with `X` and `Y`
on different probability spaces.
Result: gaussian-interpolation -/
theorem integral_comp_le_integral_comp_of_hasGaussianLaw {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X μ) (hY : HasGaussianLaw Y ν)
    (hX0 : ∀ i, ∫ ω, X ω i ∂μ = 0) (hY0 : ∀ i, ∫ ω, Y ω i ∂ν = 0)
    {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {C : ℝ} (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C)
    (hcov : ∀ x, 0 ≤ ∑ i, ∑ j, (∫ ω, Y ω i * Y ω j ∂ν - ∫ ω, X ω i * X ω j ∂μ) *
      iteratedFDeriv ℝ 2 F x ![Pi.single i 1, Pi.single j 1]) :
    ∫ ω, F (X ω) ∂μ ≤ ∫ ω, F (Y ω) ∂ν := by
  sorry

end Interpolation

section Comparison

variable {T U : Type*} [Fintype T] [Fintype U]

/-- The maximum of a finite Gaussian family is integrable. -/
theorem integrable_iSup_of_hasGaussianLaw {X : T → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω t => X t ω) μ) : Integrable (fun ω => ⨆ t, X t ω) μ := by
  sorry

/-- The min-max `min_u max_t X u t` of a finite Gaussian family on `U × T` is integrable. -/
theorem integrable_iInf_iSup_of_hasGaussianLaw {X : U → T → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ) :
    Integrable (fun ω => ⨅ u, ⨆ t, X u t ω) μ := by
  sorry

/-- **The Sudakov–Fernique inequality**: for centred finite Gaussian families `X`, `Y` with
`E (X s - X t)² ≤ E (Y s - Y t)²` for all `s`, `t`, `E max X ≤ E max Y`.
[Vershynin2018, Theorem 7.2.11]; no equal-variance hypothesis (unlike Slepian's inequality), and
the two families on different probability spaces.
Result: sudakov-fernique -/
theorem integral_iSup_le_integral_iSup_of_hasGaussianLaw {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω t => X t ω) μ) (hY : HasGaussianLaw (fun ω t => Y t ω) ν)
    (hX0 : ∀ t, ∫ ω, X t ω ∂μ = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂ν = 0)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂μ ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂ν) :
    ∫ ω, ⨆ t, X t ω ∂μ ≤ ∫ ω, ⨆ t, Y t ω ∂ν := by
  sorry

/-- **Gordon's min-max inequality**: for centred finite Gaussian families on `U × T` whose
increments are smaller for `X` within a block (`u` fixed) and larger for `X` across blocks,
`E min_u max_t X ≤ E min_u max_t Y`.
[Gordon1985]; [Vershynin2018, Exercise 7.2.14]; stated there with equal variances and as a tail
comparison, here the expectation form from increments alone, with the two families on different
probability spaces.
Result: gordon-inequality -/
theorem integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw
    {X : U → T → Ω → ℝ} {Y : U → T → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ)
    (hY : HasGaussianLaw (fun ω (p : U × T) => Y p.1 p.2 ω) ν)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂μ = 0) (hY0 : ∀ u t, ∫ ω, Y u t ω ∂ν = 0)
    (hsame : ∀ u t s, ∫ ω, (X u t ω - X u s ω) ^ 2 ∂μ ≤ ∫ ω, (Y u t ω - Y u s ω) ^ 2 ∂ν)
    (hdiff : ∀ u u' t s, u ≠ u' →
      ∫ ω, (Y u t ω - Y u' s ω) ^ 2 ∂ν ≤ ∫ ω, (X u t ω - X u' s ω) ^ 2 ∂μ) :
    ∫ ω, ⨅ u, ⨆ t, X u t ω ∂μ ≤ ∫ ω, ⨅ u, ⨆ t, Y u t ω ∂ν := by
  sorry

end Comparison

end NLAlib
