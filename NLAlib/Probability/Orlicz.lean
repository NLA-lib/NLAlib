/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.SubExponential.Basic
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Orlicz conditions: the `ψ₂` and `ψ₁` bridges

Much of the literature (Vershynin's book in particular) states sub-Gaussian and sub-exponential
hypotheses through Orlicz conditions. Here they are constructor hypotheses of the library's
interfaces, never hypotheses of a concentration theorem: the `ψ₂` condition with squared scale
`K`, `E exp (X² / K) ≤ 2`, makes a centred `X` satisfy Mathlib's `HasSubgaussianMGF` with proxy
`C K`, and the `ψ₁` condition with scale `K`, `E exp (|X| / K) ≤ 2`, makes a centred `X` satisfy
`NLAlib.HasSubexponentialMGF` with proxy `C₁ K²` and scale `C₂ K`. Each condition is written as
two hypotheses, integrability and the integral bound; no Orlicz norm is defined. Vershynin's
`‖X‖_ψ₂ ≤ K'` is `K = K' ^ 2`, his `‖X‖_ψ₁ ≤ K` is `K`.

Every conclusion is centred, so the bridges need `E X = 0`; for a variable that is not centred
the `sub_integral` forms bound `X - E X`, at the price of a factor in the scale (the centring
lemma, [Vershynin2018, Lemma 2.6.8]).

`0 < K` is needed: `X² / 0 = 0` in Lean, so the condition at `K = 0` holds for every `X`.
A probability measure is needed: under `2 • δ₀` the variable `0` satisfies the `ψ₂` condition but
has `mgf 0 = 2 > 1`. `AEMeasurable X` is a hypothesis: integrability of `exp (X² / K)` does not
give it (the sign is lost).

A `ψ₂` Hanson–Wright inequality is the `ψ₂` bridge followed by
`NLAlib.measureReal_quadForm_sub_integral_ge_le`, and a `ψ₁` Bernstein inequality is the `ψ₁`
bridge followed by `NLAlib.HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`; neither is
restated (`docs/design/Probability-P7.md` §7 D3, D4).

## Main definitions

* `NLAlib.psiTwoSubgaussianConstant`, `NLAlib.psiOneSubexponentialVarianceConstant`,
  `NLAlib.psiOneSubexponentialScaleConstant`: the constants of the bridges.

## Main results

* `NLAlib.hasSubgaussianMGF_of_integral_exp_sq_div_le_two`: the `ψ₂` bridge.
* `NLAlib.hasSubexponentialMGF_of_integral_exp_abs_div_le_two`: the `ψ₁` bridge.
* `NLAlib.hasSubgaussianMGF_sub_integral_of_integral_exp_sq_div_le_two`,
  `NLAlib.hasSubexponentialMGF_sub_integral_of_integral_exp_abs_div_le_two`: the centred forms.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], §2.5–§2.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The proxy constant of the `ψ₂` bridge `NLAlib.hasSubgaussianMGF_of_integral_exp_sq_div_le_two`.
[Vershynin2018, Proposition 2.5.2] leaves it unspecified. The proof (`e^y ≤ y + e^{y²}`, then
Jensen for `λ² K ≤ 1`, and `λ X ≤ λ² K / 2 + X² / (2K)` otherwise) reaches `1 + log 2`; the body
is an upper bound on that value, and may be lowered to it (`Real.toNNReal (1 + Real.log 2)`). A
smaller value is a better bound. Use only `psiTwoSubgaussianConstant_le`. -/
noncomputable irreducible_def psiTwoSubgaussianConstant : ℝ≥0 := 2

/-- An explicit upper bound on `psiTwoSubgaussianConstant`.
Proof: `psiTwoSubgaussianConstant_def`. Easy. -/
theorem psiTwoSubgaussianConstant_le : psiTwoSubgaussianConstant ≤ 2 := by
  sorry

/-- **A centred variable with a `ψ₂` bound is sub-Gaussian**: if `E X = 0`, `exp (X² / K)` is
integrable and `E exp (X² / K) ≤ 2`, then `HasSubgaussianMGF X (C K)` with
`C = psiTwoSubgaussianConstant`. [Vershynin2018, Proposition 2.5.2], (iv) ⟹ (v), with Vershynin's
`‖X‖_ψ₂ ≤ K'` as `K = K' ^ 2` and the constant named. The hypothesis `E X = 0` is needed (every
`HasSubgaussianMGF` variable is centred); for a variable that is not centred, use
`NLAlib.hasSubgaussianMGF_sub_integral_of_integral_exp_sq_div_le_two`. A `ψ₂` Hanson–Wright
inequality is `measureReal_quadForm_sub_integral_ge_le hind fun i => this (hψ i)`, with exponent
Vershynin's at `c = psiTwoSubgaussianConstant * K`.
Proof: `e^y ≤ y + e^{y²}`, so `mgf X μ λ ≤ E exp (λ² X²)` (the linear term vanishes). If
`λ² K ≤ 1`, Jensen for the concave `x ↦ x ^ (λ² K)` gives `≤ 2 ^ (λ² K) = e^{λ² K log 2}`;
otherwise `λ X ≤ λ² K / 2 + X² / (2K)` and Cauchy–Schwarz give `≤ e^{λ² K / 2} √2`. Both are at
most `e^{(1 + log 2) K λ² / 2}`. Integrability of `exp (λ X)` from `exp (λ X) ≤
e^{λ² K / 2} exp (X² / (2K))`. Medium.
Result: subgaussian-def -/
theorem hasSubgaussianMGF_of_integral_exp_sq_div_le_two [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (hmean : ∫ ω, X ω ∂μ = 0) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (X ω ^ 2 / K)) μ)
    (hψ : ∫ ω, rexp (X ω ^ 2 / K) ∂μ ≤ 2) :
    HasSubgaussianMGF X (psiTwoSubgaussianConstant * K) μ := by
  sorry

/-- **The centred `ψ₂` bridge**: if `exp (X² / K)` is integrable and `E exp (X² / K) ≤ 2`, then
`X - E X` is sub-Gaussian with proxy `C · 4K`, `C = psiTwoSubgaussianConstant`.
[Vershynin2018, Lemma 2.6.8] (centring costs a constant factor in the `ψ₂` norm), here with the
explicit factor `4` in the squared scale.
Proof: `X - E X` satisfies the `ψ₂` condition with squared scale `4K`: `(EX)² ≤ K log 2` by
Jensen (`exp ((EX)² / K) ≤ E exp (X² / K) ≤ 2`), `(X - EX)² ≤ 2X² + 2(EX)²`, and
`E exp (X² / (2K)) ≤ √2` by Jensen, so `E exp ((X - EX)² / (4K)) ≤ √2 · √2 = 2`; then
`NLAlib.hasSubgaussianMGF_of_integral_exp_sq_div_le_two`. Integrability of `X` from
`|X| ≤ K + exp (X² / K)`, up to constants. Easy to medium. -/
theorem hasSubgaussianMGF_sub_integral_of_integral_exp_sq_div_le_two [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (X ω ^ 2 / K)) μ)
    (hψ : ∫ ω, rexp (X ω ^ 2 / K) ∂μ ≤ 2) :
    HasSubgaussianMGF (fun ω => X ω - ∫ ω', X ω' ∂μ) (psiTwoSubgaussianConstant * (4 * K)) μ := by
  sorry

/-- The variance-proxy constant of the `ψ₁` bridge
`NLAlib.hasSubexponentialMGF_of_integral_exp_abs_div_le_two`. [Vershynin2018,
Proposition 2.7.1] leaves it unspecified. The proof (`e^y ≤ 1 + y + y² e^{|y|} / 2` on
`|λ| < 1 / (2K)`, and `u² ≤ 4 e^{u - 2}`) reaches `32 / e²`; the body is an upper bound on that
value. A smaller value is a better bound. Use only `psiOneSubexponentialVarianceConstant_le`. -/
noncomputable irreducible_def psiOneSubexponentialVarianceConstant : ℝ≥0 := 5

/-- The scale constant of the `ψ₁` bridge
`NLAlib.hasSubexponentialMGF_of_integral_exp_abs_div_le_two`. [Vershynin2018,
Proposition 2.7.1] leaves it unspecified; the proof reaches `2`. A smaller value is a better
bound. Use only `psiOneSubexponentialScaleConstant_le`. -/
noncomputable irreducible_def psiOneSubexponentialScaleConstant : ℝ≥0 := 2

/-- An explicit upper bound on `psiOneSubexponentialVarianceConstant`.
Proof: `psiOneSubexponentialVarianceConstant_def`. Easy. -/
theorem psiOneSubexponentialVarianceConstant_le : psiOneSubexponentialVarianceConstant ≤ 5 := by
  sorry

/-- An explicit upper bound on `psiOneSubexponentialScaleConstant`.
Proof: `psiOneSubexponentialScaleConstant_def`. Easy. -/
theorem psiOneSubexponentialScaleConstant_le : psiOneSubexponentialScaleConstant ≤ 2 := by
  sorry

/-- **A centred variable with a `ψ₁` bound is sub-exponential**: if `E X = 0`, `exp (|X| / K)`
is integrable and `E exp (|X| / K) ≤ 2`, then `X` is sub-exponential with variance proxy
`C₁ K²` and scale `C₂ K`, `C₁ = psiOneSubexponentialVarianceConstant`,
`C₂ = psiOneSubexponentialScaleConstant`. [Vershynin2018, Proposition 2.7.1], (iv) ⟹ (v), with
the constants named. The hypothesis `E X = 0` is needed (every `HasSubexponentialMGF` variable
is centred, `NLAlib.HasSubexponentialMGF.integral_eq_zero`); for a variable that is not
centred, use `NLAlib.hasSubexponentialMGF_sub_integral_of_integral_exp_abs_div_le_two`. A `ψ₁`
Bernstein inequality is this bridge followed by
`NLAlib.HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`.
Proof: for `|λ| < 1 / (2K)`, `e^y ≤ 1 + y + y² e^{|y|} / 2` gives
`mgf X μ λ ≤ 1 + λ² E[X² e^{|X| / (2K)}] / 2`, and `X² ≤ (16 K² / e²) e^{|X| / (2K)}` (from
`u² ≤ 4 e^{u - 2}`) bounds the expectation by `(16 K² / e²) E e^{|X| / K} ≤ 32 K² / e²`; then
`1 + a ≤ e^a`. Medium.
Result: subexponential-def -/
theorem hasSubexponentialMGF_of_integral_exp_abs_div_le_two [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (hmean : ∫ ω, X ω ∂μ = 0) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (|X ω| / K)) μ)
    (hψ : ∫ ω, rexp (|X ω| / K) ∂μ ≤ 2) :
    HasSubexponentialMGF X (psiOneSubexponentialVarianceConstant * K ^ 2)
      (psiOneSubexponentialScaleConstant * K) μ := by
  sorry

/-- **The centred `ψ₁` bridge**: if `exp (|X| / K)` is integrable and `E exp (|X| / K) ≤ 2`,
then `X - E X` is sub-exponential with variance proxy `C₁ (2K)²` and scale `C₂ (2K)`. The `ψ₁`
analogue of the centring lemma [Vershynin2018, Lemma 2.6.8], with the explicit factor `2` in the
scale.
Proof: `X - E X` satisfies the `ψ₁` condition with scale `2K`: `|EX| ≤ K log 2` by Jensen,
`E exp (|X| / (2K)) ≤ √2` by Jensen, and `|X - EX| ≤ |X| + |EX|`, so
`E exp (|X - EX| / (2K)) ≤ 2`; then
`NLAlib.hasSubexponentialMGF_of_integral_exp_abs_div_le_two`. Easy to medium. -/
theorem hasSubexponentialMGF_sub_integral_of_integral_exp_abs_div_le_two
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEMeasurable X μ) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (|X ω| / K)) μ)
    (hψ : ∫ ω, rexp (|X ω| / K) ∂μ ≤ 2) :
    HasSubexponentialMGF (fun ω => X ω - ∫ ω', X ω' ∂μ)
      (psiOneSubexponentialVarianceConstant * (2 * K) ^ 2)
      (psiOneSubexponentialScaleConstant * (2 * K)) μ := by
  sorry

end NLAlib
