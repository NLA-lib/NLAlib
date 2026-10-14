/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import NLAlib.Probability.EntropyExpBounded
public import NLAlib.Probability.EntropyTensorization

/-!
# The bounded differences inequality

A function `f` of independent coordinates `X ω i ∈ S i` whose value changes by at most `c i` when
the `i`-th coordinate alone changes is sub-Gaussian about its mean with proxy `∑ c i² / 4`, and
its upper tail is McDiarmid's `exp (-2t² / ∑ c i²)`. The proof is the entropy method: the
tensorization of entropy over the product law of `X` (`NLAlib.entropy_pi_le_sum`), the entropy
form of Hoeffding's lemma on each fibre (`NLAlib.entropy_exp_mul_le_of_abs_sub_le`) and Herbst's
argument (`NLAlib.hasSubgaussianMGF_sub_integral_of_entropy_le`).

The coordinates live in arbitrary measurable spaces. No integrability is assumed: bounded
differences on a finite product make `f` bounded. No probability hypothesis is assumed either:
`iIndepFun` gives it (`ProbabilityTheory.iIndepFun.isProbabilityMeasure`). Lower and two-sided
tails are the same statements for `-f`, with `NLAlib.measureReal_abs_ge_le_add`; they are not
restated.

## Main results

* `NLAlib.hasSubgaussianMGF_sub_integral_of_abs_update_sub_le`: bounded differences.
* `NLAlib.measureReal_sub_integral_ge_le_mcdiarmid`: McDiarmid's inequality.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Theorem 6.2.
* [C. McDiarmid, *On the method of bounded differences*][McDiarmid1989].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]
  [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)] {X : Ω → ∀ i, S i}
  {f : (∀ i, S i) → ℝ} {c : ι → ℝ≥0}

/-- **The bounded differences inequality**: a measurable function `f` of independent coordinates
whose value changes by at most `c i` when the `i`-th coordinate alone changes is sub-Gaussian
about its mean, `f (X) - E f (X)`, with proxy `∑ c i² / 4`. [BoucheronLugosiMassart2013,
Theorem 6.2]; [McDiarmid1989]. Coordinates in arbitrary measurable spaces; no integrability or
probability hypothesis (`f` is bounded; `iIndepFun` gives a probability measure).
Proof: transport to the product `Measure.pi ν` of the coordinate laws (`iIndepFun` and `hX`
give the law of `X`, `iIndepFun_iff_map_fun_eq_pi_map`). There, for each `s`, P4's
`NLAlib.entropy_pi_le_sum` bounds the entropy of `e^{s f}` by the sum over `i` of the expected
entropies in the `i`-th coordinate; on the fibre `y ↦ f (Function.update x i y)` the oscillation
is at most `c i`, so `NLAlib.entropy_exp_mul_le_of_abs_sub_le` bounds each by
`s² c i² / 8` times the fibre mean of `e^{s f}`, and `MeasureTheory.integral_integral_update_pi`
reassembles `E e^{s f}`. Herbst's argument
(`NLAlib.hasSubgaussianMGF_sub_integral_of_entropy_le`) with `c s² / 2 = s² ∑ c i² / 8`
concludes. The fibre measurability and the product law are the work. Medium.
Result: bounded-differences -/
theorem hasSubgaussianMGF_sub_integral_of_abs_update_sub_le
    (hX : ∀ i, AEMeasurable (fun ω => X ω i) μ) (hind : iIndepFun (fun i ω => X ω i) μ)
    (hf : Measurable f) (hc : ∀ i x y, |f (Function.update x i y) - f x| ≤ c i) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) ((∑ i, c i ^ 2) / 4) μ := by
  sorry

/-- **McDiarmid's inequality**: for a measurable function `f` of independent coordinates with
bounded differences `c i`, `P(t ≤ f (X) - E f (X)) ≤ exp (-2t² / ∑ c i²)` for `t ≥ 0`.
[McDiarmid1989]; [BoucheronLugosiMassart2013, Theorem 6.2]. The source's constant. At
`∑ c i² = 0` the bound is `exp 0 = 1` (Lean's `x / 0 = 0`), which is true.
Proof: `HasSubgaussianMGF.measure_ge_le` for
`NLAlib.hasSubgaussianMGF_sub_integral_of_abs_update_sub_le`, with
`t² / (2 · ∑ c i² / 4) = 2t² / ∑ c i²`. Easy.
Result: mcdiarmid -/
theorem measureReal_sub_integral_ge_le_mcdiarmid (hX : ∀ i, AEMeasurable (fun ω => X ω i) μ)
    (hind : iIndepFun (fun i ω => X ω i) μ) (hf : Measurable f)
    (hc : ∀ i x y, |f (Function.update x i y) - f x| ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ f (X ω) - ∫ ω', f (X ω') ∂μ} ≤ rexp (-2 * t ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  sorry

end NLAlib
