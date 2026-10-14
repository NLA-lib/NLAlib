/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Entropy

/-!
# The entropy of the exponential of a bounded function

If `g` takes values in `[a, b]`, then `Ent(e^{s g}) ≤ s² (b - a)² / 8 · E e^{s g}`: the entropy
form of Hoeffding's lemma. With Herbst's argument
(`NLAlib.hasSubgaussianMGF_sub_integral_of_entropy_le`) it recovers Hoeffding's lemma; with the
tensorization of entropy (`NLAlib.entropy_pi_le_sum`) applied on the fibres of a function of
independent coordinates it gives the bounded differences inequality
(`NLAlib/Probability/BoundedDifferences.lean`).

This file is a skeleton addition to `NLAlib/Probability/Entropy.lean`
(`docs/design/Probability-P7.md` §3.2, §8), to be merged into it at wrap-up.

## Main results

* `NLAlib.entropy_exp_mul_le_of_mem_Icc`: for `g` almost surely in `[a, b]`.
* `NLAlib.entropy_exp_mul_le_of_abs_sub_le`: for `g` with oscillation at most `c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}

/-- **The entropy of an exponential of a bounded function**: if `g` lies in `[a, b]` almost
surely, then `Ent(e^{s g}) ≤ s² (b - a)² / 8 · E e^{s g}` for every `s`. The entropy form of
Hoeffding's lemma, with the hypothesis of Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`.
[BoucheronLugosiMassart2013, proof of Theorem 6.2].
Proof: with `Λ = cgf g ν`, `Ent(e^{s g}) / E e^{s g} = s Λ'(s) - Λ(s) = ∫₀ˢ θ Λ''(θ) dθ`, and
`Λ''(θ)` is the variance of `g` under the tilted measure `ν.tilted (θ * g ·)`, at most
`(b - a)² / 4`. The steps are those of Mathlib's
`ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero`
(`exists_cgf_eq_iteratedDeriv_two_cgf_mul`, `variance_tilted_mul`, `variance_le_sq_of_bounded`),
with the integral form of Taylor's theorem for `s Λ'(s) - Λ(s)` in place of the mean value form.
`s = 0`: both sides are `0`. Medium. -/
theorem entropy_exp_mul_le_of_mem_Icc [IsProbabilityMeasure ν] {g : Ω → ℝ}
    (hg : AEMeasurable g ν) {a b : ℝ} (hab : ∀ᵐ ω ∂ν, g ω ∈ Set.Icc a b) (s : ℝ) :
    entropy ν (fun ω => rexp (s * g ω)) ≤ s ^ 2 * (b - a) ^ 2 / 8 * ∫ ω, rexp (s * g ω) ∂ν := by
  sorry

/-- **The entropy of an exponential of a function of bounded oscillation**: if
`|g x - g y| ≤ c` for all `x`, `y`, then `Ent(e^{s g}) ≤ s² c² / 8 · E e^{s g}`. The pointwise
form used on the fibres of a function with bounded differences.
[BoucheronLugosiMassart2013, proof of Theorem 6.2].
Proof: `Ω` is nonempty (probability measure) and `g` is bounded, so with `a = sInf (Set.range g)`
and `b = a + c`, `g` takes values in `[a, b]`; `NLAlib.entropy_exp_mul_le_of_mem_Icc`. Easy. -/
theorem entropy_exp_mul_le_of_abs_sub_le [IsProbabilityMeasure ν] {g : Ω → ℝ}
    (hg : AEMeasurable g ν) {c : ℝ≥0} (hc : ∀ x y, |g x - g y| ≤ c) (s : ℝ) :
    entropy ν (fun ω => rexp (s * g ω)) ≤ s ^ 2 * c ^ 2 / 8 * ∫ ω, rexp (s * g ω) ∂ν := by
  sorry

end NLAlib
