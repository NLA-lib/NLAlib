/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.SubGaussian

/-!
# The entropy functional and Herbst's argument

`NLAlib.entropy ν f = E f log f - E f log E f` is the entropy of a nonnegative function under a
measure. It is nonnegative under a probability measure (Jensen), it tensorizes over product
measures, and an entropy bound for `exp (s f)` of the right order in `s` makes `f - E f`
sub-Gaussian (Herbst's argument). These are the steps from a logarithmic Sobolev inequality to
concentration.

`entropy ν f` is a junk value when `f log f` or `f` is not integrable (the Bochner integral is `0`
then), so every statement about it carries the integrability it needs.

## Main definitions

* `NLAlib.entropy ν f`.

## Main results

* `NLAlib.entropy_nonneg`.
* `NLAlib.entropy_pi_le_sum`: tensorization of entropy.
* `NLAlib.hasSubgaussianMGF_sub_integral_of_entropy_le`: Herbst's argument.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Theorem 4.10 and Proposition 6.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}

/-- The entropy of a nonnegative function `f` under `ν`: `E f log f - E f log E f`. It is a junk
value when `f` or `f log f` is not integrable. -/
noncomputable def entropy (ν : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω * Real.log (f ω) ∂ν - (∫ ω, f ω ∂ν) * Real.log (∫ ω, f ω ∂ν)

/-- The entropy of a nonnegative function under a probability measure is nonnegative. -/
theorem entropy_nonneg [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[ν] f)
    (hf : Integrable f ν) (hflog : Integrable (fun ω => f ω * Real.log (f ω)) ν) :
    0 ≤ entropy ν f := by
  sorry

/-- **Tensorization of entropy** ([BoucheronLugosiMassart2013], Theorem 4.10): the entropy of a
function under a product of probability measures is at most the sum over coordinates of the
mean entropy in that coordinate, the others fixed. -/
theorem entropy_pi_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    {f : (∀ i, X i) → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f (Measure.pi ν))
    (hflog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi ν)) :
    entropy (Measure.pi ν) f ≤
      ∑ i, ∫ x, entropy (ν i) (fun y => f (Function.update x i y)) ∂Measure.pi ν := by
  sorry

/-- **Herbst's argument** ([BoucheronLugosiMassart2013], Proposition 6.1): if the entropy of
`exp (s f)` is at most `c s² / 2` times its mean for every `s`, then `f - E f` is sub-Gaussian with
proxy `c`. The hypothesis for `s > 0` gives the upper tail, for `s < 0` the lower one. -/
theorem hasSubgaussianMGF_sub_integral_of_entropy_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    {c : ℝ≥0} (hint : ∀ s, Integrable (fun ω => rexp (s * f ω)) μ)
    (hent : ∀ s, entropy μ (fun ω => rexp (s * f ω)) ≤ c * s ^ 2 / 2 * ∫ ω, rexp (s * f ω) ∂μ) :
    HasSubgaussianMGF (fun ω => f ω - ∫ ω', f ω' ∂μ) c μ := by
  sorry

end NLAlib
