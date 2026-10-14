/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.UniformOn

/-!
# Sampling an index from a finite probability vector

`NLAlib.samplingMeasure p` is the law of a random index `i` drawn with probability `p i`, for
weights `p : ι → ℝ≥0` on a finite type. The definition takes any weights, so statements carry no
proof term; it is a probability measure when `∑ i, p i = 1`. Uniform sampling is the case
`p = fun _ => (card ι)⁻¹`, which is Mathlib's `uniformOn Set.univ`, and the bridge to `PMF` is
`NLAlib.samplingMeasure_toNNReal_eq_toMeasure`.

## Main definitions

* `NLAlib.samplingMeasure p`: `∑ i, p i • dirac i`.

## Main results

* `NLAlib.isProbabilityMeasure_samplingMeasure`.
* `NLAlib.integral_samplingMeasure`: `∫ f = ∑ i, p i • f i`.
* `NLAlib.measureReal_eq_of_hasLaw_samplingMeasure`: `P(X = i) = p i`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : ι → ℝ≥0)

/-- The law of a random index that equals `i` with probability `p i`. It is a probability
measure when `∑ i, p i = 1` (`isProbabilityMeasure_samplingMeasure`); the definition takes any
weights so that statements carry no proof term. -/
noncomputable def samplingMeasure : Measure ι :=
  ∑ i, (p i : ℝ≥0∞) • Measure.dirac i

instance isFiniteMeasure_samplingMeasure : IsFiniteMeasure (samplingMeasure p) := by
  sorry

/-- With weights summing to one, `samplingMeasure p` is a probability measure. -/
theorem isProbabilityMeasure_samplingMeasure (hp : ∑ i, p i = 1) :
    IsProbabilityMeasure (samplingMeasure p) := by
  sorry

/-- The probability of a set of indices is the sum of their weights. -/
theorem samplingMeasure_real_apply (s : Finset ι) :
    (samplingMeasure p).real (s : Set ι) = ∑ i ∈ s, (p i : ℝ) := by
  sorry

/-- Every function is integrable for `samplingMeasure p`. -/
theorem integrable_samplingMeasure {E : Type*} [NormedAddCommGroup E] (f : ι → E) :
    Integrable f (samplingMeasure p) := by
  sorry

/-- The integral against `samplingMeasure p` is the weighted sum. -/
theorem integral_samplingMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ι → E) :
    ∫ i, f i ∂samplingMeasure p = ∑ i, (p i : ℝ) • f i := by
  sorry

/-- A random index with law `samplingMeasure p` equals `i` with probability `p i`. -/
theorem measureReal_eq_of_hasLaw_samplingMeasure {X : Ω → ι}
    (hX : HasLaw X (samplingMeasure p) μ) (i : ι) : μ.real {ω | X ω = i} = p i := by
  sorry

/-- The bridge to `PMF`. -/
theorem samplingMeasure_toNNReal_eq_toMeasure (q : PMF ι) :
    samplingMeasure (fun i => (q i).toNNReal) = q.toMeasure := by
  sorry

/-- Uniform weights give Mathlib's uniform measure. -/
theorem samplingMeasure_const_inv_card :
    samplingMeasure (fun _ : ι => (Fintype.card ι : ℝ≥0)⁻¹) = uniformOn Set.univ := by
  sorry

end NLAlib
