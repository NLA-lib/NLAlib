/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.OpsSampling
public import NLAlib.ForMathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measurability of the implemented word samplers

Measurable real-word rounding maps with countable ranges give measurable implemented samplers,
even when their word carrier is uncountable. Arbitrary scalar functions are measurable on
those rounded ranges. Numerical accuracy and the distribution of the ideal tape remain
separate properties.

## Main results

* `NLAlib.Ops.Machine.measurable_uniformSample`: measurable uniform word sampling.
* `NLAlib.Ops.Machine.measurable_normalSample`: measurable complex Gaussian word sampling.
* `NLAlib.Ops.Machine.sampler_regular`: the fiber and range properties of both actual samplers.
-/

@[expose] public section

namespace NLAlib.Ops.Machine

variable {K : Type} [MeasurableSpace K] [MeasurableSingletonClass K]

/-- The implemented uniform sampler is measurable when real-word rounding is measurable with
countable range. No continuity of the machine's multiplication is assumed. -/
theorem measurable_uniformSample (M : Machine K) {roundUnif : ℝ → K}
    (h : Measurable roundUnif) (hc : (Set.range roundUnif).Countable) (s : K) :
    Measurable (M.uniformSample roundUnif s) :=
  h.comp_of_countable_range hc (M.mul s)

/-- The actual complex sampler is measurable from measurable, countable-range real rounding.
The normalization is the same stored square-root word computed by the program. -/
theorem measurable_normalSample (M : Machine K) {roundGaussian : ℝ → K}
    (h : Measurable roundGaussian) (hc : (Set.range roundGaussian).Countable) :
    Measurable (M.normalSample roundGaussian) := by
  have hmul := h.comp_of_countable_range hc (fun a : K => M.mul a M.sqrtHalf)
  exact (hmul.comp (measurable_const.mul Complex.continuous_re.measurable)).prodMk
    (hmul.comp (measurable_const.mul Complex.continuous_im.measurable))

/-- The lazy-sampling theorem's regularity requirements follow from measurable rounding maps
with countable ranges. These are properties of the same implemented sampler functions,
with no algorithm-specific output or execution assumption. -/
theorem sampler_regular (M : Machine K) {roundUnif roundGaussian : ℝ → K}
    (hU : Measurable roundUnif) (hG : Measurable roundGaussian)
    (hcU : (Set.range roundUnif).Countable) (hcG : (Set.range roundGaussian).Countable) :
    (∀ c z, MeasurableSet (M.uniformSample roundUnif c ⁻¹' {z})) ∧
      (∀ c, (Set.range (M.uniformSample roundUnif c)).Countable) ∧
      (∀ z, MeasurableSet (M.normalSample roundGaussian ⁻¹' {z})) ∧
      (Set.range (M.normalSample roundGaussian)).Countable := by
  refine ⟨fun c z => (M.measurable_uniformSample hU hcU c) (measurableSet_singleton z),
    fun c => (hcU.image (M.mul c)).mono ?_,
    fun z => (M.measurable_normalSample hG hcG) (measurableSet_singleton z),
    ((hcG.prod hcG).image (fun z : K × K => M.normalWords z.1 z.2)).mono ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨roundUnif v, Set.mem_range_self v, rfl⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨(roundGaussian (√2 * z.re), roundGaussian (√2 * z.im)),
      ⟨Set.mem_range_self _, Set.mem_range_self _⟩, rfl⟩

end NLAlib.Ops.Machine
