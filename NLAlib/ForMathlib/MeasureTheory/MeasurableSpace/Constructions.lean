/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Arbitrary functions after countable-range measurable maps

An arbitrary function is measurable on a countable subtype with measurable singletons.
Therefore a measurable map with countable range may be postcomposed with any function.
Upstream candidate for `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`.

## Main results

* `Measurable.comp_of_countable_range`: postcomposition preserves measurability on countable range.
-/

@[expose] public section

/-- An arbitrary function composed after a measurable map with countable range is measurable,
provided the intermediate space has measurable singletons. -/
theorem Measurable.comp_of_countable_range {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSingletonClass β]
    {g : α → β} (hg : Measurable g) (hcount : (Set.range g).Countable) (f : β → γ) :
    Measurable (f ∘ g) := by
  have : Countable (Set.range g) := hcount.to_subtype
  exact (measurable_of_countable (fun b : Set.range g => f b)).comp
    (hg.subtype_mk (h := fun a => Set.mem_range_self a))
