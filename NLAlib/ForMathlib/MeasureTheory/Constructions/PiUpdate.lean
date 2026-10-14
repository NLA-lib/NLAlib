/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Resampling one coordinate of a product measure

For a product `Measure.pi P` of probability measures, replacing the `i`-th coordinate by an
independent draw from `P i` preserves the product. The integration lemmas that follow (Fubini in
the resampled coordinate, integrability and measurability of the partial integral) are the steps
of every argument that conditions on all coordinates but one: tensorization of entropy, bounded
differences, Efron–Stein. Upstream candidate for `Mathlib/MeasureTheory/Constructions/Pi.lean`.

## Main results

* `MeasureTheory.measurePreserving_update_pi`.
* `MeasureTheory.integral_integral_update_pi`: `∫ ∫ F (update x i t) dP i dPi = ∫ F dPi`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

section Update

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (P : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]

/-- Resampling one coordinate preserves a product of probability measures. -/
theorem measurePreserving_update_pi (i : ι) :
    MeasurePreserving (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2)
      ((Measure.pi P).prod (P i)) (Measure.pi P) := by
  refine ⟨measurable_update', (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi (Function.update s i Set.univ) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · have := h j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · have := h1 j
        rw [Function.update_of_ne hj] at this
        rw [Function.update_of_ne hj]; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have : (fun j => P j (Function.update s i Set.univ j))
      = Function.update (fun j => P j (s j)) i 1 := by
    ext1 j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ i), one_mul,
    ← Finset.mul_prod_erase Finset.univ (fun j => P j (s j)) (Finset.mem_univ i), mul_comm,
    Finset.sdiff_singleton_eq_erase]

/-- If `F` is integrable for the product, so is `F` with the `i`-th coordinate resampled. -/
theorem integrable_comp_update_pi (i : ι) {F : (∀ j, X j) → ℝ}
    (hF : Integrable F (Measure.pi P)) :
    Integrable (fun p : (∀ j, X j) × X i => F (Function.update p.1 i p.2))
      ((Measure.pi P).prod (P i)) :=
  ((measurePreserving_update_pi P i).integrable_comp hF.aestronglyMeasurable).2 hF

/-- Fubini in the resampled coordinate: integrating `F (update x i t)` over `t` and then over `x`
gives the integral of `F`. -/
theorem integral_integral_update_pi (i : ι) {F : (∀ j, X j) → ℝ}
    (hF : Integrable F (Measure.pi P)) :
    ∫ x, ∫ t, F (Function.update x i t) ∂(P i) ∂(Measure.pi P) = ∫ x, F x ∂(Measure.pi P) := by
  have hmp := measurePreserving_update_pi P i
  rw [← integral_prod _ (integrable_comp_update_pi P i hF)]
  calc ∫ p, F (Function.update p.1 i p.2) ∂((Measure.pi P).prod (P i))
      = ∫ x, F x ∂(Measure.map (fun p : (∀ j, X j) × X i => Function.update p.1 i p.2)
          ((Measure.pi P).prod (P i))) :=
        (integral_map hmp.measurable.aemeasurable
          (by rw [hmp.map_eq]; exact hF.aestronglyMeasurable)).symm
    _ = ∫ x, F x ∂(Measure.pi P) := by rw [hmp.map_eq]

/-- For almost every `x`, the section `t ↦ F (update x i t)` of an integrable `F` is
integrable. -/
theorem ae_integrable_comp_update_pi (i : ι) {F : (∀ j, X j) → ℝ}
    (hF : Integrable F (Measure.pi P)) :
    ∀ᵐ x ∂(Measure.pi P), Integrable (fun t => F (Function.update x i t)) (P i) :=
  (integrable_comp_update_pi P i hF).prod_right_ae

/-- The partial integral `x ↦ ∫ F (update x i t) dP i` of an integrable `F` is integrable. -/
theorem integrable_integral_update_pi (i : ι) {F : (∀ j, X j) → ℝ}
    (hF : Integrable F (Measure.pi P)) :
    Integrable (fun x => ∫ t, F (Function.update x i t) ∂(P i)) (Measure.pi P) :=
  (integrable_comp_update_pi P i hF).integral_prod_left

omit [Fintype ι] in
/-- The partial integral of a measurable function in one coordinate is measurable. -/
theorem measurable_integral_update_pi (i : ι) {G : (∀ j, X j) → ℝ} (hG : Measurable G) :
    Measurable (fun x => ∫ t, G (Function.update x i t) ∂(P i)) :=
  (StronglyMeasurable.integral_prod_right'
    (f := fun p : (∀ j, X j) × X i => G (Function.update p.1 i p.2))
    (hG.comp measurable_update').stronglyMeasurable).measurable

end Update

end MeasureTheory
