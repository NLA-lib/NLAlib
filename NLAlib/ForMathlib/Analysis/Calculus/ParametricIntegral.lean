/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Differentiation on a compact support

Upstream candidate for Mathlib. Compact support and joint continuity give the uniform derivative
bound needed by dominated differentiation.

## Main results

* `MeasureTheory.hasFDerivAt_integral_of_compact_support`.
-/

@[expose] public section

open MeasureTheory Filter Set

open scoped Topology

namespace MeasureTheory

variable {X E Ω : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [LocallyCompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace Ω] [T2Space Ω] [SecondCountableTopology Ω] [MeasurableSpace Ω] [BorelSpace Ω]

/-- Jointly continuous first derivatives near a compact support fibre suffice for a Fréchet
derivative under the integral. In particular no regularity assumptions outside the measure's
support are imposed. -/
theorem hasFDerivAt_integral_of_compact_support (μ : Measure Ω) [IsFiniteMeasure μ]
    (hμ : IsCompact μ.support) (F : X → Ω → E) (D : X → Ω → X →L[ℝ] E)
    (U : Set (X × Ω)) (hU : IsOpen U) (hF : ContinuousOn (fun p => F p.1 p.2) U)
    (hD : ContinuousOn (fun p => D p.1 p.2) U)
    (hderiv : ∀ p ∈ U, HasFDerivAt (fun x => F x p.2) (D p.1 p.2) p.1)
    (x₀ : X) (hpoint : ∀ a ∈ μ.support, (x₀, a) ∈ U) :
    HasFDerivAt (fun x => ∫ a, F x a ∂μ) (∫ a, D x₀ a ∂μ) x₀ := by
  obtain ⟨V, W, hVo, hWo, hxV, hsubW, hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := x₀)) hμ hU (by rintro ⟨x, a⟩ ⟨rfl, ha⟩; exact hpoint a ha)
  obtain ⟨C, hCc, hxC, hCV⟩ := exists_compact_subset (x := x₀) hVo (hxV (by simp))
  have hCU : C ×ˢ μ.support ⊆ U := fun p hp => hVW ⟨hCV hp.1, hsubW hp.2⟩
  have hCnhds : C ∈ 𝓝 x₀ := mem_interior_iff_mem_nhds.mp hxC
  have hxC' : x₀ ∈ C := interior_subset hxC
  obtain ⟨M, hM⟩ := (hCc.prod hμ).bddAbove_image (hD.norm.mono hCU)
  have hrestrict : μ.restrict μ.support = μ := Measure.restrict_eq_self_of_ae_mem μ.support_mem_ae
  have hFsection (x : X) (hx : x ∈ C) : ContinuousOn (F x) μ.support := by
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha => hCU ⟨hx, ha⟩)
  have hDsection : ContinuousOn (D x₀) μ.support := by
    exact hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha => hpoint a ha)
  have hFi : Integrable (F x₀) μ := by
    have hi := (hFsection x₀ hxC').integrableOn_compact (μ := μ) hμ
    rwa [IntegrableOn, hrestrict] at hi
  have hDm : AEStronglyMeasurable (D x₀) μ := by
    have hm := hDsection.aestronglyMeasurable_of_isCompact (μ := μ) hμ hμ.measurableSet
    rwa [hrestrict] at hm
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := C) (bound := fun _ => M) hCnhds
  · filter_upwards [hCnhds] with x hx
    have hm := (hFsection x hx).aestronglyMeasurable_of_isCompact (μ := μ) hμ hμ.measurableSet
    rwa [hrestrict] at hm
  · exact hFi
  · exact hDm
  · filter_upwards [μ.support_mem_ae] with a ha
    intro x hx
    exact hM ⟨(x, a), ⟨hx, ha⟩, rfl⟩
  · exact integrable_const M
  · filter_upwards [μ.support_mem_ae] with a ha
    intro x hx
    exact hderiv (x, a) (hCU ⟨hx, ha⟩)

end MeasureTheory
