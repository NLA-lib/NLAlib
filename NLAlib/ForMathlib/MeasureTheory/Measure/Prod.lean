/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Product laws and outer measure under projection

For probability measures, a set has real-valued outer measure at most that of its pullback
along the first projection from the product. No measurability of the set is required.
Upstream candidate for `Mathlib/MeasureTheory/Measure/Prod.lean`.

## Main results

* `MeasureTheory.measureReal_le_prod_fst`: pullback along the first product projection.
* `MeasureTheory.Measure.map_prod_eq_prod_of_ae_map_eq`: constant section laws give a product
  joint law.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A measurable family with almost everywhere constant section laws has product joint law:
if pushing $\sigma$ forward by $F(t,\cdot)$ gives $\nu$ for $\rho$-almost every $t$, then
$(t,y)\mapsto(t,F(t,y))$ sends $\rho\otimes\sigma$ to $\rho\otimes\nu$.
Only the second-factor measures need be s-finite. Upstream candidate. -/
theorem Measure.map_prod_eq_prod_of_ae_map_eq {α γ δ : Type*} [MeasurableSpace α]
    [MeasurableSpace γ] [MeasurableSpace δ] (ρ : Measure α) (σ : Measure γ)
    [SFinite σ] {ν : Measure δ} [SFinite ν]
    {F : α → γ → δ} (hF : Measurable (Function.uncurry F))
    (h : ∀ᵐ t ∂ρ, σ.map (F t) = ν) :
    (ρ.prod σ).map (fun p => (p.1, F p.1 p.2)) = ρ.prod ν := by
  have hpair : Measurable (fun p : α × γ => (p.1, F p.1 p.2)) :=
    measurable_fst.prodMk hF
  ext s hs
  rw [Measure.map_apply hpair hs, Measure.prod_apply (hpair hs), Measure.prod_apply hs]
  refine lintegral_congr_ae (h.mono fun t ht => ?_)
  have hFt : Measurable (F t) := hF.comp measurable_prodMk_left
  have heq := congrArg (fun τ : Measure δ => τ (Prod.mk t ⁻¹' s)) ht
  rw [Measure.map_apply hFt (measurable_prodMk_left hs)] at heq
  exact heq

/-- Measure of a set pulled back along the first factor of a product with a probability law:
$\mu(S) \le (\mu\otimes\nu)(\mathrm{fst}^{-1}S)$. Upstream candidate. -/
theorem measureReal_le_prod_fst {Ω₂ : Type*} [MeasurableSpace Ω₂] (ν : Measure Ω₂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (S : Set Ω) :
    μ.real S ≤ (μ.prod ν).real (Prod.fst ⁻¹' S) := by
  set H := toMeasurable (μ.prod ν) (Prod.fst ⁻¹' S) with hH
  have hHm : MeasurableSet H := measurableSet_toMeasurable _ _
  have hsub : Prod.fst ⁻¹' S ⊆ H := subset_toMeasurable _ _
  have hfH : (μ.prod ν) H = (μ.prod ν) (Prod.fst ⁻¹' S) := measure_toMeasurable _
  have hsec : ∀ x ∈ S, (1 : ENNReal) ≤ ν (Prod.mk x ⁻¹' H) := by
    intro x hx
    have huniv : Prod.mk x ⁻¹' H = Set.univ := by
      ext y
      exact ⟨fun _ => trivial, fun _ => hsub (show (x, y) ∈ Prod.fst ⁻¹' S from hx)⟩
    rw [huniv, measure_univ]
  have hAm : MeasurableSet {x | (1 : ENNReal) ≤ ν (Prod.mk x ⁻¹' H)} :=
    measurableSet_le measurable_const (measurable_measure_prodMk_left hHm)
  have hmarkov := mul_meas_ge_le_lintegral₀
    (μ := μ) (f := fun x => ν (Prod.mk x ⁻¹' H))
    (measurable_measure_prodMk_left hHm).aemeasurable 1
  have hle : μ S ≤ (μ.prod ν) (Prod.fst ⁻¹' S) := by
    rw [← hfH, Measure.prod_apply hHm]
    calc μ S ≤ μ {x | (1 : ENNReal) ≤ ν (Prod.mk x ⁻¹' H)} :=
          measure_mono fun x hx => hsec x hx
      _ = 1 * μ {x | (1 : ENNReal) ≤ ν (Prod.mk x ⁻¹' H)} := (one_mul _).symm
      _ ≤ _ := hmarkov
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle


end MeasureTheory
