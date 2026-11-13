/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# The Paley–Zygmund inequality

A nonnegative random variable with a finite second moment exceeds a fraction $\theta$ of its mean
with probability at least $(1 - \theta)^2 (\mathbb{E} Z)^2 / \mathbb{E} Z^2$. It is the
anti-concentration step of the early-truncation lower bound.
Not in Mathlib (searched: `paley`,
`zygmund`, `second moment method`); an upstream candidate for
`Mathlib/Probability/Moments/Variance.lean` or a new `Mathlib/Probability/PaleyZygmund.lean`.

The argument originates in the work of Paley and Zygmund [PaleyZygmund1932].

## Main results

* `ProbabilityTheory.sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt`: the inequality.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The Paley–Zygmund inequality for a measurable $Z$ (helper). -/
private lemma sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt_of_measurable
    [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZm : Measurable Z) (hZ0 : 0 ≤ᵐ[μ] Z)
    (hZ : MemLp Z 2 μ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤
      (∫ ω, Z ω ^ 2 ∂μ) * μ.real {ω | θ * ∫ ω', Z ω' ∂μ < Z ω} := by
  have hm0 : 0 ≤ ∫ ω, Z ω ∂μ := integral_nonneg_of_ae hZ0
  have hZi : Integrable Z μ := hZ.integrable one_le_two
  set m := ∫ ω, Z ω ∂μ with hm
  set E : Set Ω := {ω | θ * m < Z ω} with hEdef
  have hE : MeasurableSet E := measurableSet_lt measurable_const hZm
  have hθm : 0 ≤ θ * m := mul_nonneg hθ0 hm0
  have hpt : ∀ ω, Z ω ≤ θ * m + E.indicator Z ω := by
    intro ω
    by_cases h : ω ∈ E
    · rw [Set.indicator_of_mem h]
      linarith
    · rw [Set.indicator_of_notMem h]
      have h' : Z ω ≤ θ * m := not_lt.mp h
      linarith
  have hJ : (1 - θ) * m ≤ ∫ ω, E.indicator Z ω ∂μ := by
    have h1 : ∫ ω, Z ω ∂μ ≤ ∫ ω, (θ * m + E.indicator Z ω) ∂μ :=
      integral_mono hZi ((integrable_const (θ * m)).add (hZi.indicator hE)) hpt
    rw [integral_add (integrable_const _) (hZi.indicator hE), integral_const] at h1
    simp only [probReal_univ, smul_eq_mul, one_mul] at h1
    linarith
  have hf0 : 0 ≤ᵐ[μ] E.indicator Z := by
    filter_upwards [hZ0] with ω hω
    exact Set.indicator_nonneg (fun _ _ => hω) ω
  have hfM : MemLp (E.indicator Z) 2 μ := hZ.indicator hE
  have hg0 : 0 ≤ᵐ[μ] E.indicator (fun _ => (1 : ℝ)) :=
    ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hgM : MemLp (E.indicator (fun _ => (1 : ℝ))) 2 μ := (memLp_const (1 : ℝ)).indicator hE
  have hfg : (fun ω => E.indicator Z ω * E.indicator (fun _ => (1 : ℝ)) ω) = E.indicator Z := by
    funext ω
    by_cases h : ω ∈ E <;> simp [h]
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    hf0 hg0 (by rwa [ENNReal.ofReal_ofNat]) (by rwa [ENNReal.ofReal_ofNat])
  simp only [Real.rpow_two] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hfg] at hH
  have hA : ∫ ω, E.indicator Z ω ^ 2 ∂μ ≤ ∫ ω, Z ω ^ 2 ∂μ := by
    refine integral_mono_of_nonneg ?_ (hZ.integrable_sq) ?_
    · exact ae_of_all _ fun ω => sq_nonneg _
    · refine ae_of_all _ fun ω => ?_
      dsimp only
      by_cases h : ω ∈ E
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, zero_pow two_ne_zero]; exact sq_nonneg _
  have hB : ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ^ 2 ∂μ = μ.real E := by
    have : (fun ω => E.indicator (fun _ => (1 : ℝ)) ω ^ 2) = E.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : ω ∈ E <;> simp [h]
    rw [this]
    exact integral_indicator_one hE
  have hJ0 : 0 ≤ ∫ ω, E.indicator Z ω ∂μ := integral_nonneg_of_ae hf0
  have hA0 : 0 ≤ ∫ ω, E.indicator Z ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hB0 : 0 ≤ ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  have hsq := pow_le_pow_left₀ hJ0 hH 2
  rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0, hB] at hsq
  have hm1 : 0 ≤ (1 - θ) * m := mul_nonneg (by linarith) hm0
  calc (1 - θ) ^ 2 * m ^ 2 = ((1 - θ) * m) ^ 2 := by ring
    _ ≤ (∫ ω, E.indicator Z ω ∂μ) ^ 2 := pow_le_pow_left₀ hm1 hJ 2
    _ ≤ (∫ ω, Z ω ^ 2 ∂μ) * μ.real E :=
        hsq.trans (mul_le_mul_of_nonneg_right hA (measureReal_nonneg))

/-- **The Paley–Zygmund inequality.** Under a probability measure, for a random variable
$Z \ge 0$ almost surely with $\mathbb{E} Z^2 < \infty$ and $0 \le \theta \le 1$,
$$(1 - \theta)^2 (\mathbb{E} Z)^2 \le \mathbb{E} Z^2 \cdot
\mathbb{P}\bigl[Z > \theta\,\mathbb{E} Z\bigr]\,.$$
Both hypotheses on $\theta$ are needed: for $\theta < 0$ and a constant $Z > 0$ the left side
exceeds $\mathbb{E}Z^2$, and for $\theta > 1$ the event is empty for a constant $Z$.
[Yadin2014, Theorem 19.20] states the strict-event inequality in ratio form.
The product form here includes $\mathbb{E} Z^2=0$.
Result: paley-zygmund-inequality -/
theorem sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ0 : 0 ≤ᵐ[μ] Z) (hZ : MemLp Z 2 μ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤
      (∫ ω, Z ω ^ 2 ∂μ) * μ.real {ω | θ * ∫ ω', Z ω' ∂μ < Z ω} := by
  set Z' := hZ.aestronglyMeasurable.mk Z with hZ'def
  have hZeq : Z =ᵐ[μ] Z' := hZ.aestronglyMeasurable.ae_eq_mk
  have hZm : Measurable Z' := hZ.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hZ'0 : 0 ≤ᵐ[μ] Z' := by
    filter_upwards [hZ0, hZeq] with ω h1 h2
    rw [← h2]; exact h1
  have hZ' : MemLp Z' 2 μ := hZ.ae_eq hZeq
  have key := sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt_of_measurable hZm hZ'0 hZ'
    hθ0 hθ1
  have hI : ∫ ω, Z ω ∂μ = ∫ ω, Z' ω ∂μ := integral_congr_ae hZeq
  have hI2 : ∫ ω, Z ω ^ 2 ∂μ = ∫ ω, Z' ω ^ 2 ∂μ :=
    integral_congr_ae (by filter_upwards [hZeq] with ω h; simp only [h])
  have hset : {ω | θ * ∫ ω', Z' ω' ∂μ < Z ω} =ᵐ[μ] {ω | θ * ∫ ω', Z' ω' ∂μ < Z' ω} := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [hZeq] with ω h
    rw [h]
  rw [hI, hI2, measureReal_congr hset]
  exact key

end ProbabilityTheory
