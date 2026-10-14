/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Probability.Moments.Variance

/-!
# Tail probabilities and moments

Tail bounds in NLAlib are failure probabilities in `ℝ`, with non-strict events:
`μ.real {ω | t ≤ f ω} ≤ bound` (`docs/PORT_PROBABILITY.md` D3). Mathlib's Chernoff bound
`ProbabilityTheory.measure_ge_le_exp_mul_mgf` and Markov's inequality
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg` already have this form; the union bound and the
complement are `MeasureTheory.measureReal_union_le`, `MeasureTheory.measureReal_biUnion_finset_le`
and `MeasureTheory.probReal_compl_eq_one_sub`. This file adds Markov's inequality in quotient
form, Chebyshev's inequality in `ℝ`, the two-sided tail, and the passage from a tail bound to
integrability and to a bound on the mean.

## Main results

* `NLAlib.measureReal_ge_le_integral_div`: Markov's inequality.
* `NLAlib.measureReal_abs_ge_le_integral_rpow_div`: Markov's inequality for a moment.
* `NLAlib.measureReal_ge_le_variance_div_sq`: Chebyshev's inequality.
* `NLAlib.measureReal_abs_ge_le_add`: a two-sided tail is at most the sum of the one-sided tails.
* `NLAlib.integrable_of_measureReal_ge_le`, `NLAlib.integral_le_of_measureReal_ge_le`: a
  nonnegative random variable with an integrable tail bound is integrable, and its mean is at most
  the integral of the bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Markov's inequality** as a failure probability: `P(t ≤ f) ≤ E f / t` for nonnegative
integrable `f` and `t > 0`. Integrability is needed: otherwise `∫ f = 0`.
Result: markov-inequality -/
theorem measureReal_ge_le_integral_div {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hf : Integrable f μ)
    {t : ℝ} (ht : 0 < t) : μ.real {ω | t ≤ f ω} ≤ (∫ ω, f ω ∂μ) / t := by
  rw [le_div_iff₀ ht, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg hf0 hf t

/-- **Markov's inequality for a moment**: `P(t ≤ |X|) ≤ E |X| ^ p / t ^ p` for `t, p > 0`. Every
tail derived from a moment bound ends here. Integrability of `|X| ^ p` is needed: otherwise its
integral is `0`. -/
theorem measureReal_abs_ge_le_integral_rpow_div {X : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hX : Integrable (fun ω => |X ω| ^ p) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ (∫ ω, |X ω| ^ p ∂μ) / t ^ p := by
  have hset : {ω | t ≤ |X ω|} = {ω | t ^ p ≤ |X ω| ^ p} := by
    ext ω
    exact (Real.rpow_le_rpow_iff ht.le (abs_nonneg _) hp).symm
  rw [hset]
  exact measureReal_ge_le_integral_div
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p) hX
    (Real.rpow_pos_of_pos ht p)

/-- **Chebyshev's inequality** as a failure probability: `P(t ≤ |X - E X|) ≤ Var X / t²`.
Result: chebyshev-inequality -/
theorem measureReal_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤ variance X μ / t ^ 2 := by
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg t))
    (meas_ge_le_variance_div_sq hX ht)

/-- A two-sided tail is at most the sum of the upper and the lower tail. -/
theorem measureReal_abs_ge_le_add (X : Ω → ℝ) (t : ℝ) :
    μ.real {ω | t ≤ |X ω|} ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | X ω ≤ -t} := by
  have h : {ω | t ≤ |X ω|} = {ω | t ≤ X ω} ∪ {ω | X ω ≤ -t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs, le_neg]
  rw [h]
  exact measureReal_union_le _ _

private theorem lintegral_ofReal_le_of_measureReal_ge_le [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤
      μ Set.univ * ENNReal.ofReal a + ENNReal.ofReal (∫ t in Set.Ioi a, F t) := by
  have hF0 : 0 ≤ᵐ[volume.restrict (Set.Ioi a)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact measureReal_nonneg.trans (htail t ht)
  rw [lintegral_eq_lintegral_meas_lt μ hf0 hf, ← Set.Ioc_union_Ioi_eq_Ioi ha,
    lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same,
    ofReal_integral_eq_lintegral_ofReal hF hF0]
  gcongr ?_ + ?_
  · calc ∫⁻ t in Set.Ioc 0 a, μ {x | t < f x} ≤ ∫⁻ _ in Set.Ioc 0 a, μ Set.univ :=
          lintegral_mono fun _ => measure_mono (Set.subset_univ _)
      _ = μ Set.univ * ENNReal.ofReal a := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  · refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    calc μ {x | t < f x} ≤ μ {x | t ≤ f x} := measure_mono fun _ hx => le_of_lt (α := ℝ) hx
      _ = ENNReal.ofReal (μ.real {x | t ≤ f x}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (F t) := ENNReal.ofReal_le_ofReal (htail t ht)

private theorem integral_le_of_measureReal_ge_le_of_nonneg [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} (ha : 0 ≤ a) {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫ ω, f ω ∂μ ≤ a + ∫ t in Set.Ioi a, F t := by
  have hF0 : 0 ≤ ∫ t in Set.Ioi a, F t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => measureReal_nonneg.trans (htail t ht)
  have hbound := lintegral_ofReal_le_of_measureReal_ge_le hf hf0 ha hF htail
  rw [measure_univ, one_mul, ← ENNReal.ofReal_add ha hF0] at hbound
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (add_nonneg ha hF0) hbound

/-- A nonnegative random variable whose tail beyond `a` is bounded by a function integrable on
`(a, ∞)` is integrable. A bound on the strict tail `{t < f}` follows from one on `{t ≤ f}` by
monotonicity, so the hypothesis is stated in the non-strict form that tail theorems produce. -/
theorem integrable_of_measureReal_ge_le [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEMeasurable f μ)
    (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} {F : ℝ → ℝ} (hF : IntegrableOn F (Set.Ioi a))
    (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) : Integrable f μ := by
  have hF' : IntegrableOn F (Set.Ioi (max a 0)) :=
    hF.mono_set (Set.Ioi_subset_Ioi (le_max_left a 0))
  have hbound := lintegral_ofReal_le_of_measureReal_ge_le hf hf0 (le_max_right a 0) hF'
    fun t ht => htail t ((le_max_left a 0).trans_lt ht)
  refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hf0).2 ?_⟩
  exact hbound.trans_lt (ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top (measure_lt_top μ _) ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

/-- **The layer-cake bound**: the mean of a nonnegative random variable is at most `a` plus the
integral over `(a, ∞)` of a bound on its tail. Applied to `f ^ p`, whose tail at `t` is the tail of
`f` at `t ^ (1 / p)`, it bounds the moments of `f`. Integrability of `f` is
`integrable_of_measureReal_ge_le`. -/
theorem integral_le_of_measureReal_ge_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫ ω, f ω ∂μ ≤ a + ∫ t in Set.Ioi a, F t := by
  rcases le_or_gt 0 a with ha | ha
  · exact integral_le_of_measureReal_ge_le_of_nonneg hf hf0 ha hF htail
  have hF0 : IntegrableOn F (Set.Ioi 0) := hF.mono_set (Set.Ioi_subset_Ioi ha.le)
  have h0 := integral_le_of_measureReal_ge_le_of_nonneg hf hf0 le_rfl hF0
    fun t ht => htail t (ha.trans ht)
  have h1 : -a ≤ ∫ t in Set.Ioc a 0, F t := by
    have hle : ∫ _ in Set.Ioc a 0, (1 : ℝ) ≤ ∫ t in Set.Ioc a 0, F t := by
      refine setIntegral_mono_on (integrableOn_const (by simp))
        (hF.mono_set Set.Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
      refine le_trans (le_of_eq ?_) (htail t ht.1)
      rw [measureReal_def, measure_congr (ae_eq_univ.2 ?_), measure_univ, ENNReal.toReal_one]
      exact ae_iff.1 (hf0.mono fun ω hω => ht.2.trans hω)
    simpa [ha.le] using hle
  rw [← Set.Ioc_union_Ioi_eq_Ioi ha.le, setIntegral_union Set.Ioc_disjoint_Ioi_same
    measurableSet_Ioi (hF.mono_set Set.Ioc_subset_Ioi_self) hF0]
  linarith

end NLAlib
