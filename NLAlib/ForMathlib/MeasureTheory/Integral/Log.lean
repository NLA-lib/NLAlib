/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Regularization of extended logarithmic integrals

An upper bound for a nonnegative function controls the positive part of its logarithm.
Monotone convergence for its logarithmic deficit then lets a bound on all positive
regularizations pass to the extended integral, including when the negative part has infinite
integral. Upstream candidate for Mathlib's logarithmic integration theory.

The proof adapts the original formalization in `tchen-research/NLAlib@77514ce`.

## Main results

* `MeasureTheory.extendedLogIntegral` integrates the logarithm with $\log 0=-\infty$.
* `MeasureTheory.log_le_extendedLogIntegral_of_le_exp_integral_log_add` passes a lower
  bound to the extended integral.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

/-- The integral of the extended logarithm of $g$, expressed as the integral of its positive
part minus that of its negative part. Nonpositive inputs have logarithm $-\infty$. The formula
agrees with the mathematical extended integral whenever at least one of the parts is finite. -/
noncomputable def extendedLogIntegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) : EReal :=
  ((∫⁻ x, (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) : EReal) -
    ((∫⁻ x, (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) : EReal)

/-- If $g>0$ almost everywhere and $\log g$ is integrable, its extended logarithmic
integral equals the ordinary real integral. -/
theorem extendedLogIntegral_eq_integral_log {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (hlog : Integrable (fun x => Real.log (g x)) μ) :
    extendedLogIntegral μ g = ((∫ x, Real.log (g x) ∂μ : ℝ) : EReal) := by
  have hparts : (fun x => ENNReal.log (ENNReal.ofReal (g x))) =ᵐ[μ]
      fun x => (Real.log (g x) : EReal) :=
    hpos.mono fun _ hx => ENNReal.log_ofReal_of_pos hx
  have hp : (∫⁻ x, (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) =
      ∫⁻ x, ENNReal.ofReal (Real.log (g x)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hparts] with x hx
    rw [hx, EReal.real_coe_toENNReal]
  have hn : (∫⁻ x, (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) =
      ∫⁻ x, ENNReal.ofReal (-Real.log (g x)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hparts] with x hx
    rw [hx, ← EReal.coe_neg, EReal.real_coe_toENNReal]
  have hfin {f : α → ℝ} (hf : Integrable f μ) : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ :=
    ne_of_lt ((lintegral_mono fun x => Real.ofReal_le_enorm (f x)).trans_lt hf.hasFiniteIntegral)
  have hm : Integrable (fun x => -Real.log (g x)) μ := hlog.neg
  rw [extendedLogIntegral, hp, hn, ← EReal.coe_ennreal_toReal (hfin hlog),
    ← EReal.coe_ennreal_toReal (hfin hm), ← EReal.coe_sub,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hlog]

/-- Increasing $g$ almost everywhere increases its extended logarithmic integral. -/
theorem extendedLogIntegral_mono_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g h : α → ℝ} (hgh : g ≤ᵐ[μ] h) :
    extendedLogIntegral μ g ≤ extendedLogIntegral μ h := by
  apply EReal.sub_le_sub <;> apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr <;>
    apply lintegral_mono_ae <;> filter_upwards [hgh] with x hx
  · exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hx))
  · exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr
      (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hx)))

/-- A measurable function nonpositive on a set of positive measure has extended logarithmic
integral $-\infty$. Its negative logarithmic part has infinite integral. -/
theorem extendedLogIntegral_eq_bot_of_measure_nonpos_ne_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : Measurable g) (hz : μ {x | g x ≤ 0} ≠ 0) :
    extendedLogIntegral μ g = ⊥ := by
  have hneg : (∫⁻ x, (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) = ∞ := by
    apply lintegral_eq_top_of_measure_eq_top_ne_zero
    · exact (EReal.continuous_toENNReal.measurable.comp
        (ENNReal.continuous_log.measurable.comp hg.ennreal_ofReal).neg).aemeasurable
    · apply ne_of_gt
      apply (bot_lt_iff_ne_bot.mpr hz).trans_le
      apply measure_mono
      intro x hx
      change (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal = ∞
      rw [ENNReal.ofReal_of_nonpos hx]
      simp
  rw [extendedLogIntegral, hneg, EReal.coe_ennreal_top, EReal.sub_top]

private noncomputable def logDeficit (c x : ℝ) : ℝ≥0∞ :=
  ((c : EReal) - ENNReal.log (ENNReal.ofReal x)).toENNReal

private noncomputable abbrev upperLogIntegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) (c : ℝ) : EReal :=
  (c : EReal) - ((∫⁻ x, logDeficit c (g x) ∂μ) : EReal)

private theorem logDeficit_of_pos (c : ℝ) {x : ℝ} (hx : 0 < x) :
    logDeficit c x = ENNReal.ofReal (c - Real.log x) := by
  rw [logDeficit, ENNReal.log_ofReal_of_pos hx, ← EReal.coe_sub,
    EReal.real_coe_toENNReal]

private theorem logDeficit_antitone (c : ℝ) : Antitone (logDeficit c) := by
  intro x y hxy
  exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl
    (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hxy)))

private theorem continuous_logDeficit (c : ℝ) : Continuous (logDeficit c) := by
  have hc : Continuous (fun y : EReal => (c : EReal) - y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top c))
      (Or.inl (EReal.coe_ne_bot c))).comp
        (continuous_const.prodMk continuous_neg).continuousAt
  exact EReal.continuous_toENNReal.comp
    (hc.comp (ENNReal.continuous_log.comp ENNReal.continuous_ofReal))

private theorem upperLogIntegral_eq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} {c : ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 < g x)
    (hlog : Integrable (fun x => Real.log (g x)) μ)
    (hle : ∀ᵐ x ∂μ, Real.log (g x) ≤ c) :
    upperLogIntegral μ g c = ((∫ x, Real.log (g x) ∂μ : ℝ) : EReal) := by
  have hnonneg : 0 ≤ᵐ[μ] fun x => c - Real.log (g x) := by
    filter_upwards [hle] with x hx using sub_nonneg.mpr hx
  have hi := (integrable_const c).sub hlog
  have heq : (∫⁻ x, logDeficit c (g x) ∂μ) =
      ENNReal.ofReal (c - ∫ x, Real.log (g x) ∂μ) := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal (c - Real.log (g x)) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hpos] with x hx using logDeficit_of_pos c hx
      _ = ENNReal.ofReal (c - ∫ x, Real.log (g x) ∂μ) := by
        simpa only [Pi.sub_apply, integral_sub (integrable_const c) hlog, integral_const,
          probReal_univ, one_smul] using
          (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
  have hnonnegint : 0 ≤ c - ∫ x, Real.log (g x) ∂μ := by
    simpa only [Pi.sub_apply, integral_sub (integrable_const c) hlog, integral_const,
      probReal_univ, one_smul] using integral_nonneg_of_ae hnonneg
  rw [upperLogIntegral, heq, EReal.coe_ennreal_ofReal,
    max_eq_left hnonnegint, ← EReal.coe_sub]
  congr 1
  ring

private theorem deficit_add_posPart (c : ℝ) (hc : 0 ≤ c) (t : EReal) (ht : t ≤ c) :
    ((c : EReal) - t).toENNReal + t.toENNReal =
      ENNReal.ofReal c + (-t).toENNReal := by
  induction t with
  | bot => simp
  | top => exact False.elim (not_le_of_gt (EReal.coe_lt_top c) ht)
  | coe t =>
    have htc : t ≤ c := EReal.coe_le_coe_iff.mp ht
    simp only [← EReal.coe_sub, ← EReal.coe_neg, EReal.real_coe_toENNReal]
    rcases le_total 0 t with ht0 | ht0
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr ht0), add_zero,
        ← ENNReal.ofReal_add (sub_nonneg.mpr htc) ht0]
      congr 1
      ring
    · rw [ENNReal.ofReal_of_nonpos ht0, add_zero,
        ← ENNReal.ofReal_add hc (neg_nonneg.mpr ht0)]
      simp only [sub_eq_add_neg]

private theorem lintegral_log_posPart_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ} {c : ℝ}
    (hle : ∀ᵐ x ∂μ, ENNReal.log (ENNReal.ofReal (g x)) ≤ c) :
    (∫⁻ x, (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) < ∞ := by
  calc
    _ ≤ ∫⁻ _ : α, ENNReal.ofReal c ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hle] with x hx
      simpa only [EReal.real_coe_toENNReal] using EReal.toENNReal_le_toENNReal hx
    _ < ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)

/-- Under an essential upper bound $\log g\le c$ on a probability space, the logarithmic
deficit gives $\int\log g=c-\int(c-\log g)$. This includes infinite negative parts. -/
theorem extendedLogIntegral_eq_sub_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {c : ℝ} (hc : 0 ≤ c) (hle : ∀ᵐ x ∂μ, ENNReal.log (ENNReal.ofReal (g x)) ≤ c) :
    extendedLogIntegral μ g = (c : EReal) -
      ((∫⁻ x, ((c : EReal) - ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ) : EReal) := by
  symm
  let p := ∫⁻ x, (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ
  let q := ∫⁻ x, (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ
  let d := ∫⁻ x, logDeficit c (g x) ∂μ
  have hp : p ≠ ∞ := ne_of_lt (lintegral_log_posPart_lt_top hle)
  have hbalance : d + p = ENNReal.ofReal c + q := by
    calc
      _ = ∫⁻ x, logDeficit c (g x) +
          (ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ :=
        (lintegral_add_left ((continuous_logDeficit c).measurable.comp hg) _).symm
      _ = ∫⁻ x, ENNReal.ofReal c +
          (-ENNReal.log (ENNReal.ofReal (g x))).toENNReal ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hle] with x hx using deficit_add_posPart c hc _ hx
      _ = ENNReal.ofReal c + q := by
        rw [lintegral_add_left measurable_const]
        simp [q]
  change (c : EReal) - (d : EReal) = (p : EReal) - (q : EReal)
  by_cases hq : q = ∞
  · have hd : d = ∞ := by
      by_contra hd
      have hsum : d + p = ∞ := by simpa only [hq, add_top] using hbalance
      exact (ENNReal.add_ne_top.mpr ⟨hd, hp⟩) hsum
    simp [hq, hd]
  · have hd : d ≠ ∞ := by
      intro hd
      simp [hd] at hbalance
      exact (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hq⟩) hbalance.symm
    have hreal := congrArg ENNReal.toReal hbalance
    rw [ENNReal.toReal_add hd hp, ENNReal.toReal_add ENNReal.ofReal_ne_top hq,
      ENNReal.toReal_ofReal hc] at hreal
    rw [← EReal.coe_ennreal_toReal hd, ← EReal.coe_ennreal_toReal hp,
      ← EReal.coe_ennreal_toReal hq, ← EReal.coe_sub, ← EReal.coe_sub]
    congr 1
    linarith

private theorem integrable_log_add_of_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C δ : ℝ} (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C) (hδ : 0 < δ) :
    Integrable (fun x => Real.log (g x + δ)) μ := by
  apply (integrable_const (|Real.log δ| + |Real.log (C + δ)|)).mono'
    (hg.add_const δ).log.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_le]
  have hl : Real.log δ ≤ Real.log (g x + δ) :=
    Real.log_le_log hδ (le_add_of_nonneg_left (hbound x).1)
  have hu : Real.log (g x + δ) ≤ Real.log (C + δ) :=
    Real.log_le_log (by linarith [(hbound x).1]) (by linarith [(hbound x).2])
  constructor <;> linarith [le_abs_self (Real.log δ), neg_abs_le (Real.log δ),
    le_abs_self (Real.log (C + δ)), abs_nonneg (Real.log (C + δ)), abs_nonneg (Real.log δ)]

private theorem tendsto_lintegral_logDeficit_add_inv_nat {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hg : Measurable g) (c : ℝ) :
    Tendsto (fun n : ℕ => ∫⁻ x, logDeficit c (g x + 1 / ((n : ℝ) + 1)) ∂μ)
      atTop (𝓝 (∫⁻ x, logDeficit c (g x) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact ((continuous_logDeficit c).measurable.comp (hg.add_const _)).aemeasurable
  · filter_upwards [] with x i j hij
    apply logDeficit_antitone c
    apply add_le_add_right
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  · filter_upwards [] with x
    apply (continuous_logDeficit c).continuousAt.tendsto.comp
    simpa using (tendsto_const_nhds (x := g x)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem tendsto_exp_integral_log_add_inv_nat {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C : ℝ} (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (∫ x, Real.log (g x + 1 / ((n : ℝ) + 1)) ∂μ)))
      atTop (𝓝 (EReal.exp (upperLogIntegral μ g (Real.log (C + 1))))) := by
  have hdef := tendsto_lintegral_logDeficit_add_inv_nat (μ := μ) hg (Real.log (C + 1))
  have hcoe := continuous_coe_ennreal_ereal.continuousAt.tendsto.comp hdef
  have hsub : Tendsto (fun n : ℕ => (Real.log (C + 1) : EReal) -
      ((∫⁻ x, logDeficit (Real.log (C + 1)) (g x + 1 / ((n : ℝ) + 1)) ∂μ) : EReal))
      atTop (𝓝 (upperLogIntegral μ g (Real.log (C + 1)))) := by
    change Tendsto _ atTop (𝓝 ((Real.log (C + 1) : EReal) +
      -((∫⁻ x, logDeficit (Real.log (C + 1)) (g x) ∂μ) : EReal)))
    exact (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _))
      (Or.inl (EReal.coe_ne_bot _))).tendsto.comp
        (tendsto_const_nhds.prodMk_nhds hcoe.neg)
  have hexp := ENNReal.continuous_exp.continuousAt.tendsto.comp hsub
  apply hexp.congr'
  filter_upwards [] with n
  have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hδ1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have heq := upperLogIntegral_eq_integral (μ := μ)
    (g := fun x => g x + 1 / ((n : ℝ) + 1))
    (c := Real.log (C + 1))
    (ae_of_all _ (fun x => by linarith [(hbound x).1]))
    (integrable_log_add_of_bounded hg hbound hδ)
    (ae_of_all _ (fun x => Real.log_le_log (by linarith [(hbound x).1])
      (by linarith [(hbound x).2])))
  change EReal.exp (upperLogIntegral μ (fun x => g x + 1 / ((n : ℝ) + 1))
    (Real.log (C + 1))) = _
  rw [heq, EReal.exp_coe]

/-- On a probability space, let $g$ be measurable, nonnegative and bounded above. If $L$ is a
lower bound for the geometric mean of $g+\delta$ for every $\delta>0$, then the extended
logarithm of $L$ is at most the extended logarithmic integral of $g$. -/
theorem log_le_extendedLogIntegral_of_le_exp_integral_log_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g)
    {C L : ℝ} (hbound : ∀ x, 0 ≤ g x ∧ g x ≤ C)
    (hL : ∀ δ : ℝ, 0 < δ → L ≤ Real.exp (∫ x, Real.log (g x + δ) ∂μ)) :
    ENNReal.log (ENNReal.ofReal L) ≤ extendedLogIntegral μ g := by
  let C' := max C 0
  have hc : 0 ≤ C' := le_max_right _ _
  have hb (x) : 0 ≤ g x ∧ g x ≤ C' := ⟨(hbound x).1, (hbound x).2.trans (le_max_left _ _)⟩
  have ht := tendsto_exp_integral_log_add_inv_nat (μ := μ) hg hb
  have he : ENNReal.ofReal L ≤ EReal.exp (upperLogIntegral μ g (Real.log (C' + 1))) :=
    ge_of_tendsto' ht fun _ => ENNReal.ofReal_le_ofReal (hL _ (by positivity))
  have hh : upperLogIntegral μ g (Real.log (C' + 1)) = extendedLogIntegral μ g := by
    symm
    apply extendedLogIntegral_eq_sub_lintegral hg (Real.log_nonneg (by linarith))
    filter_upwards [] with x
    by_cases hx : 0 < g x
    · rw [ENNReal.log_ofReal_of_pos hx, EReal.coe_le_coe_iff]
      exact Real.log_le_log hx (by linarith [(hb x).2])
    · simp [ENNReal.ofReal_of_nonpos (le_of_not_gt hx)]
  rw [hh] at he
  simpa using ENNReal.log_monotone he

end MeasureTheory
