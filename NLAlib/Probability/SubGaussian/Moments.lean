/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.Gamma
public import NLAlib.Probability.SubGaussian.Basic
public import NLAlib.Probability.Tail

/-!
# Moments and maxima of sub-Gaussian random variables

The absolute moments of a sub-Gaussian variable, obtained by integrating its two-sided tail, and
the maximal inequality for finitely many sub-Gaussian variables, which needs no independence.
Integrability of `|X| ^ p` is Mathlib's `ProbabilityTheory.HasSubgaussianMGF.memLp`.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.integral_abs_rpow_le`: `E |X| ^ p ≤ p (2c)^{p/2} Γ(p/2)`.
* `ProbabilityTheory.HasSubgaussianMGF.integral_iSup_le`: `E max_i X_i ≤ √(2 c log N)`.
* `ProbabilityTheory.HasSubgaussianMGF.integral_iSup_abs_le`: `E max_i |X_i| ≤ √(2 c log 2N)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

private lemma integral_Ioi_two_mul_exp_mul_rpow {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => 2 * rexp (-t ^ 2 / (2 * c)) * t ^ (p - 1)) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), 2 * rexp (-t ^ 2 / (2 * c)) * t ^ (p - 1) =
        (2 * c) ^ (p / 2) * Gamma (p / 2) := by
  have hb : (0 : ℝ) < 1 / (2 * c) := by positivity
  have hfun : (fun t : ℝ => 2 * rexp (-t ^ 2 / (2 * c)) * t ^ (p - 1)) =
      fun t => 2 * (t ^ (p - 1) * rexp (-(1 / (2 * c)) * t ^ (2 : ℝ))) := by
    funext t
    rw [rpow_two]
    ring_nf
  rw [hfun]
  refine ⟨(integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) two_pos hb).const_mul 2, ?_⟩
  rw [integral_const_mul, integral_rpow_mul_exp_neg_mul_rpow two_pos (by linarith) hb]
  have h1 : (p - 1 + 1) / 2 = p / 2 := by ring
  have h2 : -(p - 1 + 1) / 2 = -(p / 2) := by ring
  rw [h1, h2, one_div (2 * c), inv_rpow (by positivity), rpow_neg (by positivity), inv_inv]
  ring

/-- The absolute moments of a sub-Gaussian variable: `E |X| ^ p ≤ p (2c)^{p/2} Γ(p/2)` for
`p > 0`. The right side is the integral of the two-sided tail bound `2 exp (-t² / (2c))` against
`p t^{p-1} dt`, so it improves only with the tail. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_abs_rpow_le
    (h : HasSubgaussianMGF X c μ) {p : ℝ} (hp : 0 < p) :
    ∫ ω, |X ω| ^ p ∂μ ≤ p * (2 * c) ^ (p / 2) * Real.Gamma (p / 2) := by
  have := h.isFiniteMeasure
  rcases eq_or_ne c 0 with rfl | hc0
  · have hint : ∫ ω, |X ω| ^ p ∂μ = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      filter_upwards [h.ae_eq_zero_of_hasSubgaussianMGF_zero] with ω hω
      simp [hω, zero_rpow hp.ne']
    rw [hint, NNReal.coe_zero, mul_zero, zero_rpow (by positivity), mul_zero, zero_mul]
  have hc : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0)
  obtain ⟨hI, hval⟩ := integral_Ioi_two_mul_exp_mul_rpow hc hp
  have hXm : AEMeasurable (fun ω => |X ω|) μ := h.aemeasurable.abs
  have hlin : ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ ≤
      ENNReal.ofReal (p * ((2 * c) ^ (p / 2) * Gamma (p / 2))) := by
    rw [lintegral_rpow_eq_lintegral_meas_le_mul μ (ae_of_all _ fun ω => abs_nonneg (X ω)) hXm hp,
      ENNReal.ofReal_mul hp.le, ← hval,
      ofReal_integral_eq_lintegral_ofReal hI (ae_restrict_of_forall_mem measurableSet_Ioi
        fun t (ht : 0 < t) => by positivity)]
    gcongr 1
    refine setLIntegral_mono' measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [ENNReal.ofReal_mul (by positivity), ← ofReal_measureReal]
    gcongr
    exact h.measure_abs_ge_le ht.le
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => by positivity)
    (hXm.pow_const p).aestronglyMeasurable]
  calc (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ).toReal
      ≤ p * ((2 * c) ^ (p / 2) * Gamma (p / 2)) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
    _ = _ := by ring

private lemma integral_le_log_div_of_integral_exp_le [IsProbabilityMeasure μ] {M : Ω → ℝ}
    (hM : Integrable M μ) {s B : ℝ} (hs : 0 < s)
    (hexp : Integrable (fun ω => rexp (s * M ω)) μ) (hB : ∫ ω, rexp (s * M ω) ∂μ ≤ B) :
    ∫ ω, M ω ∂μ ≤ log B / s := by
  have hJ : rexp (∫ ω, s * M ω ∂μ) ≤ ∫ ω, rexp (s * M ω) ∂μ :=
    convexOn_exp.map_integral_le continuousOn_exp isClosed_univ (ae_of_all _ fun _ => trivial)
      (hM.const_mul s) hexp
  rw [integral_const_mul] at hJ
  have hBpos : 0 < B := (exp_pos _).trans_le (hJ.trans hB)
  rw [le_div_iff₀ hs, mul_comm]
  exact (le_log_iff_exp_le hBpos).2 (hJ.trans hB)

private lemma abs_iSup_le_sum_abs {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    |⨆ i, f i| ≤ ∑ i, |f i| := by
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := f)
  rw [← hj]
  exact Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

/-- The pointwise supremum of finitely many integrable functions is integrable. -/
private lemma integrable_iSup_of_integrable {ι : Type*} [Finite ι]
    (Y : ι → Ω → ℝ) (hY : ∀ i, Integrable (Y i) μ) : Integrable (fun ω => ⨆ i, Y i ω) μ := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty]
    exact integrable_zero _ _ _
  exact (integrable_finsetSum Finset.univ fun i _ => (hY i).abs).mono'
    (AEMeasurable.iSup fun i => (hY i).aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, Finset.sum_apply] using abs_iSup_le_sum_abs (Y · ω))

/-- Shared skeleton of the maximal inequalities for `M ω = ⨆ᵢ Yᵢ ω`: if `e^{sM} ≤ ∑ₖ Fₖ` pointwise
with `∫ Fₖ ≤ b`, then `𝔼 M ≤ log(K b)/s`. -/
private lemma integral_iSup_le_aux [IsProbabilityMeasure μ] {ι κ : Type*} [Finite ι]
    [Fintype κ] (Y : ι → Ω → ℝ) (hY : ∀ i, Integrable (Y i) μ)
    (F : κ → Ω → ℝ) (hF : ∀ k, Integrable (F k) μ) {s b : ℝ} (hs : 0 < s)
    (hexp : ∀ ω, rexp (s * ⨆ i, Y i ω) ≤ ∑ k, F k ω) (hb : ∀ k, ∫ ω, F k ω ∂μ ≤ b) :
    ∫ ω, ⨆ i, Y i ω ∂μ ≤ log (Fintype.card κ * b) / s := by
  have hint : Integrable (fun ω => ⨆ i, Y i ω) μ := integrable_iSup_of_integrable Y hY
  have hsum : Integrable (fun ω => ∑ k, F k ω) μ :=
    integrable_finsetSum Finset.univ fun k _ => hF k
  have hexpint : Integrable (fun ω => rexp (s * ⨆ i, Y i ω)) μ :=
    hsum.mono'
      (measurable_exp.comp_aemeasurable (hint.aemeasurable.const_mul s)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact hexp ω)
  refine integral_le_log_div_of_integral_exp_le hint hs hexpint ?_
  calc ∫ ω, rexp (s * ⨆ i, Y i ω) ∂μ ≤ ∫ ω, ∑ k, F k ω ∂μ :=
        integral_mono hexpint hsum hexp
    _ = ∑ k, ∫ ω, F k ω ∂μ := integral_finsetSum _ fun k _ => hF k
    _ ≤ ∑ _k : κ, b := Finset.sum_le_sum fun k _ => hb k
    _ = Fintype.card κ * b := by simp

/-- The parametrised maximal inequality `E max_i X_i ≤ log N / s + c s / 2`. -/
private lemma integral_iSup_le_div_add [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    [Nonempty ι] {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, ⨆ i, X i ω ∂μ ≤ log (Fintype.card ι) / s + c * s / 2 := by
  have hexp : ∀ ω, rexp (s * ⨆ i, X i ω) ≤ ∑ i, rexp (s * X i ω) := by
    intro ω
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => X i ω)
    rw [← hj]
    exact Finset.single_le_sum (f := fun i => rexp (s * X i ω)) (fun i _ => (exp_pos _).le)
      (Finset.mem_univ j)
  have hle := integral_iSup_le_aux X (fun i => (h i).integrable)
    (fun i ω => rexp (s * X i ω)) (fun i => (h i).integrable_exp_mul s) hs hexp
    (fun i => (h i).mgf_le s)
  refine hle.trans_eq ?_
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [log_mul hN.ne' (exp_pos _).ne', log_exp, add_div]
  congr 1
  field_simp

/-- The parametrised maximal inequality for absolute values,
`E max_i |X_i| ≤ log (2N) / s + c s / 2`. -/
private lemma integral_iSup_abs_le_div_add [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    [Nonempty ι] {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, ⨆ i, |X i ω| ∂μ ≤ log (2 * Fintype.card ι) / s + c * s / 2 := by
  have hexp : ∀ ω, rexp (s * ⨆ i, |X i ω|) ≤
      ∑ k : ι × Bool, rexp ((if k.2 then s else -s) * X k.1 ω) := by
    intro ω
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => |X i ω|)
    rw [← hj]
    have hj2 : rexp (s * |X j ω|) ≤ ∑ b : Bool, rexp ((if b then s else -s) * X j ω) := by
      simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      rcases le_or_gt 0 (X j ω) with h0 | h0
      · rw [abs_of_nonneg h0]; linarith [exp_pos (-s * X j ω)]
      · rw [abs_of_neg h0, mul_neg, ← neg_mul]; linarith [exp_pos (s * X j ω)]
    refine hj2.trans ?_
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun i => ∑ b : Bool, rexp ((if b then s else -s) * X i ω))
      (fun i _ => Finset.sum_nonneg fun _ _ => (exp_pos _).le) (Finset.mem_univ j)
  have hb : ∀ k : ι × Bool, ∫ ω, rexp ((if k.2 then s else -s) * X k.1 ω) ∂μ ≤
      rexp (c * s ^ 2 / 2) := by
    intro k
    have := (h k.1).mgf_le (if k.2 then s else -s)
    split_ifs at this ⊢ <;> simpa [mgf] using this
  have hle := integral_iSup_le_aux (fun i ω => |X i ω|) (fun i => (h i).integrable.abs)
    (fun (k : ι × Bool) ω => rexp ((if k.2 then s else -s) * X k.1 ω))
    (fun k => (h k.1).integrable_exp_mul _) hs hexp hb
  refine hle.trans_eq ?_
  rw [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, mul_comm _ (2 : ℝ),
    log_mul (by positivity) (exp_pos _).ne', log_exp, add_div]
  congr 1
  field_simp

private lemma le_sqrt_of_forall_le_div_add {x L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (h : ∀ s : ℝ, 0 < s → x ≤ L / s + c * s / 2) : x ≤ √(2 * c * L) := by
  rcases hL.eq_or_lt with rfl | hL'
  · rw [mul_zero, sqrt_zero]
    by_contra! hx
    have := h (x / (c + 1)) (by positivity)
    rw [zero_div, zero_add] at this
    have h1 : c * (x / (c + 1)) / 2 < x := by
      rw [mul_div_assoc', div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases hc.eq_or_lt with rfl | hc'
  · rw [mul_zero, zero_mul, sqrt_zero]
    by_contra! hx
    have := h (2 * L / x) (by positivity)
    rw [zero_mul, zero_div, add_zero, div_div_eq_mul_div] at this
    have h1 : L * x / (2 * L) = x / 2 := by field_simp
    linarith
  set r := √(2 * c * L) with hr
  have hr0 : 0 < r := sqrt_pos.2 (by positivity)
  have hr2 : r * r = 2 * c * L := mul_self_sqrt (by positivity)
  have := h (r / c) (by positivity)
  have h1 : L / (r / c) + c * (r / c) / 2 = r := by
    field_simp
    nlinarith
  linarith

/-- The maximum of finitely many sub-Gaussian variables is integrable. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integrable_iSup {ι : Type*} [Finite ι]
    {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    Integrable (fun ω => ⨆ i, X i ω) μ :=
  integrable_iSup_of_integrable X fun i => (h i).integrable

/-- **The maximal inequality** (Boucheron–Lugosi–Massart, Theorem 2.5): the mean of the maximum
of `N` sub-Gaussian variables with proxy `c` is at most `√(2 c log N)`. No independence is
assumed.
Result: subgaussian-maximal-inequality -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_iSup_le [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, X i ω ∂μ ≤ √(2 * c * Real.log (Fintype.card ι)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty, integral_zero]
    exact sqrt_nonneg _
  exact le_sqrt_of_forall_le_div_add (log_nonneg (by exact_mod_cast Fintype.card_pos)) c.2
    fun _ hs => integral_iSup_le_div_add h hs

/-- The maximum of the absolute values of finitely many sub-Gaussian variables is integrable. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integrable_iSup_abs {ι : Type*} [Finite ι]
    {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    Integrable (fun ω => ⨆ i, |X i ω|) μ :=
  integrable_iSup_of_integrable (fun i ω => |X i ω|) fun i => (h i).integrable.abs

/-- The maximal inequality for absolute values: `E max_i |X_i| ≤ √(2 c log 2N)`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_iSup_abs_le [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, |X i ω| ∂μ ≤ √(2 * c * Real.log (2 * Fintype.card ι)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Real.iSup_of_isEmpty, integral_zero]
    exact sqrt_nonneg _
  have hN : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact le_sqrt_of_forall_le_div_add (log_nonneg (by linarith)) c.2
    fun _ hs => integral_iSup_abs_le_div_add h hs

end NLAlib
