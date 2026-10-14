/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import NLAlib.Probability.Tail

/-!
# Sub-Gaussian random variables

API for Mathlib's `ProbabilityTheory.HasSubgaussianMGF X c μ` (the moment generating function of
`X` is at most `exp (c t² / 2)`) that the probability layers use and Mathlib does not have:
monotonicity in the proxy, the proxy of a scalar multiple in the form `‖r‖₊ ^ 2 * c`, mean zero
and the second moment, lower and two-sided tails, weighted sums of independent variables, and
the union bound for a maximum. Proxies are `ℝ≥0` throughout (`docs/PORT_PROBABILITY.md` D2).

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.isFiniteMeasure`: the measure is finite.
* `ProbabilityTheory.HasSubgaussianMGF.mono`: a larger proxy.
* `ProbabilityTheory.HasSubgaussianMGF.integral_eq_zero`, `.integral_sq_le`: mean zero and
  second moment at most the proxy.
* `ProbabilityTheory.HasSubgaussianMGF.measure_le_le`, `.measure_abs_ge_le`: lower and two-sided
  tails.
* `ProbabilityTheory.HasSubgaussianMGF.sum_const_mul_of_iIndepFun`: `∑ aᵢ Xᵢ` has proxy `∑ aᵢ² cᵢ`.
* `ProbabilityTheory.HasSubgaussianMGF.measure_exists_ge_le`, `.measure_iSup_ge_le`,
  `.measure_exists_abs_ge_le`: the union bound for a maximum.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- A sub-Gaussian variable lives on a finite measure (Mathlib has this for the kernel form
only). -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.isFiniteMeasure (h : HasSubgaussianMGF X c μ) :
    IsFiniteMeasure μ := by
  have h0 := h.integrable_exp_mul 0
  simp only [zero_mul, exp_zero] at h0
  exact (integrable_const_iff_isFiniteMeasure one_ne_zero).mp h0

/-- A sub-Gaussian variable is sub-Gaussian with any larger proxy. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.mono (h : HasSubgaussianMGF X c μ) {d : ℝ≥0}
    (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  have hcd' : (c : ℝ) ≤ d := hcd
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans (exp_le_exp.mpr ?_)⟩
  gcongr

/-- Mathlib's `HasSubgaussianMGF.const_mul` with the proxy written `‖r‖₊ ^ 2 * c`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.const_mul' (h : HasSubgaussianMGF X c μ)
    (r : ℝ) : HasSubgaussianMGF (fun ω => r * X ω) (‖r‖₊ ^ 2 * c) μ := by
  convert h.const_mul r using 2
  ext
  simp only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]
  rfl

/-- A sub-Gaussian variable has mean zero. A probability measure is needed: if `μ univ < 1` the
moment generating function bound does not force the mean to vanish. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_eq_zero [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) : ∫ ω, X ω ∂μ = 0 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet X μ) := by
    simp [h.integrableExpSet_eq_univ]
  have h1 : HasDerivAt (fun t : ℝ => rexp ((c : ℝ) * t ^ 2 / 2)) 0 0 := by
    simpa using (((hasDerivAt_pow 2 (0 : ℝ)).const_mul (c : ℝ)).div_const 2).exp
  have h2 := hasDerivAt_mgf h0
  simp only [zero_mul, exp_zero, mul_one] at h2
  have hmin : IsLocalMin (fun t : ℝ => rexp ((c : ℝ) * t ^ 2 / 2) - mgf X μ t) 0 :=
    Filter.Eventually.of_forall fun t => by
      simp only [mgf_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        zero_div, exp_zero, sub_self]
      linarith [h.mgf_le t]
  linarith [hmin.hasDerivAt_eq_zero (h1.sub h2)]

private lemma one_add_sq_div_two_le_cosh (y : ℝ) : 1 + y ^ 2 / 2 ≤ cosh y := by
  have := sum_le_hasSum (Finset.range 2)
    (fun n _ => div_nonneg (by rw [pow_mul]; positivity) (by positivity)) (Real.hasSum_cosh y)
  simpa [Finset.sum_range_succ] using this

private lemma integral_sq_le_aux [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ)
    {u : ℝ} (hu : 0 < u) (hcu : c * u ≤ 1) : ∫ ω, X ω ^ 2 ∂μ ≤ c + c ^ 2 * u / 2 := by
  set t := √u
  have ht : t ^ 2 = u := sq_sqrt hu.le
  have hpos := h.integrable_exp_mul t
  have hneg := h.integrable_exp_mul (-t)
  have hcosh : Integrable (fun ω => cosh (t * X ω)) μ := by
    refine ((hpos.add hneg).div_const 2).congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply, cosh_eq, neg_mul]
  have hsq : Integrable (fun ω => X ω ^ 2) μ := (h.memLp 2).integrable_sq
  have hint : ∫ ω, cosh (t * X ω) ∂μ ≤ rexp (c * u / 2) := by
    have heq : ∫ ω, cosh (t * X ω) ∂μ = (mgf X μ t + mgf X μ (-t)) / 2 := by
      simp only [cosh_eq, mgf, neg_mul]
      rw [integral_div, integral_add hpos (by simpa only [neg_mul] using hneg)]
    have h1 := h.mgf_le t
    have h2 := h.mgf_le (-t)
    rw [neg_sq, ht] at h2
    rw [ht] at h1
    rw [heq]
    linarith
  have hlow : ∫ ω, (1 + (t * X ω) ^ 2 / 2) ∂μ ≤ ∫ ω, cosh (t * X ω) ∂μ :=
    integral_mono ((integrable_const 1).add ((hsq.const_mul (t ^ 2)).div_const 2 |>.congr
      (ae_of_all _ fun ω => by simp only [mul_pow]))) hcosh
      fun ω => one_add_sq_div_two_le_cosh _
  have hval : ∫ ω, (1 + (t * X ω) ^ 2 / 2) ∂μ = 1 + u / 2 * ∫ ω, X ω ^ 2 ∂μ := by
    simp only [mul_pow, ht]
    rw [integral_add (integrable_const 1) ((hsq.const_mul u).div_const 2), integral_div,
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    ring
  have hexp : rexp (c * u / 2) ≤ 1 + c * u / 2 + (c * u / 2) ^ 2 := by
    have := abs_exp_sub_one_sub_id_le (x := c * u / 2) (by
      rw [abs_of_nonneg (by positivity)]
      linarith)
    linarith [le_abs_self (rexp (c * u / 2) - 1 - c * u / 2)]
  have key : u / 2 * ∫ ω, X ω ^ 2 ∂μ ≤ u / 2 * (c + c ^ 2 * u / 2) := by
    nlinarith
  exact le_of_mul_le_mul_left key (by positivity)

/-- The second moment of a sub-Gaussian variable is at most its proxy. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_sq_le [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) : ∫ ω, X ω ^ 2 ∂μ ≤ c := by
  have hlim : Filter.Tendsto (fun u : ℝ => (c : ℝ) + (c : ℝ) ^ 2 * u / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (c : ℝ)) := by
    have : Continuous (fun u : ℝ => (c : ℝ) + (c : ℝ) ^ 2 * u / 2) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (c + 1) by positivity)] with u hu
  have hu1 : u * (c + 1) < 1 := (lt_div_iff₀ (by positivity)).mp hu.2
  exact integral_sq_le_aux h hu.1 (by nlinarith [hu.1, c.2])

/-- The lower tail of a sub-Gaussian variable. With `c = 0`, Lean's `t ^ 2 / 0 = 0` makes the
bound `1`; the variable is then `0` almost everywhere. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.measure_le_le (h : HasSubgaussianMGF X c μ)
    {t : ℝ} (ht : 0 ≤ t) : μ.real {ω | X ω ≤ -t} ≤ rexp (-t ^ 2 / (2 * c)) := by
  have hset : {ω | X ω ≤ -t} = {ω | t ≤ (-X) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, le_neg]
  rw [hset]
  exact h.neg.measure_ge_le ht

/-- The two-sided tail of a sub-Gaussian variable. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.measure_abs_ge_le
    (h : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * rexp (-t ^ 2 / (2 * c)) := by
  linarith [measureReal_abs_ge_le_add (μ := μ) X t, h.measure_ge_le ht, h.measure_le_le ht]

/-- A weighted sum of independent sub-Gaussian variables is sub-Gaussian with proxy
`∑ aᵢ² cᵢ`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.sum_const_mul_of_iIndepFun {ι : Type*}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0} {s : Finset ι}
    (h : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) (a : ι → ℝ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, a i * X i ω) (∑ i ∈ s, ‖a i‖₊ ^ 2 * c i) μ := by
  have hind : iIndepFun (fun i ω => a i * X i ω) μ :=
    h_indep.comp (fun i x => a i * x) fun i => measurable_const.mul measurable_id
  exact HasSubgaussianMGF.sum_of_iIndepFun hind fun i hi => (h i hi).const_mul' (a i)

/-- The union bound for the maximum of finitely many sub-Gaussian variables with a common proxy.
No independence is assumed. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.measure_exists_ge_le {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, t ≤ X i ω} ≤ Fintype.card ι * rexp (-t ^ 2 / (2 * c)) := by
  rw [Set.ofPred_exists]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  refine (Finset.sum_le_sum fun i _ => (h i).measure_ge_le ht).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The union bound for the maximum, with the event written through `⨆`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.measure_iSup_ge_le {ι : Type*} [Fintype ι]
    [Nonempty ι] {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ⨆ i, X i ω} ≤ Fintype.card ι * rexp (-t ^ 2 / (2 * c)) := by
  have hset : {ω | t ≤ ⨆ i, X i ω} = {ω | ∃ i, t ≤ X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hω
      obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => X i ω)
      exact ⟨j, hj ▸ hω⟩
    · rintro ⟨i, hi⟩
      exact hi.trans (le_ciSup (f := fun i => X i ω) (Finite.bddAbove_range _) i)
  rw [hset]
  exact HasSubgaussianMGF.measure_exists_ge_le h ht

/-- The union bound for the maximum of absolute values. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.measure_exists_abs_ge_le {ι : Type*}
    [Fintype ι] {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, t ≤ |X i ω|} ≤ 2 * Fintype.card ι * rexp (-t ^ 2 / (2 * c)) := by
  rw [Set.ofPred_exists]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  refine (Finset.sum_le_sum fun i _ => (h i).measure_abs_ge_le ht).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end NLAlib
