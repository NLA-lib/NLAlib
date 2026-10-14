/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.MeasureTheory.Constructions.PiUpdate
public import NLAlib.Probability.Entropy

/-!
# Tensorization of entropy

The entropy of a nonnegative function under a product of probability measures is at most the
sum over coordinates of the mean entropy in that coordinate, the others fixed
([BoucheronLugosiMassart2013], Theorem 4.10). The positive case is a telescoping sum over partial
marginals with the variational (Gibbs) inequality for entropy; the nonnegative case follows by
adding `δ` and letting `δ → 0`.

## Main results

* `NLAlib.entropy_pi_le_sum`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal ENNReal Topology

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}


/-! ### The Gibbs variational inequality -/

private theorem young_scaled {Z U m : ℝ} (hZ : 0 < Z) (hm : 0 < m) :
    Z * U ≤ Z * Real.log Z - Z * Real.log m - Z + m * rexp U := by
  have h1 := Real.add_one_le_exp (U - Real.log (Z / m))
  have h2 : rexp (U - Real.log (Z / m)) = m * rexp U / Z := by
    rw [Real.exp_sub, Real.exp_log (div_pos hZ hm)]; field_simp
  rw [h2, Real.log_div hZ.ne' hm.ne', le_div_iff₀ hZ] at h1
  nlinarith

/-- The Gibbs variational inequality: `E Z U ≤ entropy ν Z` for `Z > 0` and `E e^U ≤ 1`. -/
private theorem integral_mul_le_entropy_of_integral_exp_le_one [IsProbabilityMeasure ν]
    {Z U : Ω → ℝ} (hZ : ∀ t, 0 < Z t) (hZi : Integrable Z ν)
    (hZl : Integrable (fun t => Z t * Real.log (Z t)) ν)
    (hZU : Integrable (fun t => Z t * U t) ν) (hU : Integrable (fun t => rexp (U t)) ν)
    (hU1 : ∫ t, rexp (U t) ∂ν ≤ 1) :
    ∫ t, Z t * U t ∂ν ≤ entropy ν Z := by
  set m := ∫ t, Z t ∂ν with hm_def
  have hm : 0 < m := by
    rw [hm_def, integral_pos_iff_support_of_nonneg (fun t => (hZ t).le) hZi]
    have : Function.support Z = Set.univ := by
      ext t; simp [(hZ t).ne']
    rw [this]; simp
  have hA : Integrable (fun t => Z t * Real.log (Z t) - Z t * Real.log m) ν :=
    hZl.sub (hZi.mul_const _)
  have hint : Integrable (fun t => Z t * Real.log (Z t) - Z t * Real.log m - Z t
      + m * rexp (U t)) ν := (hA.sub hZi).add (hU.const_mul m)
  have h := integral_mono hZU hint fun t => young_scaled (U := U t) (hZ t) hm
  have e1 : ∫ t, (Z t * Real.log (Z t) - Z t * Real.log m - Z t + m * rexp (U t)) ∂ν
      = (∫ t, Z t * Real.log (Z t) ∂ν) - m * Real.log m - m + m * ∫ t, rexp (U t) ∂ν := by
    rw [integral_add (f := fun t => Z t * Real.log (Z t) - Z t * Real.log m - Z t)
      (g := fun t => m * rexp (U t)) (hA.sub hZi) (hU.const_mul m),
      integral_sub (f := fun t => Z t * Real.log (Z t) - Z t * Real.log m) hA hZi,
      integral_sub hZl (hZi.mul_const _), integral_const_mul, integral_mul_const]
  rw [e1] at h
  rw [entropy]
  nlinarith

/-! ### Partial marginals and the telescoping bound -/

section Telescope

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  {P : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (P i)]

/-- A function independent of the coordinates in `S` is fixed by `lmarginal S`. -/
private theorem lmarginal_of_indep (S : Finset ι) (F : (∀ j, X j) → ℝ≥0∞)
    (hF : ∀ x y, (∀ j ∉ S, x j = y j) → F x = F y) :
    lmarginal P S F = F := by
  ext x
  simp only [lmarginal]
  have : ∀ y, F (Function.updateFinset x S y) = F x :=
    fun y => hF _ _ (fun j hj => by simp [Function.updateFinset_def, hj])
  simp only [this, lintegral_const, measure_univ, mul_one]

private theorem lintegral_lmarginal [Fintype ι] (S : Finset ι) {F : (∀ j, X j) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ x, lmarginal P S F x ∂(Measure.pi P) = ∫⁻ x, F x ∂(Measure.pi P) :=
  lintegral_eq_of_lmarginal_eq S (hF.lmarginal P) hF
    (lmarginal_of_indep S _ (fun _ _ h => lmarginal_congr P F h))

private theorem lintegral_mul_indep [Fintype ι] (S : Finset ι) {F W : (∀ j, X j) → ℝ≥0∞}
    (hF : Measurable F) (hW : Measurable W) (hWi : ∀ x y, (∀ j ∉ S, x j = y j) → W x = W y) :
    ∫⁻ x, F x * W x ∂(Measure.pi P) = ∫⁻ x, lmarginal P S F x * W x ∂(Measure.pi P) := by
  have h1 : lmarginal P S (fun x => F x * W x) = fun x => lmarginal P S F x * W x := by
    ext x; simp only [lmarginal]
    have : ∀ y, W (Function.updateFinset x S y) = W x :=
      fun y => hWi _ _ (fun j hj => by simp [Function.updateFinset_def, hj])
    simp only [this]
    exact lintegral_mul_const _ (hF.comp measurable_updateFinset)
  have := lintegral_lmarginal (P := P) S (F := fun x => F x * W x) (hF.mul hW)
  rw [h1] at this
  exact this.symm

/-- The partial integral `E_S Z`, integrating out the coordinates in `S`. -/
private noncomputable def margE (P : ∀ i, Measure (X i)) (S : Finset ι) (Z : (∀ j, X j) → ℝ)
    (x : ∀ j, X j) : ℝ :=
  (lmarginal P S (fun y => ENNReal.ofReal (Z y)) x).toReal

private theorem mul_negLog_le {b : ℝ} (hb : 0 ≤ b) : b * max (-Real.log b) 0 ≤ 1 := by
  rcases le_total 1 b with h1 | h1
  · rw [max_eq_right (by linarith [Real.log_nonneg h1])]; norm_num
  · rw [max_eq_left (by linarith [Real.log_nonpos hb h1])]
    nlinarith [Real.self_sub_one_le_mul_log hb]

section Z

variable {Z : (∀ j, X j) → ℝ} (hZm : Measurable Z) (hZ : ∀ x, 0 < Z x)

omit [DecidableEq ι] in
include hZm in
private theorem measurable_ofReal_comp : Measurable (fun y => ENNReal.ofReal (Z y)) :=
  ENNReal.measurable_ofReal.comp hZm

include hZm in
private theorem margA_measurable (S : Finset ι) :
    Measurable (lmarginal P S (fun y => ENNReal.ofReal (Z y))) :=
  (measurable_ofReal_comp hZm).lmarginal P

include hZm in
private theorem margE_measurable (S : Finset ι) : Measurable (margE P S Z) :=
  (margA_measurable hZm S).ennreal_toReal

include hZm hZ in
private theorem margA_pos (S : Finset ι) (x : ∀ j, X j) :
    0 < lmarginal P S (fun y => ENNReal.ofReal (Z y)) x := by
  simp only [lmarginal]
  rw [lintegral_pos_iff_support
    (f := fun y => ENNReal.ofReal (Z (Function.updateFinset x S y)))
    ((measurable_ofReal_comp hZm).comp measurable_updateFinset)]
  have : Function.support
      (fun y : (∀ j : S, X j) => ENNReal.ofReal (Z (Function.updateFinset x S y))) = Set.univ := by
    ext y; simp [hZ]
  rw [this]; simp

omit [∀ i, IsProbabilityMeasure (P i)] in
include hZ in
private theorem margE_empty : margE P ∅ Z = Z := by
  ext x; simp [margE, ENNReal.toReal_ofReal (hZ x).le]

omit [∀ i, IsProbabilityMeasure (P i)] in
private theorem margE_congr (S : Finset ι) {x y : ∀ j, X j} (h : ∀ j ∉ S, x j = y j) :
    margE P S Z x = margE P S Z y := by
  simp only [margE]; rw [lmarginal_congr P _ h]

variable [Fintype ι] (hZi : Integrable Z (Measure.pi P))

include hZm hZi in
private theorem lintegral_margA (S : Finset ι) :
    ∫⁻ x, lmarginal P S (fun y => ENNReal.ofReal (Z y)) x ∂(Measure.pi P) ≠ ∞ := by
  rw [lintegral_lmarginal S (measurable_ofReal_comp hZm)]
  exact hZi.lintegral_lt_top.ne

include hZm hZi in
private theorem ae_margA_lt_top (S : Finset ι) :
    ∀ᵐ x ∂(Measure.pi P), lmarginal P S (fun y => ENNReal.ofReal (Z y)) x < ∞ :=
  ae_lt_top (margA_measurable hZm S) (lintegral_margA hZm hZi S)

include hZ hZi in
private theorem margE_univ (x : ∀ j, X j) :
    margE P Finset.univ Z x = ∫ y, Z y ∂(Measure.pi P) := by
  simp only [margE, lmarginal_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hZi (Filter.Eventually.of_forall fun y => (hZ y).le),
    ENNReal.toReal_ofReal (integral_nonneg fun y => (hZ y).le)]

include hZm hZi in
private theorem integrable_margE (S : Finset ι) : Integrable (margE P S Z) (Measure.pi P) :=
  integrable_toReal_of_lintegral_ne_top (margA_measurable hZm S).aemeasurable
    (lintegral_margA hZm hZi S)

include hZm hZ in
private theorem integrable_Z_mul_negLog (S : Finset ι) :
    Integrable (fun x => Z x * max (-Real.log (margE P S Z x)) 0) (Measure.pi P) := by
  have hm : Measurable (fun x => max (-Real.log (margE P S Z x)) 0) :=
    ((Real.measurable_log.comp (margE_measurable hZm S)).neg).max measurable_const
  refine ⟨(hZm.mul hm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
    mul_nonneg (hZ x).le (le_max_right _ _))]
  have e1 : (fun x => ENNReal.ofReal (Z x * max (-Real.log (margE P S Z x)) 0))
      = fun x => ENNReal.ofReal (Z x) * ENNReal.ofReal (max (-Real.log (margE P S Z x)) 0) := by
    ext x; rw [ENNReal.ofReal_mul (hZ x).le]
  have hW : Measurable (fun x => ENNReal.ofReal (max (-Real.log (margE P S Z x)) 0)) :=
    ENNReal.measurable_ofReal.comp hm
  rw [e1, lintegral_mul_indep S (measurable_ofReal_comp hZm) hW
    (fun x y h => by simp only [margE_congr S h])]
  calc ∫⁻ x, lmarginal P S (fun y => ENNReal.ofReal (Z y)) x
          * ENNReal.ofReal (max (-Real.log (margE P S Z x)) 0) ∂(Measure.pi P)
        ≤ ∫⁻ _x, 1 ∂(Measure.pi P) := by
          refine lintegral_mono fun x => ?_
          simp only [margE]
          set A := lmarginal P S (fun y => ENNReal.ofReal (Z y)) x
          rcases eq_or_ne A ∞ with hA | hA
          · rw [hA]; simp
          · rw [← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
            exact ENNReal.ofReal_le_one.2 (mul_negLog_le ENNReal.toReal_nonneg)
    _ < ∞ := by simp

include hZm hZ hZi in
private theorem integrable_Z_mul_log_margE
    (hZl : Integrable (fun x => Z x * Real.log (Z x)) (Measure.pi P)) (S : Finset ι) :
    Integrable (fun x => Z x * Real.log (margE P S Z x)) (Measure.pi P) := by
  refine Integrable.mono' (((hZl.abs.add hZi).add (integrable_margE hZm hZi S)).add
    (integrable_Z_mul_negLog hZm hZ S))
    (hZm.mul (Real.measurable_log.comp (margE_measurable hZm S))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hZx := hZ x
  have hb : 0 ≤ margE P S Z x := ENNReal.toReal_nonneg
  set b := margE P S Z x
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have hn : 0 ≤ max (-Real.log b) 0 := le_max_right _ _
  have hn2 : -Real.log b ≤ max (-Real.log b) 0 := le_max_left _ _
  have := abs_nonneg (Z x * Real.log (Z x))
  have := le_abs_self (Z x * Real.log (Z x))
  have := mul_nonneg hZx.le hn
  rcases hb.lt_or_eq with hb | hb
  · have hy := young_scaled (U := Real.log b) hZx one_pos
    rw [Real.log_one, Real.exp_log hb] at hy
    have hlow : -(Z x * max (-Real.log b) 0) ≤ Z x * Real.log b := by nlinarith
    rw [abs_le]; constructor <;> nlinarith
  · rw [← hb, Real.log_zero, mul_zero, abs_zero]
    linarith

include hZm hZ hZi in
private theorem step_bound (hZl : Integrable (fun x => Z x * Real.log (Z x)) (Measure.pi P))
    (S : Finset ι) (i : ι) (hi : i ∉ S) :
    ∫ x, Z x * (Real.log (margE P S Z x) - Real.log (margE P (insert i S) Z x)) ∂(Measure.pi P)
      ≤ ∫ x, entropy (P i) (fun t => Z (Function.update x i t)) ∂(Measure.pi P) := by
  set U := fun x => Real.log (margE P S Z x) - Real.log (margE P (insert i S) Z x) with hU_def
  have hZU : Integrable (fun x => Z x * U x) (Measure.pi P) := by
    refine ((integrable_Z_mul_log_margE hZm hZ hZi hZl S).sub
      (integrable_Z_mul_log_margE hZm hZ hZi hZl (insert i S))).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [hU_def, Pi.sub_apply]; ring
  rw [← integral_integral_update_pi P i hZU]
  have hinner := integrable_integral_update_pi P i hZU
  have key : ∀ x, Integrable (fun t => Z (Function.update x i t)) (P i) →
      Integrable (fun t => Z (Function.update x i t) * Real.log (Z (Function.update x i t)))
        (P i) →
      Integrable (fun t => Z (Function.update x i t) * U (Function.update x i t)) (P i) →
      lmarginal P (insert i S) (fun y => ENNReal.ofReal (Z y)) x < ∞ →
      ∫ t, Z (Function.update x i t) * U (Function.update x i t) ∂(P i) ≤
        entropy (P i) (fun t => Z (Function.update x i t)) := by
    intro x h1 h2 h3 h4
    set c := margE P (insert i S) Z x with hc_def
    have hc : 0 < c := ENNReal.toReal_pos (margA_pos hZm hZ _ x).ne' h4.ne
    have hcu : ∀ t, margE P (insert i S) Z (Function.update x i t) = c := fun t => by
      simp only [hc_def, margE]
      rw [lmarginal_update_of_mem P (Finset.mem_insert_self i S)]
    have hins := lmarginal_insert (μ := P) _ (measurable_ofReal_comp hZm) hi x
    have hmeasA : Measurable (fun t => lmarginal P S (fun y => ENNReal.ofReal (Z y))
        (Function.update x i t)) := (margA_measurable hZm S).comp (measurable_update x)
    have hfin : ∫⁻ t, lmarginal P S (fun y => ENNReal.ofReal (Z y)) (Function.update x i t)
        ∂(P i) ≠ ∞ := by rw [← hins]; exact h4.ne
    have hae := ae_lt_top hmeasA hfin
    have hexp : (fun t => rexp (U (Function.update x i t)))
        =ᵐ[P i] fun t => margE P S Z (Function.update x i t) / c := by
      filter_upwards [hae] with t ht
      have hpos : 0 < margE P S Z (Function.update x i t) :=
        ENNReal.toReal_pos (margA_pos hZm hZ _ _).ne' ht.ne
      simp only [hU_def, hcu, Real.exp_sub, Real.exp_log hpos, Real.exp_log hc]
    have hintE : Integrable (fun t => margE P S Z (Function.update x i t)) (P i) :=
      integrable_toReal_of_lintegral_ne_top hmeasA.aemeasurable hfin
    have hint1 : ∫ t, margE P S Z (Function.update x i t) ∂(P i) = c := by
      simp only [margE]
      rw [integral_toReal hmeasA.aemeasurable hae, ← hins]
      rfl
    refine integral_mul_le_entropy_of_integral_exp_le_one (fun t => hZ _) h1 h2 h3
      ((hintE.div_const c).congr hexp.symm) ?_
    rw [integral_congr_ae hexp, integral_div, hint1, div_self hc.ne']
  have hbound : ∀ᵐ x ∂(Measure.pi P),
      ∫ t, Z (Function.update x i t) * U (Function.update x i t) ∂(P i) ≤
        entropy (P i) (fun t => Z (Function.update x i t)) := by
    filter_upwards [ae_integrable_comp_update_pi P i hZi, ae_integrable_comp_update_pi P i hZl,
      ae_integrable_comp_update_pi P i hZU, ae_margA_lt_top hZm hZi (insert i S)]
      with x h1 h2 h3 h4 using key x h1 h2 h3 h4
  have hmeasEnt : Measurable (fun x => entropy (P i) (fun t => Z (Function.update x i t))) := by
    have m1 := measurable_integral_update_pi P i (hZm.mul (Real.measurable_log.comp hZm))
    have m2 := measurable_integral_update_pi P i hZm
    exact m1.sub (m2.mul (Real.measurable_log.comp m2))
  have hEnt : Integrable (fun x => entropy (P i) (fun t => Z (Function.update x i t)))
      (Measure.pi P) := by
    refine Integrable.mono' ((hinner.abs.add (integrable_integral_update_pi P i hZl).abs).add
      (integrable_const 1)) hmeasEnt.aestronglyMeasurable ?_
    filter_upwards [hbound] with x hx
    have hm0 : 0 ≤ ∫ t, Z (Function.update x i t) ∂(P i) := integral_nonneg fun t => (hZ _).le
    have hml := Real.self_sub_one_le_mul_log hm0
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [entropy] at hx ⊢
    rw [abs_le]
    constructor
    · have := neg_abs_le (∫ t, Z (Function.update x i t) * U (Function.update x i t) ∂(P i))
      have := abs_nonneg (∫ t, Z (Function.update x i t) *
        Real.log (Z (Function.update x i t)) ∂(P i))
      linarith
    · have := le_abs_self (∫ t, Z (Function.update x i t) *
        Real.log (Z (Function.update x i t)) ∂(P i))
      have := abs_nonneg (∫ t, Z (Function.update x i t) * U (Function.update x i t) ∂(P i))
      linarith
  exact integral_mono_ae hinner hEnt hbound

include hZm hZ hZi in
private theorem telescope (hZl : Integrable (fun x => Z x * Real.log (Z x)) (Measure.pi P))
    (S : Finset ι) :
    ∫ x, Z x * Real.log (Z x) ∂(Measure.pi P) - ∫ x, Z x * Real.log (margE P S Z x) ∂(Measure.pi P)
      ≤ ∑ i ∈ S, ∫ x, entropy (P i) (fun t => Z (Function.update x i t)) ∂(Measure.pi P) := by
  induction S using Finset.induction_on with
  | empty => simp [margE_empty hZ]
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    have hstep := step_bound hZm hZ hZi hZl S i hi
    have e : ∫ x, Z x * (Real.log (margE P S Z x) - Real.log (margE P (insert i S) Z x))
        ∂(Measure.pi P) = ∫ x, Z x * Real.log (margE P S Z x) ∂(Measure.pi P)
          - ∫ x, Z x * Real.log (margE P (insert i S) Z x) ∂(Measure.pi P) := by
      rw [← integral_sub (integrable_Z_mul_log_margE hZm hZ hZi hZl S)
        (integrable_Z_mul_log_margE hZm hZ hZi hZl (insert i S))]
      congr 1; ext x; ring
    rw [e] at hstep
    linarith

end Z

/-- Tensorization of entropy for a positive function. -/
private theorem entropy_pi_le_sum_of_pos [Fintype ι] {f : (∀ j, X j) → ℝ} (hfm : Measurable f)
    (hpos : ∀ x, 0 < f x) (hf : Integrable f (Measure.pi P))
    (hflog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi P)) :
    entropy (Measure.pi P) f ≤
      ∑ i, ∫ x, entropy (P i) (fun y => f (Function.update x i y)) ∂Measure.pi P := by
  have ht := telescope hfm hpos hf hflog Finset.univ
  simp only [margE_univ hpos hf, integral_mul_const] at ht
  exact ht

end Telescope

/-! ### From positive to nonnegative functions -/

private theorem abs_add_mul_log_add_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    |(a + δ) * Real.log (a + δ)| ≤ |a * Real.log a| + a + 2 := by
  set b := a + δ with hb
  have hbpos : 0 < b := by positivity
  have hconv : a * Real.log b + a - b ≤ a * Real.log a := by
    rcases ha.eq_or_lt with h0 | hpos
    · subst h0; simp; linarith
    · have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hpos hbpos)
      rw [Real.log_div hpos.ne' hbpos.ne', inv_div] at h1
      have h2 : a * (1 - b / a) ≤ a * (Real.log a - Real.log b) :=
        mul_le_mul_of_nonneg_left h1 ha
      rw [mul_sub, mul_div_cancel₀ _ hpos.ne'] at h2
      linarith
  have h4 := le_abs_self (a * Real.log a)
  have h5 := neg_abs_le (a * Real.log a)
  rcases le_or_gt 1 b with hb1 | hb1
  · have hlog0 : 0 ≤ Real.log b := Real.log_nonneg hb1
    have hlogb : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hbpos
    rw [abs_of_nonneg (mul_nonneg hbpos.le hlog0)]
    have : b * Real.log b = a * Real.log b + δ * Real.log b := by rw [hb]; ring
    nlinarith
  · have hlog0 : Real.log b ≤ 0 := Real.log_nonpos hbpos.le hb1.le
    have := Real.self_sub_one_le_mul_log hbpos.le
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hbpos.le hlog0)]
    linarith

/-- Dominated convergence for `(f + δ) log (f + δ)` as `δ → 0`. -/
private theorem tendsto_integral_mul_log_add [IsFiniteMeasure ν] {f : Ω → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f ν)
    (hflog : Integrable (fun x => f x * Real.log (f x)) ν)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n ≤ 1)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (f x + δ n) * Real.log (f x + δ n) ∂ν)
      atTop (𝓝 (∫ x, f x * Real.log (f x) ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => |f x * Real.log (f x)| + f x + 2)
    (fun n => (Real.continuous_mul_log.measurable.comp
      (hfm.add measurable_const)).aestronglyMeasurable)
    ((hflog.abs.add hf).add (integrable_const (2 : ℝ)))
    (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · rw [Real.norm_eq_abs]
    exact abs_add_mul_log_add_le (hf0 x) (hδ n) (hδ1 n)
  · have hlim : Tendsto (fun n => f x + δ n) atTop (𝓝 (f x)) := by
      simpa using (tendsto_const_nhds (x := f x)).add hδlim
    exact (Real.continuous_mul_log.tendsto (f x)).comp hlim

section Nonneg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  {P : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (P i)]

/-- `E_i g log E_i g` is integrable for a nonnegative `g` with `g, g log g` integrable. -/
private theorem integrable_mul_log_integral_update (i : ι) {g : (∀ j, X j) → ℝ}
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g (Measure.pi P))
    (hglog : Integrable (fun x => g x * Real.log (g x)) (Measure.pi P)) :
    Integrable (fun x => (∫ t, g (Function.update x i t) ∂(P i)) *
      Real.log (∫ t, g (Function.update x i t) ∂(P i))) (Measure.pi P) := by
  refine Integrable.mono' ((integrable_integral_update_pi P i hglog).abs.add
    (integrable_const (1 : ℝ)))
    (Real.continuous_mul_log.measurable.comp
      (measurable_integral_update_pi P i hgm)).aestronglyMeasurable ?_
  filter_upwards [ae_integrable_comp_update_pi P i hg,
    ae_integrable_comp_update_pi P i hglog] with x h1 h2
  have hu := entropy_nonneg (ν := P i) (ae_of_all _ fun t => hg0 (Function.update x i t)) h1 h2
  have hm0 : 0 ≤ ∫ t, g (Function.update x i t) ∂(P i) := integral_nonneg fun t => hg0 _
  have hl := Real.self_sub_one_le_mul_log hm0
  rw [entropy] at hu
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have ha := abs_nonneg
    (∫ t, g (Function.update x i t) * Real.log (g (Function.update x i t)) ∂(P i))
  have hb := le_abs_self
    (∫ t, g (Function.update x i t) * Real.log (g (Function.update x i t)) ∂(P i))
  rw [abs_le]
  constructor <;> linarith

/-- The integrated `i`-th entropy is `E g log g - E (E_i g log E_i g)`. -/
private theorem integral_entropy_update (i : ι) {g : (∀ j, X j) → ℝ}
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g (Measure.pi P))
    (hglog : Integrable (fun x => g x * Real.log (g x)) (Measure.pi P)) :
    ∫ x, entropy (P i) (fun y => g (Function.update x i y)) ∂Measure.pi P =
      (∫ x, g x * Real.log (g x) ∂(Measure.pi P)) -
        ∫ x, (∫ t, g (Function.update x i t) ∂(P i)) *
          Real.log (∫ t, g (Function.update x i t) ∂(P i)) ∂(Measure.pi P) := by
  simp only [entropy]
  rw [integral_sub (integrable_integral_update_pi P i hglog)
    (integrable_mul_log_integral_update i hgm hg0 hg hglog),
    integral_integral_update_pi P i hglog]

end Nonneg

/-- **Tensorization of entropy** ([BoucheronLugosiMassart2013], Theorem 4.10): the entropy of a
function under a product of probability measures is at most the sum over coordinates of the
mean entropy in that coordinate, the others fixed. -/
theorem entropy_pi_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    {f : (∀ i, X i) → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f (Measure.pi ν))
    (hflog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi ν)) :
    entropy (Measure.pi ν) f ≤
      ∑ i, ∫ x, entropy (ν i) (fun y => f (Function.update x i y)) ∂Measure.pi ν := by
  set mean : ι → (∀ j, X j) → ℝ := fun i x => ∫ t, f (Function.update x i t) ∂(ν i)
    with hmean
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδ
  have hδpos (n : ℕ) : 0 < δ n := by positivity
  have hδle (n : ℕ) : δ n ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsm (n : ℕ) : Measurable (fun x => f x + δ n) := hfm.add measurable_const
  have hs0 (n : ℕ) (x : ∀ j, X j) : 0 ≤ f x + δ n := by linarith [hf0 x, hδpos n]
  have hsi (n : ℕ) : Integrable (fun x => f x + δ n) (Measure.pi ν) := hf.add (integrable_const _)
  have hsl (n : ℕ) :
      Integrable (fun x => (f x + δ n) * Real.log (f x + δ n)) (Measure.pi ν) :=
    Integrable.mono' ((hflog.abs.add hf).add (integrable_const (2 : ℝ)))
      (Real.continuous_mul_log.measurable.comp (hsm n)).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact abs_add_mul_log_add_le (hf0 x) (hδpos n) (hδle n))
  have hpoint (n : ℕ) :
      (∫ x, (f x + δ n) * Real.log (f x + δ n) ∂(Measure.pi ν)) -
        ((∫ x, f x ∂(Measure.pi ν)) + δ n) * Real.log ((∫ x, f x ∂(Measure.pi ν)) + δ n) ≤
      ∑ i, ((∫ x, (f x + δ n) * Real.log (f x + δ n) ∂(Measure.pi ν)) -
        ∫ x, (mean i x + δ n) * Real.log (mean i x + δ n) ∂(Measure.pi ν)) := by
    have h := entropy_pi_le_sum_of_pos (hsm n) (fun x => by linarith [hf0 x, hδpos n]) (hsi n)
      (hsl n)
    have hint : ∫ x, f x + δ n ∂(Measure.pi ν) = (∫ x, f x ∂(Measure.pi ν)) + δ n := by
      rw [integral_add hf (integrable_const _)]; simp
    rw [entropy, hint] at h
    refine h.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
    rw [integral_entropy_update i (hsm n) (hs0 n) (hsi n) (hsl n)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_integrable_comp_update_pi ν i hf] with x hx
    have he : ∫ t, f (Function.update x i t) + δ n ∂(ν i) = mean i x + δ n := by
      rw [integral_add hx (integrable_const _)]; simp [hmean]
    simp only [he]
  have hT := tendsto_integral_mul_log_add hfm hf0 hf hflog hδpos hδle hδlim
  have hM : Tendsto (fun n => ((∫ x, f x ∂(Measure.pi ν)) + δ n) *
      Real.log ((∫ x, f x ∂(Measure.pi ν)) + δ n)) atTop
      (𝓝 ((∫ x, f x ∂(Measure.pi ν)) * Real.log (∫ x, f x ∂(Measure.pi ν)))) := by
    have hlim : Tendsto (fun n => (∫ x, f x ∂(Measure.pi ν)) + δ n) atTop
        (𝓝 (∫ x, f x ∂(Measure.pi ν))) := by
      simpa using (tendsto_const_nhds (x := ∫ x, f x ∂(Measure.pi ν))).add hδlim
    exact (Real.continuous_mul_log.tendsto _).comp hlim
  have hR := tendsto_finsetSum Finset.univ fun i _ => hT.sub
    (tendsto_integral_mul_log_add (measurable_integral_update_pi ν i hfm)
      (fun x => integral_nonneg fun t => hf0 _) (integrable_integral_update_pi ν i hf)
      (integrable_mul_log_integral_update i hfm hf0 hf hflog) hδpos hδle hδlim)
  refine (le_of_tendsto_of_tendsto' (hT.sub hM) hR hpoint).trans_eq
    (Finset.sum_congr rfl fun i _ => ?_)
  exact (integral_entropy_update i hfm hf0 hf hflog).symm
end NLAlib
