/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

/-!
# Logarithmic defect and deviation from the arithmetic mean

For positive entries with arithmetic mean one, a lower bound on the product bounds their squared
deviation from one. Upstream candidate for Mathlib.

## Main results

* `Real.sum_sq_sub_one_le_six_mul_of_exp_neg_le_prod`.
-/
@[expose] public section

namespace Real

/-- The scalar logarithmic defect `x - 1 - log x` (with `x > 0`). -/
private noncomputable def logDefect (x : ℝ) : ℝ :=
  x - 1 - Real.log x

/-- Scalar capacity certificate: for `0 < x`, if the logarithmic defect
`logDefect x` is at most `1 / 6`, then `(x - 1)^2 ≤ 6 * logDefect x`. -/
private theorem sq_sub_one_le_six_mul_logDefect {x : ℝ} (hx : 0 < x)
    (hdef : logDefect x ≤ 1 / 6) :
    (x - 1) ^ 2 ≤ 6 * logDefect x := by
  have hs_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hs_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hlog_s : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs_pos
  have hlog_x : Real.log x = 2 * Real.log (Real.sqrt x) := by
    calc
      Real.log x = 2 * (Real.log x / 2) := by ring
      _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx.le]
  have hd_eq : logDefect x =
      (Real.sqrt x - 1) ^ 2 + 2 * ((Real.sqrt x - 1) - Real.log (Real.sqrt x)) := by
    unfold logDefect
    rw [hlog_x]
    nlinarith [hs_sq]
  have hd_ge : (Real.sqrt x - 1) ^ 2 ≤ logDefect x := by
    rw [hd_eq]
    nlinarith [hlog_s]
  have hd_nonneg : 0 ≤ logDefect x := (sq_nonneg (Real.sqrt x - 1)).trans hd_ge
  have hu_sq_le : (Real.sqrt x - 1) ^ 2 ≤ 1 / 6 := hd_ge.trans hdef
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfrac : 1 / 6 < (Real.sqrt 2 - 1) ^ 2 := by
    have hlt : Real.sqrt 2 < 17 / 12 := by
      have hsq : (Real.sqrt 2) ^ 2 < (17 / 12) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
      have hlt' : |Real.sqrt 2| < |17 / 12| := sq_lt_sq.mp hsq
      simpa [abs_of_nonneg (Real.sqrt_nonneg 2),
        abs_of_nonneg (by norm_num : 0 ≤ (17 / 12 : ℝ))] using hlt'
    have hsq : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by
      nlinarith [hsqrt2_sq]
    rw [hsq]
    linarith
  have hx_lt_two : x < 2 := by
    by_contra hnot
    have hge : 2 ≤ x := le_of_not_gt hnot
    have hs2 : Real.sqrt 2 ≤ Real.sqrt x := Real.sqrt_le_sqrt hge
    have h1le_s : 1 ≤ Real.sqrt x := Real.one_lt_sqrt_two.le.trans hs2
    have hsq_le : (Real.sqrt 2 - 1) ^ 2 ≤ (Real.sqrt x - 1) ^ 2 := by
      exact (sq_le_sq₀ (sub_nonneg.mpr Real.one_lt_sqrt_two.le) (sub_nonneg.mpr h1le_s)).2
        (sub_le_sub_right hs2 1)
    have hbad : 1 / 6 < (Real.sqrt x - 1) ^ 2 := hfrac.trans_le hsq_le
    linarith [hu_sq_le, hbad]
  have hsp6up : (Real.sqrt 2 + 1) ^ 2 ≤ 6 := by
    have hlt : Real.sqrt 2 < 3 / 2 := by
      have hsq : (Real.sqrt 2) ^ 2 < (3 / 2) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]
        norm_num
      have hlt' : |Real.sqrt 2| < |3 / 2| := sq_lt_sq.mp hsq
      simpa [abs_of_nonneg (Real.sqrt_nonneg 2),
        abs_of_nonneg (by norm_num : 0 ≤ (3 / 2 : ℝ))] using hlt'
    have hsq : (Real.sqrt 2 + 1) ^ 2 = 3 + 2 * Real.sqrt 2 := by
      nlinarith [hsqrt2_sq]
    rw [hsq]
    linarith
  have hsp6 : (Real.sqrt x + 1) ^ 2 ≤ 6 := by
    have hs_lt : Real.sqrt x < Real.sqrt 2 := (Real.sqrt_lt_sqrt_iff hx.le).2 hx_lt_two
    have hlt : (Real.sqrt x + 1) ^ 2 < (Real.sqrt 2 + 1) ^ 2 := by
      nlinarith [hs_lt, hsqrt2_sq, hs_sq]
    exact le_of_lt (hlt.trans_le hsp6up)
  have hinner : (Real.sqrt x - 1) * (Real.sqrt x + 1) = x - 1 := by
    have h : (Real.sqrt x - 1) * (Real.sqrt x + 1) = (Real.sqrt x) ^ 2 - 1 := by ring
    rw [h, hs_sq]
  have hprod : (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 1) ^ 2 = (x - 1) ^ 2 := by
    rw [← mul_pow, hinner]
  calc
    (x - 1) ^ 2 = (Real.sqrt x - 1) ^ 2 * (Real.sqrt x + 1) ^ 2 := hprod.symm
    _ ≤ logDefect x * 6 := by
      exact mul_le_mul hd_ge hsp6 (sq_nonneg _) hd_nonneg
    _ = 6 * logDefect x := by ring

end Real

open scoped BigOperators

namespace Real

/-- The logarithmic defect of a positive real number is nonnegative. -/
private theorem logDefect_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ logDefect x := by
  have hlog := log_le_sub_one_of_pos hx
  unfold logDefect
  linarith

/-- A small total logarithmic defect controls the squared distance of a positive
finite family from the constant family one. -/
private theorem sum_sq_sub_one_le_six_mul_of_sum_logDefect_le
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (eps : ℝ)
    (hx : ∀ i, 0 < x i) (heps : eps ≤ 1 / 6)
    (hdef : ∑ i, logDefect (x i) ≤ eps) :
    ∑ i, (x i - 1) ^ 2 ≤ 6 * eps := by
  have hnonneg : ∀ i, 0 ≤ logDefect (x i) := fun i => logDefect_nonneg (hx i)
  have hsingle : ∀ i, logDefect (x i) ≤ 1 / 6 := by
    intro i
    exact ((Finset.single_le_sum (fun j _ => hnonneg j)
      (Finset.mem_univ i)).trans hdef).trans heps
  calc
    (∑ i, (x i - 1) ^ 2) ≤ ∑ i, 6 * logDefect (x i) :=
      Finset.sum_le_sum fun i _ => sq_sub_one_le_six_mul_logDefect (hx i) (hsingle i)
    _ = 6 * ∑ i, logDefect (x i) := (Finset.mul_sum _ _ _).symm
    _ ≤ 6 * eps := mul_le_mul_of_nonneg_left hdef (by norm_num)

/-- For a positive finite family with sum equal to its cardinality, a product
lower bound by `exp (-eps)`, with $\varepsilon\le 1/6$, implies a quadratic bound on
its distance from the constant family one. -/
theorem sum_sq_sub_one_le_six_mul_of_exp_neg_le_prod
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (eps : ℝ)
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = (Fintype.card ι : ℝ))
    (heps : eps ≤ 1 / 6) (hprod : exp (-eps) ≤ ∏ i, x i) :
    ∑ i, (x i - 1) ^ 2 ≤ 6 * eps := by
  have hlog : log (∏ i, x i) = ∑ i, log (x i) :=
    log_prod (fun i _ => ne_of_gt (hx i))
  have hlog_lower : -eps ≤ ∑ i, log (x i) := by
    have h := log_le_log (exp_pos (-eps)) hprod
    rwa [log_exp, hlog] at h
  apply sum_sq_sub_one_le_six_mul_of_sum_logDefect_le x eps hx heps
  have hdef : (∑ i, logDefect (x i)) =
      (∑ i, x i) - (Fintype.card ι : ℝ) - ∑ i, log (x i) := by
    unfold logDefect
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
  rw [hdef, hsum]
  linarith

end Real
