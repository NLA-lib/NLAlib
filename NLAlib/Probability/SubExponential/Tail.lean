/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.SubExponential.Basic

/-!
# Tails of sub-exponential random variables

The tail of a sub-exponential variable, `P(t ≤ X) ≤ exp (-min (t²/(2v)) (t/(2b)))`, its two
regimes, the lower and two-sided tails, and Bernstein's inequality for sums of independent
sub-exponential variables.

## Main results

* `NLAlib.HasSubexponentialMGF.measure_ge_le` and its regimes
  `NLAlib.HasSubexponentialMGF.measure_ge_le_of_mul_le`,
  `NLAlib.HasSubexponentialMGF.measure_ge_le_of_le_mul`.
* `NLAlib.HasSubexponentialMGF.measure_le_le`, `NLAlib.HasSubexponentialMGF.measure_abs_ge_le`.
* `NLAlib.HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`: Bernstein's inequality.

## References

* [M. J. Wainwright, *High-Dimensional Statistics*][Wainwright2019], §2.1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {v b : ℝ≥0}

namespace HasSubexponentialMGF

/-- The Chernoff bound at one tilt `l` of the closed window `b l ≤ 1`; the boundary `b l = 1` is
reached by continuity from inside the open window. -/
private lemma measure_ge_le_exp (h : HasSubexponentialMGF X v b μ) {t l : ℝ} (hl : 0 ≤ l)
    (hbl : b * l ≤ 1) : μ.real {ω | t ≤ X ω} ≤ rexp (-l * t + v * l ^ 2 / 2) := by
  have := h.isFiniteMeasure
  have key : ∀ x : ℝ, 0 ≤ x → (b : ℝ) * x < 1 →
      μ.real {ω | t ≤ X ω} ≤ rexp (-x * t + v * x ^ 2 / 2) := by
    intro x hx hbx
    have hw : (b : ℝ) * |x| < 1 := by rwa [abs_of_nonneg hx]
    calc μ.real {ω | t ≤ X ω}
    _ ≤ rexp (-x * t) * mgf X μ x := measure_ge_le_exp_mul_mgf t hx (h.integrable_exp_mul x hw)
    _ ≤ rexp (-x * t) * rexp (v * x ^ 2 / 2) := by
      gcongr
      exact h.mgf_le x hw
    _ = rexp (-x * t + v * x ^ 2 / 2) := (exp_add _ _).symm
  rcases hbl.lt_or_eq with hbl | hbl
  · exact key l hl hbl
  have hl0 : 0 < l := by
    refine lt_of_le_of_ne hl fun hl0 => ?_
    rw [← hl0, mul_zero] at hbl
    exact zero_ne_one hbl
  have hb0 : 0 < (b : ℝ) := by
    refine lt_of_le_of_ne b.2 fun hb0 => ?_
    rw [← hb0, zero_mul] at hbl
    exact zero_ne_one hbl
  have hcont : ContinuousAt (fun x : ℝ => rexp (-x * t + v * x ^ 2 / 2)) l := by fun_prop
  refine ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio l))) ?_
  filter_upwards [Ioo_mem_nhdsLT hl0] with x hx
  exact key x hx.1.le ((mul_lt_mul_of_pos_left hx.2 hb0).trans_eq hbl)

private lemma measureReal_le_one (h : HasSubexponentialMGF X v b μ) (s : Set Ω) :
    μ.real s ≤ 1 := by
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  exact (measure_mono (Set.subset_univ _)).trans h.measure_univ_le_one

/-- The sub-Gaussian regime of the sub-exponential tail: for `b t ≤ v`,
`P(t ≤ X) ≤ exp (-t² / (2v))`. With `b = 0` this is the sub-Gaussian tail. -/
theorem measure_ge_le_of_mul_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t)
    (hbt : b * t ≤ v) : μ.real {ω | t ≤ X ω} ≤ rexp (-t ^ 2 / (2 * v)) := by
  by_cases hv : (v : ℝ) = 0
  · rw [hv, mul_zero, div_zero, exp_zero]
    exact measureReal_le_one h _
  have hv0 : 0 < (v : ℝ) := lt_of_le_of_ne v.2 (Ne.symm hv)
  have hl : (b : ℝ) * (t / v) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hv0]
    exact hbt
  calc μ.real {ω | t ≤ X ω}
  _ ≤ rexp (-(t / v) * t + v * (t / v) ^ 2 / 2) := measure_ge_le_exp h (by positivity) hl
  _ = rexp (-t ^ 2 / (2 * v)) := by
    congr 1
    field_simp
    ring

/-- The exponential regime of the sub-exponential tail: for `v ≤ b t`,
`P(t ≤ X) ≤ exp (-t / (2b))`. No sign condition on `t` is needed: `v ≤ b t` forces `0 ≤ t` when
`b > 0`, and the bound is `1` when `b = 0`. -/
theorem measure_ge_le_of_le_mul (h : HasSubexponentialMGF X v b μ) {t : ℝ}
    (hbt : v ≤ b * t) : μ.real {ω | t ≤ X ω} ≤ rexp (-t / (2 * b)) := by
  by_cases hb : (b : ℝ) = 0
  · rw [hb, mul_zero, div_zero, exp_zero]
    exact measureReal_le_one h _
  have hb0 : 0 < (b : ℝ) := lt_of_le_of_ne b.2 (Ne.symm hb)
  calc μ.real {ω | t ≤ X ω}
  _ ≤ rexp (-(1 / b) * t + v * (1 / b) ^ 2 / 2) :=
    measure_ge_le_exp h (by positivity) (by rw [mul_one_div_cancel hb0.ne'])
  _ ≤ rexp (-t / (2 * b)) := by
    refine exp_le_exp.mpr ?_
    calc -(1 / b) * t + v * (1 / b) ^ 2 / 2
    _ ≤ -(1 / b) * t + b * t * (1 / b) ^ 2 / 2 := by gcongr
    _ = -t / (2 * b) := by
      field_simp
      ring

/-- **The sub-exponential tail** ([Wainwright2019], Proposition 2.9):
`P(t ≤ X) ≤ exp (-min (t² / (2v)) (t / (2b)))`. If `b = 0` or `v = 0`, Lean's division by zero
makes the exponent `0` and the bound `1`; the regime forms are the usable statements then (for a
sub-Gaussian variable, `b = 0`, use `measure_ge_le_of_mul_le`).
Result: subexponential-tail -/
theorem measure_ge_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
  rcases le_total ((b : ℝ) * t) v with hbt | hbt
  · refine (h.measure_ge_le_of_mul_le ht hbt).trans ?_
    rw [neg_div]
    exact exp_le_exp.mpr (neg_le_neg (min_le_left _ _))
  · refine (h.measure_ge_le_of_le_mul hbt).trans ?_
    rw [neg_div]
    exact exp_le_exp.mpr (neg_le_neg (min_le_right _ _))

/-- The lower tail of a sub-exponential variable. -/
theorem measure_le_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | X ω ≤ -t} ≤ rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
  simpa only [le_neg] using h.neg.measure_ge_le ht

/-- The two-sided tail of a sub-exponential variable. -/
theorem measure_abs_ge_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
  have := h.isFiniteMeasure
  calc μ.real {ω | t ≤ |X ω|}
  _ ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | X ω ≤ -t}) := by
    refine measureReal_mono fun ω hω => ?_
    rcases le_abs.mp (show t ≤ |X ω| from hω) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (le_neg.mp h1)
  _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | X ω ≤ -t} := measureReal_union_le _ _
  _ ≤ 2 * rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
    rw [two_mul]
    exact add_le_add (h.measure_ge_le ht) (h.measure_le_le ht)

/-- **Bernstein's inequality** for independent sub-exponential variables
([Wainwright2019], §2.1.3).
Result: bernstein-inequality -/
theorem measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {v b : ι → ℝ≥0} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
      rexp (-min (t ^ 2 / (2 * ∑ i ∈ s, v i)) (t / (2 * s.sup b))) := by
  simpa only [NNReal.coe_sum] using (sum_of_iIndepFun h_indep h).measure_ge_le ht

end HasSubexponentialMGF

end NLAlib
