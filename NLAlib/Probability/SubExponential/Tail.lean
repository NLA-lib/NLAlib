/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.SubExponential.Basic
public import NLAlib.Probability.Tail

/-!
# Tails of sub-exponential random variables

The tail of a sub-exponential variable,
$\mathbb{P}[X \ge t] \le \exp(-\min(t^2 / (2v), t / (2b)))$, its two regimes, the lower and
two-sided tails, the absolute moments that the two-sided tail gives, and Bernstein's inequality
for sums of independent sub-exponential variables.

## Main results

* `NLAlib.HasSubexponentialMGF.measureReal_ge_le` and its regimes
  `NLAlib.HasSubexponentialMGF.measureReal_ge_le_of_mul_le`,
  `NLAlib.HasSubexponentialMGF.measureReal_ge_le_of_le_mul`.
* `NLAlib.HasSubexponentialMGF.measureReal_le_le`,
  `NLAlib.HasSubexponentialMGF.measureReal_abs_ge_le`.
* `NLAlib.HasSubexponentialMGF.integral_abs_rpow_le`: the absolute moments, for every $p > 0$.
* `NLAlib.HasSubexponentialMGF.measureReal_sum_ge_le_of_iIndepFun`: Bernstein's inequality.
* `NLAlib.HasSubexponentialMGF.measureReal_ge_le_of_scale_eq_zero`,
  `NLAlib.HasSubexponentialMGF.measureReal_sum_ge_le_of_iIndepFun_of_scale_eq_zero`: the
  Gaussian exponent when the scale vanishes, including independent finite sums.

## References

* [M. J. Wainwright, *High-Dimensional Statistics*][Wainwright2019], §2.1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {v b : ℝ≥0}

namespace HasSubexponentialMGF

/-- The Chernoff bound at one tilt $l \ge 0$ of the closed window $b l \le 1$:
$\mu(X \ge t) \le e^{-l t + v l^2 / 2}$; the boundary $b l = 1$ is reached by continuity from
inside the open window. -/
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

/-- The sub-Gaussian regime of the sub-exponential tail: for $t \ge 0$ with $b t \le v$,
$\mu(X \ge t) \le e^{-t^2 / (2v)}$. With $b = 0$ this is the sub-Gaussian tail. -/
theorem measureReal_ge_le_of_mul_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t)
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

/-- A scale-zero sub-exponential variable has the Gaussian upper tail for $t \ge 0$:
$\mathbb{P}[X \ge t] \le \exp(-t^2/(2v))$. This uses the full MGF window available at
$b = 0$, rather than the vacuous division-by-zero branch of `measureReal_ge_le`.
When $v = 0$ the displayed bound retains the total-division value $1$. -/
theorem measureReal_ge_le_of_scale_eq_zero (h : HasSubexponentialMGF X v 0 μ) {t : ℝ}
    (ht : 0 ≤ t) : μ.real {ω | t ≤ X ω} ≤ rexp (-t ^ 2 / (2 * v)) :=
  h.measureReal_ge_le_of_mul_le ht (by simp)

/-- The exponential regime of the sub-exponential tail: for $v \le b t$,
$\mu(X \ge t) \le e^{-t / (2b)}$. No sign condition on $t$ is needed: $v \le b t$ forces
$t \ge 0$ when $b > 0$, and the bound is $1$ when $b = 0$. -/
theorem measureReal_ge_le_of_le_mul (h : HasSubexponentialMGF X v b μ) {t : ℝ}
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

/-- **The sub-exponential tail**: if $X$ has variance proxy $v$ and scale $b$, then for $t \ge 0$
$$\mu(X \ge t) \le \exp\Bigl(-\min\Bigl(\frac{t^2}{2v}, \frac{t}{2b}\Bigr)\Bigr)\,.$$
[Wainwright2019, Proposition 2.9]. If $b = 0$ or $v = 0$, Lean's division by zero makes the
exponent $0$ and the bound $1$; the regime forms are the usable statements then (for a
sub-Gaussian variable, $b = 0$, use `measureReal_ge_le_of_mul_le`).
Result: subexponential-tail -/
theorem measureReal_ge_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
  rcases le_total ((b : ℝ) * t) v with hbt | hbt
  · refine (h.measureReal_ge_le_of_mul_le ht hbt).trans ?_
    rw [neg_div]
    exact exp_le_exp.mpr (neg_le_neg (min_le_left _ _))
  · refine (h.measureReal_ge_le_of_le_mul hbt).trans ?_
    rw [neg_div]
    exact exp_le_exp.mpr (neg_le_neg (min_le_right _ _))

/-- The lower tail of a sub-exponential variable: for $t \ge 0$,
$\mu(X \le -t) \le \exp(-\min(t^2 / (2v), t / (2b)))$. -/
theorem measureReal_le_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | X ω ≤ -t} ≤ rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
  simpa only [le_neg] using h.neg.measureReal_ge_le ht

/-- The two-sided tail of a sub-exponential variable: for $t \ge 0$,
$\mu(\lvert X\rvert \ge t) \le 2 \exp(-\min(t^2 / (2v), t / (2b)))$. -/
theorem measureReal_abs_ge_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
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
    exact add_le_add (h.measureReal_ge_le ht) (h.measureReal_le_le ht)

/-- The absolute moments of a sub-exponential variable with parameters $(v, b)$, $v, b > 0$:
for $p > 0$, <!-- value subexponentialMomentBound v b p -->
$$\int \lvert X\rvert^p \, d\mu \le p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p)\,,$$
the bound being `NLAlib.subexponentialMomentBound v b p`, the layer-cake integral of the
two-sided tail `measureReal_abs_ge_le` (`NLAlib.integral_rpow_le_of_measureReal_ge_le_two_mul_exp`).
For $p \ge 2$ it is at most $2(vp)^{p/2} + 2(2bp)^{p}$ (`NLAlib.subexponentialMomentBound_le`). -/
theorem integral_abs_rpow_le (h : HasSubexponentialMGF X v b μ) (hv : 0 < v) (hb : 0 < b)
    {p : ℝ} (hp : 0 < p) :
    ∫ ω, |X ω| ^ p ∂μ ≤ subexponentialMomentBound (v : ℝ) (b : ℝ) p := by
  have := h.isFiniteMeasure
  exact (integral_rpow_le_of_measureReal_ge_le_two_mul_exp h.aemeasurable.abs
    (ae_of_all _ fun ω => abs_nonneg (X ω)) (NNReal.coe_pos.2 hv) (NNReal.coe_pos.2 hb) hp
    fun t ht => h.measureReal_abs_ge_le ht.le).2

/-- **Bernstein's inequality** for independent sub-exponential variables: if the $X_i$ are
independent and, for $i \in s$, $X_i$ is sub-exponential with parameters $(v_i, b_i)$
(`HasSubexponentialMGF`), then for $t \ge 0$
$$\mu\Bigl(\sum_{i \in s} X_i \ge t\Bigr) \le \exp\Bigl(-\min\Bigl(\frac{t^2}{2 \sum_{i \in s} v_i},
\frac{t}{2 \max_{i \in s} b_i}\Bigr)\Bigr),$$
with the convention of `measureReal_ge_le` when a denominator is $0$. [Wainwright2019, §2.1.3].
Result: bernstein-inequality -/
theorem measureReal_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {v b : ι → ℝ≥0} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
      rexp (-min (t ^ 2 / (2 * ∑ i ∈ s, v i)) (t / (2 * s.sup b))) := by
  simpa only [NNReal.coe_sum] using (sum_of_iIndepFun h_indep h).measureReal_ge_le ht

/-- Independent scale-zero sub-exponential summands retain the Gaussian Bernstein regime:
for $t \ge 0$, the upper tail of their finite sum is at most
$\exp(-t^2/(2\sum_{i\in s}v_i))$. Unlike the generic minimum formula, the bound stays
informative when every scale parameter is zero and the variance sum is positive. -/
theorem measureReal_sum_ge_le_of_iIndepFun_of_scale_eq_zero {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {v : ι → ℝ≥0} {s : Finset ι}
    (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) 0 μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤ rexp (-t ^ 2 / (2 * ∑ i ∈ s, v i)) := by
  have hsum : HasSubexponentialMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) 0 μ := by
    have hb : s.sup (fun _ : ι => (0 : ℝ≥0)) = 0 := Finset.sup_bot s
    simpa only [hb] using sum_of_iIndepFun h_indep h
  simpa only [NNReal.coe_sum] using hsum.measureReal_ge_le_of_scale_eq_zero ht

end HasSubexponentialMGF

end NLAlib
