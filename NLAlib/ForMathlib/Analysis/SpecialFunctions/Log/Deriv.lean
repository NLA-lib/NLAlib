/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Polynomial upper bounds on $\log(1 + u)$ and $\log(1 - u)$

Truncations of the series of $\log(1 + u)$ that bound it from above: the cubic
$\log(1 + u) \le u - u^2/2 + u^3/3$ for every $u > -1$, the quadratic
$\log(1 - u) \le -u - u^2/2$ on $[0, 1)$, and Laurent and Massart's
$-\log(1 - u) \le u + u^2 / (2(1 - u))$ on $[0, 1)$. They are the log terms of the Chernoff
bounds for $\chi^2$ and for sums of squares (Dasgupta and Gupta's exponent
$\varepsilon^2/4 - \varepsilon^3/6$, and the sub-gamma bound of a weighted $\chi^2$), where
$1 + v \le e^v$ is too weak. The numerical bound $\log 9 \le 9/4$ is the margin of the covering
number $9^d$ of a $1/4$-net of a sphere. The same series gives the lower bound
$e^{2r} \le (1 + r)/(1 - r)$ on $[0, 1)$ of Tropp and Webber's Chebyshev growth. Upstream
candidates for `Mathlib.Analysis.SpecialFunctions.Log.Deriv`.

## Main results

* `Real.log_one_add_le_cubic`, `Real.log_one_add_le_cubic_of_nonpos`.
* `Real.log_one_add_le_sub_sq_div`: $\log(1 + s) \le s - s^2/(2(1 + s))$ for $s \ge 0$, the
  upper Dasgupta–Gupta exponent at every $s$.
* `Real.log_one_sub_le_quadratic`.
* `Real.neg_log_one_sub_le`.
* `Real.log_nine_le_nine_div_four`, `Real.log_twentyOne_le_sixtyOne_div_twenty`.
* `Real.exp_two_mul_le_one_add_div_one_sub`: $e^{2r} \le (1 + r)/(1 - r)$ on $[0, 1)$, the first
  term of the series of $\log(1 + r) - \log(1 - r)$.
-/

@[expose] public section

namespace Real

/-- For $-1 < u \le 0$,
$$\log(1 + u) \le u - \frac{u^2}{2} + \frac{u^3}{3} \,.$$ -/
theorem log_one_add_le_cubic_of_nonpos {u : ℝ} (h1 : -1 < u) (h0 : u ≤ 0) :
    log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
  have hu : 0 ≤ -u := by linarith
  have h := hasSum_pow_div_log_of_abs_lt_one (x := -u) (by rw [abs_of_nonneg hu]; linarith)
  have := sum_le_hasSum (Finset.range 3) (fun n _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add] at this
  norm_num at this
  have e : (-u) ^ 3 = -u ^ 3 := by ring
  linarith

/-- For $u > -1$,
$$\log(1 + u) \le u - \frac{u^2}{2} + \frac{u^3}{3} \,.$$
For $u \le 0$ this is `Real.log_one_add_le_cubic_of_nonpos`; for $u \ge 0$ the difference has
derivative $u^3 / (1 + u) \ge 0$ and vanishes at $0$. -/
theorem log_one_add_le_cubic {u : ℝ} (h1 : -1 < u) :
    log (1 + u) ≤ u - u ^ 2 / 2 + u ^ 3 / 3 := by
  rcases le_or_gt u 0 with h0 | h0
  · exact log_one_add_le_cubic_of_nonpos h1 h0
  let f : ℝ → ℝ := fun t => t - t ^ 2 / 2 + t ^ 3 / 3 - log (1 + t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt f (1 - t + t ^ 2 - 1 / (1 + t)) t := by
    intro t ht
    have hlog := ((hasDerivAt_id t).const_add 1).log (by simp only [id]; linarith)
    have hp : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3) (1 - t + t ^ 2) t := by
      have := (((hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3))
      exact this.congr_deriv (by norm_num)
    exact hp.sub hlog
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hderiv t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 < t := ht
      rw [(hderiv t ht0.le).deriv]
      have : 1 - t + t ^ 2 - 1 / (1 + t) = t ^ 3 / (1 + t) := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h0.le) h0.le
  simp only [f, add_zero, log_one] at this
  norm_num at this
  linarith

/-- For $s \ge 0$,
$$\log(1 + s) \le s - \frac{s^2}{2(1 + s)} \,,$$
valid at every $s \ge 0$, unlike the cubic `Real.log_one_add_le_cubic`, whose bound is useless
for large $s$. The difference has derivative $s^2/(2(1 + s)^2) \ge 0$. It gives the upper tail
exponent $s - \log(1 + s) \ge s^2/(2(1 + s)) \ge \min(s^2, s)/4$ of a $\chi^2$ variable. -/
theorem log_one_add_le_sub_sq_div {s : ℝ} (hs : 0 ≤ s) :
    log (1 + s) ≤ s - s ^ 2 / (2 * (1 + s)) := by
  let f : ℝ → ℝ := fun t => t - t ^ 2 / (2 * (1 + t)) - log (1 + t)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt f (t ^ 2 / (2 * (1 + t) ^ 2)) t := by
    intro t ht
    have h1 : 0 < 1 + t := by linarith
    have hlog : HasDerivAt (fun x : ℝ => log (1 + x)) (1 / (1 + t)) t :=
      ((hasDerivAt_id' t).const_add 1).log h1.ne'
    have hd : HasDerivAt (fun x : ℝ => 2 * (1 + x)) (2 * 1) t :=
      ((hasDerivAt_id' t).const_add 1).const_mul 2
    have hq := (hasDerivAt_pow 2 t).div hd (by positivity)
    have h1' : 1 + t ≠ 0 := h1.ne'
    refine (((hasDerivAt_id' t).sub hq).sub hlog).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hderiv t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t (le_of_lt ht)).deriv]
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  simp only [f, add_zero, log_one] at this
  norm_num at this
  linarith

/-- For $0 \le u < 1$,
$$\log(1 - u) \le -u - \frac{u^2}{2} \,,$$
the first two terms of $-\log(1 - u) = \sum_{k \ge 1} u^k / k$, whose terms are nonnegative. -/
theorem log_one_sub_le_quadratic {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    log (1 - u) ≤ -u - u ^ 2 / 2 := by
  have h := hasSum_pow_div_log_of_abs_lt_one (x := u) (by rwa [abs_of_nonneg hu0])
  have := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num at this
  linarith

/-- **Laurent and Massart's log bound**: for $0 \le u < 1$,
$$-\log(1 - u) \le u + \frac{u^2}{2 (1 - u)} \,,$$
by comparing the series $\sum_{k \ge 1} u^k / k$ term by term with $u + (u/2) \sum_{k \ge 1}
u^k$. It turns the Laplace transform $(1 - 2\theta)^{-1/2}$ of $\chi^2_1$ into a sub-gamma
bound [LaurentMassart2000, proof of Lemma 1, p. 1326]. -/
theorem neg_log_one_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    -log (1 - u) ≤ u + u ^ 2 / (2 * (1 - u)) := by
  have h := hasSum_pow_div_log_of_abs_lt_one (x := u) (by rwa [abs_of_nonneg hu0])
  have hg : HasSum (fun k : ℕ => (if k = 0 then u / 2 else 0) + u / 2 * u ^ k)
      (u / 2 + u / 2 * (1 - u)⁻¹) :=
    (hasSum_ite_eq 0 (u / 2)).add ((hasSum_geometric_of_lt_one hu0 hu1).mul_left (u / 2))
  have hle := hasSum_le (fun k => ?_) h hg
  · have h1 : 0 < 1 - u := by linarith
    calc -log (1 - u) ≤ u / 2 + u / 2 * (1 - u)⁻¹ := hle
      _ = u + u ^ 2 / (2 * (1 - u)) := by field_simp; ring
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [if_neg hk.ne', zero_add, pow_succ, mul_comm (u / 2), mul_div_assoc']
      refine div_le_div_of_nonneg_left (by positivity) (by norm_num) ?_
      have : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk
      linarith

/-- $\log 9 \le 9/4$, that is $9 \le e^{9/4}$: from $e^{9/32} \ge 1 + 9/32 + (9/32)^2/2$ raised
to the eighth power. The margin that turns the $9^d$ points of a $1/4$-net of a $d$-dimensional
sphere into a factor $e^{9d/4}$. -/
theorem log_nine_le_nine_div_four : log 9 ≤ 9 / 4 := by
  rw [log_le_iff_le_exp (by norm_num)]
  have h := quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 9 / 32 by norm_num)
  rw [show (9 / 4 : ℝ) = ((8 : ℕ) : ℝ) * (9 / 32) by norm_num, exp_nat_mul]
  calc (9 : ℝ) ≤ (1 + 9 / 32 + (9 / 32) ^ 2 / 2) ^ 8 := by norm_num
    _ ≤ exp (9 / 32) ^ 8 := by gcongr

/-- $\log 21 \le 61/20$, that is $21 \le e^{61/20}$: from $e^{61/640} \ge 1 + 61/640 +
(61/640)^2/2$ raised to the $32$nd power. The margin that turns the $21^d$ points of a
$1/10$-net of a $d$-dimensional sphere into a factor $e^{61d/20}$. -/
theorem log_twentyOne_le_sixtyOne_div_twenty : log 21 ≤ 61 / 20 := by
  rw [log_le_iff_le_exp (by norm_num)]
  have h := quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 61 / 640 by norm_num)
  rw [show (61 / 20 : ℝ) = ((32 : ℕ) : ℝ) * (61 / 640) by norm_num, exp_nat_mul]
  calc (21 : ℝ) ≤ (1 + 61 / 640 + (61 / 640) ^ 2 / 2) ^ 32 := by norm_num
    _ ≤ exp (61 / 640) ^ 32 := by gcongr

/-- $e^{2r} \le (1 + r)/(1 - r)$ for $0 \le r < 1$, that is $r \le \operatorname{artanh} r$.
[TroppWebber2023, (C.1)]. -/
theorem exp_two_mul_le_one_add_div_one_sub {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r < 1) :
    exp (2 * r) ≤ (1 + r) / (1 - r) := by
  -- The first term of $\log(1 + r) - \log(1 - r) = \sum_k 2r^{2k+1}/(2k+1)$ is $2r$.
  have hs := hasSum_log_sub_log_of_abs_lt_one (abs_lt.2 ⟨by linarith, h₁⟩)
  have h := le_hasSum hs 0 (fun j _ => by positivity)
  rw [← log_div (by linarith) (by linarith)] at h
  rw [← exp_log (div_pos (by linarith) (by linarith : (0 : ℝ) < 1 - r))]
  exact exp_le_exp.2 (by simpa using h)

end Real
