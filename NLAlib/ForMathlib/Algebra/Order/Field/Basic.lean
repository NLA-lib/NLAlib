/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Rational identities and perturbation estimates in ordered fields

For every $t$ in an ordered field, $c = (1 - t^2) / (1 + t^2)$ and $s = 2t / (1 + t^2)$ satisfy
$c^2 + s^2 = 1$: the coefficients of a plane rotation as rational functions of one parameter.
The Bernstein coefficient $g(\theta) = (\theta^2/2)/(1 - L\theta/3)$ is nonnegative on
$(0, 3/L)$, and the choice of $\theta$ there that turns $-\theta t + g(\theta) v$ into the
Bernstein exponent $-(t^2/2)/(v + Lt/3)$. The weight $r/(\ell - r - 1)$ of the Gaussian
range-finder bounds is nonnegative for $r + 2 \le \ell$. Upstream candidates for
`Mathlib.Algebra.Order.Field.Basic`.

## Main results

* `one_sub_sq_div_one_add_sq_sq_add_two_mul_div_one_add_sq_sq`: $c^2 + s^2 = 1$.
* `mul_lt_three_of_mem_Ioo`, `sq_div_two_div_nonneg_of_mem_Ioo`: the Bernstein coefficient.
* `exists_bernstein_exponent`: the optimised exponent of the Bernstein tail.
* `natCast_div_sub_sub_one_nonneg`: $0 \le r/(\ell - r - 1)$.
* `abs_div_sub_div_le`, `abs_mul_div_sub_mul_div_le`: quotient perturbation estimates.
-/

@[expose] public section

/-- The rational parametrisation of the circle: $c = (1 - t^2) / (1 + t^2)$ and
$s = 2t / (1 + t^2)$ satisfy $c^2 + s^2 = 1$. -/
theorem one_sub_sq_div_one_add_sq_sq_add_two_mul_div_one_add_sq_sq {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (t : K) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

section Bernstein

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- On $(0, 3/L)$, $L\theta < 3$: the Bernstein coefficient $(\theta^2/2)/(1 - L\theta/3)$ has a
positive denominator. -/
theorem mul_lt_three_of_mem_Ioo {L θ : K} (hL : 0 < L) (hθ : θ ∈ Set.Ioo 0 (3 / L)) :
    L * θ < 3 := by
  have := hθ.2
  rw [lt_div_iff₀ hL] at this
  linarith

/-- On $(0, 3/L)$, the Bernstein coefficient $(\theta^2/2)/(1 - L\theta/3)$ is nonnegative. -/
theorem sq_div_two_div_nonneg_of_mem_Ioo {L θ : K} (hL : 0 < L) (hθ : θ ∈ Set.Ioo 0 (3 / L)) :
    0 ≤ θ ^ 2 / 2 / (1 - L * θ / 3) :=
  div_nonneg (by positivity) (by linarith [mul_lt_three_of_mem_Ioo hL hθ])

/-- The choice of $\theta$ in the Bernstein tail: for $L > 0$, $v \ge 0$ and $t > 0$, some
$\theta \in (0, 3/L)$ ($\theta = t / (v + Lt/3)$, or $\theta = 3/(2L)$ when $v = 0$) gives
$-\theta t + g(\theta) v \le -(t^2/2)/(v + Lt/3)$, with $g(\theta) = (\theta^2/2)/(1 - L\theta/3)$.
-/
theorem exists_bernstein_exponent {L v t : K} (hL : 0 < L) (hv : 0 ≤ v) (ht : 0 < t) :
    ∃ θ ∈ Set.Ioo 0 (3 / L),
      -θ * t + θ ^ 2 / 2 / (1 - L * θ / 3) * v ≤ -(t ^ 2 / 2) / (v + L * t / 3) := by
  rcases hv.eq_or_lt with rfl | hv'
  · refine ⟨3 / (2 * L), ⟨by positivity, ?_⟩, le_of_eq ?_⟩
    · rw [div_lt_div_iff₀ (by positivity) hL]
      nlinarith
    · field_simp
      ring
  set D := v + L * t / 3 with hD
  have hD0 : 0 < D := by positivity
  refine ⟨t / D, ⟨div_pos ht hD0, ?_⟩, le_of_eq ?_⟩
  · rw [div_lt_div_iff₀ hD0 hL, hD]
    nlinarith
  · have hq : 1 - L * (t / D) / 3 = v / D := by
      field_simp
      rw [hD]
      ring
    rw [hq]
    field_simp
    ring

end Bernstein

section Cast

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The tail weight $r/(\ell - r - 1)$ of the Gaussian range-finder bounds is nonnegative for
$r + 2 \le \ell$ (casts to an ordered field). -/
theorem natCast_div_sub_sub_one_nonneg {r l : ℕ} (hl : r + 2 ≤ l) :
    0 ≤ (r : K) / ((l : K) - r - 1) := by
  have hl' : (r : K) + 2 ≤ l := by exact_mod_cast hl
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

end Cast


/-- A positive denominator margin controls simultaneous numerator and denominator changes. -/
theorem abs_div_sub_div_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r e α β m B η : K}
    (hm : 0 < m) (hα : m / 2 ≤ α) (hβ : m ≤ β)
    (hre : |r - e| ≤ η) (he : |e| ≤ B) (hαβ : |α - β| ≤ η / m) :
    |r / α - e / β| ≤ 2 * (1 + B / m ^ 2) * η / m := by
  have hB : 0 ≤ B := (abs_nonneg e).trans he
  have hη : 0 ≤ η := (abs_nonneg (r - e)).trans hre
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < β := hm.trans_le hβ
  have hai : |α⁻¹| ≤ 2 / m := by
    rw [abs_of_pos (inv_pos.mpr hα0)]
    calc α⁻¹ ≤ (m / 2)⁻¹ := inv_anti₀ (by positivity) hα
         _ = 2 / m := by ring
  have hbi : |β⁻¹| ≤ 1 / m := by
    rw [abs_of_pos (inv_pos.mpr hβ0), one_div]
    exact inv_anti₀ hm hβ
  have hβα : |β - α| ≤ η / m := by simpa only [abs_sub_comm] using hαβ
  have hid : r / α - e / β = (r - e) * α⁻¹ + e * (β - α) * α⁻¹ * β⁻¹ := by
    field_simp [hα0.ne', hβ0.ne']
    ring
  rw [hid]
  calc |(r - e) * α⁻¹ + e * (β - α) * α⁻¹ * β⁻¹|
      ≤ |(r - e) * α⁻¹| + |e * (β - α) * α⁻¹ * β⁻¹| := abs_add_le _ _
    _ ≤ η * (2 / m) + B * (η / m) * (2 / m) * (1 / m) := by
      simp only [abs_mul]
      gcongr
    _ = 2 * (1 + B / m ^ 2) * η / m := by ring


/-- Positive denominator margins control a product quotient under three scalar perturbations. -/
theorem abs_mul_div_sub_mul_div_le {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a d x y r s B μ η : K}
    (hμ : 0 < μ) (ha : μ / 2 ≤ a) (hd : μ ≤ d)
    (hy : |y| ≤ 2 * B) (hr : |r| ≤ B) (hs : |s| ≤ B)
    (hxr : |x - r| ≤ η) (hys : |y - s| ≤ η) (had : |a - d| ≤ η) :
    |x * y / a - r * s / d| ≤
      (6 * (B / μ) + 2 * (B / μ) ^ 2) * η := by
  have hB : 0 ≤ B := (abs_nonneg r).trans hr
  have hη : 0 ≤ η := (abs_nonneg (x - r)).trans hxr
  have ha0 : 0 < a := lt_of_lt_of_le (by linarith) ha
  have hd0 : 0 < d := hμ.trans_le hd
  have hai : |a⁻¹| ≤ 2 / μ := by
    rw [abs_of_pos (inv_pos.mpr ha0)]
    calc a⁻¹ ≤ (μ / 2)⁻¹ := inv_anti₀ (by positivity) ha
         _ = 2 / μ := by ring
  have hdi : |d⁻¹| ≤ 1 / μ := by
    rw [abs_of_pos (inv_pos.mpr hd0), one_div]
    exact inv_anti₀ hμ hd
  have hda : |d - a| ≤ η := by simpa only [abs_sub_comm] using had
  have he : x * y / a - r * s / d =
      (x - r) * y * a⁻¹ + r * (y - s) * a⁻¹ + r * s * (d - a) * a⁻¹ * d⁻¹ := by
    field_simp [ha0.ne', hd0.ne']
    ring
  rw [he]
  calc |(x - r) * y * a⁻¹ + r * (y - s) * a⁻¹ + r * s * (d - a) * a⁻¹ * d⁻¹|
      ≤ |(x - r) * y * a⁻¹| + |r * (y - s) * a⁻¹| +
          |r * s * (d - a) * a⁻¹ * d⁻¹| := abs_add_three _ _ _
    _ ≤ η * (2 * B) * (2 / μ) + B * η * (2 / μ) +
          B * B * η * (2 / μ) * (1 / μ) := by
      simp only [abs_mul]
      gcongr
    _ = (6 * (B / μ) + 2 * (B / μ) ^ 2) * η := by ring
