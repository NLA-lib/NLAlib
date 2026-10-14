/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Optimising `a / u + b u` over `u > 0`

If `x ≤ a / u + b u` for every `u > 0`, with `a, b ≥ 0`, then `x ≤ √(4ab)`, the minimum of the
right-hand side (at `u = √(a / b)`). This is the step that turns a family of bounds indexed by a
free parameter (the `θ` of a Chernoff bound) into a mean bound. Upstream candidate for
`Mathlib.Analysis.Real.Sqrt`.

## Main results

* `Real.le_sqrt_of_forall_le_div_add_mul`.
-/

@[expose] public section

namespace Real

/-- **Optimising `a / u + b u`**: if `x ≤ a / u + b u` for every `u > 0`, with `a, b ≥ 0`, then
`x ≤ √(4ab)`. -/
theorem le_sqrt_of_forall_le_div_add_mul {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ u, 0 < u → x ≤ a / u + b * u) : x ≤ √(4 * a * b) := by
  rcases ha.eq_or_lt with rfl | ha'
  · refine le_trans ?_ (Real.sqrt_nonneg _)
    by_contra hx
    push Not at hx
    have h1 := h (x / (2 * (b + 1))) (by positivity)
    rw [zero_div, zero_add] at h1
    have h2 : b * (x / (2 * (b + 1))) < x := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases hb.eq_or_lt with rfl | hb'
  · refine le_trans ?_ (Real.sqrt_nonneg _)
    by_contra hx
    push Not at hx
    have h1 := h (2 * a / x) (by positivity)
    rw [zero_mul, add_zero, div_div_eq_mul_div] at h1
    have h2 : a * x / (2 * a) = x / 2 := by field_simp
    linarith
  set p := √a with hp
  set q := √b with hq
  have hp0 : 0 < p := Real.sqrt_pos.2 ha'
  have hq0 : 0 < q := Real.sqrt_pos.2 hb'
  have hpa : p ^ 2 = a := Real.sq_sqrt ha
  have hqb : q ^ 2 = b := Real.sq_sqrt hb
  have h1 := h (p / q) (div_pos hp0 hq0)
  have h4 : 4 * a * b = (2 * p * q) ^ 2 := by rw [← hpa, ← hqb]; ring
  rw [h4, Real.sqrt_sq (by positivity)]
  have h5 : a / (p / q) + b * (p / q) = 2 * p * q := by
    rw [← hpa, ← hqb]
    field_simp
    ring
  linarith

end Real
