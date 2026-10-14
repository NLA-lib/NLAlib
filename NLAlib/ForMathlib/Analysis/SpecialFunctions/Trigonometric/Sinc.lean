/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Sine truncation

The sine truncation `c sin (y / c) = y sinc (y / c)` of a real number `y` at scale `c`: it is at
most `|y|` and `|c|` in absolute value, it does not increase the derivative of a function it is
composed with, and it tends to `y` as the scale grows. Composing a `C¹` function with it gives a
bounded `C¹` approximation whose energy is at most that of the function, which is how an
inequality for bounded test functions (a logarithmic Sobolev inequality) is extended to
finite-energy ones. Upstream candidate for `Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc`.

## Main results

* `Real.abs_mul_sin_inv_mul_le`: `|c sin (c⁻¹ y)| ≤ |y|`.
* `norm_fderiv_mul_sin_inv_mul_le`: `‖D (c sin (c⁻¹ f)) x‖ ≤ ‖D f x‖`.
* `Real.tendsto_natCast_add_one_mul_sin_inv_mul`: `(n + 1) sin (y / (n + 1)) → y`.
-/

@[expose] public section

open Filter Topology

namespace Real

/-- The sine truncation at any scale `c` is at most `|y|` in absolute value:
`|c sin (c⁻¹ y)| ≤ |y|`. -/
theorem abs_mul_sin_inv_mul_le (c y : ℝ) : |c * sin (c⁻¹ * y)| ≤ |y| := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [abs_mul]
  calc |c| * |sin (c⁻¹ * y)| ≤ |c| * |c⁻¹ * y| :=
        mul_le_mul_of_nonneg_left abs_sin_le_abs (abs_nonneg c)
    _ = |y| := by rw [abs_mul, abs_inv, ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hc), one_mul]

/-- The sine truncations at scales `n + 1` converge pointwise to the identity:
`(n + 1) sin (y / (n + 1)) → y`. -/
theorem tendsto_natCast_add_one_mul_sin_inv_mul (y : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * sin (((n : ℝ) + 1)⁻¹ * y)) atTop (𝓝 y) := by
  have hs : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * y) atTop (𝓝 0) := by
    simpa only [one_div, zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const y
  have h := (tendsto_const_nhds (x := y)).mul ((continuous_sinc.tendsto 0).comp hs)
  rw [sinc_zero, mul_one] at h
  refine h.congr fun n => ?_
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  by_cases hy : y = 0
  · simp [hy]
  · simp only [Function.comp]
    rw [sinc_of_ne_zero (mul_ne_zero (inv_ne_zero hn) hy)]
    field_simp

end Real

/-- The sine truncation at any scale `c` does not increase the derivative of a function it is
composed with: `‖D (c sin (c⁻¹ f)) x‖ ≤ ‖D f x‖` where `f` is differentiable. -/
theorem norm_fderiv_mul_sin_inv_mul_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} {x : F} (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    ‖fderiv ℝ (fun x => c * Real.sin (c⁻¹ * f x)) x‖ ≤ ‖fderiv ℝ f x‖ := by
  rw [((hf.hasFDerivAt.const_mul c⁻¹).sin.const_mul c).fderiv, norm_smul, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv]
  calc |c| * (|Real.cos (c⁻¹ * f x)| * (|c|⁻¹ * ‖fderiv ℝ f x‖))
      = (|c| * |c|⁻¹) * (|Real.cos (c⁻¹ * f x)| * ‖fderiv ℝ f x‖) := by ring
    _ ≤ 1 * (1 * ‖fderiv ℝ f x‖) := by
        gcongr
        · exact mul_inv_le_one
        · exact Real.abs_cos_le_one _
    _ = ‖fderiv ℝ f x‖ := by rw [one_mul, one_mul]
