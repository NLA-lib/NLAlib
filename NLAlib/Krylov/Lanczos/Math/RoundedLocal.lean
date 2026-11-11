/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Numerical local defects of a rounded Lanczos step

Componentwise bounds supplied by actual vector calls give the Euclidean local-error bounds
used by the Lanczos stability analysis. The normalization estimate retains separate self-dot,
square-root and component-division tolerances. It includes a zero terminal coefficient and
does not assume the desired normalization defect as an input.

## Main results

* `NLAlib.Krylov.Lanczos.norm_sub_add_smul_le_of_componentwise` bounds a rounded update.
* `NLAlib.Krylov.Lanczos.abs_dotProduct_sub_le_of_componentwise` bounds a rounded projection.
* `NLAlib.Krylov.Lanczos.normalization_bounds_of_self_dot_sqrt_div` derives the normalization
  residual and near-unit property from the actual three arithmetic bounds.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open scoped Matrix

variable {n : Type*} [Fintype n]

private theorem norm_abs (x : n → ℝ) :
    ‖WithLp.toLp 2 (fun i => |x i|)‖ = ‖WithLp.toLp 2 x‖ := by
  simpa only [Real.norm_eq_abs] using EuclideanSpace.norm_toLp_norm x

/-- A componentwise axpy envelope gives the Euclidean update bound used for both Lanczos
subtractions. The bound includes zero-dimensional vectors. [Higham2002, §3.1]. -/
theorem norm_sub_add_smul_le_of_componentwise {e a : ℝ} {x y z : n → ℝ}
    (he : 0 ≤ e)
    (h : ∀ i, |(y + a • x - z) i| ≤ e * (|y i| + |a * x i|)) :
    ‖WithLp.toLp 2 (y + a • x - z)‖ ≤
      e * (‖WithLp.toLp 2 y‖ + |a| * ‖WithLp.toLp 2 x‖) := by
  have hd := EuclideanSpace.norm_toLp_le_norm_toLp (x := y + a • x - z)
    (y := e • (fun i => |y i| + |a * x i|)) fun i => by
      change |(y + a • x - z) i| ≤ |e * (|y i| + |a * x i|)|
      rw [abs_of_nonneg (mul_nonneg he (add_nonneg (abs_nonneg _) (abs_nonneg _)))]
      exact h i
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg he] at hd
  have heq : (fun i => |y i| + |a * x i|) =
      (fun i => |y i|) + (fun i => |(a • x) i|) := rfl
  rw [heq, WithLp.toLp_add] at hd
  refine hd.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) he) |>.trans_eq ?_
  rw [norm_abs, norm_abs, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- The componentwise dot-product bound gives the norm-relative projection defect, with
no assumption on the norms of its two operands. [Higham2002, §3.1]. -/
theorem abs_dotProduct_sub_le_of_componentwise {e α : ℝ} {x y : n → ℝ}
    (he : 0 ≤ e) (h : |x ⬝ᵥ y - α| ≤ e * ∑ i, |x i * y i|) :
    |x ⬝ᵥ y - α| ≤ e * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  have hs : ∑ i, |x i * y i| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
    calc
      _ = (fun i => |x i|) ⬝ᵥ (fun i => |y i|) := by simp [dotProduct, abs_mul]
      _ ≤ |(fun i => |x i|) ⬝ᵥ (fun i => |y i|)| := le_abs_self _
      _ ≤ _ := by
        simpa only [norm_abs] using
          EuclideanSpace.abs_dotProduct_le_norm (fun i => |x i|) (fun i => |y i|)
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hs he])

/-- Componentwise division errors bound the normalization residual after multiplication by
the actual nonzero divisor. The divisor may have either sign. [Higham2002, §3.1]. -/
theorem norm_sub_smul_le_of_div_error {e β : ℝ} {z q : n → ℝ} (he : 0 ≤ e) (hβ : β ≠ 0)
    (h : ∀ i, |z i / β - q i| ≤ e * |z i / β|) :
    ‖WithLp.toLp 2 (z - β • q)‖ ≤ e * ‖WithLp.toLp 2 z‖ := by
  have hp (i : n) : |(z - β • q) i| ≤ e * |z i| + 0 := by
    have heq : (z i / β - q i) * β = z i - β * q i := by field_simp
    change |z i - β * q i| ≤ _
    calc
      _ = |(z i / β - q i) * β| := congrArg abs heq.symm
      _ ≤ (e * |z i / β|) * |β| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)
      _ = _ := by rw [mul_assoc, ← abs_mul, div_mul_cancel₀ _ hβ, add_zero]
  simpa only [mul_zero, add_zero] using
    EuclideanSpace.norm_toLp_le_mul_add_of_forall_abs_le he le_rfl hp

private theorem abs_sub_sqrt_le_of_relative_sq {r σ e : ℝ} (hr : 0 ≤ r) (hσ : 0 ≤ σ)
    (h : |σ - r ^ 2| ≤ e * r ^ 2) : |r - Real.sqrt σ| ≤ e * r := by
  rcases hr.eq_or_lt with hr | hr
  · have hr0 : r = 0 := hr.symm
    have hσ0 : σ = 0 := by
      have hz : |σ| ≤ 0 := by simpa only [hr0, zero_pow (by omega : 2 ≠ 0),
        sub_zero, mul_zero] using h
      exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg σ))
    simp only [hr0, hσ0, Real.sqrt_zero, sub_self, abs_zero, mul_zero, le_refl]
  · have hprod : |r - Real.sqrt σ| * (r + Real.sqrt σ) = |r ^ 2 - σ| := by
      rw [← abs_of_nonneg (add_nonneg hr.le (Real.sqrt_nonneg σ)), ← abs_mul]
      congr 1
      nlinarith [Real.sq_sqrt hσ]
    have hm : |r - Real.sqrt σ| * r ≤ e * r ^ 2 := by
      have hb : |r ^ 2 - σ| ≤ e * r ^ 2 := by simpa only [abs_sub_comm] using h
      have hl := mul_le_mul_of_nonneg_left
        (show r ≤ r + Real.sqrt σ from le_add_of_nonneg_right (Real.sqrt_nonneg σ))
        (abs_nonneg (r - Real.sqrt σ))
      exact hl.trans (hprod.le.trans hb)
    exact (mul_le_mul_iff_right₀ hr).mp
      (by simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hm)

/-- Self-dot error followed by square-root error gives a relative norm error with coefficient
$e_d+e_s(1+e_d)$. The computed squared norm is nonnegative. [Higham2002, §3.1]. -/
theorem abs_norm_sub_le_of_self_dot_sqrt {ed es σ β : ℝ} {z : n → ℝ}
    (hes : 0 ≤ es) (hσ : 0 ≤ σ)
    (hdot : |σ - ‖WithLp.toLp 2 z‖ ^ 2| ≤ ed * ‖WithLp.toLp 2 z‖ ^ 2)
    (hsqrt : |β - Real.sqrt σ| ≤ es * Real.sqrt σ) :
    |‖WithLp.toLp 2 z‖ - β| ≤ (ed + es * (1 + ed)) * ‖WithLp.toLp 2 z‖ := by
  have hr := abs_sub_sqrt_le_of_relative_sq (norm_nonneg _) hσ hdot
  have hup : Real.sqrt σ ≤ (1 + ed) * ‖WithLp.toLp 2 z‖ := by
    linarith [(abs_le.mp hr).1]
  have hsqrt' : |Real.sqrt σ - β| ≤ es * Real.sqrt σ := by
    simpa only [abs_sub_comm] using hsqrt
  calc
    _ ≤ |‖WithLp.toLp 2 z‖ - Real.sqrt σ| + |Real.sqrt σ - β| := abs_sub_le _ _ _
    _ ≤ ed * ‖WithLp.toLp 2 z‖ + es * ((1 + ed) * ‖WithLp.toLp 2 z‖) :=
      add_le_add hr (hsqrt'.trans (mul_le_mul_of_nonneg_left hup hes))
    _ = _ := by ring

private theorem abs_norm_sq_sub_one_le_of_normalization {e g β : ℝ} {z q : n → ℝ}
    (hg : g < 1) (hβ : 0 < β)
    (hscale : |‖WithLp.toLp 2 z‖ - β| ≤ g * ‖WithLp.toLp 2 z‖)
    (hres : ‖WithLp.toLp 2 (z - β • q)‖ ≤ e * ‖WithLp.toLp 2 z‖) :
    let t := (e + g) / (1 - g)
    |‖WithLp.toLp 2 q‖ ^ 2 - 1| ≤ t * (2 + t) := by
  intro t
  have hr : 0 < ‖WithLp.toLp 2 z‖ := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro hz
    have hzero := hscale
    rw [← hz, zero_sub, abs_neg, abs_of_pos hβ, mul_zero] at hzero
    linarith
  have hd : |‖WithLp.toLp 2 z‖ - β * ‖WithLp.toLp 2 q‖| ≤ e * ‖WithLp.toLp 2 z‖ := by
    have hh := abs_norm_sub_norm_le (WithLp.toLp 2 z) (WithLp.toLp 2 (β • q))
    rw [← WithLp.toLp_sub, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hβ] at hh
    exact hh.trans hres
  have hl : (1 - g) * ‖WithLp.toLp 2 z‖ ≤ β := by linarith [(abs_le.mp hscale).2]
  have hm : β * |‖WithLp.toLp 2 q‖ - 1| ≤ (e + g) * ‖WithLp.toLp 2 z‖ := by
    have hh := abs_sub_le (β * ‖WithLp.toLp 2 q‖) ‖WithLp.toLp 2 z‖ β
    rw [show β * ‖WithLp.toLp 2 q‖ - β = β * (‖WithLp.toLp 2 q‖ - 1) by ring,
      abs_mul, abs_of_pos hβ, abs_sub_comm (β * ‖WithLp.toLp 2 q‖)] at hh
    linarith
  have hunit : |‖WithLp.toLp 2 q‖ - 1| ≤ t := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - g)).mpr
    have hh := mul_le_mul_of_nonneg_right hl (abs_nonneg (‖WithLp.toLp 2 q‖ - 1))
    exact (mul_le_mul_iff_right₀ hr).mp (by nlinarith [hm, hh])
  have ht : 0 ≤ t := (abs_nonneg _).trans hunit
  have hp : |‖WithLp.toLp 2 q‖ + 1| ≤ 2 + t := by
    rw [abs_of_nonneg (by positivity)]
    linarith [(abs_le.mp hunit).2]
  rw [show ‖WithLp.toLp 2 q‖ ^ 2 - 1 =
    (‖WithLp.toLp 2 q‖ - 1) * (‖WithLp.toLp 2 q‖ + 1) by ring, abs_mul]
  exact mul_le_mul hunit hp (abs_nonneg _) ht

/-- Actual self-dot, square-root and guarded component-division bounds imply a nonnegative
stored norm, the Lanczos normalization residual bound, and a squared near-unit bound whenever
the stored norm is nonzero. The terminal zero-norm case is included.
[Higham2002, §3.1]. -/
theorem normalization_bounds_of_self_dot_sqrt_div {ed es eq σ β : ℝ} {z q : n → ℝ}
    (hed : 0 ≤ ed) (hes : 0 ≤ es) (heq : 0 ≤ eq) (hσ : 0 ≤ σ)
    (hdot : |σ - ‖WithLp.toLp 2 z‖ ^ 2| ≤ ed * ‖WithLp.toLp 2 z‖ ^ 2)
    (hsqrt : |β - Real.sqrt σ| ≤ es * Real.sqrt σ)
    (hdiv : β ≠ 0 → ∀ i, |z i / β - q i| ≤ eq * |z i / β|)
    (hg : ed + es * (1 + ed) < 1) :
    0 ≤ β ∧ ‖WithLp.toLp 2 (z - β • q)‖ ≤ eq * ‖WithLp.toLp 2 z‖ ∧
      (β ≠ 0 → let t := (eq + (ed + es * (1 + ed))) / (1 - (ed + es * (1 + ed)))
        |‖WithLp.toLp 2 q‖ ^ 2 - 1| ≤ t * (2 + t)) := by
  have hscale := abs_norm_sub_le_of_self_dot_sqrt hes hσ hdot hsqrt
  have hes1 : es < 1 := by nlinarith [mul_nonneg hed hes]
  have hβ : 0 ≤ β := by
    have hl := (abs_le.mp hsqrt).1
    have hp := mul_nonneg (by linarith : 0 ≤ 1 - es) (Real.sqrt_nonneg σ)
    nlinarith
  have hres : ‖WithLp.toLp 2 (z - β • q)‖ ≤ eq * ‖WithLp.toLp 2 z‖ := by
    by_cases hb : β = 0
    · have hz : ‖WithLp.toLp 2 z‖ = 0 := by
        rw [hb, sub_zero, abs_of_nonneg (norm_nonneg _)] at hscale
        nlinarith [norm_nonneg (WithLp.toLp 2 z)]
      simp only [hb, zero_smul, sub_zero, hz, mul_zero, le_refl]
    · exact norm_sub_smul_le_of_div_error heq hb (hdiv hb)
  exact ⟨hβ, hres, fun hb =>
    abs_norm_sq_sub_one_le_of_normalization hg (lt_of_le_of_ne hβ hb.symm) hscale hres⟩

end NLAlib.Krylov.Lanczos
