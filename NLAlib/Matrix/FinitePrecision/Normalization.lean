/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Rounding
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# Relative norm and normalization error

Pure vector inequalities for componentwise relative rounding, decoded norm approximation,
and division by a stored norm. These statements use total real arithmetic and carry no
program execution premise.

## Main results

* `NLAlib.Computation.normalizationRoundingFactor_le` bounds the dimension-dependent defect.
* `NLAlib.Computation.RelErr.norm_sub_le` bounds componentwise forward error.
* `NLAlib.Computation.RelErr.norm_sub_smul_inv_norm_le` bounds input-direction error.
* `NLAlib.Computation.RelErr.abs_norm_sq_sub_one_le` bounds the squared norm defect.
-/

@[expose] public section

namespace NLAlib.Computation

open Finset

/-- Squared norm defect after a rounded norm and componentwise rounded division. The value is
currently <!-- value Computation.normalizationRoundingFactor n u -->
$$\frac{u+(1-u)^{-(n+1)}-1}{2-(1-u)^{-(n+1)}}
\left(2+\frac{u+(1-u)^{-(n+1)}-1}{2-(1-u)^{-(n+1)}}\right).$$
The divisions are total; theorems require the accumulated norm rounding factor to be below one. -/
noncomputable irreducible_def normalizationRoundingFactor (n : ℕ) (u : ℝ) : ℝ :=
  let t := (u + roundingFactor (n + 1) u) / (1 - roundingFactor (n + 1) u)
  t * (2 + t)

/-- The normalization defect factor is nonnegative at a nonnegative unit roundoff and
an accumulated rounding factor below one. -/
theorem normalizationRoundingFactor_nonneg {n : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hn : (n + 1 : ℕ) * u < 1) (hg : roundingFactor (n + 1) u < 1) :
    0 ≤ normalizationRoundingFactor n u := by
  rw [normalizationRoundingFactor_def]
  have hu1 : u < 1 := by
    have : u ≤ (n + 1 : ℕ) * u := le_mul_of_one_le_left hu
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    exact this.trans_lt hn
  have hγ := roundingFactor_nonneg (n := n + 1) hu hu1
  positivity

private theorem roundingFactor_succ_le_two_mul {n : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hsmall : (n + 1 : ℕ) * u ≤ 1 / 100) :
    roundingFactor (n + 1) u ≤ 2 * ((n + 1 : ℕ) * u) := by
  let q : ℝ := (n + 1 : ℕ) * u
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn : (n + 1 : ℕ) * u < 1 := by linarith
  apply (roundingFactor_le hu hn).trans
  change q / (1 - q) ≤ 2 * q
  apply (div_le_iff₀ (by change 0 < 1 - q; change q ≤ _ at hsmall; linarith)).mpr
  have hprod : 0 ≤ q * (1 - 2 * q) := mul_nonneg hq (by change q ≤ _ at hsmall; linarith)
  nlinarith

/-- At $(n+1)u\le1/100$, the squared normalization defect is at most $12(n+1)u$.
This explicitly retains the dimension dependence of the ordered dot product. -/
theorem normalizationRoundingFactor_le {n : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hsmall : (n + 1 : ℕ) * u ≤ 1 / 100) :
    normalizationRoundingFactor n u ≤ 12 * (n + 1 : ℕ) * u := by
  let q : ℝ := (n + 1 : ℕ) * u
  let g := roundingFactor (n + 1) u
  let t := (u + g) / (1 - g)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqs : q ≤ 1 / 100 := hsmall
  have hn : (n + 1 : ℕ) * u < 1 := by linarith
  have hu1 : u < 1 :=
    (le_mul_of_one_le_left hu (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))).trans_lt hn
  have hg : 0 ≤ g := roundingFactor_nonneg hu hu1
  have hgle : g ≤ 2 * q := roundingFactor_succ_le_two_mul hu hsmall
  have hgl : g < 1 := by linarith
  have huq : u ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hu]
  have ht : 0 ≤ t := div_nonneg (add_nonneg hu hg) (by linarith)
  have htle : t ≤ 4 * q := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - g)).mpr
    have hmult := mul_le_mul_of_nonneg_right hgle (by positivity : 0 ≤ 4 * q)
    have hprod : 0 ≤ q * (1 - 8 * q) := mul_nonneg hq (by linarith)
    nlinarith
  rw [normalizationRoundingFactor_def]
  change t * (2 + t) ≤ 12 * (n + 1 : ℕ) * u
  calc _ ≤ (4 * q) * (2 + 4 * q) :=
      mul_le_mul htle (by linarith) (by linarith) (by positivity)
    _ ≤ 12 * q := by
      have hprod : 0 ≤ q * (1 - 4 * q) := mul_nonneg hq (by linarith)
      nlinarith
    _ = _ := by dsimp [q]; ring

/-- One more rounded addition is bounded by the next accumulated factor. -/
theorem roundingFactor_add_mul_le {n : ℕ} {u : ℝ} (hu : 0 ≤ u)
    (hn : (n + 1 : ℕ) * u < 1) :
    roundingFactor n u + u * (1 + roundingFactor n u) ≤ roundingFactor (n + 1) u := by
  have hu1 : u < 1 := by
    have hcast : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    exact (le_mul_of_one_le_left hu hcast).trans_lt (by simpa using hn)
  have hγ := roundingFactor_nonneg (n := n) hu hu1
  have h₁ := le_roundingFactor_one (u := u) hu1
  have hprod := roundingFactor_add_add_mul (k := n) (j := 1) (u := u)
  nlinarith

/-- A relative squared-norm estimate controls its nonnegative square root. -/
theorem abs_sub_sqrt_le_roundingFactor {n : ℕ} {u r s : ℝ}
    (hu : 0 ≤ u) (hn : n * u < 1) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : |r ^ 2 - s| ≤ roundingFactor n u * r ^ 2) :
    |r - Real.sqrt s| ≤ roundingFactor n u * r := by
  have hγ := roundingFactor_nonneg_of_mul_lt_one hu hn
  have hsq := Real.sq_sqrt hs
  have hroot := Real.sqrt_nonneg s
  have hprod : |r - Real.sqrt s| * (r + Real.sqrt s) = |r ^ 2 - s| := by
    rw [← abs_of_nonneg (add_nonneg hr hroot), ← abs_mul]
    congr 1
    nlinarith
  rcases hr.eq_or_lt with rfl | hr
  · have hs0 : s = 0 := by
      simp only [zero_pow (show (2 : ℕ) ≠ 0 by omega), mul_zero, zero_sub, abs_neg] at h
      exact le_antisymm ((le_abs_self s).trans h) hs
    simp only [hs0, Real.sqrt_zero, sub_self, abs_zero, mul_zero, le_refl]
  · have hmul : |r - Real.sqrt s| * r ≤ roundingFactor n u * r ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg (r - Real.sqrt s)) hroot]
    exact (mul_le_mul_iff_left₀ hr).mp (by nlinarith [hmul])

/-- Componentwise relative error bounds the Euclidean forward error by the same coefficient. -/
theorem RelErr.norm_sub_le {ι : Type*} [Fintype ι] {u : ℝ} {x y : ι → ℝ}
    (hu : 0 ≤ u) (h : ∀ i, RelErr u (x i) (y i)) :
    ‖WithLp.toLp 2 (x - y)‖ ≤ u * ‖WithLp.toLp 2 x‖ := by
  have hpoint : ∀ i, |x i - y i| ≤ u * |x i| := by
    intro i
    obtain ⟨δ, hδ, hy⟩ := h i
    rw [hy, show x i - x i * (1 + δ) = -δ * x i by ring, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  have hnorm := EuclideanSpace.norm_toLp_le_norm_toLp (x := x - y) (y := u • x)
    (fun i => by
      change |x i - y i| ≤ |u * x i|
      rw [abs_mul, abs_of_nonneg hu]
      exact hpoint i)
  simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu] using hnorm

/-- Rounded componentwise normalization need not preserve the exact input direction.
If the stored scale $q$ is nonnegative and approximates the input norm with relative bound $g$,
and each rescaled component has relative error at most $u$, the initial-direction mismatch
obeys $\|\mathbf{x}-q\mathbf{y}/\|\mathbf{y}\|\|\le(2u+g)\|\mathbf{x}\|$.
The statement also permits zero vectors; normalization uses total real inversion. -/
theorem RelErr.norm_sub_smul_inv_norm_le {ι : Type*} [Fintype ι]
    {u q g : ℝ} {x y : ι → ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hscale : |‖WithLp.toLp 2 x‖ - q| ≤ g * ‖WithLp.toLp 2 x‖)
    (h : ∀ i, RelErr u (x i) (q * y i)) :
    ‖WithLp.toLp 2 (x - q • (‖WithLp.toLp 2 y‖⁻¹ • y))‖ ≤
      (2 * u + g) * ‖WithLp.toLp 2 x‖ := by
  have hres := RelErr.norm_sub_le hu h
  change ‖WithLp.toLp 2 (x - q • y)‖ ≤ u * ‖WithLp.toLp 2 x‖ at hres
  have hresnorm : |q * ‖WithLp.toLp 2 y‖ - ‖WithLp.toLp 2 x‖| ≤
      u * ‖WithLp.toLp 2 x‖ := by
    have hnorm := abs_norm_sub_norm_le (WithLp.toLp 2 x) (WithLp.toLp 2 (q • y))
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq] at hnorm
    rw [abs_sub_comm, ← WithLp.toLp_sub] at hnorm
    exact hnorm.trans hres
  have hqa : q * |‖WithLp.toLp 2 y‖ - 1| ≤ (u + g) * ‖WithLp.toLp 2 x‖ := by
    have htri := abs_sub_le (q * ‖WithLp.toLp 2 y‖) ‖WithLp.toLp 2 x‖ q
    rw [show q * ‖WithLp.toLp 2 y‖ - q = q * (‖WithLp.toLp 2 y‖ - 1) by ring,
      abs_mul, abs_of_nonneg hq] at htri
    nlinarith
  have hnear : ‖WithLp.toLp 2 (q • y - q • (‖WithLp.toLp 2 y‖⁻¹ • y))‖ ≤
      q * |‖WithLp.toLp 2 y‖ - 1| := by
    rw [smul_smul, ← sub_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    by_cases ha : ‖WithLp.toLp 2 y‖ = 0
    · simp [ha, hq]
    · calc
        _ = |(q - q * ‖WithLp.toLp 2 y‖⁻¹) * ‖WithLp.toLp 2 y‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
        _ = |q * (‖WithLp.toLp 2 y‖ - 1)| := by congr 1; field_simp
        _ ≤ _ := by rw [abs_mul, abs_of_nonneg hq]
  have heq : x - q • (‖WithLp.toLp 2 y‖⁻¹ • y) =
      (x - q • y) + (q • y - q • (‖WithLp.toLp 2 y‖⁻¹ • y)) := by abel
  rw [heq, WithLp.toLp_add]
  exact (norm_add_le _ _).trans (by linarith [hnear.trans hqa])

/-- Relative error in a stored norm and componentwise error in division give a squared
Euclidean norm defect bounded by the normalization factor. -/
theorem RelErr.abs_norm_sq_sub_one_le {n : ℕ} {u q : ℝ} {x y : Fin n → ℝ}
    (hu : 0 ≤ u) (hn : (n + 1 : ℕ) * u < 1) (hsmall : roundingFactor (n + 1) u < 1)
    (hx : 0 < ‖WithLp.toLp 2 x‖)
    (hq : |‖WithLp.toLp 2 x‖ - q| ≤ roundingFactor (n + 1) u * ‖WithLp.toLp 2 x‖)
    (h : ∀ i, RelErr u (x i) (q * y i)) :
    |‖WithLp.toLp 2 y‖ ^ 2 - 1| ≤ normalizationRoundingFactor n u := by
  let r := ‖WithLp.toLp 2 x‖
  let a := ‖WithLp.toLp 2 y‖
  let g := roundingFactor (n + 1) u
  let t := (u + g) / (1 - g)
  have hu1 : u < 1 :=
    (le_mul_of_one_le_left hu (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))).trans_lt hn
  have hg : 0 ≤ g := roundingFactor_nonneg hu hu1
  have ht : 0 ≤ t := div_nonneg (add_nonneg hu hg) (by linarith)
  have hqpos : 0 < q := by
    have hupper := (abs_le.mp hq).2
    nlinarith [mul_pos (sub_pos.mpr hsmall) hx]
  have hres := RelErr.norm_sub_le hu h
  have hresnorm : |r - q * a| ≤ u * r := by
    have hnorm := abs_norm_sub_norm_le (WithLp.toLp 2 x) (WithLp.toLp 2 (q • y))
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos] at hnorm
    refine hnorm.trans ?_
    rw [← WithLp.toLp_smul, ← WithLp.toLp_sub]
    exact hres
  have hqa : q * |a - 1| ≤ (u + g) * r := by
    have htri := abs_sub_le (q * a) r q
    rw [show q * a - q = q * (a - 1) by ring, abs_mul, abs_of_pos hqpos] at htri
    have hres' : |q * a - r| ≤ u * r := by rwa [abs_sub_comm] at hresnorm
    nlinarith
  have hqlo : (1 - g) * r ≤ q := by
    have hupper := (abs_le.mp hq).2
    dsimp [r, g]
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hqlo (abs_nonneg (a - 1))
  have hcancel : (1 - g) * |a - 1| ≤ u + g :=
    (mul_le_mul_iff_right₀ hx).mp (by nlinarith [hqa, hprod])
  have hnear : |a - 1| ≤ t := (le_div_iff₀ (by linarith : 0 < 1 - g)).mpr
    (by nlinarith [hcancel])
  rw [normalizationRoundingFactor_def]
  change |a ^ 2 - 1| ≤ t * (2 + t)
  rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, abs_mul,
    abs_of_nonneg (by dsimp [a]; positivity : 0 ≤ a + 1)]
  have ha : a + 1 ≤ 2 + t := by have := (abs_le.mp hnear).2; linarith
  exact mul_le_mul hnear ha (by dsimp [a]; positivity) ht

end NLAlib.Computation
