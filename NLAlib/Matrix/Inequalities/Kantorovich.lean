/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# The Kantorovich and Wielandt inequalities

For a positive definite matrix `A` with spectrum in `[a, b]`, the product of the quadratic forms
of `A` and `A⁻¹` at a unit vector is at most `(a + b)² / (4 a b)`, and the bilinear form at two
orthogonal vectors is controlled by `(b - a) / (b + a)`. These constants govern the convergence of
steepest descent and of the conjugate gradient method.

## Main results

* `NLAlib.add_smul_inv_le_smul_one`: the operator form `A + (a b) A⁻¹ ≤ (a + b) • 1`.
* `NLAlib.re_quadForm_mul_re_quadForm_inv_le`: the Kantorovich inequality.
* `Matrix.PosDef.re_quadForm_mul_re_quadForm_inv_le_conditionNumber`: with the condition number.
* `NLAlib.norm_sq_star_dotProduct_mulVec_le_of_dotProduct_eq_zero`: the Wielandt inequality.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
/-- A matrix above a positive multiple of the identity is positive definite. -/
private theorem posDef_of_smul_one_le {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) : A.PosDef := by
  have h := (Matrix.PosDef.one.smul ha).add_posSemidef (Matrix.le_iff.mp h₁)
  rwa [add_sub_cancel] at h

/-- **The Kantorovich inequality, operator form.** If `a • 1 ≤ A ≤ b • 1` with `0 < a`, then
`A + (a b) A⁻¹ ≤ (a + b) • 1`.
[HornJohnson2013, §7.4.12].
Port of `NLAlib.add_smul_inv_le_smul_one_of_sandwich`, there over `ℝ`. -/
theorem add_smul_inv_le_smul_one {A : Matrix n n 𝕜} {a b : ℝ} (ha : 0 < a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) :
    A + (a * b) • A⁻¹ ≤ (a + b) • (1 : Matrix n n 𝕜) := by
  have hA := posDef_of_smul_one_le ha h₁
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hQ : (0 : Matrix n n 𝕜) ≤ b • (1 : Matrix n n 𝕜) - A := sub_nonneg.mpr h₂
  have hR : (0 : Matrix n n 𝕜) ≤ 1 - a • A⁻¹ := by
    have h := (Matrix.le_iff.mp (inv_le_inv_smul_one_of_smul_one_le ha h₁)).smul ha.le
    rwa [smul_sub, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, ← Matrix.nonneg_iff_posSemidef]
      at h
  have hcomm : Commute (b • (1 : Matrix n n 𝕜) - A) (1 - a • A⁻¹) := by
    rw [commute_iff_eq]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
      Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet]
    module
  have h := hcomm.mul_nonneg hQ hR
  rw [← sub_nonneg]
  convert h using 1
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one,
    Matrix.mul_nonsing_inv _ hdet, smul_smul]
  module

/-- **The Kantorovich inequality.** If `a • 1 ≤ A ≤ b • 1` with `0 < a`, then for every vector
`x`, `(xᴴ A x) (xᴴ A⁻¹ x) ≤ (a + b)² / (4 a b) · ‖x‖⁴`.
[HornJohnson2013, Theorem 7.4.41].
Port of `NLAlib.quadForm_mul_quadForm_inv_le_of_sandwich`, there over `ℝ`.
Result: kantorovich-inequality -/
theorem re_quadForm_mul_re_quadForm_inv_le {A : Matrix n n 𝕜} {a b : ℝ} (ha : 0 < a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) (x : n → 𝕜) :
    RCLike.re (quadForm A x) * RCLike.re (quadForm A⁻¹ x) ≤
      (a + b) ^ 2 / (4 * a * b) * ‖WithLp.toLp 2 x‖ ^ 4 := by
  have hA := posDef_of_smul_one_le ha h₁
  have hs := hA.posSemidef.re_quadForm_nonneg x
  have ht := hA.inv.posSemidef.re_quadForm_nonneg x
  have hop := re_quadForm_le_re_quadForm_of_le (add_smul_inv_le_smul_one ha h₁ h₂) x
  have hlo := re_quadForm_le_re_quadForm_of_le h₁ x
  have hhi := re_quadForm_le_re_quadForm_of_le h₂ x
  rw [re_quadForm_real_smul_one] at hop hlo hhi
  rw [quadForm_add_left, map_add, RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left,
    RCLike.re_ofReal_mul] at hop
  rcases (sq_nonneg ‖WithLp.toLp 2 x‖).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero] at hhi
    rw [le_antisymm hhi hs, zero_mul, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← h0]
    simp
  · have hab : a ≤ b := le_of_mul_le_mul_right (hlo.trans hhi) h0
    have hb : 0 < b := ha.trans_le hab
    have h1 := pow_le_pow_left₀ (add_nonneg hs (mul_nonneg (mul_pos ha hb).le ht)) hop 2
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (RCLike.re (quadForm A x) - a * b * RCLike.re (quadForm A⁻¹ x))]

/-- **The Kantorovich inequality with the condition number**: for positive definite `A`,
`(xᴴ A x) (xᴴ A⁻¹ x) ≤ (κ + 1)² / (4 κ) · ‖x‖⁴` with `κ = conditionNumber A`.
[HornJohnson2013, Theorem 7.4.41].
Port of `NLAlib.quadForm_mul_quadForm_inv_le_moorePenroseConditionNumber_sqrt`, there over `ℝ`.
Result: kantorovich-inequality -/
theorem _root_.Matrix.PosDef.re_quadForm_mul_re_quadForm_inv_le_conditionNumber
    {A : Matrix n n 𝕜} (hA : A.PosDef) (x : n → 𝕜) :
    RCLike.re (quadForm A x) * RCLike.re (quadForm A⁻¹ x) ≤
      (conditionNumber A + 1) ^ 2 / (4 * conditionNumber A) * ‖WithLp.toLp 2 x‖ ^ 4 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim x 0, quadForm_zero_right]
    simp
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n :=
      ⟨Fintype.card n - 1, Nat.sub_add_cancel Fintype.card_pos⟩
    have ha : 0 < eigenvalue A k :=
      hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA k (by omega)
    have hb : 0 < eigenvalue A 0 :=
      hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA 0 Fintype.card_pos
    have h := re_quadForm_mul_re_quadForm_inv_le ha
      ((hA.isHermitian.smul_one_le_iff hk).mpr le_rfl) (hA.isHermitian.le_smul_one_iff.mpr le_rfl) x
    rw [hA.conditionNumber_eq hk]
    convert h using 2
    field_simp
    ring

omit [DecidableEq n] in
/-- The quadratic form of a Hermitian matrix at a real combination of two vectors. -/
private theorem re_quadForm_smul_add_smul {H : Matrix n n 𝕜} (hH : H.IsHermitian) (x y : n → 𝕜)
    (α β : ℝ) :
    RCLike.re (quadForm H ((α : 𝕜) • x + (β : 𝕜) • y)) =
      α ^ 2 * RCLike.re (quadForm H x) + 2 * (α * β * RCLike.re (star x ⬝ᵥ H *ᵥ y)) +
        β ^ 2 * RCLike.re (quadForm H y) := by
  rw [hH.re_quadForm_add, quadForm_smul_right, quadForm_smul_right, star_smul, smul_dotProduct,
    Matrix.mulVec_smul, dotProduct_smul]
  simp only [RCLike.star_def, RCLike.conj_ofReal, smul_eq_mul, ← mul_assoc, ← RCLike.ofReal_mul,
    RCLike.re_ofReal_mul]
  ring

/-- The Wielandt inequality for the real part of the bilinear form. -/
private theorem sq_re_star_dotProduct_mulVec_le {A : Matrix n n 𝕜} {a b : ℝ} (ha : 0 < a)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) {x y : n → 𝕜}
    (hxy : star x ⬝ᵥ y = 0) :
    RCLike.re (star x ⬝ᵥ A *ᵥ y) ^ 2 ≤
      ((b - a) / (b + a)) ^ 2 * RCLike.re (quadForm A x) * RCLike.re (quadForm A y) := by
  have hA := posDef_of_smul_one_le ha h₁
  rcases eq_or_ne x 0 with rfl | hx
  · simp [quadForm_zero_right]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [quadForm_zero_right]
  have hsx' := hA.re_quadForm_pos hx
  have hsy' := hA.re_quadForm_pos hy
  have hsx := hsx'.le
  have hsy := hsy'.le
  have hS := mul_pos hsx' hsy'
  have key : ∀ α β : ℝ,
      a * (α ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 + β ^ 2 * ‖WithLp.toLp 2 y‖ ^ 2) ≤
        α ^ 2 * RCLike.re (quadForm A x) + 2 * (α * β * RCLike.re (star x ⬝ᵥ A *ᵥ y)) +
          β ^ 2 * RCLike.re (quadForm A y) ∧
      α ^ 2 * RCLike.re (quadForm A x) + 2 * (α * β * RCLike.re (star x ⬝ᵥ A *ᵥ y)) +
          β ^ 2 * RCLike.re (quadForm A y) ≤
        b * (α ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 + β ^ 2 * ‖WithLp.toLp 2 y‖ ^ 2) := by
    intro α β
    have hN : ‖WithLp.toLp 2 ((α : 𝕜) • x + (β : 𝕜) • y)‖ ^ 2 =
        α ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 + β ^ 2 * ‖WithLp.toLp 2 y‖ ^ 2 := by
      have h := re_quadForm_smul_add_smul (Matrix.isHermitian_one (n := n) (α := 𝕜)) x y α β
      rwa [quadForm_one, quadForm_one, quadForm_one, Matrix.one_mulVec, hxy, RCLike.ofReal_re,
        RCLike.ofReal_re, RCLike.ofReal_re, map_zero, mul_zero, mul_zero, add_zero] at h
    have hlo := re_quadForm_le_re_quadForm_of_le h₁ ((α : 𝕜) • x + (β : 𝕜) • y)
    have hhi := re_quadForm_le_re_quadForm_of_le h₂ ((α : 𝕜) • x + (β : 𝕜) • y)
    rw [re_quadForm_real_smul_one, hN, re_quadForm_smul_add_smul hA.isHermitian] at hlo hhi
    exact ⟨hlo, hhi⟩
  have hNx : 0 < ‖WithLp.toLp 2 x‖ ^ 2 := by
    refine lt_of_le_of_ne (sq_nonneg _) fun h0 => ?_
    have := (key 1 0).2
    rw [← h0] at this
    linarith
  have hab : a ≤ b := by
    have := key 1 0
    nlinarith [this.1, this.2]
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨hp1, hp2⟩ := key (√(RCLike.re (quadForm A y))) (√(RCLike.re (quadForm A x)))
  obtain ⟨hm1, hm2⟩ := key (√(RCLike.re (quadForm A y))) (-√(RCLike.re (quadForm A x)))
  rw [neg_sq, Real.sq_sqrt hsx, Real.sq_sqrt hsy] at hm1 hm2
  rw [Real.sq_sqrt hsx, Real.sq_sqrt hsy] at hp1 hp2
  set W := √(RCLike.re (quadForm A y)) * √(RCLike.re (quadForm A x)) *
    RCLike.re (star x ⬝ᵥ A *ᵥ y) with hW
  have hW2 : W ^ 2 = RCLike.re (quadForm A x) * RCLike.re (quadForm A y) *
      RCLike.re (star x ⬝ᵥ A *ᵥ y) ^ 2 := by
    rw [hW, mul_pow, mul_pow, Real.sq_sqrt hsx, Real.sq_sqrt hsy]
    ring
  have hupper : (a + b) * W ≤
      (b - a) * (RCLike.re (quadForm A x) * RCLike.re (quadForm A y)) := by
    nlinarith [mul_le_mul_of_nonneg_left hp2 ha.le, mul_le_mul_of_nonneg_left hm1 hb.le]
  have hlower : -((b - a) * (RCLike.re (quadForm A x) * RCLike.re (quadForm A y))) ≤
      (a + b) * W := by
    nlinarith [mul_le_mul_of_nonneg_left hm2 ha.le, mul_le_mul_of_nonneg_left hp1 hb.le]
  have hsq := sq_le_sq' hlower hupper
  rw [mul_pow, hW2, mul_pow] at hsq
  have hsq' : (a + b) ^ 2 * RCLike.re (star x ⬝ᵥ A *ᵥ y) ^ 2 ≤
      (b - a) ^ 2 * (RCLike.re (quadForm A x) * RCLike.re (quadForm A y)) := by
    refine le_of_mul_le_mul_left ?_ hS
    nlinarith [hsq]
  rw [div_pow, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith [hsq']

/-- **The Wielandt inequality.** If `a • 1 ≤ A ≤ b • 1` with `0 < a` and `x`, `y` are
orthogonal, then `|xᴴ A y|² ≤ ((b - a) / (b + a))² (xᴴ A x) (yᴴ A y)`.
[HornJohnson2013, Theorem 7.4.34].
Port of `NLAlib.sq_bilinear_le_sq_ratio_mul_quadForm_of_sandwich`, there over `ℝ`.
Result: wielandt-inequality -/
theorem norm_sq_star_dotProduct_mulVec_le_of_dotProduct_eq_zero {A : Matrix n n 𝕜} {a b : ℝ}
    (ha : 0 < a) (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜))
    {x y : n → 𝕜} (hxy : star x ⬝ᵥ y = 0) :
    ‖star x ⬝ᵥ A *ᵥ y‖ ^ 2 ≤
      ((b - a) / (b + a)) ^ 2 * RCLike.re (quadForm A x) * RCLike.re (quadForm A y) := by
  have hA := posDef_of_smul_one_le ha h₁
  rcases eq_or_ne (star x ⬝ᵥ A *ᵥ y) 0 with hp | hp
  · rw [hp, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hA.posSemidef.re_quadForm_nonneg x))
      (hA.posSemidef.re_quadForm_nonneg y)
  · have hnp : (‖star x ⬝ᵥ A *ᵥ y‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hp)
    have h := sq_re_star_dotProduct_mulVec_le ha h₁ h₂ (x := x)
      (y := ((‖star x ⬝ᵥ A *ᵥ y‖ : 𝕜)⁻¹ * star (star x ⬝ᵥ A *ᵥ y)) • y)
      (by rw [dotProduct_smul, hxy, smul_zero])
    have h1 : ((‖star x ⬝ᵥ A *ᵥ y‖ : 𝕜)⁻¹ * star (star x ⬝ᵥ A *ᵥ y)) * (star x ⬝ᵥ A *ᵥ y) =
        (‖star x ⬝ᵥ A *ᵥ y‖ : 𝕜) := by
      rw [mul_assoc, RCLike.star_def, RCLike.conj_mul, sq, ← mul_assoc, inv_mul_cancel₀ hnp,
        one_mul]
    have h2 : star ((‖star x ⬝ᵥ A *ᵥ y‖ : 𝕜)⁻¹ * star (star x ⬝ᵥ A *ᵥ y)) *
        ((‖star x ⬝ᵥ A *ᵥ y‖ : 𝕜)⁻¹ * star (star x ⬝ᵥ A *ᵥ y)) = 1 := by
      rw [RCLike.star_def, RCLike.conj_mul, norm_mul, norm_inv, RCLike.norm_conj,
        RCLike.norm_ofReal, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp),
        RCLike.ofReal_one, one_pow]
    rwa [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, h1, RCLike.ofReal_re,
      quadForm_smul_right, h2, one_mul] at h

end NLAlib
