/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import NLAlib.Matrix.Basic.SchurComplement
public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Pseudoinverse.Pinv

/-!
# Positive semidefinite block matrices

Criteria for a Hermitian block matrix `fromBlocks A B Bᴴ C` to be positive semidefinite that do
not need an inverse: the Cauchy–Schwarz test on the off-diagonal block, the factorisation
`B = A^{1/2} X C^{1/2}` with a contraction `X`, and the special cases with identity or equal
diagonal blocks. The Schur complement criteria are in `NLAlib.Matrix.Basic.SchurComplement` and
`NLAlib.Matrix.Pseudoinverse.GeneralizedSchur`.

## Main results

* `Matrix.PosSemidef.norm_sq_star_dotProduct_mulVec_le`: Cauchy–Schwarz for a positive
  semidefinite form.
* `NLAlib.posSemidef_fromBlocks_iff_forall_norm_sq_le`: the bilinear test.
* `NLAlib.posSemidef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt`: the contraction factor.
* `NLAlib.posSemidef_fromBlocks_one_iff_specNorm_le_one`.
* `NLAlib.posSemidef_fromBlocks_self_iff`: equal diagonal blocks.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Cauchy–Schwarz -/

/-- **Cauchy–Schwarz for a positive semidefinite form**: `|xᴴ A y|² ≤ (xᴴ A x) (yᴴ A y)`.
[HornJohnson2013, §7.7].
Port of `NLAlib.sq_bilinear_le_quadForm_mul_of_posSemidef`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.norm_sq_star_dotProduct_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (x y : n → 𝕜) :
    ‖star x ⬝ᵥ A *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm A y) := by
  classical
  have hSS : (CFC.sqrt A)ᴴ * CFC.sqrt A = A := by
    rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  generalize CFC.sqrt A = S at hSS
  subst hSS
  rw [quadForm_conjTranspose_mul_self, quadForm_conjTranspose_mul_self, RCLike.ofReal_re,
    RCLike.ofReal_re, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    ← EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2

/-- The quadratic form of a Hermitian block matrix:
`(x, y)ᴴ [A B; Bᴴ C] (x, y) = xᴴ A x + 2 re (xᴴ B y) + yᴴ C y`, for the real parts.
Port of `NLAlib.quadForm_fromBlocks`, there over `ℝ`. -/
theorem re_quadForm_fromBlocks (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n n 𝕜)
    (x : m → 𝕜) (y : n → 𝕜) :
    RCLike.re (quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim x y)) =
      RCLike.re (quadForm A x) + 2 * RCLike.re (star x ⬝ᵥ B *ᵥ y) +
        RCLike.re (quadForm C y) := by
  have h : star y ⬝ᵥ (Bᴴ *ᵥ x) = star (star x ⬝ᵥ (B *ᵥ y)) := by
    rw [Matrix.star_dotProduct, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.dotProduct_mulVec]
  simp only [quadForm, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Function.star_sumElim, sumElim_dotProduct_sumElim, dotProduct_add, h, map_add,
    RCLike.star_def, RCLike.conj_re]
  ring

/-! ### The bilinear test -/

/-- If a Hermitian block matrix is positive semidefinite, its off-diagonal block satisfies the
Cauchy–Schwarz bound `|xᴴ B y|² ≤ (xᴴ A x) (yᴴ C y)`.
[HornJohnson2013, Theorem 7.7.7].
Port of `NLAlib.sq_bilinear_le_quadForm_mul_of_fromBlocks_posSemidef`, there over `ℝ`. -/
theorem norm_sq_star_dotProduct_mulVec_le_of_posSemidef_fromBlocks {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (x : m → 𝕜) (y : n → 𝕜) :
    ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm C y) := by
  have h1 := h.norm_sq_star_dotProduct_mulVec_le (Sum.elim x 0) (Sum.elim 0 y)
  simpa only [quadForm, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Function.star_sumElim, sumElim_dotProduct_sumElim, star_zero, Matrix.mulVec_zero,
    zero_dotProduct, dotProduct_zero, add_zero, zero_add] using h1

/-- **The bilinear test.** For positive semidefinite `A` and `C`, the block matrix
`fromBlocks A B Bᴴ C` is positive semidefinite exactly when
`|xᴴ B y|² ≤ (xᴴ A x) (yᴴ C y)` for all `x`, `y`.
[HornJohnson2013, Theorem 7.7.7].
Port of `NLAlib.posSemidef_fromBlocks_iff_bilinear_tests`, there over `ℝ`.
Result: block-positivity -/
theorem posSemidef_fromBlocks_iff_forall_norm_sq_le {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      ∀ (x : m → 𝕜) (y : n → 𝕜),
        ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm C y) := by
  refine ⟨norm_sq_star_dotProduct_mulVec_le_of_posSemidef_fromBlocks, fun h => ?_⟩
  have hH : (Matrix.fromBlocks A B Bᴴ C).IsHermitian :=
    Matrix.IsHermitian.fromBlocks hA.isHermitian rfl hC.isHermitian
  rw [posSemidef_iff_quadForm_nonneg]
  refine ⟨hH, fun z => ?_⟩
  obtain ⟨x, y, rfl⟩ : ∃ x y, z = Sum.elim x y :=
    ⟨z ∘ Sum.inl, z ∘ Sum.inr, (Sum.elim_comp_inl_inr z).symm⟩
  rw [← hH.coe_re_quadForm, RCLike.ofReal_nonneg, re_quadForm_fromBlocks]
  have ha := hA.re_quadForm_nonneg x
  have hc := hC.re_quadForm_nonneg y
  have hb := h x y
  have hre : RCLike.re (star x ⬝ᵥ B *ᵥ y) ^ 2 ≤ ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (RCLike.abs_re_le_norm _) 2
  have hsq : (2 * RCLike.re (star x ⬝ᵥ B *ᵥ y)) ^ 2 ≤
      (RCLike.re (quadForm A x) + RCLike.re (quadForm C y)) ^ 2 := by
    nlinarith [sq_nonneg (RCLike.re (quadForm A x) - RCLike.re (quadForm C y))]
  have := (abs_le_of_sq_le_sq' hsq (add_nonneg ha hc)).1
  linarith

/-! ### Contraction factors -/

/-- `[1 X; Xᴴ 1]` is positive semidefinite exactly when `‖X‖₂ ≤ 1`.
[HornJohnson2013, §7.7].
Port of `NLAlib.posSemidef_identity_fromBlocks_iff_specNorm_le_one`, there over `ℝ`. -/
theorem posSemidef_fromBlocks_one_iff_specNorm_le_one [DecidableEq m] [DecidableEq n]
    (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks 1 X Xᴴ 1).PosSemidef ↔ specNorm X ≤ 1 := by
  rw [posSemidef_fromBlocks_iff_exists, ← sq_le_one_iff₀ (specNorm_nonneg X),
    specNorm_sq_le_iff_conjTranspose_mul_self_le zero_le_one, one_smul, Matrix.le_iff]
  constructor
  · rintro ⟨-, Y, hY, h⟩
    rw [Matrix.one_mul] at hY
    subst hY
    rwa [Matrix.mul_one] at h
  · intro h
    exact ⟨Matrix.PosSemidef.one, X, Matrix.one_mul X, by rwa [Matrix.mul_one]⟩

/-- `1 - Xᴴ * X` is positive definite exactly when `‖X‖₂ < 1`. -/
private theorem posDef_one_sub_conjTranspose_mul_self_iff [DecidableEq n] (X : Matrix m n 𝕜) :
    (1 - Xᴴ * X).PosDef ↔ specNorm X < 1 := by
  have hH : (1 - Xᴴ * X).IsHermitian :=
    Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self X)
  have hq : ∀ x : n → 𝕜, RCLike.re (quadForm (1 - Xᴴ * X) x) =
      ‖WithLp.toLp 2 x‖ ^ 2 - ‖WithLp.toLp 2 (X *ᵥ x)‖ ^ 2 := by
    intro x
    rw [quadForm_sub_left, map_sub, quadForm_one, quadForm_conjTranspose_mul_self,
      RCLike.ofReal_re, RCLike.ofReal_re]
  constructor
  · intro h
    rcases isEmpty_or_nonempty n with hn | hn
    · rw [Subsingleton.elim X 0, specNorm_zero]
      exact zero_lt_one
    · obtain ⟨u, hu, hXu⟩ := exists_norm_eq_one_and_norm_mulVec_eq_specNorm X
      have hu0 : u ≠ 0 := by
        rintro rfl
        simp at hu
      have hpos := h.re_quadForm_pos hu0
      rw [hq, hu, hXu] at hpos
      nlinarith [specNorm_nonneg X]
  · intro h
    rw [posDef_iff_quadForm_pos]
    refine ⟨hH, fun x hx => ?_⟩
    rw [← hH.coe_re_quadForm, hq, RCLike.ofReal_pos]
    have hx' : 0 < ‖WithLp.toLp 2 x‖ := by
      have : WithLp.toLp 2 x ≠ 0 := by simpa using hx
      positivity
    have h1 := norm_toLp_mulVec_le X x
    have h2 : ‖WithLp.toLp 2 (X *ᵥ x)‖ < ‖WithLp.toLp 2 x‖ :=
      h1.trans_lt (by nlinarith)
    nlinarith [norm_nonneg (WithLp.toLp 2 (X *ᵥ x))]

/-- `[1 X; Xᴴ 1]` is positive definite exactly when `‖X‖₂ < 1`.
Port of `NLAlib.posDef_identity_fromBlocks_iff_specNorm_lt_one`, there over `ℝ`. -/
theorem posDef_fromBlocks_one_iff_specNorm_lt_one [DecidableEq m] [DecidableEq n]
    (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks 1 X Xᴴ 1).PosDef ↔ specNorm X < 1 := by
  rw [posDef_fromBlocks_iff, inv_one, Matrix.mul_one, posDef_one_sub_conjTranspose_mul_self_iff]
  exact and_iff_right Matrix.PosDef.one

/-- For Hermitian `S`, the form of `S * S` at `S⁺ u` is at most `‖u‖²`. -/
private theorem re_quadForm_mul_self_pinv_mulVec_le {S : Matrix n n 𝕜} (hS : S.IsHermitian)
    (u : n → 𝕜) :
    RCLike.re (quadForm (S * S) (pinv S *ᵥ u)) ≤ ‖WithLp.toLp 2 u‖ ^ 2 := by
  have e : S * S = Sᴴ * S := by rw [hS.eq]
  rw [e, quadForm_conjTranspose_mul_self, RCLike.ofReal_re, Matrix.mulVec_mulVec, mul_pinv]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((isStarProjection_rangeProjector S).norm_toLp_mulVec_le u) 2

/-- The contraction factor of a positive semidefinite block matrix, for any Hermitian square
roots `S`, `T` of the diagonal blocks: `X = S⁺ B T⁺`. -/
private theorem exists_specNorm_le_one_and_eq_mul_mul {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} {S : Matrix m m 𝕜} {T : Matrix n n 𝕜} (hS : S.IsHermitian)
    (hT : T.IsHermitian) (hA : S * S = A) (hC : T * T = C)
    (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    ∃ X : Matrix m n 𝕜, specNorm X ≤ 1 ∧ B = S * X * T := by
  classical
  subst hA hC
  have h' : (Matrix.fromBlocks (T * T) Bᴴ Bᴴᴴ (S * S)).PosSemidef := by
    have h1 := h.submatrix Sum.swap
    rwa [Matrix.fromBlocks_submatrix_sum_swap_sum_swap,
      ← Matrix.conjTranspose_conjTranspose B, Matrix.conjTranspose_conjTranspose Bᴴ] at h1
  have hB1 : S * pinv S * B = B := mul_pinv_mul_eq_of_range_le
    ((range_mulVecLin_le_of_posSemidef_fromBlocks h).trans
      (range_mulVecLin_le_iff_exists_mul.mpr ⟨S, rfl⟩))
  have hB2 : B * pinv T * T = B := by
    have h2 : T * pinv T * Bᴴ = Bᴴ := mul_pinv_mul_eq_of_range_le
      ((range_mulVecLin_le_of_posSemidef_fromBlocks h').trans
        (range_mulVecLin_le_iff_exists_mul.mpr ⟨T, rfl⟩))
    have h3 := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hT.pinv.eq, hT.eq,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc] at h3
  refine ⟨pinv S * B * pinv T, ?_, ?_⟩
  · refine specNorm_le_of_forall_norm_star_dotProduct_mulVec_le zero_le_one fun u v hu hv => ?_
    have e : star u ⬝ᵥ (pinv S * B * pinv T) *ᵥ v =
        star (pinv S *ᵥ u) ⬝ᵥ B *ᵥ (pinv T *ᵥ v) := by
      rw [Matrix.star_mulVec, hS.pinv.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec]
    have key := norm_sq_star_dotProduct_mulVec_le_of_posSemidef_fromBlocks h (pinv S *ᵥ u)
      (pinv T *ᵥ v)
    have h1 := re_quadForm_mul_self_pinv_mulVec_le hS u
    have h2 := re_quadForm_mul_self_pinv_mulVec_le hT v
    rw [hu, one_pow] at h1
    rw [hv, one_pow] at h2
    have h0 := (posSemidef_fromBlocks_iff_exists.mp h').1.re_quadForm_nonneg (pinv T *ᵥ v)
    rw [e, ← sq_le_one_iff₀ (norm_nonneg _)]
    exact key.trans (mul_le_one₀ h1 h0 h2)
  · calc B = S * pinv S * (B * pinv T * T) := by rw [hB2, hB1]
      _ = S * (pinv S * B * pinv T) * T := by simp only [Matrix.mul_assoc]

open scoped Classical in
/-- **The contraction factor.** For positive semidefinite `A` and `C`, the block matrix
`fromBlocks A B Bᴴ C` is positive semidefinite exactly when `B = A^{1/2} X C^{1/2}` for some
contraction `X`.
[HornJohnson2013, Theorem 7.7.9].
Port of `NLAlib.posSemidef_fromBlocks_iff_exists_sqrt_contraction_factor`, there over `ℝ`.
Result: block-positivity -/
theorem posSemidef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      ∃ X : Matrix m n 𝕜, specNorm X ≤ 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C := by
  have hS : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hT : (CFC.sqrt C).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hTT : CFC.sqrt C * CFC.sqrt C = C := CFC.sqrt_mul_sqrt_self C hC.nonneg
  refine ⟨exists_specNorm_le_one_and_eq_mul_mul hS hT hSS hTT, ?_⟩
  rintro ⟨X, hX, rfl⟩
  have h := ((posSemidef_fromBlocks_one_iff_specNorm_le_one X).mpr hX).conjTranspose_mul_mul_same
    (Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt C))
  have e : (Matrix.fromBlocks (CFC.sqrt A) (0 : Matrix m n 𝕜) (0 : Matrix n m 𝕜)
      (CFC.sqrt C))ᴴ * Matrix.fromBlocks 1 X Xᴴ 1 *
        Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt C) =
      Matrix.fromBlocks A (CFC.sqrt A * X * CFC.sqrt C) (CFC.sqrt A * X * CFC.sqrt C)ᴴ C := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hS.eq, hT.eq,
      Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one, Matrix.conjTranspose_mul, hSS, hTT, Matrix.mul_assoc]
  rwa [e] at h

omit [Fintype n] in
/-- For positive definite `A` and any `X`, `[A X; Xᴴ Xᴴ A⁻¹ X]` is positive semidefinite.
Port of `NLAlib.fromBlocks_inverse_gram_posSemidef`. -/
theorem posSemidef_fromBlocks_conjTranspose_mul_inv_mul [Finite n] [DecidableEq m]
    {A : Matrix m m 𝕜} (hA : A.PosDef) (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks A X Xᴴ (Xᴴ * A⁻¹ * X)).PosSemidef := by
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  refine posSemidef_fromBlocks_iff_exists.mpr
    ⟨hA.posSemidef, A⁻¹ * X, by rw [← Matrix.mul_assoc, hAA, Matrix.one_mul], ?_⟩
  have e : (A⁻¹ * X)ᴴ * A * (A⁻¹ * X) = Xᴴ * A⁻¹ * X := by
    rw [Matrix.conjTranspose_mul, hA.isHermitian.inv.eq, Matrix.mul_assoc, ← Matrix.mul_assoc A,
      hAA, Matrix.one_mul]
  rw [e, sub_self]
  exact Matrix.PosSemidef.zero

/-! ### Equal diagonal blocks -/

omit [Fintype n] in
/-- **Equal diagonal blocks.** `[A B; B A]` is positive semidefinite exactly when `-A ≤ B ≤ A`.
[HornJohnson2013, §7.7].
Port of `NLAlib.posSemidef_equal_diagonal_fromBlocks_iff_le`, there for positive semidefinite `B`
over `ℝ`. -/
theorem posSemidef_fromBlocks_self_iff [Finite n] {A B : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B B A).PosSemidef ↔ -A ≤ B ∧ B ≤ A := by
  classical
  have := Fintype.ofFinite n
  rw [Matrix.le_iff, Matrix.le_iff, sub_neg_eq_add]
  constructor
  · intro h
    have h1 := (h.conjTranspose_mul_mul_same (Matrix.fromRows (1 : Matrix n n 𝕜) 1)).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h2 := (h.conjTranspose_mul_mul_same (Matrix.fromRows (1 : Matrix n n 𝕜) (-1))).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows] at h1 h2
    constructor
    · convert h1 using 1
      simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      module
    · convert h2 using 1
      simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_neg, Matrix.one_mul,
        Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
      module
  · rintro ⟨h1, h2⟩
    have hd : (Matrix.fromBlocks (B + A) 0 (0 : Matrix n n 𝕜)ᴴ (A - B)).PosSemidef :=
      posSemidef_fromBlocks_iff_exists.mpr ⟨h1, 0, by simp, by simpa using h2⟩
    have h := (hd.conjTranspose_mul_mul_same
      (Matrix.fromBlocks 1 1 1 (-1) : Matrix (n ⊕ n) (n ⊕ n) 𝕜)).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_one, Matrix.conjTranspose_neg, Matrix.conjTranspose_zero,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_zero,
      add_zero, zero_add, Matrix.fromBlocks_smul]
    congr 1 <;> module

/-- For Hermitian `B`, the bound `-A ≤ B ≤ A` is the quadratic-form bound
`|xᴴ B x| ≤ xᴴ A x`. Port of `NLAlib.abs_quadForm_le_iff_neg_le_and_le`, there over `ℝ`. -/
theorem neg_le_and_le_iff_forall_abs_re_quadForm_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    -A ≤ B ∧ B ≤ A ↔ ∀ x : n → 𝕜, |RCLike.re (quadForm B x)| ≤ RCLike.re (quadForm A x) := by
  rw [hA.neg.le_iff_re_quadForm_le hB, hB.le_iff_re_quadForm_le hA, ← forall_and]
  simp only [quadForm_neg_left, map_neg, abs_le]

end NLAlib
