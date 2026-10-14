/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Hadamard
public import NLAlib.Matrix.Inequalities.Block
public import NLAlib.Matrix.Inequalities.Determinant

/-!
# Inequalities for the Hadamard product

Mathlib has the Schur product theorem (`Matrix.PosSemidef.hadamard`). This file adds what follows
from it: monotonicity of the Hadamard product in the Loewner order, lower bounds for its smallest
eigenvalue, the bound of its spectral norm, the inequality between the inverse of a Hadamard
product and the Hadamard product of the inverses, and Oppenheim's determinant inequality.

## Main results

* `Matrix.PosSemidef.hadamard_le_hadamard_of_le`: monotonicity.
* `Matrix.PosSemidef.smul_diagonal_le_hadamard`: a lower bound from a lower bound of one factor.
* `NLAlib.specNorm_hadamard_le`: `‖A ⊙ B‖₂ ≤ ‖A‖₂ ‖B‖₂`.
* `Matrix.PosDef.inv_hadamard_le_hadamard_inv`, `Matrix.PosDef.one_le_hadamard_inv`.
* `Matrix.PosDef.smul_one_le_hadamard_of_smul_inv_le`: the smallest eigenvalue of `A ⊙ B` is at
  least the smallest eigenvalue of `A * B`, in Loewner form.
* `Matrix.PosSemidef.re_det_mul_prod_re_diag_le_re_det_hadamard`: Oppenheim's inequality.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Norms -/

omit [DecidableEq n] in
/-- **The spectral norm is submultiplicative for the Hadamard product**:
`‖A ⊙ B‖₂ ≤ ‖A‖₂ ‖B‖₂`. [HornJohnson1991, Theorem 5.5.1]. -/
theorem specNorm_hadamard_le (A B : Matrix m n 𝕜) :
    specNorm (A ⊙ B) ≤ specNorm A * specNorm B := by
  classical
  rcases (specNorm_nonneg A).eq_or_lt with ha | ha
  · rw [specNorm_eq_zero_iff.mp ha.symm, Matrix.zero_hadamard, specNorm_zero, zero_mul]
  rcases (specNorm_nonneg B).eq_or_lt with hb | hb
  · rw [specNorm_eq_zero_iff.mp hb.symm, Matrix.hadamard_zero, specNorm_zero, mul_zero]
  have hA : (Matrix.fromBlocks 1 ((specNorm A)⁻¹ • A) ((specNorm A)⁻¹ • A)ᴴ 1).PosSemidef := by
    rw [posSemidef_fromBlocks_one_iff_specNorm_le_one, specNorm_real_smul,
      abs_of_pos (inv_pos.mpr ha), inv_mul_cancel₀ ha.ne']
  have hB : (Matrix.fromBlocks 1 ((specNorm B)⁻¹ • B) ((specNorm B)⁻¹ • B)ᴴ 1).PosSemidef := by
    rw [posSemidef_fromBlocks_one_iff_specNorm_le_one, specNorm_real_smul,
      abs_of_pos (inv_pos.mpr hb), inv_mul_cancel₀ hb.ne']
  have e : ∀ X Y : Matrix m n 𝕜, Matrix.fromBlocks 1 X Xᴴ 1 ⊙ Matrix.fromBlocks 1 Y Yᴴ 1 =
      Matrix.fromBlocks 1 (X ⊙ Y) (X ⊙ Y)ᴴ 1 := by
    intro X Y
    ext (i | i) (j | j) <;> simp [Matrix.hadamard_apply, Matrix.one_apply]
  have h := hA.hadamard hB
  rw [e, posSemidef_fromBlocks_one_iff_specNorm_le_one, Matrix.smul_hadamard,
    Matrix.hadamard_smul, smul_smul, specNorm_real_smul,
    abs_of_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hb)), ← mul_inv,
    inv_mul_le_iff₀ (mul_pos ha hb), mul_one] at h
  exact h

omit [DecidableEq n] in
/-- The Frobenius norm is submultiplicative for the Hadamard product. -/
theorem frobNorm_hadamard_le (A B : Matrix m n 𝕜) :
    frobNorm (A ⊙ B) ≤ frobNorm A * frobNorm B := by
  refine le_of_sq_le_sq ?_ (mul_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B))
  rw [mul_pow, frobNorm_sq_eq_sum, frobNorm_sq_eq_sum A, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.hadamard_apply, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le_frobNorm B i j) 2) (sq_nonneg _)

/-! ### Order -/

omit [Fintype n] [DecidableEq n] in
/-- **The Hadamard product with a positive semidefinite matrix is monotone.**
[HornJohnson1991, §5.2]. Port of `NLAlib.hadamard_le_hadamard_of_posSemidef_left`, there over
`ℝ`. -/
theorem _root_.Matrix.PosSemidef.hadamard_le_hadamard_of_le {A B C : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : B ≤ C) : A ⊙ B ≤ A ⊙ C := by
  rw [Matrix.le_iff] at h ⊢
  have e : A ⊙ C - A ⊙ B = A ⊙ (C - B) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.hadamard_apply, mul_sub]
  rw [e]
  exact hA.hadamard h

omit [Fintype n] [DecidableEq n] in
/-- A two-sided Loewner bound `-A ≤ B ≤ A` says that `A + B` and `A - B` are positive
semidefinite. -/
private theorem posSemidef_add_and_sub {A B : Matrix n n 𝕜} (hAB : -A ≤ B) (hBA : B ≤ A) :
    (A + B).PosSemidef ∧ (A - B).PosSemidef := by
  rw [Matrix.le_iff, sub_neg_eq_add, add_comm] at hAB
  exact ⟨hAB, Matrix.le_iff.mp hBA⟩

omit [Fintype n] [DecidableEq n] in
/-- A two-sided bound is preserved by Hadamard products, upper half: if `-A ≤ B ≤ A` and
`-C ≤ D ≤ C` then `B ⊙ D ≤ A ⊙ C`.
Port of `NLAlib.hadamard_le_hadamard_of_neg_le_of_le`, there over `ℝ`. -/
theorem hadamard_le_hadamard_of_neg_le_of_le {A B C D : Matrix n n 𝕜} (hAB : -A ≤ B)
    (hBA : B ≤ A) (hCD : -C ≤ D) (hDC : D ≤ C) : B ⊙ D ≤ A ⊙ C := by
  obtain ⟨hp, hm⟩ := posSemidef_add_and_sub hAB hBA
  obtain ⟨hp', hm'⟩ := posSemidef_add_and_sub hCD hDC
  have e : A ⊙ C - B ⊙ D = (1 / 2 : ℝ) • ((A + B) ⊙ (C - D) + (A - B) ⊙ (C + D)) := by
    ext i j
    simp only [Matrix.hadamard_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      RCLike.real_smul_eq_coe_mul]
    push_cast
    ring
  rw [Matrix.le_iff, e]
  exact ((hp.hadamard hm').add (hm.hadamard hp')).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

omit [Fintype n] [DecidableEq n] in
/-- A two-sided bound is preserved by Hadamard products, lower half: `-(A ⊙ C) ≤ B ⊙ D`.
Port of `NLAlib.neg_hadamard_le_hadamard_of_neg_le_of_le`, there over `ℝ`. -/
theorem neg_hadamard_le_hadamard_of_neg_le_of_le {A B C D : Matrix n n 𝕜} (hAB : -A ≤ B)
    (hBA : B ≤ A) (hCD : -C ≤ D) (hDC : D ≤ C) : -(A ⊙ C) ≤ B ⊙ D := by
  obtain ⟨hp, hm⟩ := posSemidef_add_and_sub hAB hBA
  obtain ⟨hp', hm'⟩ := posSemidef_add_and_sub hCD hDC
  have e : B ⊙ D - -(A ⊙ C) = (1 / 2 : ℝ) • ((A + B) ⊙ (C + D) + (A - B) ⊙ (C - D)) := by
    ext i j
    simp only [Matrix.hadamard_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.neg_apply, RCLike.real_smul_eq_coe_mul]
    push_cast
    ring
  rw [Matrix.le_iff, e]
  exact ((hp.hadamard hp').add (hm.hadamard hm')).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

omit [Fintype n] in
/-- The Hadamard product with a real multiple of the identity keeps the diagonal. -/
private theorem smul_one_hadamard (a : ℝ) (B : Matrix n n 𝕜) :
    (a • (1 : Matrix n n 𝕜)) ⊙ B = a • Matrix.diagonal (fun i => B i i) := by
  rw [Matrix.smul_hadamard, Matrix.one_hadamard]
  rfl

omit [Fintype n] in
/-- **A lower bound for a Hadamard product.** If `a • 1 ≤ A` and `B` is positive semidefinite,
then `a • diagonal (diag B) ≤ A ⊙ B`. In particular the smallest eigenvalue of `A ⊙ B` is at
least `λ_min(A) · min_i B i i`. [HornJohnson1991, Theorem 5.3.4]. -/
theorem _root_.Matrix.PosSemidef.smul_diagonal_le_hadamard {A B : Matrix n n 𝕜} {a : ℝ}
    (hB : B.PosSemidef) (hA : a • (1 : Matrix n n 𝕜) ≤ A) :
    a • Matrix.diagonal (fun i => B i i) ≤ A ⊙ B := by
  have h := (Matrix.le_iff.mp hA).hadamard hB
  rwa [Matrix.le_iff, ← smul_one_hadamard, ← Matrix.sub_hadamard]

omit [Fintype n] in
/-- The upper companion: if `A ≤ b • 1` and `B` is positive semidefinite then
`A ⊙ B ≤ b • diagonal (diag B)`. -/
theorem _root_.Matrix.PosSemidef.hadamard_le_smul_diagonal {A B : Matrix n n 𝕜} {b : ℝ}
    (hB : B.PosSemidef) (hA : A ≤ b • (1 : Matrix n n 𝕜)) :
    A ⊙ B ≤ b • Matrix.diagonal (fun i => B i i) := by
  have h := (Matrix.le_iff.mp hA).hadamard hB
  rwa [Matrix.le_iff, ← smul_one_hadamard, ← Matrix.sub_hadamard]

omit [Fintype n] [DecidableEq n] in
/-- The Hadamard product of a positive definite matrix with a positive semidefinite matrix with
positive diagonal is positive definite. [HornJohnson1991, Theorem 5.2.1].
Port of `NLAlib.posDef_hadamard_of_posDef_of_diag_pos`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.hadamard_of_forall_diag_pos [Finite n] {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosSemidef) (hdiag : ∀ i, 0 < RCLike.re (B i i)) :
    (A ⊙ B).PosDef := by
  classical
  obtain ⟨a, ha, hle⟩ := hA.exists_pos_smul_one_le
  have hd : (a • Matrix.diagonal (fun i => B i i)).PosDef :=
    (Matrix.PosDef.diagonal fun i =>
      RCLike.pos_iff.mpr ⟨hdiag i, (RCLike.nonneg_iff.mp hB.diag_nonneg).2⟩).smul ha
  have h := hd.add_posSemidef (Matrix.le_iff.mp (hB.smul_diagonal_le_hadamard hle))
  rwa [add_sub_cancel] at h

/-! ### Inverses -/

/-- **The inverse of a Hadamard product is at most the Hadamard product of the inverses.**
[HornJohnson1991, Theorem 5.4.3 context].
Port of `NLAlib.inv_hadamard_le_hadamard_inv`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.inv_hadamard_le_hadamard_inv {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) : (A ⊙ B)⁻¹ ≤ A⁻¹ ⊙ B⁻¹ := by
  have h := (hA.kronecker hB).inv_submatrix_le (f := fun i : n => (i, i))
    fun _ _ he => congrArg Prod.fst he
  rwa [Matrix.inv_kronecker, ← Matrix.hadamard_eq_submatrix_kronecker,
    ← Matrix.hadamard_eq_submatrix_kronecker] at h

/-- **Fiedler's inequality**: `1 ≤ A ⊙ A⁻¹` for positive definite `A`.
[HornJohnson1991, Theorem 5.4.3]. Port of `NLAlib.one_le_hadamard_inv`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.one_le_hadamard_inv {A : Matrix n n 𝕜} (hA : A.PosDef) :
    1 ≤ A ⊙ A⁻¹ := by
  have h1 : (Matrix.fromBlocks A 1 1 A⁻¹).PosSemidef := by
    simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
      posSemidef_fromBlocks_conjTranspose_mul_inv_mul hA (1 : Matrix n n 𝕜)
  have h2 : (Matrix.fromBlocks A⁻¹ 1 1 A).PosSemidef := by
    simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
      Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)] using
      posSemidef_fromBlocks_conjTranspose_mul_inv_mul hA.inv (1 : Matrix n n 𝕜)
  have e : Matrix.fromBlocks A 1 1 A⁻¹ ⊙ Matrix.fromBlocks A⁻¹ 1 1 A =
      Matrix.fromBlocks (A ⊙ A⁻¹) 1 1 (A ⊙ A⁻¹) := by
    ext (i | i) (j | j) <;> simp [Matrix.hadamard_apply, Matrix.one_apply, mul_comm]
  have h := h1.hadamard h2
  rw [e] at h
  exact (posSemidef_fromBlocks_self_iff.mp h).2

/-- **A lower bound for a Hadamard product from the ordinary product.** For positive definite
`A` and `c ≥ 0`, if `c • A⁻¹ ≤ B` then `c • 1 ≤ A ⊙ B`. For Hermitian `B` the hypothesis says that
the eigenvalues of `A * B` are at least `c` (the lower half of
`Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset`, applied to `A⁻¹`), so this is
`λ_min(A ⊙ B) ≥ λ_min(A B)`. For `c < 0` the bound can fail, already for `B = c • A⁻¹`.
[HornJohnson2013, Theorem 7.7.18]; stated there for the smallest eigenvalues of two positive
definite matrices.
Port of `NLAlib.max_sInf_spectrum_mul_le_sInf_spectrum_hadamard`, there over `ℝ` for positive
definite `B` with `c` the infimum of the spectrum of `A * B`. -/
theorem _root_.Matrix.PosDef.smul_one_le_hadamard_of_smul_inv_le {A B : Matrix n n 𝕜} {c : ℝ}
    (hA : A.PosDef) (hc : 0 ≤ c) (h : c • A⁻¹ ≤ B) : c • (1 : Matrix n n 𝕜) ≤ A ⊙ B := by
  have h1 : c • (1 : Matrix n n 𝕜) ≤ c • (A ⊙ A⁻¹) :=
    smul_le_smul_of_nonneg_left hA.one_le_hadamard_inv hc
  have h2 := hA.posSemidef.hadamard_le_hadamard_of_le h
  rw [Matrix.hadamard_smul] at h2
  exact h1.trans h2

/-! ### Determinants -/

section Oppenheim

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] in
/-- The lower left block of a Hermitian block matrix. -/
private theorem toBlocks₂₁_eq {M : Matrix (ι ⊕ α) (ι ⊕ α) 𝕜} (hM : M.IsHermitian) :
    M.toBlocks₂₁ = M.toBlocks₁₂ᴴ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, hM.apply]

omit [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] in
/-- A Hermitian block matrix in terms of its blocks. -/
private theorem eq_fromBlocks_toBlocks {M : Matrix (ι ⊕ α) (ι ⊕ α) 𝕜} (hM : M.IsHermitian) :
    M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
  rw [← toBlocks₂₁_eq hM, Matrix.fromBlocks_toBlocks]

variable [Unique ι]

omit [Fintype α] [DecidableEq α] in
/-- An entry of `X * M⁻¹ * Y` when `M` is a one by one matrix. -/
private theorem mul_inv_mul_apply_of_unique (X : Matrix α ι 𝕜) (M : Matrix ι ι 𝕜)
    (Y : Matrix ι α 𝕜) (i j : α) :
    (X * M⁻¹ * Y) i j = X i default * (M default default)⁻¹ * Y default j := by
  simp [Matrix.mul_apply, Matrix.inv_subsingleton]

omit [Fintype α] [DecidableEq α] in
/-- The Schur complement of the leading entry of a Hadamard product is the Hadamard product of
a Schur complement with a trailing block, plus a Hadamard product of two matrices that are
positive semidefinite when the factors are. -/
private theorem schur_hadamard_eq (H K : Matrix (ι ⊕ α) (ι ⊕ α) 𝕜) :
    (H ⊙ K).toBlocks₂₂ - (H ⊙ K).toBlocks₂₁ * (H ⊙ K).toBlocks₁₁⁻¹ * (H ⊙ K).toBlocks₁₂ =
      (H.toBlocks₂₂ - H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂) ⊙ K.toBlocks₂₂ +
        (H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂) ⊙
          (K.toBlocks₂₂ - K.toBlocks₂₁ * K.toBlocks₁₁⁻¹ * K.toBlocks₁₂) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.hadamard_apply,
    mul_inv_mul_apply_of_unique, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
    Matrix.toBlocks₂₂, Matrix.of_apply, mul_inv]
  ring

/-- The induction step of Oppenheim's inequality: one more leading index. -/
private theorem re_det_mul_prod_le_step
    (ih : ∀ A B : Matrix α α 𝕜, A.PosDef → B.PosSemidef → (∀ i, 0 < RCLike.re (B i i)) →
      RCLike.re A.det * ∏ i, RCLike.re (B i i) ≤ RCLike.re (A ⊙ B).det)
    {H K : Matrix (ι ⊕ α) (ι ⊕ α) 𝕜} (hH : H.PosDef) (hK : K.PosSemidef)
    (hd : ∀ i, 0 < RCLike.re (K i i)) :
    RCLike.re H.det * ∏ i, RCLike.re (K i i) ≤ RCLike.re (H ⊙ K).det := by
  have hA : H.toBlocks₁₁.PosDef := hH.submatrix Sum.inl_injective
  have hA' : K.toBlocks₁₁.PosDef := by
    refine (hK.submatrix Sum.inl).posDef_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr ?_)
    rw [Matrix.det_unique, isUnit_iff_ne_zero]
    intro h0
    exact (hd (Sum.inl default)).ne' (by simpa [Matrix.toBlocks₁₁] using congrArg RCLike.re h0)
  let : Invertible K.toBlocks₁₁ := hA'.isUnit.invertible
  have hS : (H.toBlocks₂₂ - H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂).PosDef := by
    rw [toBlocks₂₁_eq hH.isHermitian]
    exact (posDef_fromBlocks_iff.mp (eq_fromBlocks_toBlocks hH.isHermitian ▸ hH)).2
  have hR : (H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂).PosSemidef := by
    rw [toBlocks₂₁_eq hH.isHermitian]
    exact hA.inv.posSemidef.conjTranspose_mul_mul_same _
  have hS' : (K.toBlocks₂₂ - K.toBlocks₂₁ * K.toBlocks₁₁⁻¹ * K.toBlocks₁₂).PosSemidef := by
    rw [toBlocks₂₁_eq hK.isHermitian]
    exact (Matrix.PosDef.fromBlocks₁₁ _ _ hA').mp
      (eq_fromBlocks_toBlocks hK.isHermitian ▸ hK)
  have hK₂ : K.toBlocks₂₂.PosSemidef := hK.submatrix Sum.inr
  have hAA' : (H ⊙ K).toBlocks₁₁.PosDef := hA.hadamard hA'
  have hle : (H.toBlocks₂₂ - H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂) ⊙ K.toBlocks₂₂ ≤
      (H ⊙ K).toBlocks₂₂ - (H ⊙ K).toBlocks₂₁ * (H ⊙ K).toBlocks₁₁⁻¹ * (H ⊙ K).toBlocks₁₂ := by
    rw [schur_hadamard_eq, Matrix.le_iff, add_sub_cancel_left]
    exact hR.hadamard hS'
  have h1 : RCLike.re (H.toBlocks₂₂ - H.toBlocks₂₁ * H.toBlocks₁₁⁻¹ * H.toBlocks₁₂).det *
      ∏ j, RCLike.re (K (Sum.inr j) (Sum.inr j)) ≤ _ := ih _ _ hS hK₂ fun j => hd (Sum.inr j)
  have h2 := (hS.posSemidef.hadamard hK₂).re_det_le_re_det_of_le hle
  have h11 : RCLike.re (H ⊙ K).toBlocks₁₁.det =
      RCLike.re H.toBlocks₁₁.det * RCLike.re (K (Sum.inl default) (Sum.inl default)) := by
    rw [← hA.isHermitian.re_det_mul, Matrix.det_unique, Matrix.det_unique]
    rfl
  have hp : 0 ≤ RCLike.re H.toBlocks₁₁.det := (RCLike.pos_iff.mp hA.det_pos).1.le
  rw [det_eq_det_toBlocks₁₁_mul_det H hA.isUnit,
    det_eq_det_toBlocks₁₁_mul_det (H ⊙ K) hAA'.isUnit, hA.isHermitian.re_det_mul,
    hAA'.isHermitian.re_det_mul, h11, Fintype.prod_sum_type,
    Fintype.prod_unique]
  calc RCLike.re H.toBlocks₁₁.det * _ * (_ * _) = RCLike.re H.toBlocks₁₁.det *
        RCLike.re (K (Sum.inl default) (Sum.inl default)) * (_ * _) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hp (hd _).le)

end Oppenheim

/-- Oppenheim's inequality is invariant under reindexing. -/
private theorem re_det_mul_prod_le_of_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β)
    (h : ∀ A B : Matrix α α 𝕜, A.PosDef → B.PosSemidef → (∀ i, 0 < RCLike.re (B i i)) →
      RCLike.re A.det * ∏ i, RCLike.re (B i i) ≤ RCLike.re (A ⊙ B).det)
    {A B : Matrix β β 𝕜} (hA : A.PosDef) (hB : B.PosSemidef)
    (hd : ∀ i, 0 < RCLike.re (B i i)) :
    RCLike.re A.det * ∏ i, RCLike.re (B i i) ≤ RCLike.re (A ⊙ B).det := by
  have h' := h (A.submatrix e e) (B.submatrix e e) (hA.submatrix e.injective) (hB.submatrix e)
    fun i => hd (e i)
  rw [Matrix.det_submatrix_equiv_self, ← Matrix.submatrix_hadamard,
    Matrix.det_submatrix_equiv_self] at h'
  simp only [Matrix.submatrix_apply] at h'
  rwa [e.prod_comp fun i => RCLike.re (B i i)] at h'

/-- Oppenheim's inequality for a positive definite matrix and a positive semidefinite matrix
with positive diagonal, by induction on the size. -/
private theorem re_det_mul_prod_le_of_posDef {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosSemidef) (hd : ∀ i, 0 < RCLike.re (B i i)) :
    RCLike.re A.det * ∏ i, RCLike.re (B i i) ≤ RCLike.re (A ⊙ B).det := by
  refine Finite.induction_empty_option
    (P := fun α => ∀ [Fintype α] [DecidableEq α] (A B : Matrix α α 𝕜), A.PosDef →
      B.PosSemidef → (∀ i, 0 < RCLike.re (B i i)) →
      RCLike.re A.det * ∏ i, RCLike.re (B i i) ≤ RCLike.re (A ⊙ B).det)
    ?_ ?_ ?_ n A B hA hB hd
  · intro α β e h _ _ A B hA hB hd
    classical
    have := Fintype.ofEquiv β e.symm
    exact re_det_mul_prod_le_of_equiv e (fun A B => h A B) hA hB hd
  · intro _ _ A B _ _ _
    simp
  · intro α _ ih _ _ A B hA hB hd
    classical
    exact re_det_mul_prod_le_of_equiv
      ((Equiv.sumComm Unit α).trans (Equiv.optionEquivSumPUnit α).symm)
      (fun H K hH hK hd' => re_det_mul_prod_le_step (fun A B => ih A B) hH hK hd') hA hB hd

/-- **Oppenheim's inequality**: `det A · ∏ B i i ≤ det (A ⊙ B)` for positive semidefinite `A`,
`B`. [HornJohnson2013, Theorem 7.8.16].
Port of `NLAlib.det_mul_prod_diag_le_det_hadamard`, there over `ℝ`.
Result: oppenheim-inequality -/
theorem _root_.Matrix.PosSemidef.re_det_mul_prod_re_diag_le_re_det_hadamard {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det * ∏ i, RCLike.re (B i i) ≤ RCLike.re (A ⊙ B).det := by
  have h0 : 0 ≤ RCLike.re (A ⊙ B).det := (RCLike.nonneg_iff.mp (hA.hadamard hB).det_nonneg).1
  by_cases hdet : A.det = 0
  · rw [hdet, map_zero, zero_mul]
    exact h0
  by_cases hzero : ∃ i, RCLike.re (B i i) = 0
  · obtain ⟨i, hi⟩ := hzero
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]
    exact h0
  refine re_det_mul_prod_le_of_posDef (hA.posDef_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet))) hB fun i => ?_
  exact lt_of_le_of_ne (RCLike.nonneg_iff.mp hB.diag_nonneg).1
    (Ne.symm fun hi => hzero ⟨i, hi⟩)

/-- The determinant of a Hadamard product dominates the product of the determinants:
`det A · det B ≤ det (A ⊙ B)`. [HornJohnson2013, Theorem 7.8.16]. -/
theorem _root_.Matrix.PosSemidef.re_det_mul_re_det_le_re_det_hadamard {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det * RCLike.re B.det ≤ RCLike.re (A ⊙ B).det :=
  (mul_le_mul_of_nonneg_left hB.re_det_le_prod_re_diag
    (RCLike.nonneg_iff.mp hA.det_nonneg).1).trans
    (hA.re_det_mul_prod_re_diag_le_re_det_hadamard hB)

end NLAlib
