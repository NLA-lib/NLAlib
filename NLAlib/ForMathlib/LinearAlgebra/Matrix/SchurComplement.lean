/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Jacobi's formula for the minors of an inverse

A minor of the inverse of an invertible matrix is, up to sign, the complementary minor of the
matrix divided by its determinant. Upstream candidate for
`Mathlib.LinearAlgebra.Matrix.SchurComplement`.

## Main results

* `Matrix.det_inv_toBlocks₂₂`: the block form, with no sign.
* `Matrix.det_inv_submatrix_inr`: the form for arbitrary complementary index selections.
-/

@[expose] public section

namespace Matrix

variable {K : Type*} [Field K] {n p q : Type*} [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-- **Jacobi's complementary minor formula**, block form. For an invertible block matrix `M`, the
determinant of the lower right block of `M⁻¹` is the determinant of the upper left block of `M`
divided by `det M`. The upper left block may be singular and either block may be empty.
[HornJohnson2013, §0.8.4]; here over any field.
Port of `NLAlib.det_inverse_bottomRight_eq_topLeft_div_det`, there over `ℝ`.
Result: jacobi-complementary-minors -/
theorem det_inv_toBlocks₂₂ (M : Matrix (p ⊕ q) (p ⊕ q) K) (hM : IsUnit M) :
    M⁻¹.toBlocks₂₂.det = M.toBlocks₁₁.det / M.det := by
  have hdet : IsUnit M.det := (isUnit_iff_isUnit_det M).mp hM
  have hmul := mul_nonsing_inv M hdet
  generalize M⁻¹ = N at hmul ⊢
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, M = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks M).symm⟩
  obtain ⟨W, X, Y, Z, rfl⟩ : ∃ W X Y Z, N = fromBlocks W X Y Z :=
    ⟨_, _, _, _, (fromBlocks_toBlocks N).symm⟩
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hmul
  obtain ⟨-, h₁₂, -, h₂₂⟩ := hmul
  have h : fromBlocks A B C D * fromBlocks 1 X 0 Z = fromBlocks A 0 C 1 := by
    rw [fromBlocks_multiply, h₁₂, h₂₂]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero]
  have h' := congrArg det h
  simp only [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, one_mul,
    mul_one] at h'
  rw [toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, eq_div_iff hdet.ne_zero, mul_comm, h']

/-- **Jacobi's complementary minor formula.** Let `er` and `ec` split the index type of an
invertible `A` into a selected part `p` and its complement `q`, for rows and for columns. The
minor of `A⁻¹` on rows `ec ∘ inr` and columns `er ∘ inr` is the minor of `A` on rows `er ∘ inl`
and columns `ec ∘ inl`, times the sign of the permutation `ec.trans er.symm`, divided by `det A`.
[HornJohnson2013, §0.8.4]; stated there for increasing index sets with the sign
`(-1) ^ (sum of the selected indices)`, here for any finite index types over any field.
Port of `NLAlib.det_inverse_complement_minor_eq_sign_mul_div`, there over `ℝ`.
Result: jacobi-complementary-minors -/
theorem det_inv_submatrix_inr (A : Matrix n n K) (hA : IsUnit A) (er ec : p ⊕ q ≃ n) :
    (A⁻¹.submatrix (fun i => ec (Sum.inr i)) (fun j => er (Sum.inr j))).det =
      (Equiv.Perm.sign (ec.trans er.symm) : ℤ) *
        (A.submatrix (fun i => er (Sum.inl i)) (fun j => ec (Sum.inl j))).det / A.det := by
  have h := det_inv_toBlocks₂₂ (A.submatrix er ec) ((isUnit_submatrix_equiv er ec).mpr hA)
  rw [inv_submatrix_equiv, det_submatrix_equiv_equiv] at h
  have hs : ((Equiv.Perm.sign (ec.trans er.symm) : ℤ) : K) *
      (Equiv.Perm.sign (ec.trans er.symm) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (ec.trans er.symm)) with hs | hs <;> simp [hs]
  have hA' : A.det ≠ 0 := ((isUnit_iff_isUnit_det A).mp hA).ne_zero
  have hs' : ((Equiv.Perm.sign (ec.trans er.symm) : ℤ) : K) ≠ 0 := left_ne_zero_of_mul_eq_one hs
  refine h.trans ?_
  rw [div_eq_div_iff (mul_ne_zero hs' hA') hA', mul_mul_mul_comm, hs, one_mul]
  rfl

end Matrix
