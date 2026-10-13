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
  sorry

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
  sorry

end Matrix
