/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import NLAlib.Matrix.Factorizations.QR

/-!
# Gram–Schmidt orthogonalisation of the columns of a matrix

The Gram–Schmidt process applied to the columns of `A`, in the order of the column index, gives
`NLAlib.gramSchmidtQ A`, whose nonzero columns are orthonormal, and the upper triangular
`NLAlib.gramSchmidtR A = Qᴴ A` with nonnegative diagonal, with `A = Q R` always. A column of `Q`
vanishes exactly when the corresponding column of `A` depends on the earlier ones; for `A` of full
column rank this is the QR factorization with positive diagonal.

The process is Mathlib's `InnerProductSpace.gramSchmidtNormed` on the columns.

## Main definitions

* `NLAlib.gramSchmidtQ`, `NLAlib.gramSchmidtR`: the two factors.

## Main results

* `NLAlib.gramSchmidtQ_mul_gramSchmidtR`: `Q R = A`.
* `NLAlib.isUpperTriangular_gramSchmidtR`, `NLAlib.gramSchmidtR_apply_self_nonneg`.
* `NLAlib.gramSchmidtR_apply_self_smul_col`: the classical recursion.
* `NLAlib.isQR_gramSchmidt`: the QR factorization of a matrix of full column rank.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [LinearOrder n]
  [LocallyFiniteOrderBot n] [WellFoundedLT n] [DecidableEq n]

/-- The matrix of Gram–Schmidt vectors of the columns of `A`: column `j` is the normalised
component of column `j` of `A` orthogonal to the earlier columns, or zero if there is none.
Port of `NLAlib.gramSchmidtQ`, there by an explicit recursion over `ℝ`. -/
noncomputable def gramSchmidtQ (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  Matrix.of fun i j =>
    InnerProductSpace.gramSchmidtNormed 𝕜 (fun k => WithLp.toLp 2 (A.col k)) j i

/-- The triangular factor of the Gram–Schmidt process, `R = Qᴴ A`.
Port of `NLAlib.gramSchmidtR`. -/
noncomputable def gramSchmidtR (A : Matrix m n 𝕜) : Matrix n n 𝕜 :=
  (gramSchmidtQ A)ᴴ * A

/-- **Gram–Schmidt factors the matrix**: `Q R = A`, with no rank assumption.
Port of `NLAlib.gramSchmidtQ_mul_gramSchmidtR`. -/
theorem gramSchmidtQ_mul_gramSchmidtR (A : Matrix m n 𝕜) :
    gramSchmidtQ A * gramSchmidtR A = A := by
  sorry

/-- The triangular factor is upper triangular. Port of `NLAlib.isUpperTriangular_gramSchmidtR`. -/
theorem isUpperTriangular_gramSchmidtR (A : Matrix m n 𝕜) :
    (gramSchmidtR A).IsUpperTriangular := by
  sorry

/-- The diagonal of the triangular factor is nonnegative.
Port of `NLAlib.gramSchmidtR_apply_self_nonneg`. -/
theorem gramSchmidtR_apply_self_nonneg (A : Matrix m n 𝕜) (j : n) : 0 ≤ gramSchmidtR A j j := by
  sorry

/-- **The classical Gram–Schmidt recursion**: `r_jj q_j = a_j - ∑_{k < j} r_kj q_k`.
Port of `NLAlib.gramSchmidtResidual_eq_sum` and `NLAlib.norm_smul_gramSchmidtCol`. -/
theorem gramSchmidtR_apply_self_smul_col (A : Matrix m n 𝕜) (j : n) :
    gramSchmidtR A j j • (gramSchmidtQ A).col j =
      A.col j - ∑ k ∈ Finset.Iio j, gramSchmidtR A k j • (gramSchmidtQ A).col k := by
  sorry

/-- The Gram matrix of the Gram–Schmidt vectors is diagonal with entries zero or one.
Port of `NLAlib.transpose_gramSchmidtQ_mul_self`. -/
theorem conjTranspose_gramSchmidtQ_mul_self (A : Matrix m n 𝕜) :
    (gramSchmidtQ A)ᴴ * gramSchmidtQ A =
      Matrix.diagonal fun j => if gramSchmidtR A j j = 0 then 0 else 1 := by
  sorry

/-- A diagonal entry of `R` vanishes exactly when the column of `A` depends on the earlier ones.
Port of `NLAlib.gramSchmidtResidual_eq_zero_iff`. -/
theorem gramSchmidtR_apply_self_eq_zero_iff (A : Matrix m n 𝕜) (j : n) :
    gramSchmidtR A j j = 0 ↔ A.col j ∈ Submodule.span 𝕜 (A.col '' Set.Iio j) := by
  sorry

/-- The diagonal of `R` has no zero exactly when `A` has full column rank.
Port of `NLAlib.gramSchmidtSucceeds_iff_linearIndependent`. -/
theorem forall_gramSchmidtR_apply_self_ne_zero_iff (A : Matrix m n 𝕜) :
    (∀ j, gramSchmidtR A j j ≠ 0) ↔ Function.Injective A.mulVec := by
  sorry

/-- The first Gram–Schmidt vectors span the same subspace as the first columns of `A`.
Port of `NLAlib.span_gramSchmidtCol_image_Iic`. -/
theorem span_gramSchmidtQ_col_image_Iic (A : Matrix m n 𝕜) (j : n) :
    Submodule.span 𝕜 ((gramSchmidtQ A).col '' Set.Iic j) =
      Submodule.span 𝕜 (A.col '' Set.Iic j) := by
  sorry

/-- For `A` of full column rank the Gram–Schmidt vectors are orthonormal.
Port of `NLAlib.hasOrthonormalCols_gramSchmidtQ`. -/
theorem hasOrthonormalCols_gramSchmidtQ {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) :
    HasOrthonormalCols (gramSchmidtQ A) := by
  sorry

/-- **Gram–Schmidt computes the QR factorization** of a matrix of full column rank, with positive
diagonal. [TrefethenBau1997, Lecture 7]. Port of `NLAlib.isQR_gramSchmidt`. -/
theorem isQR_gramSchmidt {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) :
    IsQR A (gramSchmidtQ A) (gramSchmidtR A) ∧ ∀ j, 0 < gramSchmidtR A j j := by
  sorry

/-- Gram–Schmidt commutes with a unitary factor on the left: `Q(W A) = W Q(A)` and
`R(W A) = R(A)`. Port of `NLAlib.qrNormalizedArray_orthogonal_mul` and
`NLAlib.canonicalQRUpper_orthogonal_mul`. -/
theorem gramSchmidt_mul_left {l : Type*} [Fintype l] [DecidableEq m] {W : Matrix l m 𝕜}
    (hW : HasOrthonormalCols W) (A : Matrix m n 𝕜) :
    gramSchmidtQ (W * A) = W * gramSchmidtQ A ∧ gramSchmidtR (W * A) = gramSchmidtR A := by
  sorry

end NLAlib
