/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Elimination

/-!
# The Cholesky factorization

`NLAlib.IsCholesky A L` says that `A = L * Lᴴ` with `L` lower triangular with positive diagonal.
A matrix has a Cholesky factorization exactly when it is positive definite, and the factor is
unique. A positive semidefinite matrix has a factorization with nonnegative diagonal, and after a
symmetric permutation one whose nonzero columns are the first `rank A`.

## Main definitions

* `NLAlib.IsCholesky`: the factorization predicate.
* `NLAlib.choleskyLower`: the factor computed by elimination, for a matrix indexed by `Fin n`.

## Main results

* `NLAlib.IsCholesky.posDef`, `NLAlib.IsCholesky.unique`.
* `NLAlib.exists_isCholesky_iff_posDef`, `Matrix.PosDef.existsUnique_isCholesky`.
* `Matrix.PosDef.isCholesky_choleskyLower`: elimination computes the factorization.
* `Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose`: the pivoted factorization.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [LinearOrder m] [LinearOrder n] [Fintype m]
  [Fintype n]

/-- `IsCholesky A L`: **`A = L * Lᴴ` is a Cholesky factorization**, with `L` lower triangular
with positive diagonal. [GolubVanLoan2013, Theorem 4.2.7]; [HornJohnson2013, Corollary 7.2.9].
Port of `NLAlib.IsCholesky`, there over `ℝ`. -/
structure IsCholesky (A L : Matrix n n 𝕜) : Prop where
  /-- The factor is lower triangular. -/
  isLowerTriangular : L.IsLowerTriangular
  /-- The diagonal of the factor is positive. -/
  apply_self_pos : ∀ i, 0 < L i i
  /-- The matrix is the factor times its conjugate transpose. -/
  eq_mul_conjTranspose : A = L * Lᴴ

section

variable [DecidableEq n] {A L : Matrix n n 𝕜}

/-- A Cholesky factor is invertible. Port of `NLAlib.IsCholesky.isUnit_det`. -/
theorem IsCholesky.isUnit_det (h : IsCholesky A L) : IsUnit L.det := by
  sorry

/-- A matrix with a Cholesky factorization is positive definite.
Port of `NLAlib.IsCholesky.posDef`. -/
theorem IsCholesky.posDef (h : IsCholesky A L) : A.PosDef := by
  sorry

/-- **The Cholesky factor is unique.** [GolubVanLoan2013, Theorem 4.2.7].
Port of `NLAlib.IsCholesky.unique`. -/
theorem IsCholesky.unique {L' : Matrix n n 𝕜} (h : IsCholesky A L) (h' : IsCholesky A L') :
    L = L' := by
  sorry

/-- The determinant is the product of the squared diagonal of the Cholesky factor.
Port of `NLAlib.det_eq_prod_sq_diag_of_cholesky`. -/
theorem IsCholesky.det_eq_prod (h : IsCholesky A L) : A.det = ∏ i, L i i ^ 2 := by
  sorry

/-- A Cholesky factorization is preserved by an order isomorphism of the index type. -/
theorem IsCholesky.submatrix_orderIso (h : IsCholesky A L) (e : m ≃o n) :
    IsCholesky (A.submatrix e e) (L.submatrix e e) := by
  sorry

/-- **A matrix has a Cholesky factorization exactly when it is positive definite.**
Port of `NLAlib.exists_isCholesky_iff_posDef`.
Result: cholesky-existence -/
theorem exists_isCholesky_iff_posDef (A : Matrix n n 𝕜) : (∃ L, IsCholesky A L) ↔ A.PosDef := by
  sorry

/-- A positive definite matrix has exactly one Cholesky factor.
Port of `NLAlib.existsUnique_cholesky_of_posDef`. -/
theorem _root_.Matrix.PosDef.existsUnique_isCholesky (hA : A.PosDef) :
    ∃! L, IsCholesky A L := by
  sorry

/-- A positive semidefinite matrix is `L * Lᴴ` for a lower triangular `L` with nonnegative
diagonal. Port of `NLAlib.exists_eq_mul_transpose_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.exists_eq_mul_conjTranspose_of_isLowerTriangular
    (hA : A.PosSemidef) :
    ∃ L : Matrix n n 𝕜, L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ A = L * Lᴴ := by
  sorry

/-- **Pivoted Cholesky.** A positive semidefinite matrix has, after a symmetric permutation, a
factorization `L * Lᴴ` with `L` lower triangular whose first `rank A` diagonal entries are
positive and whose remaining columns vanish. [Higham2002, Theorem 10.9].
Port of `NLAlib.isPivotedCholesky_choleskyPivoted`, with the rank statements
`NLAlib.choleskyPivoted_apply_self_pos_iff_lt_rank` and
`NLAlib.choleskyPivoted_apply_eq_zero_of_rank_le`, which the prototype leaves unproved. -/
theorem _root_.Matrix.PosSemidef.exists_perm_eq_mul_conjTranspose [LocallyFiniteOrderBot n]
    (hA : A.PosSemidef) :
    ∃ (σ : Equiv.Perm n) (L : Matrix n n 𝕜), L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧
      A.submatrix σ σ = L * Lᴴ ∧ (∀ i, 0 < L i i ↔ (Finset.Iio i).card < A.rank) ∧
      ∀ i j, A.rank ≤ (Finset.Iio j).card → L i j = 0 := by
  sorry

end

/-! ### Elimination -/

section Recursion

variable {n : ℕ}

/-- The Cholesky factor computed by elimination: column `j` is the pivot column of step `j`
divided by the square root of the pivot. A zero pivot gives a zero column.
Port of `NLAlib.cholesky`, there by recursion on the dimension over `ℝ`. -/
noncomputable def choleskyLower (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j =>
    if j ≤ i then gaussState A j i j / ((√(RCLike.re (gaussState A j j j)) : ℝ) : 𝕜) else 0

/-- The factor computed by elimination is lower triangular.
Port of `NLAlib.isLowerTriangular_cholesky`. -/
theorem isLowerTriangular_choleskyLower (A : Matrix (Fin n) (Fin n) 𝕜) :
    (choleskyLower A).IsLowerTriangular := by
  sorry

/-- **Elimination computes the Cholesky factorization** of a positive definite matrix.
Port of `NLAlib.isCholesky_cholesky_of_posDef`. -/
theorem _root_.Matrix.PosDef.isCholesky_choleskyLower {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.PosDef) : IsCholesky A (choleskyLower A) := by
  sorry

/-- Elimination factors a positive semidefinite matrix, with nonnegative diagonal.
Port of `NLAlib.eq_cholesky_mul_transpose_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.eq_choleskyLower_mul_conjTranspose
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosSemidef) :
    A = choleskyLower A * (choleskyLower A)ᴴ ∧ ∀ i, 0 ≤ choleskyLower A i i := by
  sorry

/-- **Elimination on a Hermitian matrix produces a positive diagonal exactly when the matrix is
positive definite.** Port of `NLAlib.choleskySucceeds_iff_posDef`.
Result: cholesky-existence -/
theorem forall_choleskyLower_apply_self_pos_iff {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) : (∀ i, 0 < choleskyLower A i i) ↔ A.PosDef := by
  sorry

end Recursion

end NLAlib
