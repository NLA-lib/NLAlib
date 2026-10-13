/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Dilation
public import NLAlib.Matrix.Norms.Compare

/-!
# Norms of block matrices and submatrices

The Frobenius norm is additive in squares over blocks; the spectral norm is subadditive in
squares over rows or columns of blocks, and exactly additive in that sense when the summands have
orthogonal ranges. Submatrices have smaller norms.

## Main results

* `NLAlib.frobNorm_fromRows_sq`, `NLAlib.frobNorm_fromCols_sq`, `NLAlib.frobNorm_fromBlocks_sq`.
* `NLAlib.specNorm_fromRows_sq_le`, `NLAlib.specNorm_fromCols_sq_le`.
* `NLAlib.specNorm_submatrix_le`, `NLAlib.frobNorm_submatrix_le`.
* `NLAlib.specNorm_fromBlocks_zero₁₂_zero₂₁`: a block diagonal matrix has the larger of the two
  spectral norms.
* `NLAlib.specNorm_add_sq_le_of_conjTranspose_mul_eq_zero`: summands with orthogonal ranges.
* `NLAlib.specNorm_dilation`: the Hermitian dilation has the spectral norm of the matrix.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p q : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype p] [Fintype q]

/-! ### Frobenius norm -/

/-- The squared Frobenius norm is additive over stacked rows.
Port of `NLAlib.frobSq_fromRows`, there over `ℝ`. -/
theorem frobNorm_fromRows_sq (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    frobNorm (Matrix.fromRows A B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  sorry

/-- The squared Frobenius norm is additive over adjoined columns.
Port of `NLAlib.frobSq_fromCols`, there over `ℝ`. -/
theorem frobNorm_fromCols_sq (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    frobNorm (Matrix.fromCols A B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  sorry

/-- The squared Frobenius norm of a block matrix is the sum over the four blocks. -/
theorem frobNorm_fromBlocks_sq (A : Matrix m n 𝕜) (B : Matrix m q 𝕜) (C : Matrix p n 𝕜)
    (D : Matrix p q 𝕜) :
    frobNorm (Matrix.fromBlocks A B C D) ^ 2 =
      frobNorm A ^ 2 + frobNorm B ^ 2 + frobNorm C ^ 2 + frobNorm D ^ 2 := by
  sorry

/-- A submatrix selected by injective maps has Frobenius norm at most that of the matrix. -/
theorem frobNorm_submatrix_le (A : Matrix m n 𝕜) {r : l → m} {c : p → n}
    (hr : Function.Injective r) (hc : Function.Injective c) :
    frobNorm (A.submatrix r c) ≤ frobNorm A := by
  sorry

/-- **Pythagoras for summands with orthogonal ranges**: if `Aᴴ * B = 0` then
`‖A + B‖_F² = ‖A‖_F² + ‖B‖_F²`. -/
theorem frobNorm_add_sq_of_conjTranspose_mul_eq_zero {A B : Matrix m n 𝕜} (h : Aᴴ * B = 0) :
    frobNorm (A + B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  sorry

/-- Pythagoras for summands with orthogonal row spaces: if `A * Bᴴ = 0` then
`‖A + B‖_F² = ‖A‖_F² + ‖B‖_F²`. -/
theorem frobNorm_add_sq_of_mul_conjTranspose_eq_zero {A B : Matrix m n 𝕜} (h : A * Bᴴ = 0) :
    frobNorm (A + B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  sorry

/-! ### Spectral norm -/

/-- A submatrix selected by injective maps has spectral norm at most that of the matrix. -/
theorem specNorm_submatrix_le (A : Matrix m n 𝕜) {r : l → m} {c : p → n}
    (hr : Function.Injective r) (hc : Function.Injective c) :
    specNorm (A.submatrix r c) ≤ specNorm A := by
  sorry

/-- The squared spectral norm of stacked rows is at most the sum of the squares.
Port of `NLAlib.specNorm_fromRows_sq_le`, there over `ℝ`. -/
theorem specNorm_fromRows_sq_le (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    specNorm (Matrix.fromRows A B) ^ 2 ≤ specNorm A ^ 2 + specNorm B ^ 2 := by
  sorry

/-- The squared spectral norm of adjoined columns is at most the sum of the squares.
Port of `NLAlib.specNorm_fromCols_sq_le`, there over `ℝ`. -/
theorem specNorm_fromCols_sq_le (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    specNorm (Matrix.fromCols A B) ^ 2 ≤ specNorm A ^ 2 + specNorm B ^ 2 := by
  sorry

/-- A block of rows has spectral norm at most that of the stacked matrix. -/
theorem specNorm_le_specNorm_fromRows_left (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    specNorm A ≤ specNorm (Matrix.fromRows A B) := by
  sorry

/-- A block of rows has spectral norm at most that of the stacked matrix. -/
theorem specNorm_le_specNorm_fromRows_right (A : Matrix m n 𝕜) (B : Matrix p n 𝕜) :
    specNorm B ≤ specNorm (Matrix.fromRows A B) := by
  sorry

/-- A block of columns has spectral norm at most that of the adjoined matrix. -/
theorem specNorm_le_specNorm_fromCols_left (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    specNorm A ≤ specNorm (Matrix.fromCols A B) := by
  sorry

/-- A block of columns has spectral norm at most that of the adjoined matrix. -/
theorem specNorm_le_specNorm_fromCols_right (A : Matrix m n 𝕜) (B : Matrix m p 𝕜) :
    specNorm B ≤ specNorm (Matrix.fromCols A B) := by
  sorry

/-- Stacking zero rows under a matrix does not change its spectral norm.
Port of `NLAlib.specNorm_fromRows_zero_sq`. -/
@[simp]
theorem specNorm_fromRows_zero (A : Matrix m n 𝕜) :
    specNorm (Matrix.fromRows A (0 : Matrix p n 𝕜)) = specNorm A := by
  sorry

/-- Adjoining zero columns to a matrix does not change its spectral norm. -/
@[simp]
theorem specNorm_fromCols_zero (A : Matrix m n 𝕜) :
    specNorm (Matrix.fromCols A (0 : Matrix m p 𝕜)) = specNorm A := by
  sorry

/-- The spectral norm of a block diagonal matrix is the larger of the spectral norms of the
blocks. -/
theorem specNorm_fromBlocks_zero₁₂_zero₂₁ (A : Matrix m n 𝕜) (D : Matrix p q 𝕜) :
    specNorm (Matrix.fromBlocks A 0 0 D) = max (specNorm A) (specNorm D) := by
  sorry

/-- For summands with orthogonal ranges (`Xᴴ * Y = 0`), the squared spectral norm of the sum is
at most the sum of the squares.
Port of `NLAlib.specNorm_add_sq_le_of_conjTranspose_mul_eq_zero`. -/
theorem specNorm_add_sq_le_of_conjTranspose_mul_eq_zero {X Y : Matrix m n 𝕜} (h : Xᴴ * Y = 0) :
    specNorm (X + Y) ^ 2 ≤ specNorm X ^ 2 + specNorm Y ^ 2 := by
  sorry

/-- For summands with orthogonal row spaces (`X * Yᴴ = 0`), the squared spectral norm of the sum
is at most the sum of the squares.
Port of `NLAlib.specNorm_add_sq_le_of_mul_conjTranspose_eq_zero`. -/
theorem specNorm_add_sq_le_of_mul_conjTranspose_eq_zero {X Y : Matrix m n 𝕜} (h : X * Yᴴ = 0) :
    specNorm (X + Y) ^ 2 ≤ specNorm X ^ 2 + specNorm Y ^ 2 := by
  sorry

/-! ### The Hermitian dilation -/

/-- The Hermitian dilation has the spectral norm of the matrix. [Tropp2015, (2.1.28)]. -/
@[simp]
theorem specNorm_dilation (A : Matrix m n 𝕜) : specNorm (dilation A) = specNorm A := by
  sorry

/-- The squared Frobenius norm of the Hermitian dilation is twice that of the matrix. -/
theorem frobNorm_dilation_sq (A : Matrix m n 𝕜) :
    frobNorm (dilation A) ^ 2 = 2 * frobNorm A ^ 2 := by
  sorry

end NLAlib
