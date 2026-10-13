/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.FieldTheory.Separable
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Functions.Complexification

/-!
# Schur triangularisation

Every square complex matrix is unitarily similar to an upper triangular matrix, with its
eigenvalues on the diagonal in any prescribed order. Over a general `RCLike` field the same holds
when the characteristic polynomial splits, in particular for a real matrix all of whose complex
eigenvalues are real.

The eigenvalues of a matrix that need not be Hermitian are given by a listing `d : n → 𝕜` with
`A.charpoly = ∏ i, (X - C (d i))`.

## Main results

* `NLAlib.exists_hasOrthonormalCols_isUpperTriangular_of_charpoly_eq`: Schur's theorem with a
  prescribed diagonal.
* `NLAlib.exists_hasOrthonormalCols_isUpperTriangular`: Schur's theorem over `ℂ`.
* `NLAlib.sum_norm_sq_le_frobNorm_sq_of_charpoly_eq`: Schur's inequality.
* `NLAlib.sum_norm_sq_eq_frobNorm_sq_iff_isStarNormal`: equality exactly for normal matrices.
* `NLAlib.exists_charpoly_add_eq_prod_of_commute`: eigenvalues of commuting matrices add.
* `NLAlib.dense_setOf_separable_charpoly`: matrices with distinct eigenvalues are dense.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Listings of the eigenvalues -/

/-- A complex matrix has a listing of its eigenvalues with multiplicity. -/
theorem exists_charpoly_eq_prod (A : Matrix n n ℂ) :
    ∃ d : n → ℂ, A.charpoly = ∏ i, (X - C (d i)) := by
  sorry

/-- Two listings of the roots of the same polynomial differ by a permutation.
Port of `NLAlib.exists_perm_eq_of_prod_X_sub_C_eq`, there over `ℂ`. -/
theorem exists_perm_eq_of_prod_X_sub_C_eq {K : Type*} [Field K] {a b : n → K}
    (h : ∏ i, (X - C (a i)) = ∏ i, (X - C (b i))) : ∃ σ : Equiv.Perm n, a = b ∘ σ := by
  sorry

/-- The spectrum is the set of listed eigenvalues. -/
theorem spectrum_eq_range_of_charpoly_eq {K : Type*} [Field K] {A : Matrix n n K} {d : n → K}
    (hd : A.charpoly = ∏ i, (X - C (d i))) : spectrum K A = Set.range d := by
  sorry

/-- The trace is the sum of the listed eigenvalues.
Port of `NLAlib.trace_eq_sum_of_charpoly_eq_prod`. -/
theorem trace_eq_sum_of_charpoly_eq {K : Type*} [Field K] {A : Matrix n n K} {d : n → K}
    (hd : A.charpoly = ∏ i, (X - C (d i))) : A.trace = ∑ i, d i := by
  sorry

/-- The determinant is the product of the listed eigenvalues. -/
theorem det_eq_prod_of_charpoly_eq {K : Type*} [Field K] {A : Matrix n n K} {d : n → K}
    (hd : A.charpoly = ∏ i, (X - C (d i))) : A.det = ∏ i, d i := by
  sorry

/-- A real matrix all of whose complex eigenvalues are real has a real listing of its
eigenvalues. Port of `NLAlib.exists_real_charpoly_factors_of_complex_spectrum_real`. -/
theorem exists_charpoly_eq_prod_of_forall_im_eq_zero {A : Matrix n n ℝ}
    (h : ∀ μ ∈ spectrum ℂ (complexify A), μ.im = 0) :
    ∃ d : n → ℝ, A.charpoly = ∏ i, (X - C (d i)) := by
  sorry

/-! ### Schur's theorem -/

/-- **Schur triangularisation with a prescribed diagonal.** If the characteristic polynomial of
`A` splits with roots `d`, there is a unitary `U` with `Uᴴ A U` upper triangular with diagonal
`d`, in the given order. Over `ℝ` this is orthogonal triangularisation of a matrix with real
eigenvalues. [HornJohnson2013, Theorem 2.3.1].
Port of `NLAlib.exists_unitary_schur_triangularization_with_charpoly`.
Result: schur-triangularization -/
theorem exists_hasOrthonormalCols_isUpperTriangular_of_charpoly_eq [LinearOrder n]
    (A : Matrix n n 𝕜) {d : n → 𝕜} (hd : A.charpoly = ∏ i, (X - C (d i))) :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ (Uᴴ * A * U).IsUpperTriangular ∧
      ∀ i, (Uᴴ * A * U) i i = d i := by
  sorry

/-- **Schur's theorem.** Every square complex matrix is unitarily similar to an upper triangular
matrix. [HornJohnson2013, Theorem 2.3.1]; [GolubVanLoan2013, Theorem 7.1.3].
Port of `NLAlib.exists_unitary_schur_triangularization`.
Result: schur-triangularization -/
theorem exists_hasOrthonormalCols_isUpperTriangular [LinearOrder n] (A : Matrix n n ℂ) :
    ∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧ (Uᴴ * A * U).IsUpperTriangular := by
  sorry

/-- The diagonal of a triangular matrix similar to `A` lists the eigenvalues of `A`. -/
theorem charpoly_eq_prod_of_isUpperTriangular_conjTranspose_mul_mul [LinearOrder n]
    {A U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) (hT : (Uᴴ * A * U).IsUpperTriangular) :
    A.charpoly = ∏ i, (X - C ((Uᴴ * A * U) i i)) := by
  sorry

/-- **Triangularisation with small off-diagonal part.** For every `ε > 0` a complex matrix is
similar to an upper triangular matrix whose off-diagonal entries are smaller than `ε`. This is
the step from the spectral radius to a norm in which the matrix is almost as small.
[HornJohnson2013, Lemma 5.6.10].
Port of `NLAlib.exists_similarity_upper_triangular_small_entries`. -/
theorem exists_isUpperTriangular_inv_mul_mul_norm_apply_lt [LinearOrder n] (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ (S⁻¹ * A * S).IsUpperTriangular ∧
      ∀ i j, i ≠ j → ‖(S⁻¹ * A * S) i j‖ < ε := by
  sorry

/-! ### Schur's inequality -/

/-- **Schur's inequality**: the sum of the squared moduli of the eigenvalues is at most the
squared Frobenius norm. [HornJohnson2013, §2.3].
Port of `NLAlib.sum_norm_sq_schur_diagonal_le_frobSq`. -/
theorem sum_norm_sq_le_frobNorm_sq_of_charpoly_eq (A : Matrix n n 𝕜) {d : n → 𝕜}
    (hd : A.charpoly = ∏ i, (X - C (d i))) : ∑ i, ‖d i‖ ^ 2 ≤ frobNorm A ^ 2 := by
  sorry

/-- **Equality in Schur's inequality holds exactly for normal matrices.**
[HornJohnson2013, Theorem 2.5.3].
Port of `NLAlib.sum_norm_sq_characteristic_eq_frobSq_iff_normal`. -/
theorem sum_norm_sq_eq_frobNorm_sq_iff_isStarNormal (A : Matrix n n 𝕜) {d : n → 𝕜}
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    ∑ i, ‖d i‖ ^ 2 = frobNorm A ^ 2 ↔ IsStarNormal A := by
  sorry

/-! ### Commuting matrices and density -/

/-- **Eigenvalues of commuting matrices pair up**: commuting complex matrices have listings of
their eigenvalues whose sums and products list the eigenvalues of `A + B` and `A * B`.
[HornJohnson2013, Theorem 2.4.8.1].
Port of `NLAlib.exists_paired_charpoly_factors_add_mul_of_commute`. -/
theorem exists_charpoly_add_eq_prod_of_commute {A B : Matrix n n ℂ} (h : Commute A B) :
    ∃ a b : n → ℂ, A.charpoly = ∏ i, (X - C (a i)) ∧ B.charpoly = ∏ i, (X - C (b i)) ∧
      (A + B).charpoly = ∏ i, (X - C (a i + b i)) ∧
      (A * B).charpoly = ∏ i, (X - C (a i * b i)) := by
  sorry

/-- **Matrices with distinct eigenvalues are dense.**
[HornJohnson2013, Theorem 2.4.7.1]. Port of `NLAlib.dense_separable_charpoly`. -/
theorem dense_setOf_separable_charpoly : Dense {A : Matrix n n 𝕜 | A.charpoly.Separable} := by
  sorry

end NLAlib
