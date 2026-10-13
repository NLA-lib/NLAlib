/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Schur
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import NLAlib.Matrix.Majorization.DoublyStochastic

/-!
# Normal matrices

A square matrix is normal, Mathlib's `IsStarNormal A`, when it commutes with its conjugate
transpose. A complex matrix is normal exactly when it is unitarily diagonalisable. Normal upper
triangular matrices are diagonal; intertwining relations between normal matrices pass to the
conjugate transposes (Fuglede–Putnam); normal matrices with the same characteristic polynomial
are unitarily similar; and the eigenvalues of two normal matrices can be matched within the
Frobenius distance (Hoffman–Wielandt).

## Main results

* `NLAlib.isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose`: the spectral theorem.
* `IsStarNormal.exists_eq_mul_diagonal_mul_conjTranspose_of_charpoly_eq`: with prescribed order.
* `IsStarNormal.isDiag_of_isUpperTriangular`.
* `IsStarNormal.mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose`: Fuglede–Putnam.
* `IsStarNormal.exists_eq_mul_mul_conjTranspose_iff_charpoly_eq`: unitary similarity.
* `IsStarNormal.exists_perm_sum_norm_sub_sq_le_frobNorm_sq`: Hoffman–Wielandt.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### The spectral theorem -/

/-- A unitarily diagonalisable matrix is normal.
Port of `NLAlib.mul_conjTranspose_eq_conjTranspose_mul_of_unitary_diagonalization`. -/
theorem isStarNormal_mul_diagonal_mul_conjTranspose {U : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) (d : n → 𝕜) : IsStarNormal (U * Matrix.diagonal d * Uᴴ) := by
  sorry

/-- **A normal matrix whose characteristic polynomial splits is unitarily diagonalisable**, with
its eigenvalues in any prescribed order. [HornJohnson2013, Theorem 2.5.3].
Port of `NLAlib.exists_unitary_diagonalization_of_normal_with_charpoly`, there over `ℂ`. -/
theorem _root_.IsStarNormal.exists_eq_mul_diagonal_mul_conjTranspose_of_charpoly_eq
    {A : Matrix n n 𝕜} (hA : IsStarNormal A) {d : n → 𝕜}
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ A = U * Matrix.diagonal d * Uᴴ := by
  sorry

/-- **The spectral theorem for normal matrices**: a complex matrix is normal exactly when it is
unitarily diagonalisable. [HornJohnson2013, Theorem 2.5.3].
Port of `NLAlib.normal_iff_exists_unitary_diagonalization`.
Result: normal-spectral-theorem -/
theorem isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose {A : Matrix n n ℂ} :
    IsStarNormal A ↔
      ∃ (U : Matrix n n ℂ) (d : n → ℂ), HasOrthonormalCols U ∧
        A = U * Matrix.diagonal d * Uᴴ := by
  sorry

/-- A normal upper triangular matrix is diagonal. [HornJohnson2013, Lemma 2.5.2].
Port of `NLAlib.upper_fromBlocks_eq_diagonal_of_normal`, for a triangular matrix. -/
theorem _root_.IsStarNormal.isDiag_of_isUpperTriangular [LinearOrder n] {T : Matrix n n 𝕜}
    (hT : IsStarNormal T) (h : T.IsUpperTriangular) : T.IsDiag := by
  sorry

/-- A normal block upper triangular matrix is block diagonal.
Port of `NLAlib.eq_zero_of_normal_upper_fromBlocks`, there over `ℂ`. -/
theorem eq_zero_of_isStarNormal_fromBlocks {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    {C : Matrix m n 𝕜} (h : IsStarNormal (Matrix.fromBlocks A C 0 B)) : C = 0 := by
  sorry

/-- A normal matrix with listed eigenvalues `d` is Hermitian exactly when the `d i` are real. -/
theorem _root_.IsStarNormal.isHermitian_iff_forall_im_eq_zero {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) {d : n → 𝕜} (hd : A.charpoly = ∏ i, (X - C (d i))) :
    A.IsHermitian ↔ ∀ i, RCLike.im (d i) = 0 := by
  sorry

/-- A normal matrix with listed eigenvalues `d` is unitary exactly when the `d i` have modulus
one. -/
theorem _root_.IsStarNormal.hasOrthonormalCols_iff_forall_norm_eq_one {A : Matrix n n 𝕜}
    (hA : IsStarNormal A) {d : n → 𝕜} (hd : A.charpoly = ∏ i, (X - C (d i))) :
    HasOrthonormalCols A ↔ ∀ i, ‖d i‖ = 1 := by
  sorry

/-- The squared Frobenius norm of a normal matrix is the sum of the squared moduli of its
eigenvalues. Port of `NLAlib.frobSq_eq_sum_norm_sq_of_normal`. -/
theorem _root_.IsStarNormal.frobNorm_sq_eq_sum {A : Matrix n n 𝕜} (hA : IsStarNormal A)
    {d : n → 𝕜} (hd : A.charpoly = ∏ i, (X - C (d i))) : frobNorm A ^ 2 = ∑ i, ‖d i‖ ^ 2 := by
  sorry

/-- The spectral norm of a normal matrix is the largest modulus of an eigenvalue. -/
theorem _root_.IsStarNormal.specNorm_le_iff {A : Matrix n n 𝕜} (hA : IsStarNormal A)
    {d : n → 𝕜} (hd : A.charpoly = ∏ i, (X - C (d i))) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ ∀ i, ‖d i‖ ≤ c := by
  sorry

/-! ### Intertwining and similarity -/

/-- **The Fuglede–Putnam theorem**: for normal `A`, `B`, `A X = X B` exactly when
`Aᴴ X = X Bᴴ`. [HornJohnson2013, Theorem 2.5.16].
Port of `NLAlib.mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose_of_normal_rectangular`. -/
theorem _root_.IsStarNormal.mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : IsStarNormal A) (hB : IsStarNormal B)
    {X : Matrix m n ℂ} : A * X = X * B ↔ Aᴴ * X = X * Bᴴ := by
  sorry

/-- **Normal matrices are unitarily similar exactly when they have the same characteristic
polynomial.** Port of `NLAlib.exists_unitary_similarity_iff_charpoly_eq_of_normal`. -/
theorem _root_.IsStarNormal.exists_eq_mul_mul_conjTranspose_iff_charpoly_eq {A B : Matrix n n ℂ}
    (hA : IsStarNormal A) (hB : IsStarNormal B) :
    (∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧ B = U * A * Uᴴ) ↔ A.charpoly = B.charpoly := by
  sorry

/-! ### Eigenvalue variation -/

/-- **The Hoffman–Wielandt theorem for normal matrices.** The eigenvalues of two normal matrices
can be matched so that the sum of squared distances is at most `‖A - B‖_F²`.
[HornJohnson2013, Theorem 6.3.5]; [Bhatia1997, Theorem VI.4.1].
Result: hoffman-wielandt-normal -/
theorem _root_.IsStarNormal.exists_perm_sum_norm_sub_sq_le_frobNorm_sq {A B : Matrix n n 𝕜}
    (hA : IsStarNormal A) (hB : IsStarNormal B) {a b : n → 𝕜}
    (ha : A.charpoly = ∏ i, (X - C (a i))) (hb : B.charpoly = ∏ i, (X - C (b i))) :
    ∃ σ : Equiv.Perm n, ∑ i, ‖a i - b (σ i)‖ ^ 2 ≤ frobNorm (A - B) ^ 2 := by
  sorry

end NLAlib
