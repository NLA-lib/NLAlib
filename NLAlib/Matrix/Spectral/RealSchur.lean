/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Simultaneous
public import NLAlib.Matrix.Factorizations.Hessenberg

/-!
# The real Schur form

A real square matrix is orthogonally similar to an upper quasi-triangular matrix: block upper
triangular with diagonal blocks of size one and two, the blocks of size two having a pair of
complex conjugate eigenvalues. A real normal matrix is orthogonally similar to a direct sum of
real scalars and scaled rotations. Real matrices that are similar, or unitarily similar, over
`ℂ` are so over `ℝ`.

## Main definitions

* `NLAlib.IsUpperQuasiTriangular`: upper Hessenberg with no two consecutive nonzero subdiagonal
  entries.
* `NLAlib.IsRealSchurForm`: upper quasi-triangular with standardised blocks of size two.

## Main results

* `NLAlib.exists_hasOrthonormalCols_isRealSchurForm`: the real Schur form.
* `NLAlib.exists_hasOrthonormalCols_isRealSchurForm_of_isStarNormal`: real normal matrices.
* `NLAlib.exists_real_similarity_of_complexify`, `NLAlib.exists_real_orthogonal_of_complexify`:
  descent of similarity from `ℂ` to `ℝ`.
* `NLAlib.exists_hasOrthonormalCols_isUpperQuasiTriangular_pair`: the real QZ decomposition.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {R : Type*} {k : ℕ}

/-! ### Quasi-triangular matrices -/

/-- A matrix indexed by `Fin k` is **upper quasi-triangular** if it is upper Hessenberg and no
two consecutive subdiagonal entries are nonzero: it is block upper triangular with diagonal
blocks of size at most two. [HornJohnson2013, §2.3].
Port of `NLAlib.IsUpperQuasiTriangular`. -/
def IsUpperQuasiTriangular [Zero R] (T : Matrix (Fin k) (Fin k) R) : Prop :=
  IsUpperHessenberg T ∧
    ∀ i j l : Fin k, (j : ℕ) + 1 = (i : ℕ) → (l : ℕ) + 1 = (j : ℕ) → T i j = 0 ∨ T j l = 0

/-- An upper triangular matrix is upper quasi-triangular.
Port of `NLAlib.isUpperQuasiTriangular_of_isUpperTriangular`. -/
theorem _root_.Matrix.IsUpperTriangular.isUpperQuasiTriangular [Zero R]
    {T : Matrix (Fin k) (Fin k) R} (hT : T.IsUpperTriangular) : IsUpperQuasiTriangular T := by
  sorry

/-- An upper triangular matrix times an upper quasi-triangular one is upper quasi-triangular.
Port of `NLAlib.IsUpperQuasiTriangular.upperTriangular_mul`. -/
theorem IsUpperQuasiTriangular.isUpperTriangular_mul [Semiring R] [NoZeroDivisors R]
    {U T : Matrix (Fin k) (Fin k) R} (hU : U.IsUpperTriangular)
    (hT : IsUpperQuasiTriangular T) : IsUpperQuasiTriangular (U * T) := by
  sorry

/-- A real matrix is in **real Schur form** if it is upper quasi-triangular and each diagonal
block of size two has equal diagonal entries and off-diagonal entries of opposite sign, so that
its eigenvalues are a pair of non-real complex conjugates. [HornJohnson2013, Theorem 2.3.4].
Port of `NLAlib.IsRealSchurForm`. -/
def IsRealSchurForm (T : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsUpperQuasiTriangular T ∧
    ∀ i j : Fin k, (j : ℕ) + 1 = (i : ℕ) → T i j ≠ 0 → T i i = T j j ∧ T j i * T i j < 0

/-! ### Real Schur and real normal forms -/

/-- **The real Schur form.** Every real square matrix is orthogonally similar to a matrix in real
Schur form. [HornJohnson2013, Theorem 2.3.4]; [GolubVanLoan2013, Theorem 7.4.1].
Port of `NLAlib.exists_orthogonal_real_schur`.
Result: real-schur -/
theorem exists_hasOrthonormalCols_isRealSchurForm (A : Matrix (Fin k) (Fin k) ℝ) :
    ∃ Q T : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᵀ ∧
      IsRealSchurForm T := by
  sorry

/-- **The real normal form.** Every real normal matrix is orthogonally similar to a direct sum of
real scalars and blocks `[[a, b], [-b, a]]`. [HornJohnson2013, Theorem 2.5.8].
Port of `NLAlib.exists_orthogonal_real_normal_form`. -/
theorem exists_hasOrthonormalCols_isRealSchurForm_of_isStarNormal
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsStarNormal A) :
    ∃ Q T : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᵀ ∧
      IsRealSchurForm T ∧ ∀ i j, i ≠ j → T i j = -T j i := by
  sorry

/-- The real normal form of a skew-symmetric matrix has zero diagonal: a direct sum of zeros
and blocks `[[0, b], [-b, 0]]`. [HornJohnson2013, Corollary 2.5.11].
Port of `NLAlib.exists_orthogonal_real_skew_normal_form`. -/
theorem exists_hasOrthonormalCols_isRealSchurForm_of_transpose_eq_neg
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : Aᵀ = -A) :
    ∃ Q T : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᵀ ∧
      IsRealSchurForm T ∧ Tᵀ = -T := by
  sorry

/-- The real normal form of an orthogonal matrix is orthogonal: a direct sum of `±1` and plane
rotations. [HornJohnson2013, Corollary 2.5.11].
Port of `NLAlib.exists_orthogonal_real_orthogonal_normal_form`. -/
theorem exists_hasOrthonormalCols_isRealSchurForm_of_hasOrthonormalCols
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : HasOrthonormalCols A) :
    ∃ Q T : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᵀ ∧
      IsRealSchurForm T ∧ (∀ i j, i ≠ j → T i j = -T j i) ∧ HasOrthonormalCols T := by
  sorry

/-- **The real QZ decomposition.** Every pair of real square matrices is reduced by two
orthogonal matrices to an upper quasi-triangular and an upper triangular matrix.
[GolubVanLoan2013, Theorem 7.7.2]. Port of `NLAlib.exists_orthogonal_qz_triangularization`. -/
theorem exists_hasOrthonormalCols_isUpperQuasiTriangular_pair (A B : Matrix (Fin k) (Fin k) ℝ) :
    ∃ Q Z : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧ HasOrthonormalCols Z ∧
      IsUpperQuasiTriangular (Qᵀ * A * Z) ∧ (Qᵀ * B * Z).IsUpperTriangular := by
  sorry

/-! ### Descent from `ℂ` to `ℝ` -/

section Descent

variable {ι n : Type*} [Fintype n] [DecidableEq n]

/-- **Real matrices similar over `ℂ` are similar over `ℝ`**, simultaneously for a family.
[HornJohnson2013, Theorem 1.3.29].
Port of `NLAlib.exists_real_similarity_of_complex_similarity`. -/
theorem exists_real_similarity_of_complexify {A B : ι → Matrix n n ℝ} {S : Matrix n n ℂ}
    (hS : IsUnit S.det) (h : ∀ i, complexify (A i) * S = S * complexify (B i)) :
    ∃ T : Matrix n n ℝ, IsUnit T.det ∧ ∀ i, A i * T = T * B i := by
  sorry

/-- **Real matrices unitarily similar over `ℂ` are orthogonally similar over `ℝ`**,
simultaneously for a family. [HornJohnson2013, Theorem 2.5.21].
Port of `NLAlib.exists_real_orthogonal_similarity_of_complex_unitary_similarity`. -/
theorem exists_real_orthogonal_of_complexify {A B : ι → Matrix n n ℝ} {U : Matrix n n ℂ}
    (hU : HasOrthonormalCols U) (h : ∀ i, complexify (A i) = U * complexify (B i) * Uᴴ) :
    ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ ∀ i, A i = Q * B i * Qᵀ := by
  sorry

end Descent

end NLAlib
