/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Diagonalizable
public import NLAlib.Matrix.Spectral.Inertia

/-!
# Simultaneous diagonalisation by congruence

A positive definite `A` and a Hermitian `B` are simultaneously diagonalised by congruence:
`A = S Sᴴ` and `B = S D Sᴴ` with `D` real diagonal. The entries of `D` are the generalized
eigenvalues of the pair, the eigenvalues of `A⁻¹ B`, so `A⁻¹ B` and `A B` are diagonalisable with
real spectrum. Two positive semidefinite matrices are simultaneously diagonalised by congruence
as well, and for an indefinite invertible `A` this happens exactly when `A⁻¹ B` is diagonalisable
with real eigenvalues. Over `ℂ` every pair of square matrices is simultaneously unitarily
triangularised (the generalized Schur, or QZ, decomposition).

## Main results

* `Matrix.PosDef.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose`: the definite
  pair.
* `NLAlib.isEigenvalueListing_inv_mul_of_eq_mul_diagonal_mul_conjTranspose`,
  `Matrix.PosDef.isDiagonalizable_inv_mul`.
* `Matrix.PosSemidef.exists_conjTranspose_mul_mul_eq_diagonal`: the semidefinite pair.
* `NLAlib.exists_hasOrthonormalCols_isUpperTriangular_isUpperTriangular`: the QZ decomposition.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Definite pairs -/

/-- **Simultaneous diagonalisation of a definite pair.** For `A` positive definite and `B`
Hermitian there are an invertible `S` and a real `d` with `A = S Sᴴ` and `B = S diag(d) Sᴴ`.
[HornJohnson2013, Theorem 7.6.4]; [GolubVanLoan2013, Theorem 8.7.1].
Port of `NLAlib.exists_definite_pair_congruence_diagonal`, there over `ℝ`.
Result: definite-pair -/
theorem _root_.Matrix.PosDef.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose
    {A B : Matrix n n 𝕜} (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (S : Matrix n n 𝕜) (d : n → ℝ), IsUnit S.det ∧ A = S * Sᴴ ∧
      B = S * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Sᴴ := by
  sorry

/-- **The generalized eigenvalues of a definite pair** are the eigenvalues of `A⁻¹ B`.
Port of `NLAlib.charpoly_inverse_mul_eq_prod_of_congruence`. -/
theorem isEigenvalueListing_inv_mul_of_eq_mul_diagonal_mul_conjTranspose {A B S : Matrix n n 𝕜}
    {d : n → ℝ} (hS : IsUnit S.det) (hA : A = S * Sᴴ)
    (hB : B = S * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Sᴴ) :
    IsEigenvalueListing (A⁻¹ * B) (fun i => ((d i : ℝ) : 𝕜)) := by
  sorry

/-- For `A` positive definite and `B` Hermitian, `A⁻¹ B` is diagonalisable.
[HornJohnson2013, Theorem 7.6.3]. Port of `NLAlib.isDiagonalizable_inverse_mul_of_posDef`. -/
theorem _root_.Matrix.PosDef.isDiagonalizable_inv_mul {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.IsHermitian) : IsDiagonalizable (A⁻¹ * B) := by
  sorry

/-- For `A` positive definite and `B` Hermitian, `A B` is diagonalisable.
Port of `NLAlib.isDiagonalizable_mul_of_posDef`. -/
theorem _root_.Matrix.PosDef.isDiagonalizable_mul {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.IsHermitian) : IsDiagonalizable (A * B) := by
  sorry

/-- For `A` positive definite and `B` Hermitian, the eigenvalues of `A B` are real: its
characteristic polynomial splits with real roots. -/
theorem _root_.Matrix.PosDef.exists_isEigenvalueListing_mul {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.IsHermitian) : ∃ d : n → ℝ, IsEigenvalueListing (A * B) (fun i => ((d i : ℝ) : 𝕜)) := by
  sorry

/-- For `A` positive definite and `B` positive semidefinite, the eigenvalues of `A B` are real
and nonnegative. Port of `NLAlib.spectrum_mul_subset_nonneg_of_posDef`. -/
theorem _root_.Matrix.PosDef.exists_isEigenvalueListing_mul_nonneg {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosSemidef) :
    ∃ d : n → ℝ, IsEigenvalueListing (A * B) (fun i => ((d i : ℝ) : 𝕜)) ∧ ∀ i, 0 ≤ d i := by
  sorry

/-- The inertia of `B` is read off the diagonal of a congruence.
Port of `NLAlib.inertia_diagonal_eq_of_congruence`. -/
theorem inertiaPos_eq_card_of_eq_mul_diagonal_mul_conjTranspose {B S : Matrix n n 𝕜} {d : n → ℝ}
    (hS : IsUnit S.det) (hB : B = S * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Sᴴ) :
    inertiaPos B = (Finset.univ.filter fun i => 0 < d i).card := by
  sorry

/-! ### Semidefinite and indefinite pairs -/

/-- The kernel of a sum of positive semidefinite matrices is the intersection of the kernels.
Port of `NLAlib.ker_add_eq_inf_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.ker_add {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    LinearMap.ker (A + B).mulVecLin = LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin := by
  sorry

/-- **Two positive semidefinite matrices are simultaneously diagonalised by congruence.**
[HornJohnson2013, Theorem 7.6.4 context].
Port of `NLAlib.exists_diagonal_congruence_of_posSemidef`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.exists_conjTranspose_mul_mul_eq_diagonal {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ (X : Matrix n n 𝕜) (a b : n → ℝ), IsUnit X.det ∧
      Xᴴ * A * X = Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) ∧
      Xᴴ * B * X = Matrix.diagonal (fun i => ((b i : ℝ) : 𝕜)) := by
  sorry

/-- **A real symmetric pair with invertible `A` is simultaneously diagonalised by congruence
exactly when `A⁻¹ B` is diagonalisable over `ℝ`.** [HornJohnson2013, Theorem 4.5.17].
Port of `NLAlib.exists_diagonal_congruence_iff_isDiagonalizable_inverse_mul`. -/
theorem _root_.Matrix.IsHermitian.exists_conjTranspose_mul_mul_eq_diagonal_iff
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hAu : IsUnit A.det) (hB : B.IsHermitian) :
    (∃ (X : Matrix n n ℝ) (a b : n → ℝ), IsUnit X.det ∧ Xᴴ * A * X = Matrix.diagonal a ∧
      Xᴴ * B * X = Matrix.diagonal b) ↔ IsDiagonalizable (A⁻¹ * B) := by
  sorry

/-! ### The generalized Schur decomposition -/

/-- **The QZ decomposition.** Every pair of square complex matrices is simultaneously reduced to
upper triangular form by two unitary matrices.
[GolubVanLoan2013, Theorem 7.7.1]; [HornJohnson2013, Theorem 2.6.1].
Port of `NLAlib.exists_unitary_qz_triangularization`.
Result: qz -/
theorem exists_hasOrthonormalCols_isUpperTriangular_isUpperTriangular
    [LinearOrder n] (A B : Matrix n n ℂ) :
    ∃ Q Z : Matrix n n ℂ, HasOrthonormalCols Q ∧ HasOrthonormalCols Z ∧
      (Qᴴ * A * Z).IsUpperTriangular ∧ (Qᴴ * B * Z).IsUpperTriangular := by
  sorry

end NLAlib
