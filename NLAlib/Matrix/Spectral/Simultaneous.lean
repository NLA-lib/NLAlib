/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Normal

/-!
# Simultaneous triangularisation and diagonalisation

A commuting family of complex matrices has a common eigenvector and is simultaneously unitarily
triangularisable. A family of normal matrices commutes exactly when it is simultaneously
unitarily diagonalisable; for Hermitian matrices over `𝕜` the diagonals are real, and over `ℝ`
the unitary matrix is orthogonal.

## Main results

* `NLAlib.exists_mulVec_eq_smul_of_pairwise_commute`: a common eigenvector.
* `NLAlib.exists_hasOrthonormalCols_forall_isUpperTriangular_of_pairwise_commute`.
* `NLAlib.pairwise_commute_iff_exists_forall_eq_mul_diagonal_mul_conjTranspose`: normal families.
* `NLAlib.exists_hasOrthonormalCols_forall_eq_mul_diagonal_of_pairwise_commute`: Hermitian
  families over `𝕜`.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {ι n : Type*} [Fintype n] [DecidableEq n]

/-- **A commuting family of complex matrices has a common eigenvector.**
[HornJohnson2013, Lemma 1.3.19].
Port of `NLAlib.exists_common_mulVec_eigenvector_of_commute`. -/
theorem exists_mulVec_eq_smul_of_pairwise_commute [Nonempty n] (A : ι → Matrix n n ℂ)
    (h : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ (x : n → ℂ) (d : ι → ℂ), x ≠ 0 ∧ ∀ i, A i *ᵥ x = d i • x := by
  sorry

/-- **A commuting family of complex matrices is simultaneously unitarily triangularisable.**
[HornJohnson2013, Theorem 2.3.3].
Port of `NLAlib.exists_simultaneous_unitary_schur_triangularization`.
Result: simultaneous-triangularization -/
theorem exists_hasOrthonormalCols_forall_isUpperTriangular_of_pairwise_commute [LinearOrder n]
    (A : ι → Matrix n n ℂ) (h : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧ ∀ i, (Uᴴ * A i * U).IsUpperTriangular := by
  sorry

/-- **A family of normal matrices commutes exactly when it is simultaneously unitarily
diagonalisable.** [HornJohnson2013, Theorem 2.5.5].
Port of `NLAlib.pairwise_commute_iff_exists_simultaneous_unitary_diagonalization`.
Result: simultaneous-diagonalization -/
theorem pairwise_commute_iff_exists_forall_eq_mul_diagonal_mul_conjTranspose
    {A : ι → Matrix n n ℂ} (hA : ∀ i, IsStarNormal (A i)) :
    (Pairwise fun i j => Commute (A i) (A j)) ↔
      ∃ U : Matrix n n ℂ, HasOrthonormalCols U ∧
        ∀ i, ∃ d : n → ℂ, A i = U * Matrix.diagonal d * Uᴴ := by
  sorry

/-- **A commuting family of Hermitian matrices is simultaneously unitarily diagonalisable**,
with real diagonals; over `ℝ` the unitary matrix is orthogonal.
[HornJohnson2013, Theorem 4.1.6 context].
Port of `NLAlib.exists_simultaneous_orthogonal_diagonalization_of_commute`, there over `ℝ`.
Result: simultaneous-diagonalization -/
theorem exists_hasOrthonormalCols_forall_eq_mul_diagonal_of_pairwise_commute
    {A : ι → Matrix n n 𝕜} (hA : ∀ i, (A i).IsHermitian)
    (h : Pairwise fun i j => Commute (A i) (A j)) :
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧
      ∀ i, ∃ d : n → ℝ, A i = U * Matrix.diagonal (fun j => ((d j : ℝ) : 𝕜)) * Uᴴ := by
  sorry

/-- Two Hermitian matrices commute exactly when they are simultaneously unitarily
diagonalisable. Port of `NLAlib.exists_orthogonal_congruence_diagonal_of_commute`. -/
theorem _root_.Matrix.IsHermitian.commute_iff_exists_eq_mul_diagonal_mul_conjTranspose
    {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Commute A B ↔
      ∃ (U : Matrix n n 𝕜) (a b : n → ℝ), HasOrthonormalCols U ∧
        A = U * Matrix.diagonal (fun j => ((a j : ℝ) : 𝕜)) * Uᴴ ∧
        B = U * Matrix.diagonal (fun j => ((b j : ℝ) : 𝕜)) * Uᴴ := by
  sorry

/-- The product of two commuting positive semidefinite matrices is positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.mul_of_commute {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (h : Commute A B) : (A * B).PosSemidef := by
  sorry

end NLAlib
