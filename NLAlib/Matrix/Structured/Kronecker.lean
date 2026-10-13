/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import NLAlib.Matrix.Norms.Nuclear
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Kronecker products

The Kronecker product is Mathlib's `A ⊗ₖ B` (`Matrix.kroneckerMap (· * ·)`), with the mixed
product rule `Matrix.mul_kronecker_mul` and the vectorisation identity
`Matrix.kronecker_mulVec_vec`. This file adds the spectral facts: Kronecker products of frames,
of singular value decompositions and of unitary diagonalisations, and the multiplicativity of the
spectral, Frobenius and nuclear norms, the rank, the pseudoinverse and the condition number.

## Main results

* `NLAlib.HasOrthonormalCols.kronecker`, `NLAlib.IsSVD.kronecker`.
* `NLAlib.specNorm_kronecker`, `NLAlib.frobNorm_kronecker`, `NLAlib.nuclearNorm_kronecker`,
  `NLAlib.rank_kronecker`, `NLAlib.pinv_kronecker`, `NLAlib.conditionNumber_kronecker`.
* `NLAlib.kronecker_eq_mul_diagonal_mul_conjTranspose`,
  `NLAlib.kronecker_one_add_one_kronecker_eq_mul_diagonal_mul_conjTranspose`: eigenvalues of a
  Kronecker product and of a Kronecker sum.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q r s : Type*} [Fintype m] [Fintype n] [Fintype p]
  [Fintype q] [Fintype r] [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq p]
  [DecidableEq q] [DecidableEq r] [DecidableEq s]

/-! ### Frames and decompositions -/

/-- The Kronecker product of two matrices with orthonormal columns has orthonormal columns.
Port of `NLAlib.hasOrthonormalCols_kronecker`, there for real orthogonal matrices. -/
theorem HasOrthonormalCols.kronecker {U : Matrix m n 𝕜} {V : Matrix p q 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) : HasOrthonormalCols (U ⊗ₖ V) := by
  sorry

/-- The Kronecker product of two Hermitian matrices is Hermitian.
Port of `NLAlib.isHermitian_kronecker`. -/
theorem _root_.Matrix.IsHermitian.kronecker {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  sorry

/-- **The singular value decomposition of a Kronecker product** is the Kronecker product of the
singular value decompositions, with singular values the products.
[HornJohnson1991, Theorem 4.2.15]. Port of `NLAlib.IsSVD.kronecker_factorization`. -/
theorem IsSVD.kronecker {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜}
    {B : Matrix p q 𝕜} {P : Matrix p s 𝕜} {τ : s → ℝ} {W : Matrix q s 𝕜} (hA : IsSVD A U σ V)
    (hB : IsSVD B P τ W) :
    IsSVD (A ⊗ₖ B) (U ⊗ₖ P) (fun ij : r × s => σ ij.1 * τ ij.2) (V ⊗ₖ W) := by
  sorry

/-- **Eigenvalues of a Kronecker product.** If `A = U diag(a) Uᴴ` and `B = V diag(b) Vᴴ`, then
`A ⊗ B = (U ⊗ V) diag(a_i b_j) (U ⊗ V)ᴴ`. [HornJohnson1991, Theorem 4.2.12].
Port of `NLAlib.eq_eigenvectorUnitary_kronecker_mul_diagonal_mul_transpose`. -/
theorem kronecker_eq_mul_diagonal_mul_conjTranspose {A U : Matrix m m 𝕜} {B V : Matrix n n 𝕜}
    {a : m → 𝕜} {b : n → 𝕜} (hA : A = U * Matrix.diagonal a * Uᴴ)
    (hB : B = V * Matrix.diagonal b * Vᴴ) :
    A ⊗ₖ B = (U ⊗ₖ V) * Matrix.diagonal (fun ij : m × n => a ij.1 * b ij.2) * (U ⊗ₖ V)ᴴ := by
  sorry

/-- **Eigenvalues of a Kronecker sum.** If `A = U diag(a) Uᴴ` and `B = V diag(b) Vᴴ` with `U`,
`V` unitary, then `A ⊗ 1 + 1 ⊗ B = (U ⊗ V) diag(a_i + b_j) (U ⊗ V)ᴴ`.
[HornJohnson1991, Theorem 4.4.5]. Port of `NLAlib.multiset_eigenvalues_kronecker_sum`. -/
theorem kronecker_one_add_one_kronecker_eq_mul_diagonal_mul_conjTranspose {A U : Matrix m m 𝕜}
    {B V : Matrix n n 𝕜} {a : m → 𝕜} {b : n → 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (hA : A = U * Matrix.diagonal a * Uᴴ)
    (hB : B = V * Matrix.diagonal b * Vᴴ) :
    A ⊗ₖ (1 : Matrix n n 𝕜) + (1 : Matrix m m 𝕜) ⊗ₖ B =
      (U ⊗ₖ V) * Matrix.diagonal (fun ij : m × n => a ij.1 + b ij.2) * (U ⊗ₖ V)ᴴ := by
  sorry

/-- The largest eigenvalue of a Kronecker sum of Hermitian matrices is the sum of the largest
eigenvalues. -/
theorem eigenvalue_zero_kronecker_one_add_one_kronecker [Nonempty m] [Nonempty n]
    {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    eigenvalue (A ⊗ₖ (1 : Matrix n n 𝕜) + (1 : Matrix m m 𝕜) ⊗ₖ B) 0 =
      eigenvalue A 0 + eigenvalue B 0 := by
  sorry

/-- The largest eigenvalue of a Kronecker product of positive semidefinite matrices is the
product of the largest eigenvalues. -/
theorem eigenvalue_zero_kronecker {A : Matrix m m 𝕜} {B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : eigenvalue (A ⊗ₖ B) 0 = eigenvalue A 0 * eigenvalue B 0 := by
  sorry

/-! ### Norms, rank and pseudoinverse -/

/-- **The spectral norm is multiplicative on Kronecker products.**
[HornJohnson1991, Theorem 4.2.15]. Port of `NLAlib.specNorm_kronecker`, there over `ℝ`. -/
theorem specNorm_kronecker (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    specNorm (A ⊗ₖ B) = specNorm A * specNorm B := by
  sorry

/-- The Frobenius norm is multiplicative on Kronecker products.
Port of `NLAlib.frobNorm_kronecker`. -/
theorem frobNorm_kronecker (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    frobNorm (A ⊗ₖ B) = frobNorm A * frobNorm B := by
  sorry

/-- The nuclear norm is multiplicative on Kronecker products. -/
theorem nuclearNorm_kronecker (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    nuclearNorm (A ⊗ₖ B) = nuclearNorm A * nuclearNorm B := by
  sorry

/-- **The rank is multiplicative on Kronecker products.**
[HornJohnson1991, Theorem 4.2.15]. Port of `NLAlib.rank_kronecker`, there over `ℝ`. -/
theorem rank_kronecker (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  sorry

/-- **The pseudoinverse of a Kronecker product** is the Kronecker product of the pseudoinverses.
Port of `NLAlib.moorePenroseInverse_kronecker`, there over `ℝ`. -/
theorem pinv_kronecker (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    pinv (A ⊗ₖ B) = pinv A ⊗ₖ pinv B := by
  sorry

/-- The condition number is multiplicative on Kronecker products. -/
theorem conditionNumber_kronecker (A : Matrix m n 𝕜) (B : Matrix p q 𝕜) :
    conditionNumber (A ⊗ₖ B) = conditionNumber A * conditionNumber B := by
  sorry

end NLAlib
