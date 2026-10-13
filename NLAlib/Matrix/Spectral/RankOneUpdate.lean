/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import NLAlib.Matrix.Spectral.SylvesterCriterion
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Rank-one updates and bordered matrices

The determinant and the characteristic polynomial of a rank-one update `A + x yᵀ` and of a
bordered matrix: the matrix determinant lemma, the secular equation of a diagonal matrix plus a
rank-one matrix and of an arrowhead matrix, and Brauer's theorem on the eigenvalues after a
rank-one update along an eigenvector. The converses of the interlacing theorems: every sequence
interlacing the eigenvalues of a Hermitian matrix is the spectrum of a rank-one update, and of a
bordering, of it.

## Main results

* `NLAlib.det_add_vecMulVec`: the matrix determinant lemma.
* `NLAlib.charpoly_diagonal_add_vecMulVec`: the secular equation.
* `NLAlib.charpoly_add_vecMulVec_mul`: Brauer's theorem.
* `Matrix.IsHermitian.exists_eigenvalue_add_vecMulVec_star_eq`,
  `Matrix.IsHermitian.exists_eigenvalue_fromBlocks_eq`: the converses of interlacing.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Determinants and characteristic polynomials -/

/-- **The matrix determinant lemma**: `det (M + u vᵀ) = det M · (1 + vᵀ M⁻¹ u)` for invertible
`M`. Port of `NLAlib.det_add_vecMulVec`. -/
theorem det_add_vecMulVec {K : Type*} [Field K] {M : Matrix n n K} (hM : IsUnit M.det)
    (u v : n → K) : (M + Matrix.vecMulVec u v).det = M.det * (1 + v ⬝ᵥ M⁻¹ *ᵥ u) := by
  sorry

/-- The determinant of a diagonal matrix plus a rank-one matrix, with no invertibility
assumption. Port of `NLAlib.det_diagonal_add_vecMulVec_of_forall_ne_zero`. -/
theorem det_diagonal_add_vecMulVec {R : Type*} [CommRing R] (d u v : n → R) :
    (Matrix.diagonal d + Matrix.vecMulVec u v).det =
      ∏ i, d i + ∑ i, u i * v i * ∏ j ∈ Finset.univ.erase i, d j := by
  sorry

/-- **The secular equation**: the characteristic polynomial of a diagonal matrix plus a rank-one
matrix. [GolubVanLoan2013, §8.4.3]. Port of `NLAlib.charpoly_diagonal_add_vecMulVec`. -/
theorem charpoly_diagonal_add_vecMulVec {R : Type*} [CommRing R] (d u v : n → R) :
    (Matrix.diagonal d + Matrix.vecMulVec u v).charpoly =
      ∏ i, (X - C (d i)) - ∑ i, C (u i * v i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  sorry

/-- **The characteristic polynomial of an arrowhead matrix**: a diagonal matrix bordered by one
row and one column. [GolubVanLoan2013, §8.4.3 context].
Port of `NLAlib.charpoly_fromBlocks_diagonal_replicate`. -/
theorem charpoly_fromBlocks_diagonal_replicateCol {R : Type*} [CommRing R] (d u w : n → R)
    (a : R) :
    (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol Unit u)
      (Matrix.replicateRow Unit w) (Matrix.of fun _ _ => a)).charpoly =
      (X - C a) * ∏ i, (X - C (d i)) -
        ∑ i, C (u i * w i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  sorry

/-- **Brauer's theorem.** A rank-one update along an eigenvector `x` of `A` with eigenvalue `μ`
moves `μ` to `μ + yᵀ x` and leaves the other eigenvalues in place.
[HornJohnson2013, Theorem 1.2.8 context].
Port of `NLAlib.charpoly_add_vecMulVec_mul_X_sub_C`. -/
theorem charpoly_add_vecMulVec_mul {K : Type*} [Field K] {A : Matrix n n K} {x : n → K} {μ : K}
    (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) (y : n → K) :
    (X - C μ) * (A + Matrix.vecMulVec x y).charpoly = (X - C (μ + y ⬝ᵥ x)) * A.charpoly := by
  sorry

/-! ### Eigenvalues determined by the characteristic polynomial -/

/-- The characteristic polynomial of a Hermitian matrix through its sorted eigenvalues. -/
theorem _root_.Matrix.IsHermitian.charpoly_eq_prod_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    A.charpoly = ∏ i : Fin (Fintype.card n), (X - C ((eigenvalue A i : ℝ) : 𝕜)) := by
  sorry

/-- Hermitian matrices with the same characteristic polynomial have the same eigenvalues.
Port of `NLAlib.eigenvalues₀_eq_of_charpoly_eq`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_of_charpoly_eq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    eigenvalue A = eigenvalue B := by
  sorry

/-! ### Converses of interlacing -/

/-- **The converse of interlacing for a rank-one update.** If `b` interlaces the eigenvalues of
the Hermitian matrix `A` from above, `λ_i ≤ b_i` and `b_{i+1} ≤ λ_i`, there is a vector `z` such
that `A + z zᴴ` has eigenvalues `b`. [HornJohnson2013, Theorem 4.3.26].
Port of `NLAlib.exists_add_vecMulVec_charpoly_of_interlacing`, there over `ℝ`.
Result: interlacing-converse -/
theorem _root_.Matrix.IsHermitian.exists_eigenvalue_add_vecMulVec_star_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : ℕ → ℝ} (h₁ : ∀ i, i < Fintype.card n → eigenvalue A i ≤ b i)
    (h₂ : ∀ i, i + 1 < Fintype.card n → b (i + 1) ≤ eigenvalue A i) :
    ∃ z : n → 𝕜, ∀ i, i < Fintype.card n →
      eigenvalue (A + Matrix.vecMulVec z (star z)) i = b i := by
  sorry

/-- **The converse of Cauchy interlacing.** If `b_0 ≥ … ≥ b_n` interlaces the eigenvalues of the
Hermitian matrix `A` of size `n`, `b_{i+1} ≤ λ_i ≤ b_i`, there is a bordering of `A` by one row
and column with eigenvalues `b`. [HornJohnson2013, Theorem 4.3.21].
Port of `NLAlib.exists_bordered_charpoly_of_interlacing`, there over `ℝ`.
Result: interlacing-converse -/
theorem _root_.Matrix.IsHermitian.exists_eigenvalue_fromBlocks_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : ℕ → ℝ} (h₁ : ∀ i, i < Fintype.card n → eigenvalue A i ≤ b i)
    (h₂ : ∀ i, i < Fintype.card n → b (i + 1) ≤ eigenvalue A i) :
    ∃ (z : n → 𝕜) (a : ℝ), ∀ i, i < Fintype.card n + 1 →
      eigenvalue (Matrix.fromBlocks A (Matrix.replicateCol Unit z)
        (Matrix.replicateRow Unit (star z)) (Matrix.of fun _ _ => ((a : ℝ) : 𝕜))) i = b i := by
  sorry

end NLAlib
