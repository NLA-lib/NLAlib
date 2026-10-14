/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import NLAlib.Matrix.Norms.Nuclear
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.Schur

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
  `NLAlib.rank_kronecker`, `NLAlib.IsPinv.kronecker`, `NLAlib.pinv_kronecker`,
  `NLAlib.conditionNumber_kronecker`.
* `NLAlib.kronecker_eq_mul_diagonal_mul_conjTranspose`,
  `NLAlib.kronecker_one_add_one_kronecker_eq_mul_diagonal_mul_conjTranspose`: eigenvalues of a
  Kronecker product and of a Kronecker sum.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q r s : Type*}

/-! ### Frames and decompositions -/

/-- The Kronecker product of two matrices with orthonormal columns has orthonormal columns.
Port of `NLAlib.hasOrthonormalCols_kronecker`, there for real orthogonal matrices. -/
theorem HasOrthonormalCols.kronecker [Fintype m] [Fintype p] [DecidableEq n] [DecidableEq q]
    {U : Matrix m n 𝕜} {V : Matrix p q 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) : HasOrthonormalCols (U ⊗ₖ V) := by
  change (U ⊗ₖ V)ᴴ * (U ⊗ₖ V) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU.conjTranspose_mul_self,
    hV.conjTranspose_mul_self, Matrix.one_kronecker_one]

/-- The Kronecker product of two Hermitian matrices is Hermitian.
Port of `NLAlib.isHermitian_kronecker`. -/
theorem _root_.Matrix.IsHermitian.kronecker {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hA.eq, hB.eq]

/-- The Kronecker product of two diagonal factorizations. -/
private theorem mul_diagonal_mul_kronecker [Fintype r] [Fintype s] [DecidableEq r]
    [DecidableEq s] (U : Matrix m r 𝕜) (U' : Matrix n r 𝕜)
    (V : Matrix p s 𝕜) (V' : Matrix q s 𝕜) (a : r → 𝕜) (b : s → 𝕜) :
    (U * Matrix.diagonal a * U'ᴴ) ⊗ₖ (V * Matrix.diagonal b * V'ᴴ) =
      (U ⊗ₖ V) * Matrix.diagonal (fun ij : r × s => a ij.1 * b ij.2) * (U' ⊗ₖ V')ᴴ := by
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
    Matrix.conjTranspose_kronecker]

/-- **The singular value decomposition of a Kronecker product** is the Kronecker product of the
singular value decompositions, with singular values the products.
[HornJohnson1991, Theorem 4.2.15]. Port of `NLAlib.IsSVD.kronecker_factorization`. -/
theorem IsSVD.kronecker [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r] [Fintype s]
    [DecidableEq r] [DecidableEq s] {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ}
    {V : Matrix n r 𝕜} {B : Matrix p q 𝕜} {P : Matrix p s 𝕜} {τ : s → ℝ} {W : Matrix q s 𝕜}
    (hA : IsSVD A U σ V) (hB : IsSVD B P τ W) :
    IsSVD (A ⊗ₖ B) (U ⊗ₖ P) (fun ij : r × s => σ ij.1 * τ ij.2) (V ⊗ₖ W) := by
  refine ⟨hA.hasOrthonormalCols_left.kronecker hB.hasOrthonormalCols_left,
    hA.hasOrthonormalCols_right.kronecker hB.hasOrthonormalCols_right,
    fun ij => mul_nonneg (hA.nonneg _) (hB.nonneg _), ?_⟩
  have h := mul_diagonal_mul_kronecker U V P W (fun i => ((σ i : ℝ) : 𝕜))
    fun j => ((τ j : ℝ) : 𝕜)
  rw [← hA.eq, ← hB.eq] at h
  simpa only [RCLike.ofReal_mul] using h

/-- **Eigenvalues of a Kronecker product.** If `A = U diag(a) Uᴴ` and `B = V diag(b) Vᴴ`, then
`A ⊗ B = (U ⊗ V) diag(a_i b_j) (U ⊗ V)ᴴ`. [HornJohnson1991, Theorem 4.2.12].
Port of `NLAlib.eq_eigenvectorUnitary_kronecker_mul_diagonal_mul_transpose`. -/
theorem kronecker_eq_mul_diagonal_mul_conjTranspose [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {A U : Matrix m m 𝕜} {B V : Matrix n n 𝕜} {a : m → 𝕜} {b : n → 𝕜}
    (hA : A = U * Matrix.diagonal a * Uᴴ) (hB : B = V * Matrix.diagonal b * Vᴴ) :
    A ⊗ₖ B = (U ⊗ₖ V) * Matrix.diagonal (fun ij : m × n => a ij.1 * b ij.2) * (U ⊗ₖ V)ᴴ := by
  rw [← mul_diagonal_mul_kronecker, ← hA, ← hB]

/-- The diagonalisation of a Kronecker sum, for factors that need not be square. -/
private theorem kronecker_one_add_one_kronecker_eq [Fintype r] [Fintype s] [DecidableEq m]
    [DecidableEq n] [DecidableEq r] [DecidableEq s] {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    {U : Matrix m r 𝕜} {V : Matrix n s 𝕜} {a : r → 𝕜} {b : s → 𝕜} (hU : U * Uᴴ = 1)
    (hV : V * Vᴴ = 1) (hA : A = U * Matrix.diagonal a * Uᴴ)
    (hB : B = V * Matrix.diagonal b * Vᴴ) :
    A ⊗ₖ (1 : Matrix n n 𝕜) + (1 : Matrix m m 𝕜) ⊗ₖ B =
      (U ⊗ₖ V) * Matrix.diagonal (fun ij : r × s => a ij.1 + b ij.2) * (U ⊗ₖ V)ᴴ := by
  have h1 : (1 : Matrix n n 𝕜) = V * Matrix.diagonal (fun _ : s => (1 : 𝕜)) * Vᴴ := by
    rw [Matrix.diagonal_one, Matrix.mul_one, hV]
  have h2 : (1 : Matrix m m 𝕜) = U * Matrix.diagonal (fun _ : r => (1 : 𝕜)) * Uᴴ := by
    rw [Matrix.diagonal_one, Matrix.mul_one, hU]
  calc A ⊗ₖ (1 : Matrix n n 𝕜) + (1 : Matrix m m 𝕜) ⊗ₖ B
      = (U * Matrix.diagonal a * Uᴴ) ⊗ₖ (V * Matrix.diagonal (fun _ : s => (1 : 𝕜)) * Vᴴ) +
        (U * Matrix.diagonal (fun _ : r => (1 : 𝕜)) * Uᴴ) ⊗ₖ (V * Matrix.diagonal b * Vᴴ) := by
        rw [← h1, ← h2, ← hA, ← hB]
    _ = _ := by
        rw [mul_diagonal_mul_kronecker, mul_diagonal_mul_kronecker, ← Matrix.add_mul,
          ← Matrix.mul_add, Matrix.diagonal_add]
        simp only [mul_one, one_mul]

/-- **Eigenvalues of a Kronecker sum.** If `A = U diag(a) Uᴴ` and `B = V diag(b) Vᴴ` with `U`,
`V` unitary, then `A ⊗ 1 + 1 ⊗ B = (U ⊗ V) diag(a_i + b_j) (U ⊗ V)ᴴ`.
[HornJohnson1991, Theorem 4.4.5]. Port of `NLAlib.multiset_eigenvalues_kronecker_sum`. -/
theorem kronecker_one_add_one_kronecker_eq_mul_diagonal_mul_conjTranspose [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {A U : Matrix m m 𝕜} {B V : Matrix n n 𝕜} {a : m → 𝕜}
    {b : n → 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hA : A = U * Matrix.diagonal a * Uᴴ) (hB : B = V * Matrix.diagonal b * Vᴴ) :
    A ⊗ₖ (1 : Matrix n n 𝕜) + (1 : Matrix m m 𝕜) ⊗ₖ B =
      (U ⊗ₖ V) * Matrix.diagonal (fun ij : m × n => a ij.1 + b ij.2) * (U ⊗ₖ V)ᴴ :=
  kronecker_one_add_one_kronecker_eq hU.mul_conjTranspose_self hV.mul_conjTranspose_self hA hB

/-- The Kronecker product of two upper triangular matrices is triangular for the lexicographic
order. -/
private theorem blockTriangular_toLex_kronecker {K : Type*} [Field K] [LinearOrder m]
    [LinearOrder n] {M : Matrix m m K} {N : Matrix n n K} (hM : M.IsUpperTriangular)
    (hN : N.IsUpperTriangular) : (M ⊗ₖ N).BlockTriangular (toLex : m × n → m ×ₗ n) := by
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ h
  rw [Matrix.kronecker_apply]
  rcases Prod.Lex.toLex_lt_toLex.mp h with h1 | ⟨-, h2⟩
  · rw [hM h1, zero_mul]
  · rw [hN h2, mul_zero]

/-- The diagonal of a matrix that is triangular for the lexicographic order lists its
eigenvalues. -/
private theorem charpoly_of_blockTriangular_toLex [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {K : Type*} [Field K] [LinearOrder m] [LinearOrder n]
    {M : Matrix (m × n) (m × n) K}
    (h : M.BlockTriangular (toLex : m × n → m ×ₗ n)) :
    M.charpoly = ∏ ij, (X - C (M ij ij)) := by
  have h' : (Matrix.reindex toLex toLex M).IsUpperTriangular := fun i j hij => h hij
  rw [← Matrix.charpoly_reindex toLex M, Matrix.charpoly_of_isUpperTriangular _ h']
  exact Equiv.prod_comp toLex.symm fun ij : m × n => X - C (M ij ij)

/-- Two matrices whose eigenvalues are listed are similar to triangular matrices with the
listings on the diagonal; the Kronecker product of the similarities triangularises the Kronecker
product and the Kronecker sum. -/
private theorem exists_kronecker_similarity [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {K : Type*} [Field K] [LinearOrder m] [LinearOrder n] {A : Matrix m m K}
    {B : Matrix n n K} {a : m → K} {b : n → K}
    (hA : IsEigenvalueListing A a) (hB : IsEigenvalueListing B b) :
    ∃ (P Q : Matrix (m × n) (m × n) K) (S : Matrix m m K) (T : Matrix n n K), Q * P = 1 ∧
      S.IsUpperTriangular ∧ T.IsUpperTriangular ∧ (∀ i, S i i = a i) ∧ (∀ j, T j j = b j) ∧
      P * (A ⊗ₖ B) * Q = S ⊗ₖ T ∧
      P * (A ⊗ₖ (1 : Matrix n n K) + (1 : Matrix m m K) ⊗ₖ B) * Q =
        S ⊗ₖ (1 : Matrix n n K) + (1 : Matrix m m K) ⊗ₖ T := by
  obtain ⟨F, hF, hS, hdS, -⟩ :=
    hA.exists_isUpperTriangular_inv_mul_mul_of_commute (Commute.refl A) hA.splits_charpoly
  obtain ⟨G, hG, hT, hdT, -⟩ :=
    hB.exists_isUpperTriangular_inv_mul_mul_of_commute (Commute.refl B) hB.splits_charpoly
  refine ⟨F⁻¹ ⊗ₖ G⁻¹, F ⊗ₖ G, F⁻¹ * A * F, G⁻¹ * B * G, ?_, hS, hT, hdS, hdT, ?_, ?_⟩
  · rw [← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv _ hF, Matrix.mul_nonsing_inv _ hG,
      Matrix.one_kronecker_one]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  · rw [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hF, Matrix.nonsing_inv_mul _ hG]

/-- **The eigenvalues of a Kronecker product are the products of the eigenvalues**, for any two
square matrices whose eigenvalues are listed. [HornJohnson1991, Theorem 4.2.12]. -/
theorem IsEigenvalueListing.kronecker [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {K : Type*} [Field K] {A : Matrix m m K} {B : Matrix n n K} {a : m → K} {b : n → K}
    (hA : IsEigenvalueListing A a) (hB : IsEigenvalueListing B b) :
    IsEigenvalueListing (A ⊗ₖ B) fun ij : m × n => a ij.1 * b ij.2 := by
  let _ : LinearOrder m := LinearOrder.lift' (Fintype.equivFin m) (Fintype.equivFin m).injective
  let _ : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨P, Q, S, T, hQP, hS, hT, hdS, hdT, hprod, -⟩ := exists_kronecker_similarity hA hB
  rw [isEigenvalueListing_iff, ← charpoly_mul_mul_of_mul_eq_one (mul_eq_one_comm.mp hQP), hprod,
    charpoly_of_blockTriangular_toLex (blockTriangular_toLex_kronecker hS hT)]
  simp only [Matrix.kroneckerMap_apply, hdS, hdT]

/-- **The eigenvalues of a Kronecker sum are the sums of the eigenvalues.**
[HornJohnson1991, Theorem 4.4.5]. -/
theorem IsEigenvalueListing.kronecker_one_add_one_kronecker [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {K : Type*} [Field K] {A : Matrix m m K} {B : Matrix n n K}
    {a : m → K} {b : n → K} (hA : IsEigenvalueListing A a) (hB : IsEigenvalueListing B b) :
    IsEigenvalueListing (A ⊗ₖ (1 : Matrix n n K) + (1 : Matrix m m K) ⊗ₖ B)
      fun ij : m × n => a ij.1 + b ij.2 := by
  let _ : LinearOrder m := LinearOrder.lift' (Fintype.equivFin m) (Fintype.equivFin m).injective
  let _ : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  obtain ⟨P, Q, S, T, hQP, hS, hT, hdS, hdT, -, hsum⟩ := exists_kronecker_similarity hA hB
  rw [isEigenvalueListing_iff, ← charpoly_mul_mul_of_mul_eq_one (mul_eq_one_comm.mp hQP), hsum,
    charpoly_of_blockTriangular_toLex
      ((blockTriangular_toLex_kronecker hS Matrix.blockTriangular_one).add
        (blockTriangular_toLex_kronecker Matrix.blockTriangular_one hT))]
  simp only [Matrix.add_apply, Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one, one_mul,
    hdS, hdT]

/-- The largest eigenvalue of a unitarily diagonalised Hermitian matrix is the largest entry of
the diagonal factor. -/
private theorem eigenvalue_zero_eq_of_eq_mul_diagonal_mul_conjTranspose [Fintype m] [Fintype r]
    [DecidableEq r] {M : Matrix m m 𝕜} {W : Matrix m r 𝕜} {d : r → ℝ} (hM : M.IsHermitian)
    (hW : HasOrthonormalCols W)
    (hr : Fintype.card m = Fintype.card r)
    (h : M = W * (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) * Wᴴ) {i₀ : r}
    (hi₀ : ∀ i, d i ≤ d i₀) : eigenvalue M 0 = d i₀ := by
  obtain ⟨e, he⟩ := exists_equiv_eq_eigenvalue_of_eq_mul_diagonal_mul_conjTranspose hW hr h
  have hpos : 0 < Fintype.card m := hr ▸ Fintype.card_pos_iff.mpr ⟨i₀⟩
  refine le_antisymm ?_ ?_
  · calc eigenvalue M 0 = d (e.symm ⟨0, hpos⟩) := by rw [he, Equiv.apply_symm_apply]
      _ ≤ d i₀ := hi₀ _
  · rw [he i₀]
    exact hM.eigenvalue_le_eigenvalue (Nat.zero_le _) (e i₀).isLt

/-- The largest eigenvalue of a Kronecker sum of Hermitian matrices is the sum of the largest
eigenvalues. -/
theorem eigenvalue_zero_kronecker_one_add_one_kronecker [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [Nonempty m] [Nonempty n] {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    eigenvalue (A ⊗ₖ (1 : Matrix n n 𝕜) + (1 : Matrix m m 𝕜) ⊗ₖ B) 0 =
      eigenvalue A 0 + eigenvalue B 0 := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  obtain ⟨V, hV, hBV⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  have hM := kronecker_one_add_one_kronecker_eq
    (hU.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm)
    (hV.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm) hAU hBV
  simp only [← RCLike.ofReal_add] at hM
  exact eigenvalue_zero_eq_of_eq_mul_diagonal_mul_conjTranspose
    ((hA.kronecker Matrix.isHermitian_one).add (Matrix.isHermitian_one.kronecker hB))
    (hU.kronecker hV) (by simp only [Fintype.card_prod, Fintype.card_fin]) hM
    (i₀ := (⟨0, Fintype.card_pos⟩, ⟨0, Fintype.card_pos⟩)) fun ij =>
      add_le_add (hA.eigenvalue_le_eigenvalue (Nat.zero_le _) ij.1.isLt)
        (hB.eigenvalue_le_eigenvalue (Nat.zero_le _) ij.2.isLt)

/-- The largest eigenvalue of a Kronecker product of positive semidefinite matrices is the
product of the largest eigenvalues. -/
theorem eigenvalue_zero_kronecker [Fintype m] [Fintype n] {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    eigenvalue (A ⊗ₖ B) 0 = eigenvalue A 0 * eigenvalue B 0 := by
  rcases isEmpty_or_nonempty m with hm | hm
  · rw [eigenvalue_of_card_le _ (by simp), eigenvalue_of_card_le A (by simp), zero_mul]
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [eigenvalue_of_card_le _ (by simp), eigenvalue_of_card_le B (by simp), mul_zero]
  obtain ⟨U, hU, hAU⟩ := hA.isHermitian.exists_eq_mul_diagonal_mul_conjTranspose
  obtain ⟨V, hV, hBV⟩ := hB.isHermitian.exists_eq_mul_diagonal_mul_conjTranspose
  have hM := mul_diagonal_mul_kronecker U U V V (fun i => ((eigenvalue A i : ℝ) : 𝕜))
    fun i => ((eigenvalue B i : ℝ) : 𝕜)
  simp only [← RCLike.ofReal_mul] at hM
  rw [← hAU, ← hBV] at hM
  exact eigenvalue_zero_eq_of_eq_mul_diagonal_mul_conjTranspose
    (hA.isHermitian.kronecker hB.isHermitian) (hU.kronecker hV)
    (by simp only [Fintype.card_prod, Fintype.card_fin]) hM
    (i₀ := (⟨0, Fintype.card_pos⟩, ⟨0, Fintype.card_pos⟩)) fun ij =>
      mul_le_mul (hA.isHermitian.eigenvalue_le_eigenvalue (Nat.zero_le _) ij.1.isLt)
        (hB.isHermitian.eigenvalue_le_eigenvalue (Nat.zero_le _) ij.2.isLt)
        (hB.eigenvalue_nonneg _) (hA.eigenvalue_nonneg _)

/-! ### Norms, rank and pseudoinverse -/

/-- A supremum norm bound through a positive factor. -/
private theorem mul_pi_norm_le {ι : Type*} [Fintype ι] {f : ι → ℝ} {a c : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (h : ∀ i, a * ‖f i‖ ≤ c) : a * ‖f‖ ≤ c := by
  rcases ha.eq_or_lt with rfl | ha'
  · rwa [zero_mul]
  · rw [← le_div_iff₀' ha']
    exact (pi_norm_le_iff_of_nonneg (div_nonneg hc ha)).2 fun i => (le_div_iff₀' ha').2 (h i)

/-- The supremum norm of a family of products is the product of the supremum norms. -/
private theorem pi_norm_mul_apply [Fintype r] [Fintype s] (σ : r → ℝ) (τ : s → ℝ) :
    ‖fun ij : r × s => σ ij.1 * τ ij.2‖ = ‖σ‖ * ‖τ‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun ij => ?_) ?_
  · rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm σ ij.1) (norm_le_pi_norm τ ij.2) (norm_nonneg _)
      (norm_nonneg _)
  · refine mul_pi_norm_le (norm_nonneg _) (norm_nonneg _) fun j => ?_
    rw [mul_comm]
    refine mul_pi_norm_le (norm_nonneg _) (norm_nonneg _) fun i => ?_
    rw [mul_comm, ← norm_mul]
    exact norm_le_pi_norm (fun ij : r × s => σ ij.1 * τ ij.2) (i, j)

/-- **The spectral norm is multiplicative on Kronecker products.**
[HornJohnson1991, Theorem 4.2.15]. Port of `NLAlib.specNorm_kronecker`, there over `ℝ`. -/
theorem specNorm_kronecker [Fintype m] [Fintype n] [Fintype p] [Fintype q] (A : Matrix m n 𝕜)
    (B : Matrix p q 𝕜) :
    specNorm (A ⊗ₖ B) = specNorm A * specNorm B := by
  obtain ⟨U, V, hA⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  obtain ⟨P, W, hB⟩ := exists_isSVD B le_rfl B.rank_le_card_height B.rank_le_card_width
  rw [(hA.kronecker hB).specNorm_eq, hA.specNorm_eq, hB.specNorm_eq]
  exact pi_norm_mul_apply (fun i : Fin A.rank => singularValues A i) fun j : Fin B.rank =>
    singularValues B j

/-- The Frobenius norm is multiplicative on Kronecker products.
Port of `NLAlib.frobNorm_kronecker`. -/
theorem frobNorm_kronecker [Fintype m] [Fintype n] [Fintype p] [Fintype q] (A : Matrix m n 𝕜)
    (B : Matrix p q 𝕜) :
    frobNorm (A ⊗ₖ B) = frobNorm A * frobNorm B := by
  obtain ⟨U, V, hA⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  obtain ⟨P, W, hB⟩ := exists_isSVD B le_rfl B.rank_le_card_height B.rank_le_card_width
  refine (sq_eq_sq₀ (frobNorm_nonneg _) (mul_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _))).mp ?_
  rw [mul_pow, (hA.kronecker hB).frobNorm_sq_eq, hA.frobNorm_sq_eq, hB.frobNorm_sq_eq,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp only [mul_pow]

/-- The nuclear norm is multiplicative on Kronecker products. -/
theorem nuclearNorm_kronecker [Fintype m] [Fintype n] [Fintype p] [Fintype q] (A : Matrix m n 𝕜)
    (B : Matrix p q 𝕜) :
    nuclearNorm (A ⊗ₖ B) = nuclearNorm A * nuclearNorm B := by
  obtain ⟨U, V, hA⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  obtain ⟨P, W, hB⟩ := exists_isSVD B le_rfl B.rank_le_card_height B.rank_le_card_width
  rw [(hA.kronecker hB).nuclearNorm_eq_sum, hA.nuclearNorm_eq_sum, hB.nuclearNorm_eq_sum,
    Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- **The rank is multiplicative on Kronecker products.**
[HornJohnson1991, Theorem 4.2.15]. Port of `NLAlib.rank_kronecker`, there over `ℝ`. -/
theorem rank_kronecker [Finite m] [Fintype n] [Finite p] [Fintype q] (A : Matrix m n 𝕜)
    (B : Matrix p q 𝕜) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  cases nonempty_fintype m
  cases nonempty_fintype p
  obtain ⟨U, V, hA⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  obtain ⟨P, W, hB⟩ := exists_isSVD B le_rfl B.rank_le_card_height B.rank_le_card_width
  rw [(hA.kronecker hB).rank_eq]
  conv_rhs => rw [hA.rank_eq, hB.rank_eq, ← Finset.card_product]
  refine congrArg Finset.card (Finset.ext fun ij => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, mul_ne_zero_iff]

/-- The Penrose identities pass to Kronecker products: if `A'` is the pseudoinverse of `A` and
`B'` that of `B`, both recognised through `IsPinv`, then `A' ⊗ₖ B'` is the pseudoinverse of
`A ⊗ₖ B`. -/
theorem IsPinv.kronecker [Fintype m] [Fintype n] [Fintype p] [Fintype q] {A : Matrix m n 𝕜}
    {A' : Matrix n m 𝕜} {B : Matrix p q 𝕜} {B' : Matrix q p 𝕜} (hA : IsPinv A A')
    (hB : IsPinv B B') : IsPinv (A ⊗ₖ B) (A' ⊗ₖ B') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hA.mul_mul_left,
      hB.mul_mul_left]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hA.mul_mul_right,
      hB.mul_mul_right]
  · rw [← Matrix.mul_kronecker_mul]
    exact hA.isHermitian_left.kronecker hB.isHermitian_left
  · rw [← Matrix.mul_kronecker_mul]
    exact hA.isHermitian_right.kronecker hB.isHermitian_right

/-- **The pseudoinverse of a Kronecker product** is the Kronecker product of the pseudoinverses.
Port of `NLAlib.moorePenroseInverse_kronecker`, there over `ℝ`. -/
theorem pinv_kronecker [Fintype m] [Fintype n] [Fintype p] [Fintype q] (A : Matrix m n 𝕜)
    (B : Matrix p q 𝕜) :
    pinv (A ⊗ₖ B) = pinv A ⊗ₖ pinv B :=
  ((isPinv_pinv A).kronecker (isPinv_pinv B)).pinv_eq

/-- The condition number is multiplicative on Kronecker products. -/
theorem conditionNumber_kronecker [Fintype m] [Fintype n] [Fintype p] [Fintype q] (A : Matrix m n 𝕜)
    (B : Matrix p q 𝕜) :
    conditionNumber (A ⊗ₖ B) = conditionNumber A * conditionNumber B := by
  rw [conditionNumber, pinv_kronecker, specNorm_kronecker, specNorm_kronecker, conditionNumber,
    conditionNumber, mul_mul_mul_comm]

end NLAlib
