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
rank-one update along an eigenvector. The sorted eigenvalues of a Hermitian matrix are a listing
of its eigenvalues, so they are determined by the characteristic polynomial. The converses of
the interlacing theorems, which rest on the secular equation, are in
`NLAlib.Matrix.Spectral.InterlacingConverse`.

## Main results

* `NLAlib.det_add_vecMulVec`: the matrix determinant lemma.
* `NLAlib.charpoly_diagonal_add_vecMulVec`: the secular equation.
* `NLAlib.charpoly_fromBlocks_diagonal_replicateCol`: the characteristic polynomial of an
  arrowhead matrix.
* `NLAlib.charpoly_add_vecMulVec_mul`: Brauer's theorem.
* `Matrix.IsHermitian.isEigenvalueListing_eigenvalue`: the sorted eigenvalues are a listing.
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
  have hfactor : M + Matrix.vecMulVec u v = M * (1 + Matrix.vecMulVec (M⁻¹ *ᵥ u) v) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
  rw [hfactor, Matrix.det_mul, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]

/-- The determinant of a matrix bordered by one row and one column, through the adjugate, when
the determinant of the matrix is not a zero divisor. -/
private theorem det_fromBlocks_replicateCol_of_isRegular {S : Type*} [CommRing S]
    {A : Matrix n n S} (hA : IsRegular A.det) (u w : n → S) (a : S) :
    (Matrix.fromBlocks A (Matrix.replicateCol Unit u) (Matrix.replicateRow Unit w)
      (Matrix.of fun _ _ => a)).det = A.det * a - w ⬝ᵥ A.adjugate *ᵥ u := by
  have hmul : Matrix.fromBlocks A.adjugate 0 (-(Matrix.replicateRow Unit w * A.adjugate))
        (A.det • (1 : Matrix Unit Unit S)) *
      Matrix.fromBlocks A (Matrix.replicateCol Unit u) (Matrix.replicateRow Unit w)
        (Matrix.of fun _ _ => a) =
      Matrix.fromBlocks (A.det • (1 : Matrix n n S)) (A.adjugate * Matrix.replicateCol Unit u) 0
        (Matrix.of fun _ _ => A.det * a - w ⬝ᵥ A.adjugate *ᵥ u) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · rw [Matrix.adjugate_mul, Matrix.zero_mul, add_zero]
    · rw [Matrix.zero_mul, add_zero]
    · rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.one_mul, neg_add_cancel]
    · ext i j
      rw [Matrix.neg_mul, Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, Matrix.add_apply,
        Matrix.neg_apply, Matrix.replicateRow_mul_replicateCol_apply, Matrix.smul_mul,
        Matrix.one_mul, Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, smul_eq_mul]
      ring
  have h := congrArg Matrix.det hmul
  have h1 : (A.det • (1 : Matrix n n S)).det = A.adjugate.det * A.det := by
    rw [← Matrix.adjugate_mul, Matrix.det_mul]
  have hreg : IsRegular (A.adjugate.det * A.det) := by
    rw [← h1, Matrix.det_smul, Matrix.det_one, mul_one]
    exact hA.pow _
  have h2 : (A.det • (1 : Matrix Unit Unit S)).det = A.det := by
    rw [Matrix.det_unique, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁, h1, h2,
    Matrix.det_unique (Matrix.of _), Matrix.of_apply] at h
  exact hreg.left h

/-- The determinant of a rank-one update through the adjugate, when the determinant of the
matrix is not a zero divisor. -/
private theorem det_sub_vecMulVec_of_isRegular {S : Type*} [CommRing S] {A : Matrix n n S}
    (hA : IsRegular A.det) (u v : n → S) :
    (A - Matrix.vecMulVec u v).det = A.det - v ⬝ᵥ A.adjugate *ᵥ u := by
  have h1 : (1 : Matrix Unit Unit S) = Matrix.of fun _ _ => 1 := by
    ext i j
    rw [Matrix.one_apply_eq, Matrix.of_apply]
  rw [Matrix.vecMulVec_eq Unit, ← Matrix.det_fromBlocks_one₂₂, h1,
    det_fromBlocks_replicateCol_of_isRegular hA, mul_one]

/-- **The secular equation**: the characteristic polynomial of a diagonal matrix plus a rank-one
matrix. [GolubVanLoan2013, §8.4.3]. Port of `NLAlib.charpoly_diagonal_add_vecMulVec`. -/
theorem charpoly_diagonal_add_vecMulVec {R : Type*} [CommRing R] (d u v : n → R) :
    (Matrix.diagonal d + Matrix.vecMulVec u v).charpoly =
      ∏ i, (X - C (d i)) - ∑ i, C (u i * v i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  have hcm : (Matrix.diagonal d + Matrix.vecMulVec u v).charmatrix =
      Matrix.diagonal (fun i => X - C (d i)) -
        Matrix.vecMulVec (fun i => C (u i)) fun i => C (v i) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.charmatrix_apply_eq, Matrix.add_apply, Matrix.diagonal_apply_eq,
        Matrix.vecMulVec_apply, Matrix.sub_apply, C_add, C_mul]
      ring
    · simp only [Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.add_apply,
        Matrix.diagonal_apply_ne _ hij, Matrix.vecMulVec_apply, Matrix.sub_apply, C_add, C_mul,
        C_0]
      ring
  have hreg : IsRegular (Matrix.diagonal fun i => X - C (d i)).det := by
    rw [Matrix.det_diagonal]
    exact (monic_prod_X_sub_C d Finset.univ).isRegular
  rw [Matrix.charpoly, hcm, det_sub_vecMulVec_of_isRegular hreg, Matrix.det_diagonal,
    Matrix.adjugate_diagonal, dotProduct]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [Matrix.mulVec_diagonal, C_mul]
  ring

/-- The determinant of a diagonal matrix plus a rank-one matrix, with no invertibility
assumption. Port of `NLAlib.det_diagonal_add_vecMulVec_of_forall_ne_zero`. -/
theorem det_diagonal_add_vecMulVec {R : Type*} [CommRing R] (d u v : n → R) :
    (Matrix.diagonal d + Matrix.vecMulVec u v).det =
      ∏ i, d i + ∑ i, u i * v i * ∏ j ∈ Finset.univ.erase i, d j := by
  have h := congrArg (Polynomial.eval 0)
    (charpoly_diagonal_add_vecMulVec (fun i => -d i) (fun i => -u i) v)
  have hmat : Matrix.scalar n (0 : R) -
      (Matrix.diagonal (fun i => -d i) + Matrix.vecMulVec (fun i => -u i) v) =
      Matrix.diagonal d + Matrix.vecMulVec u v := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Matrix.add_apply, Matrix.vecMulVec_apply]
      ring
    · simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij,
        Matrix.add_apply, Matrix.vecMulVec_apply]
      ring
  rw [Matrix.eval_charpoly, hmat] at h
  rw [h]
  simp only [eval_sub, eval_prod, eval_X, eval_C, eval_finsetSum, eval_mul, neg_mul,
    Finset.sum_neg_distrib, sub_neg_eq_add, zero_add]

/-- **The characteristic polynomial of an arrowhead matrix**: a diagonal matrix bordered by one
row and one column. [GolubVanLoan2013, §8.4.3 context].
Port of `NLAlib.charpoly_fromBlocks_diagonal_replicate`. -/
theorem charpoly_fromBlocks_diagonal_replicateCol {R : Type*} [CommRing R] (d u w : n → R)
    (a : R) :
    (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol Unit u)
      (Matrix.replicateRow Unit w) (Matrix.of fun _ _ => a)).charpoly =
      (X - C a) * ∏ i, (X - C (d i)) -
        ∑ i, C (u i * w i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  have hcm : (Matrix.fromBlocks (Matrix.diagonal d) (Matrix.replicateCol Unit u)
      (Matrix.replicateRow Unit w) (Matrix.of fun _ _ => a)).charmatrix =
      Matrix.fromBlocks (Matrix.diagonal fun i => X - C (d i))
        (Matrix.replicateCol Unit fun i => -C (u i)) (Matrix.replicateRow Unit fun i => -C (w i))
        (Matrix.of fun _ _ => X - C a) := by
    rw [Matrix.charmatrix_fromBlocks, Matrix.charmatrix_diagonal]
    congr 1
  have hreg : IsRegular (Matrix.diagonal fun i => X - C (d i)).det := by
    rw [Matrix.det_diagonal]
    exact (monic_prod_X_sub_C d Finset.univ).isRegular
  rw [Matrix.charpoly, hcm, det_fromBlocks_replicateCol_of_isRegular hreg, Matrix.det_diagonal,
    Matrix.adjugate_diagonal, dotProduct, mul_comm]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [Matrix.mulVec_diagonal, C_mul]
  ring

/-- **Brauer's theorem.** A rank-one update along an eigenvector `x` of `A` with eigenvalue `μ`
moves `μ` to `μ + yᵀ x` and leaves the other eigenvalues in place, as an identity of
characteristic polynomials over any commutative ring.
[HornJohnson2013, Theorem 1.2.8 context], there over `ℂ`.
Port of `NLAlib.charpoly_add_vecMulVec_mul_X_sub_C`. -/
theorem charpoly_add_vecMulVec_mul {R : Type*} [CommRing R] {A : Matrix n n R} {x : n → R}
    {μ : R} (hAx : A *ᵥ x = μ • x) (y : n → R) :
    (X - C μ) * (A + Matrix.vecMulVec x y).charpoly = (X - C (μ + y ⬝ᵥ x)) * A.charpoly := by
  have hcm : (A + Matrix.vecMulVec x y).charmatrix =
      A.charmatrix - Matrix.vecMulVec (fun i => C (x i)) fun i => C (y i) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.charmatrix_apply_eq, Matrix.add_apply, Matrix.vecMulVec_apply,
        Matrix.sub_apply, C_add, C_mul]
      ring
    · simp only [Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.add_apply, Matrix.vecMulVec_apply,
        Matrix.sub_apply, C_add, C_mul]
      ring
  have hreg : IsRegular A.charmatrix.det := (Matrix.charpoly_monic A).isRegular
  have hmv : A.charmatrix *ᵥ (fun i => C (x i)) = (X - C μ) • fun i => C (x i) := by
    funext i
    have h1 := congrArg C (congrFun hAx i)
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, map_sum, C_mul] at h1 ⊢
    rw [Finset.sum_congr rfl fun j _ => by rw [Matrix.charmatrix_apply, sub_mul],
      Finset.sum_sub_distrib, h1, Finset.sum_eq_single i (fun j _ hji => by
        rw [Matrix.diagonal_apply_ne _ hji.symm, zero_mul]) (fun h => absurd (Finset.mem_univ i) h),
      Matrix.diagonal_apply_eq]
    ring
  have hadj : (X - C μ) • A.charmatrix.adjugate *ᵥ (fun i => C (x i)) =
      A.charpoly • fun i => C (x i) := by
    rw [← Matrix.mulVec_smul, ← hmv, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  have hdot : (X - C μ) * ((fun i => C (y i)) ⬝ᵥ A.charmatrix.adjugate *ᵥ fun i => C (x i)) =
      A.charpoly * C (y ⬝ᵥ x) := by
    rw [← smul_eq_mul, ← dotProduct_smul, hadj, dotProduct_smul, smul_eq_mul]
    congr 1
    simp only [dotProduct, map_sum, C_mul]
  rw [Matrix.charpoly, hcm, det_sub_vecMulVec_of_isRegular hreg, mul_sub, hdot, C_add]
  rw [Matrix.charpoly]
  ring

/-! ### Eigenvalues determined by the characteristic polynomial -/

/-- The sorted eigenvalues of a Hermitian matrix list its eigenvalues. -/
theorem _root_.Matrix.IsHermitian.isEigenvalueListing_eigenvalue {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    IsEigenvalueListing A (fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) := by
  obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
  rw [isEigenvalueListing_iff, hA.charpoly_eq]
  exact Fintype.prod_equiv e _ _ fun i => by rw [he]

/-- Hermitian matrices with the same characteristic polynomial have the same eigenvalues.
Port of `NLAlib.eigenvalues₀_eq_of_charpoly_eq`. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_of_charpoly_eq {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    eigenvalue A = eigenvalue B := by
  funext k
  by_cases hk : k < Fintype.card n
  · have h1 := hA.sort_roots_charpoly_eq_eigenvalues₀
    rw [h, hB.sort_roots_charpoly_eq_eigenvalues₀] at h1
    rw [hA.eigenvalue_eq_eigenvalues₀ ⟨k, hk⟩, hB.eigenvalue_eq_eigenvalues₀ ⟨k, hk⟩,
      List.ofFn_injective h1]
  · rw [eigenvalue_of_card_le A (not_lt.mp hk), eigenvalue_of_card_le B (not_lt.mp hk)]

end NLAlib
