/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SVD
public import NLAlib.Matrix.Spectral.SingularValueInequalities

/-!
# Best low-rank approximation: the Eckart–Young theorem

`NLAlib.truncatedSVD A k` is a best approximation of `A` of rank at most `k`, obtained by keeping
the `k` largest singular triples of a singular value decomposition. Its error is
`singularValues A k` in the spectral norm and `√(∑_{i ≥ k} σ_i²)` in the Frobenius norm, and no
matrix of rank at most `k` does better in either norm.

The best rank-`k` error is spelled `singularValues A k` in the spectral norm and
`frobNorm (A - truncatedSVD A k)` in the Frobenius norm; `NLAlib.frobNorm_sub_truncatedSVD_sq`
rewrites the latter as the tail sum of squared singular values.

When `singularValues A (k - 1) = singularValues A k` the best approximation is not unique;
`truncatedSVD A k` is one of them, built from a chosen decomposition.

## Main definitions

* `NLAlib.truncatedSVD`: a best approximation of rank at most `k`.

## Main results

* `NLAlib.rank_truncatedSVD_le`, `NLAlib.specNorm_sub_truncatedSVD`,
  `NLAlib.frobNorm_sub_truncatedSVD_sq`: rank and errors of the truncation.
* `NLAlib.singularValues_le_specNorm_sub_of_rank_le`: Eckart–Young in the spectral norm.
* `NLAlib.frobNorm_sub_truncatedSVD_le_of_rank_le`: Eckart–Young in the Frobenius norm.
* `NLAlib.isLeast_specNorm_sub_of_rank_le`, `NLAlib.isLeast_frobNorm_sub_of_rank_le`: the same as
  least elements.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The **truncated singular value decomposition**: a best approximation of `A` of rank at most
`k`, obtained from a singular value decomposition `A = U Σ Vᴴ` by keeping the `k` largest
singular values. The decomposition is chosen, so when `σ_{k-1} = σ_k` this is one of several
best approximations. For `k ≥ rank A` it is `A`.
[GolubVanLoan2013, Theorem 2.4.8]. Port of `NLAlib.truncatedSVD`. -/
noncomputable def truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  let h := exists_isSVD A (k := min (Fintype.card m) (Fintype.card n))
    (le_min A.rank_le_card_height A.rank_le_card_width) (min_le_left _ _) (min_le_right _ _)
  h.choose *
    Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) *
    h.choose_spec.chooseᴴ

/-! ### The truncation -/

/-- The truncated SVD has rank at most `k`. Port of `NLAlib.IsSVD.rank_truncatedMatrix_le`. -/
theorem rank_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) : (truncatedSVD A k).rank ≤ k := by
  sorry

/-- The truncated SVD has rank exactly `k` when `k` is at most the rank of `A`. -/
theorem rank_truncatedSVD (A : Matrix m n 𝕜) {k : ℕ} (hk : k ≤ A.rank) :
    (truncatedSVD A k).rank = k := by
  sorry

/-- Truncating at or beyond the rank returns the matrix. -/
theorem truncatedSVD_of_rank_le (A : Matrix m n 𝕜) {k : ℕ} (hk : A.rank ≤ k) :
    truncatedSVD A k = A := by
  sorry

/-- Truncating to rank zero gives the zero matrix. -/
@[simp]
theorem truncatedSVD_zero (A : Matrix m n 𝕜) : truncatedSVD A 0 = 0 := by
  sorry

/-- The singular values of the truncated SVD are the first `k` singular values of `A`. -/
theorem singularValues_truncatedSVD (A : Matrix m n 𝕜) (k i : ℕ) :
    singularValues (truncatedSVD A k) i = if i < k then singularValues A i else 0 := by
  sorry

/-- The singular values of the truncation error are the singular values of `A` from the `k`-th
on. -/
theorem singularValues_sub_truncatedSVD (A : Matrix m n 𝕜) (k i : ℕ) :
    singularValues (A - truncatedSVD A k) i = singularValues A (k + i) := by
  sorry

/-- **The spectral error of the truncated SVD is the `k`-th singular value.**
[GolubVanLoan2013, Theorem 2.4.8]. Port of `NLAlib.specNorm_sub_truncatedSVD_eq`. -/
@[simp]
theorem specNorm_sub_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    specNorm (A - truncatedSVD A k) = singularValues A k := by
  sorry

/-- **The squared Frobenius error of the truncated SVD is the tail sum of squared singular
values.** This is the rewrite rule that turns the best rank-`k` Frobenius error into a sum.
[GolubVanLoan2013, §2.4]. Port of `NLAlib.frobSq_sub_truncatedSVD_eq_bestRankFrobSq`, there
through a named `bestRankFrobSq`. -/
theorem frobNorm_sub_truncatedSVD_sq (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD A k) ^ 2 =
      ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 := by
  sorry

/-- The truncated SVD and its error are orthogonal in the Frobenius inner product. -/
theorem frobInner_truncatedSVD_sub (A : Matrix m n 𝕜) (k : ℕ) :
    frobInner (truncatedSVD A k) (A - truncatedSVD A k) = 0 := by
  sorry

/-- Pythagoras for the truncated SVD: `‖A‖_F² = ‖A_k‖_F² + ‖A - A_k‖_F²`. -/
theorem frobNorm_sq_eq_truncatedSVD_add (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm A ^ 2 = frobNorm (truncatedSVD A k) ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2 := by
  sorry

/-- The truncated SVD is the projection of `A` onto its own column space:
`rangeProjector (truncatedSVD A k) * A = truncatedSVD A k`. -/
theorem rangeProjector_truncatedSVD_mul (A : Matrix m n 𝕜) (k : ℕ) :
    rangeProjector (truncatedSVD A k) * A = truncatedSVD A k := by
  sorry

/-- The column space of the truncated SVD is inside the column space of `A`. -/
theorem range_mulVecLin_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) :
    LinearMap.range (truncatedSVD A k).mulVecLin ≤ LinearMap.range A.mulVecLin := by
  sorry

/-! ### Eckart–Young -/

/-- **Eckart–Young in the spectral norm.** No matrix of rank at most `k` is closer to `A` in
spectral norm than `singularValues A k`.
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9].
Port of `NLAlib.singularValues_le_specNorm_sub_of_rank_le`.
Result: eckart-young-spectral -/
theorem singularValues_le_specNorm_sub_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : singularValues A k ≤ specNorm (A - B) := by
  sorry

/-- **Eckart–Young in the Frobenius norm**, tail-sum form. For every `B` of rank at most `k`,
`∑_{i ≥ k} σ_i(A)² ≤ ‖A - B‖_F²`.
[HornJohnson2013, §7.4.9]. Port of `NLAlib.bestRankFrobSq_le_frobSq_sub_of_rank_le`.
Result: eckart-young-frobenius -/
theorem sum_Ico_singularValues_sq_le_frobNorm_sub_sq_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) :
    ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 ≤
      frobNorm (A - B) ^ 2 := by
  sorry

/-- **Eckart–Young in the Frobenius norm.** No matrix of rank at most `k` is closer to `A` in
Frobenius norm than the truncated SVD.
[HornJohnson2013, §7.4.9]. Port of `NLAlib.isBestFrobRankApprox_truncatedSVD`, there through a
predicate `IsBestFrobRankApprox`.
Result: eckart-young-frobenius -/
theorem frobNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : frobNorm (A - truncatedSVD A k) ≤ frobNorm (A - B) := by
  sorry

/-- Eckart–Young in the spectral norm as a least element: `singularValues A k` is the smallest
spectral distance from `A` to a matrix of rank at most `k`.
Port of `NLAlib.isLeast_specNorm_sub_of_rank_le`.
Result: eckart-young-spectral -/
theorem isLeast_specNorm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => specNorm (A - B)) '' {B | B.rank ≤ k})
      (singularValues A k) := by
  sorry

/-- Eckart–Young in the Frobenius norm as a least element.
Port of `NLAlib.bestRankFrobSq_eq_sInf`.
Result: eckart-young-frobenius -/
theorem isLeast_frobNorm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => frobNorm (A - B)) '' {B | B.rank ≤ k})
      (frobNorm (A - truncatedSVD A k)) := by
  sorry

end NLAlib
