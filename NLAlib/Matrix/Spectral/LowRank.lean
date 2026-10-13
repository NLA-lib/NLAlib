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

/-- The chosen thin SVD from which `truncatedSVD` is built. -/
private theorem exists_isSVD_truncatedSVD (A : Matrix m n 𝕜) :
    ∃ (U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
      (V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜),
      IsSVD A U (fun i => singularValues A i) V ∧
        ∀ k, truncatedSVD A k = U * Matrix.diagonal (fun i : Fin _ =>
          if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) * Vᴴ :=
  ⟨_, _, (exists_isSVD A (le_min A.rank_le_card_height A.rank_le_card_width) (min_le_left _ _)
    (min_le_right _ _)).choose_spec.choose_spec, fun _ => rfl⟩

/-- The truncation and its error have singular value decompositions with the same factors: the
truncation keeps the entries `i < k` of the diagonal and the error keeps the others. -/
private theorem exists_isSVD_truncatedSVD_sub (A : Matrix m n 𝕜) (k : ℕ) :
    ∃ (U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
      (V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜),
      IsSVD (truncatedSVD A k) U (fun i => if (i : ℕ) < k then singularValues A i else 0) V ∧
        IsSVD (A - truncatedSVD A k) U
          (fun i => if (i : ℕ) < k then 0 else singularValues A i) V := by
  obtain ⟨U, V, h, hT⟩ := exists_isSVD_truncatedSVD A
  refine ⟨U, V, ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_right, fun i => ?_, ?_⟩,
    ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_right, fun i => ?_, ?_⟩⟩
  · split_ifs
    exacts [singularValues_nonneg A i, le_rfl]
  · have hd : (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
        (((if (i : ℕ) < k then singularValues A i else 0 : ℝ)) : 𝕜)) =
        fun i : Fin _ => if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0 := by
      funext i
      split_ifs
      exacts [rfl, RCLike.ofReal_zero]
    rw [hT k, hd]
  · split_ifs
    exacts [le_rfl, singularValues_nonneg A i]
  · have hd : Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
          ((singularValues A i : ℝ) : 𝕜)) -
        Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
          if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) =
        Matrix.diagonal fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
          (((if (i : ℕ) < k then 0 else singularValues A i : ℝ)) : 𝕜) := by
      rw [Matrix.diagonal_sub]
      congr 1
      funext i
      split_ifs
      · rw [sub_self, RCLike.ofReal_zero]
      · rw [sub_zero]
    rw [← hd, Matrix.mul_sub, Matrix.sub_mul, ← h.eq, ← hT k]

/-- The conjugate transpose of the truncation annihilates the error. -/
private theorem conjTranspose_truncatedSVD_mul_sub (A : Matrix m n 𝕜) (k : ℕ) :
    (truncatedSVD A k)ᴴ * (A - truncatedSVD A k) = 0 := by
  obtain ⟨U, V, hT, hE⟩ := exists_isSVD_truncatedSVD_sub A k
  rw [hT.conjTranspose.eq, Matrix.mul_assoc, hE.conjTranspose_mul_eq, Matrix.mul_assoc V,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  have hd : (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      (((if (i : ℕ) < k then singularValues A i else 0 : ℝ)) : 𝕜) *
        (((if (i : ℕ) < k then 0 else singularValues A i : ℝ)) : 𝕜)) = fun _ => 0 := by
    funext i
    split_ifs
    · rw [RCLike.ofReal_zero, mul_zero]
    · rw [RCLike.ofReal_zero, zero_mul]
  rw [hd, Matrix.diagonal_zero, Matrix.zero_mul, Matrix.mul_zero]

/-- The tail sum of squared singular values, reindexed from zero. -/
private theorem sum_Ico_singularValues_sq (A : Matrix m n 𝕜) (k : ℕ) :
    ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 =
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A (k + i) ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _)) fun i _ hi => ?_
  rw [Finset.mem_range, not_lt, Nat.sub_le_iff_le_add'] at hi
  rw [(singularValues_eq_zero_iff A).mpr
    ((le_min A.rank_le_card_height A.rank_le_card_width).trans hi), zero_pow two_ne_zero]

/-- The truncated SVD has rank at most `k`. Port of `NLAlib.IsSVD.rank_truncatedMatrix_le`. -/
theorem rank_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) : (truncatedSVD A k).rank ≤ k := by
  obtain ⟨U, V, hT, -⟩ := exists_isSVD_truncatedSVD_sub A k
  rw [hT.rank_eq]
  refine (Finset.card_le_card_of_injOn (fun i : Fin _ => (i : ℕ)) (fun i hi => ?_)
    Fin.val_injective.injOn).trans_eq (Finset.card_range k)
  rw [Finset.mem_coe, Finset.mem_filter] at hi
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hik
  exact hi.2 (if_neg hik)

/-- The singular values of the truncated SVD are the first `k` singular values of `A`. -/
theorem singularValues_truncatedSVD (A : Matrix m n 𝕜) (k i : ℕ) :
    singularValues (truncatedSVD A k) i = if i < k then singularValues A i else 0 := by
  obtain ⟨U, V, hT, -⟩ := exists_isSVD_truncatedSVD_sub A k
  have hanti : Antitone fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      if (i : ℕ) < k then singularValues A i else 0 := by
    intro i j hij
    change (if (j : ℕ) < k then singularValues A j else 0) ≤
      if (i : ℕ) < k then singularValues A i else 0
    by_cases hj : (j : ℕ) < k
    · rw [if_pos hj, if_pos (lt_of_le_of_lt (Fin.le_def.mp hij) hj)]
      exact singularValues_antitone A hij
    · rw [if_neg hj]
      split_ifs
      exacts [singularValues_nonneg A i, le_rfl]
  by_cases hi : i < min (Fintype.card m) (Fintype.card n)
  · exact hT.singularValues_eq hanti ⟨i, hi⟩
  · rw [hT.singularValues_of_le (not_lt.mp hi), (singularValues_eq_zero_iff A).mpr
      ((le_min A.rank_le_card_height A.rank_le_card_width).trans (not_lt.mp hi)), ite_self]

/-- Truncating at or beyond the rank returns the matrix. -/
theorem truncatedSVD_of_rank_le (A : Matrix m n 𝕜) {k : ℕ} (hk : A.rank ≤ k) :
    truncatedSVD A k = A := by
  obtain ⟨U, V, h, hT⟩ := exists_isSVD_truncatedSVD A
  have hd : (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) =
      fun i : Fin _ => ((singularValues A i : ℝ) : 𝕜) := by
    funext i
    split_ifs with hi
    · rfl
    · rw [(singularValues_eq_zero_iff A).mpr (hk.trans (not_lt.mp hi)), RCLike.ofReal_zero]
  rw [hT k, hd]
  exact h.eq.symm

/-- The truncated SVD has rank `min k (rank A)`: exactly `k` when `k` is at most the rank of `A`,
and the rank of `A` otherwise. -/
theorem rank_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    (truncatedSVD A k).rank = min k A.rank := by
  rcases le_total k A.rank with hk | hk
  · rw [min_eq_left hk]
    refine le_antisymm (rank_truncatedSVD_le A k) (not_lt.mp fun hlt => ?_)
    have h0 := (singularValues_eq_zero_iff (truncatedSVD A k)).mpr le_rfl
    rw [singularValues_truncatedSVD, if_pos hlt] at h0
    exact ((singularValues_pos_iff A).mpr (hlt.trans_le hk)).ne' h0
  · rw [truncatedSVD_of_rank_le A hk, min_eq_right hk]

/-- Truncating to rank zero gives the zero matrix. -/
@[simp]
theorem truncatedSVD_zero (A : Matrix m n 𝕜) : truncatedSVD A 0 = 0 := by
  obtain ⟨U, V, -, hT⟩ := exists_isSVD_truncatedSVD A
  simp only [hT 0, Nat.not_lt_zero, if_false, Matrix.diagonal_zero, Matrix.mul_zero,
    Matrix.zero_mul]

/-- **The squared Frobenius error of the truncated SVD is the tail sum of squared singular
values.** This is the rewrite rule that turns the best rank-`k` Frobenius error into a sum.
[GolubVanLoan2013, §2.4]. Port of `NLAlib.frobSq_sub_truncatedSVD_eq_bestRankFrobSq`, there
through a named `bestRankFrobSq`. -/
theorem frobNorm_sub_truncatedSVD_sq (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD A k) ^ 2 =
      ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 := by
  obtain ⟨U, V, -, hE⟩ := exists_isSVD_truncatedSVD_sub A k
  rw [hE.frobNorm_sq_eq,
    Fin.sum_univ_eq_sum_range (fun i => (if i < k then 0 else singularValues A i) ^ 2)]
  refine (Finset.sum_subset (fun i hi => ?_) fun i hi hni => ?_).symm.trans
    (Finset.sum_congr rfl fun i hi => ?_)
  · exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
  · rw [Finset.mem_Ico, not_and, not_lt] at hni
    rw [if_pos (not_le.mp fun hki => (hni hki).not_gt (Finset.mem_range.mp hi)),
      zero_pow two_ne_zero]
  · rw [if_neg (not_lt.mpr (Finset.mem_Ico.mp hi).1)]

/-- The singular values of the truncation error are the singular values of `A` from the `k`-th
on. -/
theorem singularValues_sub_truncatedSVD (A : Matrix m n 𝕜) (k i : ℕ) :
    singularValues (A - truncatedSVD A k) i = singularValues A (k + i) := by
  have hle := singularValues_add_le_singularValues_sub_of_rank_le A (rank_truncatedSVD_le A k)
  have hrank : (A - truncatedSVD A k).rank ≤ min (Fintype.card m) (Fintype.card n) :=
    le_min (Matrix.rank_le_card_height _) (Matrix.rank_le_card_width _)
  by_cases hi : i < min (Fintype.card m) (Fintype.card n)
  · have hsum : ∑ j ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
          singularValues A (k + j) ^ 2 =
        ∑ j ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
          singularValues (A - truncatedSVD A k) j ^ 2 := by
      rw [← sum_Ico_singularValues_sq, ← frobNorm_sub_truncatedSVD_sq,
        frobNorm_sq_eq_sum_range_singularValues_sq _ hrank]
    have hall := (Finset.sum_eq_sum_iff_of_le fun j _ =>
      pow_le_pow_left₀ (singularValues_nonneg A (k + j)) (hle j) 2).mp hsum
    exact ((sq_eq_sq₀ (singularValues_nonneg A _) (singularValues_nonneg _ _)).mp
      (hall i (Finset.mem_range.mpr hi))).symm
  · rw [(singularValues_eq_zero_iff _).mpr (hrank.trans (not_lt.mp hi)),
      (singularValues_eq_zero_iff A).mpr
        ((le_min A.rank_le_card_height A.rank_le_card_width).trans
          ((not_lt.mp hi).trans (Nat.le_add_left i k)))]

/-- **The spectral error of the truncated SVD is the `k`-th singular value.**
[GolubVanLoan2013, Theorem 2.4.8]. Port of `NLAlib.specNorm_sub_truncatedSVD_eq`. -/
@[simp]
theorem specNorm_sub_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    specNorm (A - truncatedSVD A k) = singularValues A k := by
  rw [← singularValues_zero_eq_specNorm, singularValues_sub_truncatedSVD, add_zero]

/-- The truncated SVD and its error are orthogonal in the Frobenius inner product. -/
theorem frobInner_truncatedSVD_sub (A : Matrix m n 𝕜) (k : ℕ) :
    frobInner (truncatedSVD A k) (A - truncatedSVD A k) = 0 := by
  rw [frobInner_eq_re_trace, conjTranspose_truncatedSVD_mul_sub, Matrix.trace_zero, map_zero]

/-- Pythagoras for the truncated SVD: `‖A‖_F² = ‖A_k‖_F² + ‖A - A_k‖_F²`. -/
theorem frobNorm_sq_eq_truncatedSVD_add (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm A ^ 2 = frobNorm (truncatedSVD A k) ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2 := by
  have h := frobNorm_add_sq_of_frobInner_eq_zero (frobInner_truncatedSVD_sub A k)
  rwa [add_sub_cancel] at h

/-- The truncated SVD is the projection of `A` onto its own column space:
`rangeProjector (truncatedSVD A k) * A = truncatedSVD A k`. -/
theorem rangeProjector_truncatedSVD_mul (A : Matrix m n 𝕜) (k : ℕ) :
    rangeProjector (truncatedSVD A k) * A = truncatedSVD A k := by
  have h := rangeProjector_mul_eq_zero_iff.mpr (conjTranspose_truncatedSVD_mul_sub A k)
  rwa [Matrix.mul_sub, rangeProjector_mul_self, sub_eq_zero] at h

/-- The column space of the truncated SVD is inside the column space of `A`. -/
theorem range_mulVecLin_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) :
    LinearMap.range (truncatedSVD A k).mulVecLin ≤ LinearMap.range A.mulVecLin := by
  obtain ⟨U, V, h, hT⟩ := exists_isSVD_truncatedSVD A
  refine range_mulVecLin_le_iff_exists_mul.mpr ⟨V * (Matrix.diagonal
    (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => if (i : ℕ) < k then (1 : 𝕜) else 0) *
      Vᴴ), ?_⟩
  rw [← Matrix.mul_assoc, h.mul_right_eq, ← Matrix.mul_assoc, Matrix.mul_assoc U,
    Matrix.diagonal_mul_diagonal, hT k]
  simp only [mul_ite, mul_one, mul_zero]

/-! ### Eckart–Young -/

/-- **Eckart–Young in the spectral norm.** No matrix of rank at most `k` is closer to `A` in
spectral norm than `singularValues A k`.
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9].
Port of `NLAlib.singularValues_le_specNorm_sub_of_rank_le`.
Result: eckart-young-spectral -/
theorem singularValues_le_specNorm_sub_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : singularValues A k ≤ specNorm (A - B) := by
  have h := singularValues_add_le_singularValues_sub_of_rank_le A hB 0
  rwa [add_zero, singularValues_zero_eq_specNorm] at h

/-- **Eckart–Young in the Frobenius norm**, tail-sum form. For every `B` of rank at most `k`,
`∑_{i ≥ k} σ_i(A)² ≤ ‖A - B‖_F²`.
[HornJohnson2013, §7.4.9]. Port of `NLAlib.bestRankFrobSq_le_frobSq_sub_of_rank_le`.
Result: eckart-young-frobenius -/
theorem sum_Ico_singularValues_sq_le_frobNorm_sub_sq_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) :
    ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 ≤
      frobNorm (A - B) ^ 2 := by
  rw [sum_Ico_singularValues_sq, frobNorm_sq_eq_sum_range_singularValues_sq (A - B)
    (le_min (Matrix.rank_le_card_height _) (Matrix.rank_le_card_width _))]
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (singularValues_nonneg A (k + i))
    (singularValues_add_le_singularValues_sub_of_rank_le A hB i) 2

/-- **Eckart–Young in the Frobenius norm.** No matrix of rank at most `k` is closer to `A` in
Frobenius norm than the truncated SVD.
[HornJohnson2013, §7.4.9]. Port of `NLAlib.isBestFrobRankApprox_truncatedSVD`, there through a
predicate `IsBestFrobRankApprox`.
Result: eckart-young-frobenius -/
theorem frobNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : frobNorm (A - truncatedSVD A k) ≤ frobNorm (A - B) := by
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp ?_
  rw [frobNorm_sub_truncatedSVD_sq]
  exact sum_Ico_singularValues_sq_le_frobNorm_sub_sq_of_rank_le A hB

/-- Eckart–Young in the spectral norm as a least element: `singularValues A k` is the smallest
spectral distance from `A` to a matrix of rank at most `k`.
Port of `NLAlib.isLeast_specNorm_sub_of_rank_le`.
Result: eckart-young-spectral -/
theorem isLeast_specNorm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => specNorm (A - B)) '' {B | B.rank ≤ k})
      (singularValues A k) := by
  refine ⟨⟨truncatedSVD A k, rank_truncatedSVD_le A k, specNorm_sub_truncatedSVD A k⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact singularValues_le_specNorm_sub_of_rank_le A hB

/-- Eckart–Young in the Frobenius norm as a least element.
Port of `NLAlib.bestRankFrobSq_eq_sInf`.
Result: eckart-young-frobenius -/
theorem isLeast_frobNorm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => frobNorm (A - B)) '' {B | B.rank ≤ k})
      (frobNorm (A - truncatedSVD A k)) := by
  refine ⟨⟨truncatedSVD A k, rank_truncatedSVD_le A k, rfl⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact frobNorm_sub_truncatedSVD_le_of_rank_le A hB

end NLAlib
