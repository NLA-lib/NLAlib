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

`NLAlib.truncatedSVD A k`, written $\llbracket \mathbf{A} \rrbracket_k$, is a best approximation of
$\mathbf{A}$ of rank at most $k$, obtained by keeping the $k$ largest singular triples of a
singular value decomposition. Its error is $\sigma_k(\mathbf{A})$ in the spectral norm and
$\bigl(\sum_{i \ge k} \sigma_i(\mathbf{A})^2\bigr)^{1/2}$ in the Frobenius norm, and no matrix of
rank at most $k$ does better in either norm.

The best rank-$k$ error is spelled `singularValues A k` in the spectral norm and
`frobNorm (A - truncatedSVD A k)` in the Frobenius norm; `NLAlib.frobNorm_sub_truncatedSVD_sq`
rewrites the latter as the tail sum of squared singular values.

When $\sigma_{k-1}(\mathbf{A}) = \sigma_k(\mathbf{A})$ the best approximation is not unique;
$\llbracket \mathbf{A} \rrbracket_k$ is one of them, built from the library's chosen
decomposition, the lexicographically least thin SVD (`NLAlib.svdU`, `NLAlib.svdV`), which is the
same for every $k$ and makes the truncation measurable in $\mathbf{A}$.

## Main definitions

* `NLAlib.truncatedSVD`: a best approximation of rank at most $k$.

## Main results

* `NLAlib.truncatedSVD_def`: the truncation of the chosen SVD.
* `NLAlib.rank_truncatedSVD_le`, `NLAlib.specNorm_sub_truncatedSVD`,
  `NLAlib.frobNorm_sub_truncatedSVD_sq`: rank and errors of the truncation;
  `NLAlib.frobNorm_truncatedSVD_sq`, `NLAlib.frobNorm_truncatedSVD_le`: its Frobenius norm.
* `NLAlib.natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq`: tail flattening, $d$
  copies of $\sigma_{k+d}(\mathbf{A})^2$ below the Frobenius tail at $k$.
* `NLAlib.mul_rangeProjector_conjTranspose_truncatedSVD`,
  `NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`: the row space of the
  truncation, and a frame $\mathbf{Z}$ with
  $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket \mathbf{A} \rrbracket_k$.
* `NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion`: that frame
  with an orthonormal completion carrying $\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k$.
* `NLAlib.exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal`: the same frames
  as invariant frames of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$, nested in $k$.
* `NLAlib.range_truncatedSVD_mono`: the column spaces of the truncations are nested.
* `NLAlib.HasOrthonormalCols.mul_conjTranspose_mul_truncatedSVD`: the truncation of
  $\mathbf{Q}\mathbf{X}$ stays in the range of $\mathbf{Q}$.
* `Matrix.PosSemidef.truncatedSVD`, `Matrix.PosSemidef.one_sub_mul_mul_one_sub_eq_sub_truncatedSVD`,
  `Matrix.PosSemidef.truncatedSVD_le`: positive semidefinite inputs, and the truncation below the
  matrix in the Loewner order.
* `NLAlib.singularValues_le_specNorm_sub_of_rank_le`: Eckart–Young in the spectral norm.
* `NLAlib.frobNorm_sub_truncatedSVD_le_of_rank_le`: Eckart–Young in the Frobenius norm.
* `NLAlib.isLeast_specNorm_sub_of_rank_le`, `NLAlib.isLeast_frobNorm_sub_of_rank_le`: the same as
  least elements.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The **truncated singular value decomposition** $\llbracket \mathbf{A} \rrbracket_k$: a best
approximation of $\mathbf{A}$ of rank at most $k$, obtained from the chosen thin singular value
decomposition $\mathbf{A} = \mathsf{svdU}(\mathbf{A})\,\mathbf{\Sigma}\,
\mathsf{svdV}(\mathbf{A})^{\mathsf{H}}$, the lexicographically least one (`NLAlib.svdU`,
`NLAlib.svdV`), by keeping the $k$ largest singular values:
$$\llbracket \mathbf{A} \rrbracket_k = \mathsf{svdU}(\mathbf{A})\,
\operatorname{diag}\bigl(\sigma_0(\mathbf{A}), \dots, \sigma_{k-1}(\mathbf{A}), 0, \dots, 0\bigr)\,
\mathsf{svdV}(\mathbf{A})^{\mathsf{H}}$$
(`NLAlib.truncatedSVD_def`). The decomposition is a fixed function of $\mathbf{A}$, so the
truncation is Borel measurable in $\mathbf{A}$ (`NLAlib.measurable_truncatedSVD`), and one
decomposition serves every $k$. When $\sigma_{k-1}(\mathbf{A}) = \sigma_k(\mathbf{A})$ this is one
of several best approximations. For $k \ge \operatorname{rank} \mathbf{A}$ it is $\mathbf{A}$.
[GolubVanLoan2013, Theorem 2.4.8]. -/
noncomputable def truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  svdU A *
    Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) *
    (svdV A)ᴴ

/-- The truncated SVD is the chosen SVD with the singular values $\sigma_i(\mathbf{A})$,
$i \ge k$, set to zero:
$$\llbracket\mathbf{A}\rrbracket_k = \mathsf{svdU}(\mathbf{A})\,
\operatorname{diag}\bigl(\sigma_0(\mathbf{A}), \dots, \sigma_{k-1}(\mathbf{A}), 0, \dots, 0\bigr)\,
\mathsf{svdV}(\mathbf{A})^{\mathsf{H}}\,.$$ -/
theorem truncatedSVD_def (A : Matrix m n 𝕜) (k : ℕ) :
    truncatedSVD A k = svdU A *
      Matrix.diagonal (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
        if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) * (svdV A)ᴴ :=
  rfl

/-! ### The truncation -/

/-- The chosen thin SVD from which `truncatedSVD` is built. -/
private theorem exists_isSVD_truncatedSVD (A : Matrix m n 𝕜) :
    ∃ (U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜)
      (V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜),
      IsSVD A U (fun i => singularValues A i) V ∧
        ∀ k, truncatedSVD A k = U * Matrix.diagonal (fun i : Fin _ =>
          if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) * Vᴴ :=
  ⟨svdU A, svdV A, isSVD_svdU_svdV A, truncatedSVD_def A⟩

/-- The truncation and its error have singular value decompositions with the same factors: the
truncation keeps the entries $i < k$ of the diagonal and the error keeps the others. -/
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

/-- The conjugate transpose of the truncation annihilates the error:
$\llbracket \mathbf{A} \rrbracket_k^{\mathsf{H}} (\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k)
= \mathbf{0}$. -/
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

/-- The truncated SVD has rank at most $k$:
$\operatorname{rank} \llbracket \mathbf{A} \rrbracket_k \le k$. -/
theorem rank_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) : (truncatedSVD A k).rank ≤ k := by
  obtain ⟨U, V, hT, -⟩ := exists_isSVD_truncatedSVD_sub A k
  rw [hT.rank_eq]
  refine (Finset.card_le_card_of_injOn (fun i : Fin _ => (i : ℕ)) (fun i hi => ?_)
    Fin.val_injective.injOn).trans_eq (Finset.card_range k)
  rw [Finset.mem_coe, Finset.mem_filter] at hi
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hik
  exact hi.2 (if_neg hik)

/-- The singular values of the truncated SVD are the first $k$ singular values of $\mathbf{A}$:
$\sigma_i(\llbracket \mathbf{A} \rrbracket_k) = \sigma_i(\mathbf{A})$ for $i < k$ and $0$ for
$i \ge k$. -/
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

/-- Truncating at or beyond the rank returns the matrix: $\llbracket \mathbf{A} \rrbracket_k =
\mathbf{A}$ for $\operatorname{rank} \mathbf{A} \le k$. -/
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

/-- Truncating at an index whose singular value vanishes returns the matrix:
$\sigma_k(\mathbf{A}) = 0$ gives $\llbracket \mathbf{A} \rrbracket_k = \mathbf{A}$, so the
truncation error $\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k$ is $\mathbf{0}$. The
singular-value form of `NLAlib.truncatedSVD_of_rank_le`. -/
theorem truncatedSVD_of_singularValues_eq_zero (A : Matrix m n 𝕜) {k : ℕ}
    (h : singularValues A k = 0) : truncatedSVD A k = A :=
  truncatedSVD_of_rank_le A ((singularValues_eq_zero_iff A).mp h)

/-- The truncated SVD has rank $\min(k, \operatorname{rank} \mathbf{A})$: exactly $k$ when $k$ is
at most the rank of $\mathbf{A}$, and the rank of $\mathbf{A}$ otherwise. -/
theorem rank_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    (truncatedSVD A k).rank = min k A.rank := by
  rcases le_total k A.rank with hk | hk
  · rw [min_eq_left hk]
    refine le_antisymm (rank_truncatedSVD_le A k) (not_lt.mp fun hlt => ?_)
    have h0 := (singularValues_eq_zero_iff (truncatedSVD A k)).mpr le_rfl
    rw [singularValues_truncatedSVD, if_pos hlt] at h0
    exact ((singularValues_pos_iff A).mpr (hlt.trans_le hk)).ne' h0
  · rw [truncatedSVD_of_rank_le A hk, min_eq_right hk]

/-- Truncating to rank zero gives the zero matrix: $\llbracket \mathbf{A} \rrbracket_0 =
\mathbf{0}$. -/
@[simp]
theorem truncatedSVD_zero (A : Matrix m n 𝕜) : truncatedSVD A 0 = 0 := by
  obtain ⟨U, V, -, hT⟩ := exists_isSVD_truncatedSVD A
  simp only [hT 0, Nat.not_lt_zero, if_false, Matrix.diagonal_zero, Matrix.mul_zero,
    Matrix.zero_mul]

/-- **The squared Frobenius error of the truncated SVD is the tail sum of squared singular
values**:
$$\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2
  = \sum_{k \le i < \min(\lvert m \rvert, \lvert n \rvert)} \sigma_i(\mathbf{A})^2.$$
This is the rewrite rule that turns the best rank-$k$ Frobenius error into a sum.
[GolubVanLoan2013, §2.4]. -/
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

/-- The squared Frobenius error of the truncated SVD is at most $\min(\lvert m \rvert,
\lvert n \rvert)$ times the squared $k$-th singular value:
$\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le
\min(\lvert m \rvert, \lvert n \rvert)\,\sigma_k(\mathbf{A})^2$. -/
theorem frobNorm_sub_truncatedSVD_sq_le_min_card_mul_sq (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD A k) ^ 2 ≤
      (min (Fintype.card m) (Fintype.card n) : ℕ) * singularValues A k ^ 2 := by
  rw [frobNorm_sub_truncatedSVD_sq]
  calc ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2
      ≤ ∑ _i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues A k ^ 2 :=
        Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (singularValues_nonneg A i)
          (singularValues_antitone A (Finset.mem_Ico.mp hi).1) 2
    _ = ((min (Fintype.card m) (Fintype.card n) - k : ℕ) : ℝ) * singularValues A k ^ 2 := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (sq_nonneg _)

/-- The truncated SVD keeps the leading singular values in the Frobenius norm:
$$\|\llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2 = \sum_{i < k} \sigma_i(\mathbf{A})^2\,,$$
for every choice of the truncation; indices at or above $\min(\lvert m \rvert, \lvert n \rvert)$
contribute $0$. -/
theorem frobNorm_truncatedSVD_sq (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (truncatedSVD A k) ^ 2 = ∑ i ∈ Finset.range k, singularValues A i ^ 2 := by
  rw [frobNorm_sq_eq_sum_range_singularValues_sq _ (rank_truncatedSVD_le A k)]
  exact Finset.sum_congr rfl fun i hi => by
    rw [singularValues_truncatedSVD, if_pos (Finset.mem_range.mp hi)]

/-- Truncation does not increase the Frobenius norm, for every $k$:
$\|\llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem frobNorm_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (truncatedSVD A k) ≤ frobNorm A := by
  have hle : frobNorm (truncatedSVD A k) ^ 2 ≤ frobNorm A ^ 2 := by
    rw [frobNorm_truncatedSVD_sq, frobNorm_sq_eq_sum_range_singularValues_sq A
      (Nat.le_add_left A.rank k)]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (Nat.le_add_right k _)) fun i _ _ => sq_nonneg _
  exact (pow_le_pow_iff_left₀ (frobNorm_nonneg _) (frobNorm_nonneg _) two_ne_zero).1 hle

/-- The singular values of the truncation error are the singular values of $\mathbf{A}$ from the
$k$-th on: $\sigma_i(\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k) = \sigma_{k+i}(\mathbf{A})$.
-/
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

/-- **The spectral error of the truncated SVD is the $k$-th singular value**:
$\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_2 = \sigma_k(\mathbf{A})$.
[GolubVanLoan2013, Theorem 2.4.8]. -/
@[simp]
theorem specNorm_sub_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    specNorm (A - truncatedSVD A k) = singularValues A k := by
  rw [← singularValues_zero_eq_specNorm, singularValues_sub_truncatedSVD, add_zero]

/-- Tail flattening:
$$d\,\sigma_{k+d}(\mathbf{A})^2 \le
\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2\,,$$
since the $d$ singular values
$\sigma_k(\mathbf{A}), \dots, \sigma_{k+d-1}(\mathbf{A})$ are at least $\sigma_{k+d}(\mathbf{A})$.
It bounds the spectral residual of a range finder split at $k + d$ by the Frobenius tail at $k$.
True at every $k$ and $d$, including indices past the smaller dimension, where
$\sigma_{k+d}(\mathbf{A}) = 0$. -/
theorem natCast_mul_singularValues_add_sq_le_frobNorm_sub_truncatedSVD_sq (A : Matrix m n 𝕜)
    (k d : ℕ) : (d : ℝ) * singularValues A (k + d) ^ 2 ≤ frobNorm (A - truncatedSVD A k) ^ 2 := by
  rw [frobNorm_sq_eq_sum_range_singularValues_sq (A - truncatedSVD A k)
    (le_self_add : (A - truncatedSVD A k).rank ≤ (A - truncatedSVD A k).rank + d)]
  calc (d : ℝ) * singularValues A (k + d) ^ 2
      = (Finset.range d).card • singularValues A (k + d) ^ 2 := by
        rw [Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.range d, singularValues (A - truncatedSVD A k) i ^ 2 :=
        Finset.card_nsmul_le_sum _ _ _ fun i hi => by
          rw [singularValues_sub_truncatedSVD]
          exact pow_le_pow_left₀ (singularValues_nonneg _ _)
            (singularValues_antitone A (by have := Finset.mem_range.mp hi; omega)) 2
    _ ≤ ∑ i ∈ Finset.range ((A - truncatedSVD A k).rank + d),
          singularValues (A - truncatedSVD A k) i ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono le_add_self)
          fun _ _ _ => sq_nonneg _

/-- The truncated SVD and its error are orthogonal in the Frobenius inner product:
$\langle \llbracket \mathbf{A} \rrbracket_k, \mathbf{A} - \llbracket \mathbf{A} \rrbracket_k
\rangle_{\mathsf{F}} = 0$. -/
theorem frobInner_truncatedSVD_sub (A : Matrix m n 𝕜) (k : ℕ) :
    frobInner (truncatedSVD A k) (A - truncatedSVD A k) = 0 := by
  rw [frobInner_eq_re_trace, conjTranspose_truncatedSVD_mul_sub, Matrix.trace_zero, map_zero]

/-- Pythagoras for the truncated SVD:
$\|\mathbf{A}\|_{\mathsf{F}}^2 = \|\llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2 +
\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$. -/
theorem frobNorm_sq_eq_truncatedSVD_add (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm A ^ 2 = frobNorm (truncatedSVD A k) ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2 := by
  have h := frobNorm_add_sq_of_frobInner_eq_zero (frobInner_truncatedSVD_sub A k)
  rwa [add_sub_cancel] at h

/-- The residual tail at rank $k+d$ and the $d$ intervening singular values spend disjoint
parts of the Frobenius tail at rank $k$:
$$\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_{k+d}\|_{\mathsf{F}}^2
+d\,\sigma_{k+d}(\mathbf{A})^2 \le
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
This retains the coupling between a comparison rank's spectral and Frobenius tails.
No printed source. -/
theorem frobNorm_sub_truncatedSVD_sq_add_natCast_mul_singularValues_sq_le
    (A : Matrix m n 𝕜) (k d : ℕ) :
    frobNorm (A - truncatedSVD A (k + d)) ^ 2 +
        (d : ℝ) * singularValues A (k + d) ^ 2 ≤
      frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hflat : (d : ℝ) * singularValues A (k + d) ^ 2 ≤
      ∑ i ∈ Finset.range d, singularValues A (k + i) ^ 2 := by
    calc (d : ℝ) * singularValues A (k + d) ^ 2
        = (Finset.range d).card • singularValues A (k + d) ^ 2 := by
          rw [Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := Finset.card_nsmul_le_sum _ _ _ fun i hi =>
        pow_le_pow_left₀ (singularValues_nonneg _ _)
          (singularValues_antitone A (by have := Finset.mem_range.mp hi; omega)) 2
  have hsum := Finset.sum_range_add (fun i => singularValues A i ^ 2) k d
  have hk := frobNorm_sq_eq_truncatedSVD_add A k
  have hkd := frobNorm_sq_eq_truncatedSVD_add A (k + d)
  rw [frobNorm_truncatedSVD_sq] at hk hkd
  nlinarith

/-- The truncated SVD is the projection of $\mathbf{A}$ onto its own column space:
$\mathbf{P}_{\llbracket \mathbf{A} \rrbracket_k} \mathbf{A} = \llbracket \mathbf{A} \rrbracket_k$.
-/
theorem rangeProjector_truncatedSVD_mul (A : Matrix m n 𝕜) (k : ℕ) :
    rangeProjector (truncatedSVD A k) * A = truncatedSVD A k := by
  have h := rangeProjector_mul_eq_zero_iff.mpr (conjTranspose_truncatedSVD_mul_sub A k)
  rwa [Matrix.mul_sub, rangeProjector_mul_self, sub_eq_zero] at h

/-- The column space of the truncated SVD is inside the column space of $\mathbf{A}$. -/
theorem range_truncatedSVD_le (A : Matrix m n 𝕜) (k : ℕ) :
    LinearMap.range (truncatedSVD A k).mulVecLin ≤ LinearMap.range A.mulVecLin := by
  obtain ⟨U, V, h, hT⟩ := exists_isSVD_truncatedSVD A
  refine range_le_iff_exists_mul.mpr ⟨V * (Matrix.diagonal
    (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => if (i : ℕ) < k then (1 : 𝕜) else 0) *
      Vᴴ), ?_⟩
  rw [← Matrix.mul_assoc, h.mul_right_eq, ← Matrix.mul_assoc, Matrix.mul_assoc U,
    Matrix.diagonal_mul_diagonal, hT k]
  simp only [mul_ite, mul_one, mul_zero]

/-- The truncation of $\mathbf{Q}\mathbf{X}$ lies in the range of $\mathbf{Q}$:
$$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k =
\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k\,,$$
so $\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k = \mathbf{Q}\mathbf{Y}$ with
$\mathbf{Y} = \mathbf{Q}^{\mathsf{H}}\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k$ a best
approximation of
$\mathbf{X}$ (`NLAlib.HasOrthonormalCols.isBestRankApprox_conjTranspose_mul_truncatedSVD`). The
projector form
$$\mathbf{P}_{\mathbf{Q}}\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k =
\llbracket\mathbf{Q}\mathbf{X}\rrbracket_k$$
holds for every $\mathbf{Q}$.
[TroppYurtseverUdellCevher2017, §6.2, (6.3)]; there "there is a best rank-$r$ approximation of
$\mathbf{Q}\mathbf{X}$" with this property, here the truncated SVD itself. -/
theorem HasOrthonormalCols.mul_conjTranspose_mul_truncatedSVD {q : Type*} [Fintype q]
    [DecidableEq q] {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (X : Matrix q n 𝕜) (k : ℕ) :
    Q * (Qᴴ * truncatedSVD (Q * X) k) = truncatedSVD (Q * X) k := by
  rw [← Matrix.mul_assoc, ← hQ.rangeProjector_eq, rangeProjector_mul_eq_self_iff]
  exact (range_truncatedSVD_le _ k).trans
    (range_le_iff_exists_mul.mpr ⟨X, rfl⟩)

/-! ### Row spaces, frames of dominant singular subspaces, positive semidefinite inputs -/

/-- The truncation annihilates the conjugate transpose of the error:
$$\llbracket \mathbf{A} \rrbracket_k (\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k)^{\mathsf{H}}
= \mathbf{0}\,.$$ -/
private theorem truncatedSVD_mul_conjTranspose_sub (A : Matrix m n 𝕜) (k : ℕ) :
    truncatedSVD A k * (A - truncatedSVD A k)ᴴ = 0 := by
  obtain ⟨U, V, hT, hE⟩ := exists_isSVD_truncatedSVD_sub A k
  rw [hE.conjTranspose.eq, hT.eq]
  simp only [Matrix.mul_assoc]
  rw [hT.hasOrthonormalCols_right.conjTranspose_mul_cancel_left,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  have hd : (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
      (((if (i : ℕ) < k then singularValues A i else 0 : ℝ)) : 𝕜) *
        (((if (i : ℕ) < k then 0 else singularValues A i : ℝ)) : 𝕜)) = fun _ => 0 := by
    funext i
    split_ifs
    · rw [RCLike.ofReal_zero, mul_zero]
    · rw [RCLike.ofReal_zero, zero_mul]
  rw [hd, Matrix.diagonal_zero, Matrix.zero_mul, Matrix.mul_zero]

/-- The truncated SVD is $\mathbf{A}$ times the projector onto its own row space:
$$\mathbf{A}\mathbf{P}_{\llbracket \mathbf{A} \rrbracket_k^{\mathsf{H}}} =
\llbracket \mathbf{A} \rrbracket_k\,.$$
The row twin of
`NLAlib.rangeProjector_truncatedSVD_mul`; it identifies a frame of a dominant right singular
subspace (`NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`). -/
theorem mul_rangeProjector_conjTranspose_truncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    A * rangeProjector (truncatedSVD A k)ᴴ = truncatedSVD A k := by
  have h0 : ((truncatedSVD A k)ᴴ)ᴴ * (A - truncatedSVD A k)ᴴ = 0 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact truncatedSVD_mul_conjTranspose_sub A k
  have h := congrArg Matrix.conjTranspose (rangeProjector_mul_eq_zero_iff.mpr h0)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, conjTranspose_rangeProjector,
    Matrix.conjTranspose_zero, Matrix.sub_mul, sub_eq_zero] at h
  have hT := congrArg Matrix.conjTranspose (rangeProjector_mul_self (truncatedSVD A k)ᴴ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    conjTranspose_rangeProjector] at hT
  rw [h, hT]

open scoped ComplexOrder in
/-- For positive semidefinite $\mathbf{A}$ with an SVD
$\mathbf{U}\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$, the left and right singular vectors agree
wherever the singular value is nonzero. -/
private theorem IsSVD.mul_diagonal_eq_of_posSemidef {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {U V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V)
    {d : r → 𝕜} (hd : ∀ i, σ i = 0 → d i = 0) : U * Matrix.diagonal d = V * Matrix.diagonal d := by
  ext j i
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hσ : σ i = 0
  · rw [hd i hσ, mul_zero, mul_zero]
  have h1 := h.mulVec_col i
  have h2 := h.conjTranspose.mulVec_col i
  rw [hA.isHermitian.eq] at h2
  have hx : A *ᵥ (U.col i - V.col i) = (-((σ i : ℝ) : 𝕜)) • (U.col i - V.col i) := by
    rw [Matrix.mulVec_sub, h1, h2, neg_smul, smul_sub, neg_sub,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  have hnn := hA.dotProduct_mulVec_nonneg (U.col i - V.col i)
  rw [hx, dotProduct_smul, smul_eq_mul, neg_mul, neg_nonneg] at hnn
  have hσpos : (0 : 𝕜) < ((σ i : ℝ) : 𝕜) :=
    RCLike.ofReal_pos.mpr (lt_of_le_of_ne (h.nonneg i) (Ne.symm hσ))
  have hs : star (U.col i - V.col i) ⬝ᵥ (U.col i - V.col i) = 0 :=
    (mul_eq_zero.mp (le_antisymm hnn (mul_nonneg hσpos.le
      (dotProduct_star_self_nonneg _)))).resolve_left hσpos.ne'
  have hj := congrFun (dotProduct_star_self_eq_zero.mp hs) j
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hj
  exact congrArg (· * d i) hj

open scoped ComplexOrder in
/-- The truncated SVD of a positive semidefinite matrix is positive semidefinite:
$\llbracket \mathbf{A} \rrbracket_k \succeq \mathbf{0}$ for $\mathbf{A} \succeq \mathbf{0}$,
whatever singular value decomposition the definition chose, ties included. (For Hermitian
$\mathbf{A}$ that is not positive semidefinite the chosen truncation need not be Hermitian.) -/
theorem _root_.Matrix.PosSemidef.truncatedSVD {A : Matrix n n 𝕜} (hA : A.PosSemidef) (k : ℕ) :
    (truncatedSVD A k).PosSemidef := by
  obtain ⟨U, V, h, hT⟩ := exists_isSVD_truncatedSVD A
  rw [hT k, h.mul_diagonal_eq_of_posSemidef hA fun i hi => by
    split_ifs
    · rw [hi, RCLike.ofReal_zero]
    · rfl]
  refine (Matrix.PosSemidef.diagonal fun i => ?_).mul_mul_conjTranspose_same V
  change (0 : 𝕜) ≤ if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0
  split_ifs
  · exact RCLike.ofReal_nonneg.mpr (singularValues_nonneg A i)
  · exact le_rfl

open scoped ComplexOrder in
/-- For positive semidefinite $\mathbf{H}$ and a frame $\mathbf{Z}$ with
$\mathbf{H}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket \mathbf{H} \rrbracket_k$, the
compression of $\mathbf{H}$ to the complement of $\operatorname{range}\mathbf{Z}$ is the
truncation error:
$$(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{H}
(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}}) =
\mathbf{H} - \llbracket \mathbf{H} \rrbracket_k\,.$$
It is the top-$k$ reading of the Nyström structural bound; the frame comes from
`NLAlib.exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD` at $\mathbf{H}$. -/
theorem _root_.Matrix.PosSemidef.one_sub_mul_mul_one_sub_eq_sub_truncatedSVD [DecidableEq n]
    {r : Type*} [Fintype r] [DecidableEq r] {H : Matrix n n 𝕜} (hH : H.PosSemidef)
    {Z : Matrix n r 𝕜} (hZ : HasOrthonormalCols Z) {k : ℕ}
    (hZH : H * Z * Zᴴ = truncatedSVD H k) :
    (1 - Z * Zᴴ) * H * (1 - Z * Zᴴ) = H - truncatedSVD H k := by
  have hT := (hH.truncatedSVD k).isHermitian.eq
  have hPH : Z * Zᴴ * H = truncatedSVD H k := by
    have h := congrArg Matrix.conjTranspose hZH
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hH.isHermitian.eq, hT, ← Matrix.mul_assoc] at h
  have hPHP : Z * Zᴴ * H * (Z * Zᴴ) = truncatedSVD H k := by
    rw [hPH, ← hZH, ← Matrix.mul_assoc, hZ.mul_conjTranspose_mul_cancel_right]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  rw [hPHP, hPH, ← Matrix.mul_assoc H, hZH]
  abel

open scoped ComplexOrder in
/-- A frame of a dominant right singular subspace: for an index type $p$ with
$\lvert p \rvert = k \le \lvert n \rvert$ there is $\mathbf{Z}$ with orthonormal columns indexed by
$p$ and $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket \mathbf{A} \rrbracket_k$; for
$k \ge \operatorname{rank}\mathbf{A}$ it is any frame whose range contains the row space. Rewriting
with the equation turns a statement about any frame into its top-$k$ form, where
$$\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\,.$$ -/
theorem exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD {p : Type*} [Fintype p]
    [DecidableEq p] (A : Matrix m n 𝕜) {k : ℕ} (hp : Fintype.card p = k)
    (hk : k ≤ Fintype.card n) :
    ∃ Z : Matrix n p 𝕜, HasOrthonormalCols Z ∧ A * Z * Zᴴ = truncatedSVD A k := by
  obtain ⟨Z, hZ, hle⟩ := exists_hasOrthonormalCols_range_le (truncatedSVD A k)ᴴ
    (by rw [Matrix.rank_conjTranspose, hp]; exact rank_truncatedSVD_le A k) (hp ▸ hk)
  refine ⟨Z, hZ, ?_⟩
  rw [Matrix.mul_assoc, ← hZ.rangeProjector_eq]
  rcases le_total k A.rank with hkA | hkA
  · have hr : (truncatedSVD A k)ᴴ.rank = Z.rank := by
      rw [Matrix.rank_conjTranspose, rank_truncatedSVD, min_eq_left hkA, hZ.rank_eq, hp]
    rw [← rangeProjector_inj.mpr (Submodule.eq_of_le_of_finrank_eq hle hr),
      mul_rangeProjector_conjTranspose_truncatedSVD]
  · rw [truncatedSVD_of_rank_le A hkA] at hle ⊢
    have h := congrArg Matrix.conjTranspose (rangeProjector_mul_eq_self_iff.mpr hle)
    rwa [Matrix.conjTranspose_mul, conjTranspose_rangeProjector,
      Matrix.conjTranspose_conjTranspose] at h

open scoped ComplexOrder in
/-- A frame of the row space of the truncated SVD: for an index type $p$ with
$\lvert p \rvert = \operatorname{rank} \llbracket \mathbf{A} \rrbracket_k$ there is
$\mathbf{Z}$ with orthonormal columns indexed by $p$ whose column space is that of
$\llbracket \mathbf{A} \rrbracket_k^{\mathsf{H}}$, so that
$\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \mathbf{P}_{\llbracket \mathbf{A} \rrbracket_k^{\mathsf{H}}}$
and $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket \mathbf{A} \rrbracket_k$. -/
theorem exists_hasOrthonormalCols_range_eq_range_conjTranspose_truncatedSVD {p : Type*}
    [Fintype p] [DecidableEq p] (A : Matrix m n 𝕜) (k : ℕ)
    (hp : Fintype.card p = (truncatedSVD A k).rank) :
    ∃ Z : Matrix n p 𝕜, HasOrthonormalCols Z ∧
      LinearMap.range Z.mulVecLin = LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin ∧
      Z * Zᴴ = rangeProjector (truncatedSVD A k)ᴴ ∧ A * Z * Zᴴ = truncatedSVD A k := by
  obtain ⟨Z, hZ, hR⟩ := exists_hasOrthonormalCols_range_eq (truncatedSVD A k)ᴴ
    (by rw [Matrix.rank_conjTranspose, hp])
  have hP : Z * Zᴴ = rangeProjector (truncatedSVD A k)ᴴ := by
    rw [← hZ.rangeProjector_eq, rangeProjector_inj, hR]
  exact ⟨Z, hZ, hR, hP, by rw [Matrix.mul_assoc, hP, mul_rangeProjector_conjTranspose_truncatedSVD]⟩

/-- A top-$k$ frame and its orthonormal completion: for $\lvert p \rvert = k$ and
$\lvert p \rvert + \lvert q \rvert = \lvert n \rvert$ there are $\mathbf{Z}$ and $\mathbf{V}$
with orthonormal columns indexed by $p$ and $q$, $\mathbf{Z}^{\mathsf{H}}\mathbf{V} = \mathbf{0}$
(so $\begin{bmatrix} \mathbf{Z} & \mathbf{V} \end{bmatrix}$ is unitary up to relabelling),
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket \mathbf{A} \rrbracket_k$ and
$$\mathbf{E}\mathbf{V}\mathbf{V}^{\mathsf{H}} = \mathbf{E},\qquad
\mathbf{E} = \mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\,:$$
the error of the truncation lives on the completion, so $\mathbf{E}\mathbf{V}$ has the norms of
$\mathbf{E}$ (`NLAlib.SymmetricGauge.matrixNorm_mul_of_mul_mul_conjTranspose_eq`). This is the
frame in which the randomized SVD is analysed: the noise term of the structural bound becomes
$(\mathbf{E}\mathbf{V})(\mathbf{V}^{\mathsf{H}}\mathbf{\Omega})
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$. -/
theorem exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion {p q : Type*}
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] (A : Matrix m n 𝕜) {k : ℕ}
    (hp : Fintype.card p = k) (hpq : Fintype.card p + Fintype.card q = Fintype.card n) :
    ∃ (Z : Matrix n p 𝕜) (V : Matrix n q 𝕜), HasOrthonormalCols Z ∧ HasOrthonormalCols V ∧
      Zᴴ * V = 0 ∧ A * Z * Zᴴ = truncatedSVD A k ∧
        (A - truncatedSVD A k) * V * Vᴴ = A - truncatedSVD A k := by
  classical
  obtain ⟨Z, hZ, hZA⟩ :=
    exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD A hp (by omega)
  obtain ⟨V, hZV⟩ := hZ.exists_fromCols hpq
  obtain ⟨-, hV, h0⟩ := hasOrthonormalCols_fromCols_iff.mp hZV
  refine ⟨Z, V, hZ, hV, h0, hZA, ?_⟩
  have hV' : V * Vᴴ = 1 - Z * Zᴴ :=
    eq_sub_of_add_eq' (hZV.mul_conjTranspose_add_mul_conjTranspose hpq)
  have hP : A * Z * Zᴴ * (Z * Zᴴ) = A * (Z * Zᴴ) := by
    rw [Matrix.mul_assoc A Z Zᴴ, Matrix.mul_assoc A, Matrix.mul_assoc Z Zᴴ,
      ← Matrix.mul_assoc Zᴴ Z Zᴴ, hZ.conjTranspose_mul_self, Matrix.one_mul]
  rw [← hZA, Matrix.mul_assoc, hV', Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_mul A (A * Z * Zᴴ), hP, sub_self, sub_zero]

open scoped ComplexOrder MatrixOrder in
/-- The truncated SVD of a positive semidefinite matrix lies below it:
$\llbracket\mathbf{A}\rrbracket_k \preceq \mathbf{A}$, for every choice of the truncation.
[MartinssonTropp2020, §14.3]; there the positive semidefiniteness of the approximation, here the
order. -/
theorem _root_.Matrix.PosSemidef.truncatedSVD_le {A : Matrix n n 𝕜} (hA : A.PosSemidef) (k : ℕ) :
    truncatedSVD A k ≤ A := by
  classical
  rcases le_or_gt k (Fintype.card n) with hk | hk
  · obtain ⟨Z, hZ, hZA⟩ := exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD
      (p := Fin k) A (Fintype.card_fin k) hk
    rw [Matrix.le_iff, ← hA.one_sub_mul_mul_one_sub_eq_sub_truncatedSVD hZ hZA]
    have h := hA.conjTranspose_mul_mul_same (1 - Z * Zᴴ)
    rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose] at h
  · rw [truncatedSVD_of_rank_le A (A.rank_le_card_width.trans hk.le)]

/-! ### Eckart–Young -/

/-- **Eckart–Young in the spectral norm.** No matrix of rank at most $k$ is closer to $\mathbf{A}$
in spectral norm than $\sigma_k(\mathbf{A})$: if $\operatorname{rank} \mathbf{B} \le k$ then
$\sigma_k(\mathbf{A}) \le \|\mathbf{A} - \mathbf{B}\|_2$.
[GolubVanLoan2013, Theorem 2.4.8]; [HornJohnson2013, §7.4.9].
Result: eckart-young-spectral -/
theorem singularValues_le_specNorm_sub_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : singularValues A k ≤ specNorm (A - B) := by
  have h := singularValues_add_le_singularValues_sub_of_rank_le A hB 0
  rwa [add_zero, singularValues_zero_eq_specNorm] at h

/-- **Eckart–Young in the Frobenius norm**, tail-sum form. For every $\mathbf{B}$ of rank at most
$k$,
$$\sum_{k \le i < \min(\lvert m \rvert, \lvert n \rvert)} \sigma_i(\mathbf{A})^2
  \le \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}^2.$$
[HornJohnson2013, §7.4.9].
Result: eckart-young-frobenius -/
theorem sum_Ico_singularValues_sq_le_frobNorm_sub_sq_of_rank_le (A : Matrix m n 𝕜)
    {B : Matrix m n 𝕜} {k : ℕ} (hB : B.rank ≤ k) :
    ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues A i ^ 2 ≤
      frobNorm (A - B) ^ 2 := by
  rw [sum_Ico_singularValues_sq, frobNorm_sq_eq_sum_range_singularValues_sq (A - B)
    (le_min (Matrix.rank_le_card_height _) (Matrix.rank_le_card_width _))]
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (singularValues_nonneg A (k + i))
    (singularValues_add_le_singularValues_sub_of_rank_le A hB i) 2

/-- **Eckart–Young in the Frobenius norm.** No matrix of rank at most $k$ is closer to
$\mathbf{A}$ in Frobenius norm than the truncated SVD: if $\operatorname{rank} \mathbf{B} \le k$
then $\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}
\le \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}$.
[HornJohnson2013, §7.4.9].
Result: eckart-young-frobenius -/
theorem frobNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : frobNorm (A - truncatedSVD A k) ≤ frobNorm (A - B) := by
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp ?_
  rw [frobNorm_sub_truncatedSVD_sq]
  exact sum_Ico_singularValues_sq_le_frobNorm_sub_sq_of_rank_le A hB

/-- **Eckart–Young in the spectral norm**, as a least element: $\sigma_k(\mathbf{A})$ is the
smallest spectral distance $\|\mathbf{A} - \mathbf{B}\|_2$ from $\mathbf{A}$ to a matrix
$\mathbf{B}$ of rank at most $k$.
Result: eckart-young-spectral -/
theorem isLeast_specNorm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => specNorm (A - B)) '' {B | B.rank ≤ k})
      (singularValues A k) := by
  refine ⟨⟨truncatedSVD A k, rank_truncatedSVD_le A k, specNorm_sub_truncatedSVD A k⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact singularValues_le_specNorm_sub_of_rank_le A hB

/-- **Eckart–Young in the Frobenius norm**, as a least element: over the matrices $\mathbf{B}$ of
rank at most $k$, the distance $\|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}$ has a least value, and
it is $\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}$.
Result: eckart-young-frobenius -/
theorem isLeast_frobNorm_sub_of_rank_le (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => frobNorm (A - B)) '' {B | B.rank ≤ k})
      (frobNorm (A - truncatedSVD A k)) := by
  refine ⟨⟨truncatedSVD A k, rank_truncatedSVD_le A k, rfl⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact frobNorm_sub_truncatedSVD_le_of_rank_le A hB


/-- The column spaces of the truncations are nested:
$\operatorname{range}\llbracket\mathbf{A}\rrbracket_k \subseteq
\operatorname{range}\llbracket\mathbf{A}\rrbracket_{k'}$ for $k \le k'$, since every truncation
is built from the same chosen SVD. With ties among the singular values this can fail for other
best approximations. -/
theorem range_truncatedSVD_mono (A : Matrix m n 𝕜) :
    Monotone fun k => LinearMap.range (truncatedSVD A k).mulVecLin := by
  intro k k' hk
  obtain ⟨U, V, h, hT⟩ := exists_isSVD_truncatedSVD A
  refine range_le_iff_exists_mul.mpr ⟨V * (Matrix.diagonal
    (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => if (i : ℕ) < k then (1 : 𝕜) else 0) *
      Vᴴ), ?_⟩
  rw [hT k, hT k']
  simp only [Matrix.mul_assoc]
  rw [h.hasOrthonormalCols_right.conjTranspose_mul_cancel_left,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 3
  funext i
  split_ifs with h₁ h₂ <;> first | rfl | (exfalso; omega) | simp


/-- The truncation clause of
`exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal`: the first $r$ columns
$\mathbf{Z}_r$ of an orthonormal frame $\mathbf{F}$ extending the right singular vectors
$\mathbf{V}_0$ of the chosen SVD give
$\mathbf{A}\mathbf{Z}_r\mathbf{Z}_r^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_r$. -/
private theorem mul_submatrix_castLE_mul_conjTranspose_eq_truncatedSVD {A : Matrix m n 𝕜}
    {μ p r : ℕ} {U : Matrix m (Fin μ) 𝕜} {V₀ : Matrix n (Fin μ) 𝕜}
    (h : IsSVD A U (fun i => singularValues A i) V₀)
    (hT : ∀ k, truncatedSVD A k = U * Matrix.diagonal (fun i : Fin μ =>
      if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) * V₀ᴴ)
    {F : Matrix n (Fin (μ + p)) 𝕜} (hF : HasOrthonormalCols F)
    (hF₀ : ∀ a j, F a (Fin.castAdd p j) = V₀ a j) (hrL : r ≤ μ + p) :
    A * F.submatrix id (Fin.castLE hrL) * (F.submatrix id (Fin.castLE hrL))ᴴ =
      truncatedSVD A r := by
  set Zr := F.submatrix id (Fin.castLE hrL)
  have hV₀F : V₀ = F.submatrix id (Fin.castAdd p) := by
    ext a j
    exact (hF₀ a j).symm
  have hZrV₀ : Zrᴴ * V₀ =
      (Fᴴ * F).submatrix (Fin.castLE hrL) (Fin.castAdd p) := by
    rw [hV₀F]
    rfl
  have hP : Zr * Zrᴴ * V₀ =
      V₀ * Matrix.diagonal fun j : Fin μ => if (j : ℕ) < r then (1 : 𝕜) else 0 := by
    rw [Matrix.mul_assoc, hZrV₀, hF.conjTranspose_mul_self]
    ext a j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.ext_iff, Fin.val_castLE,
      Fin.val_castAdd, mul_ite, mul_one, mul_zero]
    split_ifs with hj
    · rw [Finset.sum_eq_single_of_mem ⟨j, hj⟩ (Finset.mem_univ _) fun i _ hi => if_neg
        fun hij => hi (Fin.ext hij), if_pos rfl, ← hF₀]
      rfl
    · exact Finset.sum_eq_zero fun i _ => if_neg fun hij => hj (by have := i.isLt; omega)
  have hVD : V₀ᴴ * (Zr * Zrᴴ) =
      (Matrix.diagonal fun j : Fin μ => if (j : ℕ) < r then (1 : 𝕜) else 0) * V₀ᴴ := by
    have hc := congrArg Matrix.conjTranspose hP
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose] at hc
    rw [hc]
    congr 2
    funext j
    rw [Pi.star_apply]
    split_ifs <;> simp
  have hA : A * V₀ * V₀ᴴ = A := by
    rw [h.mul_right_eq, ← h.eq]
  rw [Matrix.mul_assoc A Zr]
  conv_lhs => rw [← hA]
  rw [Matrix.mul_assoc (A * V₀), hVD, h.mul_right_eq, hT r, ← Matrix.mul_assoc,
    Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
  simp only [mul_ite, mul_one, mul_zero]

-- SKELETON-NOTE: true as stated, but the last clause (every prefix gives the chosen truncation)
-- forces Z to be built from the chosen `svdV A` (then completed by null vectors of A when
-- k > rank A); a frame of right singular vectors chosen otherwise fails it under ties.
/-- Nested invariant frames of the Gram matrix: for $k \le \lvert n \rvert$ there are
$\mathbf{Z} \in \Bbbk^{n \times k}$ and $\mathbf{V} \in \Bbbk^{n \times (\lvert n \rvert - k)}$ with
orthonormal columns, $\mathbf{Z}^{\mathsf{H}}\mathbf{V} = \mathbf{0}$ and
$\mathbf{Z}\mathbf{Z}^{\mathsf{H}} + \mathbf{V}\mathbf{V}^{\mathsf{H}} = \mathbf{I}$, made of right
singular vectors:
$$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{Z} =
\mathbf{Z}\operatorname{diag}(\sigma_i(\mathbf{A})^2)_{i < k}\,,\qquad
\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\sigma_{k+j}(\mathbf{A})^2)_j\,,$$
and whose first $r$ columns $\mathbf{Z}_r$ give the chosen truncation,
$\mathbf{A}\mathbf{Z}_r\mathbf{Z}_r^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_r$, for every
$r \le k$. These are the head frame $\mathbf{W} = \mathbf{Z}_r$, the frame $\mathbf{Z}$ and its
completion $\mathbf{V}$ of the filtered range finder. -/
theorem exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal [DecidableEq n]
    (A : Matrix m n 𝕜) {k : ℕ} (hk : k ≤ Fintype.card n) :
    ∃ (Z : Matrix n (Fin k) 𝕜) (V : Matrix n (Fin (Fintype.card n - k)) 𝕜),
      HasOrthonormalCols Z ∧ HasOrthonormalCols V ∧ Zᴴ * V = 0 ∧ Z * Zᴴ + V * Vᴴ = 1 ∧
      Aᴴ * A * Z = Z * Matrix.diagonal (fun i : Fin k => ((singularValues A i ^ 2 : ℝ) : 𝕜)) ∧
      Aᴴ * A * V = V * Matrix.diagonal
        (fun j : Fin (Fintype.card n - k) => ((singularValues A (k + j) ^ 2 : ℝ) : 𝕜)) ∧
      ∀ r (hr : r ≤ k), A * Z.submatrix id (Fin.castLE hr) * (Z.submatrix id (Fin.castLE hr))ᴴ =
        truncatedSVD A r := by
  have hex := exists_isSVD_truncatedSVD A
  have hμN := min_le_right (Fintype.card m) (Fintype.card n)
  have hrank := le_min A.rank_le_card_height A.rank_le_card_width
  generalize min (Fintype.card m) (Fintype.card n) = μ at hex hμN hrank
  obtain ⟨U, V₀, h, hT⟩ := hex
  obtain ⟨V₁, hV⟩ := h.hasOrthonormalCols_right.exists_fromCols (p := Fin (Fintype.card n - μ))
    (by rw [Fintype.card_fin, Fintype.card_fin]; omega)
  obtain ⟨-, -, h01⟩ := hasOrthonormalCols_fromCols_iff.mp hV
  -- the chosen right singular vectors completed to a unitary frame `F = [svdV A, V₁]`
  let F : Matrix n (Fin (μ + (Fintype.card n - μ))) 𝕜 :=
    (Matrix.fromCols V₀ V₁).submatrix (Equiv.refl n) finSumFinEquiv.symm
  have hF : HasOrthonormalCols F := hV.submatrix (Equiv.refl n) finSumFinEquiv.symm.injective
  have hF₀ (a : n) (j : Fin μ) : F a (Fin.castAdd (Fintype.card n - μ) j) = V₀ a j := by simp [F]
  have hF₁ (a : n) (j : Fin (Fintype.card n - μ)) : F a (Fin.natAdd μ j) = V₁ a j := by simp [F]
  have hσ (i : ℕ) (hi : μ ≤ i) : singularValues A i = 0 :=
    (singularValues_eq_zero_iff A).mpr (hrank.trans hi)
  have hAF : Aᴴ * A * F = F * Matrix.diagonal
      fun i : Fin (μ + (Fintype.card n - μ)) => ((singularValues A i ^ 2 : ℝ) : 𝕜) := by
    have hG := h.conjTranspose_mul_self_eq
    have h0 : Aᴴ * A * V₀ =
        V₀ * Matrix.diagonal fun j : Fin μ => ((singularValues A j ^ 2 : ℝ) : 𝕜) := by
      rw [hG, h.hasOrthonormalCols_right.mul_conjTranspose_mul_cancel_right]
    have h1 : Aᴴ * A * V₁ = 0 := by
      rw [hG, Matrix.mul_assoc, h01, Matrix.mul_zero]
    ext a i
    rw [Matrix.mul_diagonal]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have e := congrFun (congrFun h0 a) j
      rw [Matrix.mul_diagonal] at e
      rw [hF₀, Fin.val_castAdd, ← e]
      simp only [Matrix.mul_apply (M := Aᴴ * A), hF₀]
    · have e := congrFun (congrFun h1 a) j
      rw [Fin.val_natAdd, hσ _ (Nat.le_add_right _ _), zero_pow two_ne_zero,
        RCLike.ofReal_zero, mul_zero]
      rw [Matrix.zero_apply] at e
      rw [← e]
      simp only [Matrix.mul_apply (M := Aᴴ * A), hF₁]
  have hkL : k ≤ μ + (Fintype.card n - μ) := by omega
  let c : Fin k → Fin (μ + (Fintype.card n - μ)) := Fin.castLE hkL
  let c' : Fin (Fintype.card n - k) → Fin (μ + (Fintype.card n - μ)) := fun j => ⟨k + j, by omega⟩
  let e : Fin k ⊕ Fin (Fintype.card n - k) → Fin (μ + (Fintype.card n - μ)) := Sum.elim c c'
  have he : Function.Injective e := by
    rintro (x | x) (y | y) hxy <;> simp [e, c, c', Fin.ext_iff] at hxy ⊢ <;> omega
  have hZV : HasOrthonormalCols (Matrix.fromCols (F.submatrix id c) (F.submatrix id c')) := by
    have hfc : Matrix.fromCols (F.submatrix id c) (F.submatrix id c') = F.submatrix id e := by
      ext a (j | j) <;> rfl
    rw [hfc]
    exact hF.submatrix (Equiv.refl n) he
  obtain ⟨hZ, hV', hZV0⟩ := hasOrthonormalCols_fromCols_iff.mp hZV
  refine ⟨F.submatrix id c, F.submatrix id c', hZ, hV', hZV0,
    hZV.mul_conjTranspose_add_mul_conjTranspose (by rw [Fintype.card_fin, Fintype.card_fin]; omega),
    ?_, ?_, ?_⟩
  · ext a i
    calc (Aᴴ * A * F.submatrix id c) a i = (Aᴴ * A * F) a (c i) := rfl
      _ = F a (c i) * ((singularValues A (c i) ^ 2 : ℝ) : 𝕜) := by rw [hAF, Matrix.mul_diagonal]
      _ = _ := by rw [Matrix.mul_diagonal]; rfl
  · ext a j
    calc (Aᴴ * A * F.submatrix id c') a j = (Aᴴ * A * F) a (c' j) := rfl
      _ = F a (c' j) * ((singularValues A (c' j) ^ 2 : ℝ) : 𝕜) := by
        rw [hAF, Matrix.mul_diagonal]
      _ = _ := by rw [Matrix.mul_diagonal]; rfl
  · intro r hr
    exact mul_submatrix_castLE_mul_conjTranspose_eq_truncatedSVD h hT hF hF₀ (hr.trans hkL)

end NLAlib
