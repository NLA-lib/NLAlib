/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Deflating a frame of right singular vectors

For an orthonormal frame $\mathbf{W} \in \Bbbk^{n \times r}$ of eigenvectors of the Gram matrix,
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{W} =
\mathbf{W}\operatorname{diag}(\sigma_0(\mathbf{A})^2, \dots, \sigma_{r-1}(\mathbf{A})^2)$, the
deflated matrix $\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}$ has the remaining
singular values of $\mathbf{A}$, $\sigma_i(\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}})
= \sigma_{r+i}(\mathbf{A})$, whichever eigenvectors the frame picks under ties: the deflation
has rank at most $r$, so each singular value is at least $\sigma_{r+i}(\mathbf{A})$, and the
squared Frobenius norms agree. So the deflated matrix has the spectral and Frobenius errors of the
truncated SVD without being it.

## Main results

* `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_mul_conjTranspose_sq`: the squared Frobenius norm
  of the deflation by an invariant frame of the Gram matrix.
* `NLAlib.HasOrthonormalCols.singularValues_sub_mul_mul_conjTranspose`: the singular values of
  the deflation by a frame of top right singular vectors.
* `NLAlib.HasOrthonormalCols.specNorm_sub_mul_mul_conjTranspose`,
  `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_mul_conjTranspose_sq_eq_truncatedSVD`: its
  spectral and Frobenius norms.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The Frobenius norm of a deflation by an invariant frame: for an orthonormal frame
$\mathbf{W}$ with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{W} =
\mathbf{W}\operatorname{diag}(\mathbf{d})$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}\|_{\mathsf{F}}^2 =
\|\mathbf{A}\|_{\mathsf{F}}^2 - \sum_i d_i\,.$$ -/
theorem HasOrthonormalCols.frobNorm_sub_mul_mul_conjTranspose_sq {r : Type*} [Fintype r]
    [DecidableEq r] {A : Matrix m n 𝕜} {W : Matrix n r 𝕜} (hW : HasOrthonormalCols W)
    {d : r → ℝ} (hAW : Aᴴ * A * W = W * Matrix.diagonal fun i => (d i : 𝕜)) :
    frobNorm (A - A * W * Wᴴ) ^ 2 = frobNorm A ^ 2 - ∑ i, d i := by
  classical
  have hP := hW.isStarProjection_mul_conjTranspose.frobNorm_sq_eq_add_mul_right A
  have h1 : A * (1 - W * Wᴴ) = A - A * W * Wᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have h2 : frobNorm (A * (W * Wᴴ)) ^ 2 = ∑ i, d i := by
    rw [← Matrix.mul_assoc, hW.frobNorm_mul_conjTranspose_right, frobNorm_sq_eq_re_trace,
      Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hAW, ← Matrix.mul_assoc,
      hW.conjTranspose_mul_self, Matrix.one_mul, Matrix.trace_diagonal, map_sum]
    exact Finset.sum_congr rfl fun i _ => RCLike.ofReal_re (d i)
  rw [h1, h2] at hP
  linarith

/-- **Deflating top right singular vectors shifts the singular values**: for an orthonormal frame
$\mathbf{W} \in \Bbbk^{n \times r}$ with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{W} =
\mathbf{W}\operatorname{diag}(\sigma_0(\mathbf{A})^2, \dots, \sigma_{r-1}(\mathbf{A})^2)$ and
every $i$,
$$\sigma_i(\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}) =
\sigma_{r+i}(\mathbf{A})\,.$$
No gap is assumed: under ties $\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}$ need not be the chosen
truncated SVD, but the deflated matrix has the same singular values.
No printed source.
Result: eigenframe-deflation-singular-values -/
theorem HasOrthonormalCols.singularValues_sub_mul_mul_conjTranspose {r : ℕ} {A : Matrix m n 𝕜}
    {W : Matrix n (Fin r) 𝕜} (hW : HasOrthonormalCols W)
    (hAW : Aᴴ * A * W =
      W * Matrix.diagonal fun i : Fin r => ((singularValues A i ^ 2 : ℝ) : 𝕜)) (i : ℕ) :
    singularValues (A - A * W * Wᴴ) i = singularValues A (r + i) := by
  have hrank : (A * W * Wᴴ).rank ≤ r :=
    (Matrix.rank_mul_le_left _ _).trans ((A * W).rank_le_card_width.trans_eq (Fintype.card_fin r))
  have hle : ∀ k, singularValues A (r + k) ^ 2 ≤ singularValues (A - A * W * Wᴴ) k ^ 2 :=
    fun k => pow_le_pow_left₀ (singularValues_nonneg _ _)
      (singularValues_add_le_singularValues_sub_of_rank_le A hrank k) 2
  have hsum : ∑ k ∈ Finset.range (Fintype.card n), singularValues A (r + k) ^ 2 =
      ∑ k ∈ Finset.range (Fintype.card n), singularValues (A - A * W * Wᴴ) k ^ 2 := by
    rw [← frobNorm_sq_eq_sum_singularValues_sq, hW.frobNorm_sub_mul_mul_conjTranspose_sq hAW,
      frobNorm_sq_eq_sum_range_singularValues_sq A
        (A.rank_le_card_width.trans (Nat.le_add_left _ r)), Finset.sum_range_add,
      Fin.sum_univ_eq_sum_range (fun k => singularValues A k ^ 2), add_sub_cancel_left]
  rcases lt_or_ge i (Fintype.card n) with hi | hi
  · have h := (Finset.sum_eq_sum_iff_of_le fun k _ => hle k).mp hsum i (Finset.mem_range.mpr hi)
    exact ((sq_eq_sq₀ (singularValues_nonneg _ _) (singularValues_nonneg _ _)).mp h).symm
  · rw [singularValues_of_card_cols_le _ hi,
      singularValues_of_card_cols_le _ (hi.trans (Nat.le_add_left _ r))]

/-- **The spectral norm of a deflation by top right singular vectors**: for an orthonormal frame
$\mathbf{W} \in \Bbbk^{n \times r}$ with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{W} =
\mathbf{W}\operatorname{diag}(\sigma_0(\mathbf{A})^2, \dots, \sigma_{r-1}(\mathbf{A})^2)$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}\|_2 = \sigma_r(\mathbf{A})\,.$$
No printed source.
Result: eigenframe-deflation-singular-values -/
theorem HasOrthonormalCols.specNorm_sub_mul_mul_conjTranspose {r : ℕ} {A : Matrix m n 𝕜}
    {W : Matrix n (Fin r) 𝕜} (hW : HasOrthonormalCols W)
    (hAW : Aᴴ * A * W =
      W * Matrix.diagonal fun i : Fin r => ((singularValues A i ^ 2 : ℝ) : 𝕜)) :
    specNorm (A - A * W * Wᴴ) = singularValues A r := by
  rw [← singularValues_zero_eq_specNorm, hW.singularValues_sub_mul_mul_conjTranspose hAW,
    add_zero]

/-- **The Frobenius norm of a deflation by top right singular vectors**: for an orthonormal frame
$\mathbf{W} \in \Bbbk^{n \times r}$ with $\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{W} =
\mathbf{W}\operatorname{diag}(\sigma_0(\mathbf{A})^2, \dots, \sigma_{r-1}(\mathbf{A})^2)$,
$$\|\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}\|_{\mathsf{F}}^2 =
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,,$$
although $\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}$ need not be
$\llbracket\mathbf{A}\rrbracket_r$ under ties.
No printed source.
Result: eigenframe-deflation-singular-values -/
theorem HasOrthonormalCols.frobNorm_sub_mul_mul_conjTranspose_sq_eq_truncatedSVD {r : ℕ}
    {A : Matrix m n 𝕜} {W : Matrix n (Fin r) 𝕜} (hW : HasOrthonormalCols W)
    (hAW : Aᴴ * A * W =
      W * Matrix.diagonal fun i : Fin r => ((singularValues A i ^ 2 : ℝ) : 𝕜)) :
    frobNorm (A - A * W * Wᴴ) ^ 2 = frobNorm (A - truncatedSVD A r) ^ 2 := by
  have hμ : min (Fintype.card m) (Fintype.card n) ≤ r + Fintype.card n :=
    (min_le_right _ _).trans (Nat.le_add_left _ r)
  rw [frobNorm_sq_eq_sum_singularValues_sq, frobNorm_sub_truncatedSVD_sq,
    Finset.sum_congr rfl fun i _ => by rw [hW.singularValues_sub_mul_mul_conjTranspose hAW i],
    Finset.sum_subset (Finset.Ico_subset_Ico_right hμ) fun i hi hni => ?_,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have hi' : min (Fintype.card m) (Fintype.card n) ≤ i := by
    rw [Finset.mem_Ico] at hi hni
    exact not_lt.mp fun h => hni ⟨hi.1, h⟩
  rw [(singularValues_eq_zero_iff A).mpr
    ((le_min A.rank_le_card_height A.rank_le_card_width).trans hi'), zero_pow two_ne_zero]

end NLAlib
