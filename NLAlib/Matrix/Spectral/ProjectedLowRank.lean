/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.LowRank

/-!
# Best low-rank approximation with columns in a given range

For a matrix `Q` with orthonormal columns, the approximations `Q * B` of `A` with `B` of rank at
most `k` are compared through the compression `Qᴴ * A`: the squared Frobenius error of `Q * B` is
the squared projection residual of `A` plus the squared error of `B` as an approximation of
`Qᴴ * A`. By the Eckart–Young theorem the error is therefore least at
`B = truncatedSVD (Qᴴ * A) k`. This is the truncation step of the randomized singular value
decomposition, where `Q` is the output of a range finder.

## Main results

* `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_sq`: the error split
  `‖A - Q B‖_F² = ‖(1 - Q Qᴴ) A‖_F² + ‖Qᴴ A - B‖_F²`.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_le_of_rank_le`,
  `NLAlib.HasOrthonormalCols.isLeast_frobNorm_sub_mul_of_rank_le`: `Q * truncatedSVD (Qᴴ * A) k`
  is a best approximation of `A` among the matrices `Q * B` with `B` of rank at most `k`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq r]

/-- **The exact error split for a frame.** For `Q` with orthonormal columns and any coefficient
matrix `B`, the squared Frobenius error of `Q * B` as an approximation of `A` is the squared
projection residual plus the squared error of `B` as an approximation of the compression
`Qᴴ * A`. This is `NLAlib.frobNorm_sub_mul_sq` with the range projector written `Q * Qᴴ` and the
error inside the range pulled back through `Q`.
[HalkoMartinssonTropp2011, Theorem 9.1 (proof)].
Port of `NLAlib.frobSq_sub_mul_eq`. -/
theorem HasOrthonormalCols.frobNorm_sub_mul_sq [DecidableEq m] {Q : Matrix m r 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) (B : Matrix r n 𝕜) :
    frobNorm (A - Q * B) ^ 2 =
      frobNorm ((1 - Q * Qᴴ) * A) ^ 2 + frobNorm (Qᴴ * A - B) ^ 2 := by
  rw [NLAlib.frobNorm_sub_mul_sq Q A B, hQ.rangeProjector_eq, Matrix.mul_assoc, ← Matrix.mul_sub,
    hQ.frobNorm_mul_left]

/-- **Truncation inside a range is optimal.** For `Q` with orthonormal columns, the truncated
singular value decomposition of the compression `Qᴴ * A` gives the best Frobenius approximation
of `A` among the matrices `Q * B` with `B` of rank at most `k`. For `k` at least the rank of
`Qᴴ * A` the left side is the projection residual `‖(1 - Q Qᴴ) A‖_F`.
[HalkoMartinssonTropp2011, Theorem 9.1 (proof)]; there in the analysis of the fixed-rank
randomized singular value decomposition.
Port of `NLAlib.frobSq_sub_mul_le_of_isBestFrobRankApprox`, there for any best approximation of
`Qᴴ * A` in place of `truncatedSVD (Qᴴ * A) k`. -/
theorem HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_le_of_rank_le {Q : Matrix m r 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) {B : Matrix r n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) :
    frobNorm (A - Q * truncatedSVD (Qᴴ * A) k) ≤ frobNorm (A - Q * B) := by
  classical
  refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp ?_
  rw [hQ.frobNorm_sub_mul_sq, hQ.frobNorm_sub_mul_sq]
  exact add_le_add_right (pow_le_pow_left₀ (frobNorm_nonneg _)
    (frobNorm_sub_truncatedSVD_le_of_rank_le _ hB) 2) _

/-- Truncation inside a range is optimal, as a least element: among the matrices `Q * B` with `B`
of rank at most `k`, the least Frobenius error is attained at `B = truncatedSVD (Qᴴ * A) k`. -/
theorem HasOrthonormalCols.isLeast_frobNorm_sub_mul_of_rank_le {Q : Matrix m r 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) (k : ℕ) :
    IsLeast ((fun B : Matrix r n 𝕜 => frobNorm (A - Q * B)) '' {B | B.rank ≤ k})
      (frobNorm (A - Q * truncatedSVD (Qᴴ * A) k)) := by
  refine ⟨⟨truncatedSVD (Qᴴ * A) k, rank_truncatedSVD_le _ k, rfl⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact hQ.frobNorm_sub_mul_truncatedSVD_le_of_rank_le A hB

end NLAlib
