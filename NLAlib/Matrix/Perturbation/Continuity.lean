/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import NLAlib.Matrix.Majorization.TraceInequalities
public import NLAlib.Matrix.Perturbation.Pseudoinverse

/-!
# Continuity of spectral quantities

Eigenvalues, singular values, the named norms and the optimal low-rank approximation errors are
continuous functions of the matrix; the rank is lower semicontinuous; the pseudoinverse and the
range projector are continuous on each set of matrices of a fixed rank. The quantitative
statements behind these (Weyl, Mirsky, Wedin) are in the earlier files; this file records the
topological consequences in Mathlib's vocabulary, for the product topology on matrices.

## Main results

* `NLAlib.continuous_singularValues`, `NLAlib.continuousOn_eigenvalue`.
* `NLAlib.SymmetricGauge.continuous_matrixNorm`.
* `NLAlib.SymmetricGauge.abs_matrixNorm_sub_truncatedSVD_sub_le`: the optimal error of rank-`k`
  approximation is `1`-Lipschitz in every unitarily invariant norm.
* `NLAlib.isClosed_setOf_rank_le`, `NLAlib.isOpen_setOf_injective_mulVec`.
* `NLAlib.continuousOn_pinv_setOf_rank_eq`, `NLAlib.continuousOn_rangeProjector_setOf_rank_eq`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Singular values, eigenvalues and norms -/

/-- Each singular value is a continuous function of the matrix.
Port of `NLAlib.continuous_singularValues_array`. -/
theorem continuous_singularValues (k : ℕ) :
    Continuous fun A : Matrix m n 𝕜 => singularValues A k := by
  sorry

/-- Each sorted eigenvalue is a continuous function on the Hermitian matrices.
Port of `NLAlib.continuous_eigenvalues₀_pencil`, there along a line. -/
theorem continuousOn_eigenvalue (k : ℕ) :
    ContinuousOn (fun A : Matrix n n 𝕜 => eigenvalue A k) {A | A.IsHermitian} := by
  sorry

/-- Ky Fan norms are continuous. -/
theorem continuous_kyFanNorm (k : ℕ) : Continuous fun A : Matrix m n 𝕜 => kyFanNorm k A := by
  sorry

/-- The nuclear norm is continuous. -/
theorem continuous_nuclearNorm : Continuous (nuclearNorm : Matrix m n 𝕜 → ℝ) := by
  sorry

/-- Every unitarily invariant norm is continuous. -/
theorem SymmetricGauge.continuous_matrixNorm (Φ : SymmetricGauge) :
    Continuous fun A : Matrix m n 𝕜 => Φ.matrixNorm A := by
  sorry

/-! ### Optimal low-rank approximation errors -/

/-- **The optimal error of rank-`k` approximation is `1`-Lipschitz** in every unitarily
invariant norm: `|‖A - A_k‖ - ‖B - B_k‖| ≤ ‖A - B‖`. (In the spectral norm the error is
`singularValues A k` and this is Weyl's inequality.)
Port of `NLAlib.abs_sqrt_bestRankFrobSq_sub_le_frobNorm`, there over `ℝ` in the Frobenius norm. -/
theorem SymmetricGauge.abs_matrixNorm_sub_truncatedSVD_sub_le (Φ : SymmetricGauge)
    (A B : Matrix m n 𝕜) (k : ℕ) :
    |Φ.matrixNorm (A - truncatedSVD A k) - Φ.matrixNorm (B - truncatedSVD B k)| ≤
      Φ.matrixNorm (A - B) := by
  sorry

/-- The optimal Frobenius error of rank-`k` approximation is `1`-Lipschitz in the Frobenius
norm. Port of `NLAlib.abs_sqrt_bestRankFrobSq_sub_le_frobNorm`. -/
theorem abs_frobNorm_sub_truncatedSVD_sub_le (A B : Matrix m n 𝕜) (k : ℕ) :
    |frobNorm (A - truncatedSVD A k) - frobNorm (B - truncatedSVD B k)| ≤ frobNorm (A - B) := by
  sorry

/-- The optimal error of rank-`k` approximation is continuous, in every unitarily invariant norm.
The truncated SVD itself is not: it jumps where `σ_{k-1} = σ_k`.
Port of `NLAlib.continuous_bestRankFrobSq`. -/
theorem SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD (Φ : SymmetricGauge) (k : ℕ) :
    Continuous fun A : Matrix m n 𝕜 => Φ.matrixNorm (A - truncatedSVD A k) := by
  sorry

/-! ### Rank -/

/-- **The matrices of rank at most `r` form a closed set**: the rank is lower semicontinuous. -/
theorem isClosed_setOf_rank_le (r : ℕ) : IsClosed {A : Matrix m n 𝕜 | A.rank ≤ r} := by
  sorry

/-- The matrices of full column rank form an open set. -/
theorem isOpen_setOf_injective_mulVec :
    IsOpen {A : Matrix m n 𝕜 | Function.Injective A.mulVec} := by
  sorry

/-- A best approximation of rank at most `r` exists in every unitarily invariant norm: the
distance to the closed set of matrices of rank at most `r` is attained (by the truncated SVD). -/
theorem SymmetricGauge.isLeast_matrixNorm_sub_of_rank_le (Φ : SymmetricGauge) (A : Matrix m n 𝕜)
    (r : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => Φ.matrixNorm (A - B)) '' {B | B.rank ≤ r})
      (Φ.matrixNorm (A - truncatedSVD A r)) := by
  sorry

/-! ### The pseudoinverse and the range projector -/

/-- **The pseudoinverse is continuous on each set of matrices of a fixed rank.** It is not
continuous on the whole space. [StewartSun1990, §III.3]; [Wedin1973]. -/
theorem continuousOn_pinv_setOf_rank_eq [DecidableEq m] [DecidableEq n] (r : ℕ) :
    ContinuousOn (pinv : Matrix m n 𝕜 → Matrix n m 𝕜) {A | A.rank = r} := by
  sorry

/-- The range projector is continuous on each set of matrices of a fixed rank. -/
theorem continuousOn_rangeProjector_setOf_rank_eq [DecidableEq m] [DecidableEq n] (r : ℕ) :
    ContinuousOn (fun A : Matrix m n 𝕜 => rangeProjector A) {A | A.rank = r} := by
  sorry

end NLAlib
