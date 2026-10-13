/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Projector
public import NLAlib.Matrix.Spectral.SingularValues

/-!
# Pairs of orthogonal projectors

Two subspaces are compared through their orthogonal projectors `P` and `Q` (star projections).
The matrix `(1 - Q) * P` measures how far the range of `P` is from the range of `Q`: its singular
values are the sines of the principal angles between the two ranges (see
`NLAlib.Matrix.Subspaces.PrincipalAngles`), and it is the object that perturbation theorems
bound. This file relates it to the difference `P - Q`, to the product `Q * P`, and to the same
quantity with the roles exchanged.

## Main results

* `NLAlib.sq_singularValues_eq_one_sub_of_conjTranspose_mul_self_add_eq_one`: if
  `Aᴴ * A + Bᴴ * B = 1`, the singular values of `B` are `√(1 - σ²)` for those of `A`, in reverse
  order (the value part of the thin CS decomposition).
* `IsStarProjection.sq_singularValues_one_sub_mul`: the singular values of `(1 - Q) * P` from
  those of `Q * P`.
* `IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq`: for projectors of equal rank,
  `(1 - Q) * P` and `(1 - P) * Q` have the same singular values.
* `IsStarProjection.specNorm_sub_eq_max`, `IsStarProjection.specNorm_sub_eq_of_rank_eq`: the gap
  `‖P - Q‖₂`.
* `IsStarProjection.frobNorm_sub_sq`: the gap in the Frobenius norm.
* `IsStarProjection.specNorm_one_sub_mul_le_add`: the triangle inequality for directed gaps.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq n] [DecidableEq p]

/-! ### Complementary Gram matrices -/

/-- **The value part of the thin CS decomposition.** If `Aᴴ * A + Bᴴ * B = 1`, the squared
singular values of `B` are one minus those of `A`, in reverse order:
`σ_i(B)² = 1 - σ_j(A)²` for `i + j + 1` the number of columns.
[GolubVanLoan2013, Theorem 2.5.2]. -/
theorem sq_singularValues_eq_one_sub_of_conjTranspose_mul_self_add_eq_one {A : Matrix m p 𝕜}
    {B : Matrix n p 𝕜} (h : Aᴴ * A + Bᴴ * B = 1) {i j : ℕ} (hij : i + j + 1 = Fintype.card p) :
    singularValues B i ^ 2 = 1 - singularValues A j ^ 2 := by
  sorry

/-- If `Aᴴ * A + Bᴴ * B = 1`, the singular values of `A` are at most one. -/
theorem singularValues_le_one_of_conjTranspose_mul_self_add_eq_one {A : Matrix m p 𝕜}
    {B : Matrix n p 𝕜} (h : Aᴴ * A + Bᴴ * B = 1) (i : ℕ) : singularValues A i ≤ 1 := by
  sorry

/-- If `U * Uᴴ + W * Wᴴ = 1` and `W` has orthonormal columns, then `Wᴴ * A` and
`(1 - U * Uᴴ) * A` have the same singular values: the complement of a subspace can be given by a
frame or by a projector. Port of `NLAlib.residual_eq_complement_mul_overlap`. -/
theorem singularValues_conjTranspose_mul_eq_of_mul_conjTranspose_add_eq_one [DecidableEq q]
    {U : Matrix n p 𝕜} {W : Matrix n q 𝕜} (hW : HasOrthonormalCols W) (h : U * Uᴴ + W * Wᴴ = 1)
    (A : Matrix n m 𝕜) :
    singularValues (Wᴴ * A) = singularValues ((1 - U * Uᴴ) * A) := by
  sorry

/-! ### Traces and diagonals of a projector -/

/-- The trace of an orthogonal projector is its rank.
Port of `NLAlib.trace_eq_rank_of_isIdempotentElem` for star projections. -/
theorem _root_.IsStarProjection.trace_eq_rank {P : Matrix n n 𝕜} (hP : IsStarProjection P) :
    P.trace = P.rank := by
  sorry

/-- The diagonal entries of an orthogonal projector (the leverage scores of its range) lie in
`[0, 1]`. Port of `NLAlib.re_diag_mem_Icc_of_isHermitian_of_isIdempotentElem`. -/
theorem _root_.IsStarProjection.re_apply_self_mem_Icc {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) (i : n) : RCLike.re (P i i) ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- The diagonal entries of an orthogonal projector sum to its rank. -/
theorem _root_.IsStarProjection.sum_re_apply_self {P : Matrix n n 𝕜} (hP : IsStarProjection P) :
    ∑ i, RCLike.re (P i i) = P.rank := by
  sorry

/-- A diagonal entry of an orthogonal projector is the squared norm of the corresponding
column. -/
theorem _root_.IsStarProjection.re_apply_self_eq_norm_sq {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) (i : n) :
    RCLike.re (P i i) = ‖WithLp.toLp 2 (P.col i)‖ ^ 2 := by
  sorry

/-- The trace of a product of two orthogonal projectors is the squared Frobenius norm of the
product. Port of `NLAlib.frobInner_frame_projectors_eq_frobSq_overlap`. -/
theorem _root_.IsStarProjection.re_trace_mul {P Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : RCLike.re (P * Q).trace = frobNorm (P * Q) ^ 2 := by
  sorry

/-- Orthogonal projectors are ordered as their ranges: `P ≤ Q` exactly when `Q * P = P`. -/
theorem _root_.IsStarProjection.le_iff_mul_eq {P Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : P ≤ Q ↔ Q * P = P := by
  sorry

/-! ### The matrix `(1 - Q) * P` -/

/-- The difference of two matrices in terms of the two one-sided products.
Port of `NLAlib.sub_projector_eq_complement_mul_sub`. -/
theorem sub_eq_one_sub_mul_sub_mul_one_sub (P Q : Matrix n n 𝕜) :
    P - Q = (1 - Q) * P - Q * (1 - P) := by
  sorry

/-- The Gram matrix of `(1 - Q) * P`.
Port of `NLAlib.conjTranspose_residual_mul_residual_eq_one_sub_overlap`. -/
theorem _root_.IsStarProjection.conjTranspose_one_sub_mul_mul_one_sub_mul {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ((1 - Q) * P)ᴴ * ((1 - Q) * P) = P - P * Q * P := by
  sorry

/-- **The singular values of `(1 - Q) * P`** in terms of those of `Q * P`:
`σ_i((1 - Q) P)² = 1 - σ_j(Q P)²` for `i + j + 1 = rank P`. These are the squared sines and
cosines of the principal angles between the ranges.
[GolubVanLoan2013, §2.5.3]. -/
theorem _root_.IsStarProjection.sq_singularValues_one_sub_mul {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {i j : ℕ} (hij : i + j + 1 = P.rank) :
    singularValues ((1 - Q) * P) i ^ 2 = 1 - singularValues (Q * P) j ^ 2 := by
  sorry

/-- The spectral norm of `(1 - Q) * P` from the smallest relevant singular value of `Q * P`.
Port of `NLAlib.specNorm_residual_sq_eq_one_sub_singularValues_last_sq`. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_sq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {k : ℕ} (hk : k + 1 = P.rank) :
    specNorm ((1 - Q) * P) ^ 2 = 1 - singularValues (Q * P) k ^ 2 := by
  sorry

/-- The Frobenius norm of `(1 - Q) * P`.
Port of `NLAlib.frobSq_residual_eq_card_sub`. -/
theorem _root_.IsStarProjection.frobNorm_one_sub_mul_sq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    frobNorm ((1 - Q) * P) ^ 2 = P.rank - frobNorm (Q * P) ^ 2 := by
  sorry

/-- `‖(1 - Q) P‖₂ ≤ 1`. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_le_one {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : specNorm ((1 - Q) * P) ≤ 1 := by
  sorry

/-- **The acute case.** `‖(1 - Q) P‖₂ < 1` exactly when `Q` is injective on the range of `P`,
that is, when `Q * P` has the rank of `P`.
Port of `NLAlib.directedSubspaceGap_lt_one_iff_isUnit`. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_lt_one_iff {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    specNorm ((1 - Q) * P) < 1 ↔ (Q * P).rank = P.rank := by
  sorry

/-- **The triangle inequality for directed gaps**:
`‖(1 - P) R‖₂ ≤ ‖(1 - P) Q‖₂ + ‖(1 - Q) R‖₂`. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_le_add {P R : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (Q : Matrix n n 𝕜) :
    specNorm ((1 - P) * R) ≤ specNorm ((1 - P) * Q) + specNorm ((1 - Q) * R) := by
  sorry

/-- The triangle inequality for directed gaps in the Frobenius norm. -/
theorem _root_.IsStarProjection.frobNorm_one_sub_mul_le_add {P R : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (Q : Matrix n n 𝕜) :
    frobNorm ((1 - P) * R) ≤ frobNorm ((1 - P) * Q) + frobNorm ((1 - Q) * R) := by
  sorry

/-! ### Projectors of equal rank -/

/-- **Symmetry for equal ranks.** For orthogonal projectors of the same rank, `(1 - Q) * P` and
`(1 - P) * Q` have the same singular values, hence the same norm in every unitarily invariant
norm. [GolubVanLoan2013, Theorem 2.5.1 context].
Port of `NLAlib.specNorm_complement_mul_projector_eq_of_rank_eq` and its Frobenius twin. -/
theorem _root_.IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    singularValues ((1 - Q) * P) = singularValues ((1 - P) * Q) := by
  sorry

/-- For projectors of equal rank the two directed gaps agree in the spectral norm. -/
theorem _root_.IsStarProjection.specNorm_one_sub_mul_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    specNorm ((1 - Q) * P) = specNorm ((1 - P) * Q) := by
  sorry

/-- For projectors of equal rank the two directed gaps agree in the Frobenius norm.
Port of `NLAlib.frobSq_complement_mul_projector_eq_of_rank_eq`. -/
theorem _root_.IsStarProjection.frobNorm_one_sub_mul_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    frobNorm ((1 - Q) * P) = frobNorm ((1 - P) * Q) := by
  sorry

/-! ### The difference of two projectors -/

/-- **The gap between two orthogonal projectors**: `‖P - Q‖₂` is the larger of the two directed
gaps. [GolubVanLoan2013, §2.5.3]; [Kato1995, §I.6.8].
Port of `NLAlib.specNorm_sub_projector_eq_max`.
Result: projector-gap -/
theorem _root_.IsStarProjection.specNorm_sub_eq_max {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    specNorm (P - Q) = max (specNorm ((1 - Q) * P)) (specNorm ((1 - P) * Q)) := by
  sorry

/-- `‖P - Q‖₂ ≤ 1` for orthogonal projectors. -/
theorem _root_.IsStarProjection.specNorm_sub_le_one {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : specNorm (P - Q) ≤ 1 := by
  sorry

/-- For projectors of equal rank, `‖P - Q‖₂ = ‖(1 - Q) P‖₂`.
Port of `NLAlib.specNorm_sub_projector_eq_complement_mul_of_rank_eq`.
Result: projector-gap -/
theorem _root_.IsStarProjection.specNorm_sub_eq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    specNorm (P - Q) = specNorm ((1 - Q) * P) := by
  sorry

/-- `‖P - Q‖_F² = ‖(1 - Q) P‖_F² + ‖(1 - P) Q‖_F²`. -/
theorem _root_.IsStarProjection.frobNorm_sub_sq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    frobNorm (P - Q) ^ 2 = frobNorm ((1 - Q) * P) ^ 2 + frobNorm ((1 - P) * Q) ^ 2 := by
  sorry

/-- For projectors of equal rank, `‖P - Q‖_F² = 2 ‖(1 - Q) P‖_F²`.
Port of `NLAlib.frobSq_sub_frame_projector_eq_two_mul_residual`. -/
theorem _root_.IsStarProjection.frobNorm_sub_sq_of_rank_eq {P Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (h : P.rank = Q.rank) :
    frobNorm (P - Q) ^ 2 = 2 * frobNorm ((1 - Q) * P) ^ 2 := by
  sorry

/-- A sum of two matrices with orthogonal supports on a projector and its complement has spectral
norm at most the larger of the two. Port of `NLAlib.specNorm_add_le_max_of_projector_supports`. -/
theorem _root_.IsStarProjection.specNorm_add_le_max {P : Matrix n n 𝕜} (hP : IsStarProjection P)
    {X Y : Matrix m n 𝕜} (hX : X * P = X) (hY : Y * (1 - P) = Y) (hXY : Xᴴ * Y = 0) :
    specNorm (X + Y) ≤ max (specNorm X) (specNorm Y) := by
  sorry

end NLAlib
