/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Matrix.Norms.Compare

/-!
# Norms and orthogonal projectors

An orthogonal projector is a contraction in both norms, splits the squared Frobenius norm
(Pythagoras), and gives the best approximation from its range. The statements about
`(1 - rangeProjector Y) * A`, the projection residual, are the ones range finders and low-rank
approximation bounds consume.

## Main results

* `IsStarProjection.specNorm_le_one`, `IsStarProjection.specNorm_mul_le`,
  `IsStarProjection.frobNorm_mul_le`: contraction.
* `IsStarProjection.frobNorm_sq_eq_add`: Pythagoras.
* `NLAlib.frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul`,
  `NLAlib.specNorm_one_sub_rangeProjector_mul_le_specNorm_sub_mul`: the projection residual is
  the smallest residual `A - B * X`.
* `NLAlib.frobNorm_sub_mul_sq`: the exact error split for an arbitrary `X`.
* `NLAlib.specNorm_one_sub_rangeProjector_mul_le_of_range_le`: a larger range gives a smaller
  residual.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Star projections -/

/-- An orthogonal projector has spectral norm at most one.
Port of `Matrix.IsHermitian.specNorm_le_one_of_isIdempotentElem`. -/
theorem _root_.IsStarProjection.specNorm_le_one {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    specNorm P ≤ 1 := by
  sorry

/-- A nonzero orthogonal projector has spectral norm one. -/
theorem _root_.IsStarProjection.specNorm_eq_one {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (h : P ≠ 0) : specNorm P = 1 := by
  sorry

/-- Left multiplication by an orthogonal projector does not increase the spectral norm. -/
theorem _root_.IsStarProjection.specNorm_mul_le {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : specNorm (P * A) ≤ specNorm A := by
  sorry

/-- Left multiplication by an orthogonal projector does not increase the Frobenius norm.
Port of `NLAlib.frobSq_proj_le`. -/
theorem _root_.IsStarProjection.frobNorm_mul_le {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : frobNorm (P * A) ≤ frobNorm A := by
  sorry

/-- The two parts of a matrix cut out by an orthogonal projector and its complement are
orthogonal in the Frobenius inner product. Port of `NLAlib.frobInner_mul_residual`. -/
theorem _root_.IsStarProjection.frobInner_mul_one_sub_mul [DecidableEq m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A B : Matrix m n 𝕜) :
    frobInner (P * A) ((1 - P) * B) = 0 := by
  sorry

/-- **Pythagoras** for an orthogonal projector:
`‖A‖_F² = ‖P A‖_F² + ‖(1 - P) A‖_F²`.
Port of `NLAlib.frobSq_eq_frobSq_proj_add_residual`. -/
theorem _root_.IsStarProjection.frobNorm_sq_eq_add [DecidableEq m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = frobNorm (P * A) ^ 2 + frobNorm ((1 - P) * A) ^ 2 := by
  sorry

/-! ### The projection residual -/

variable [DecidableEq m]

/-- The projection residual has spectral norm at most that of the matrix.
Port of `NLAlib.specNorm_sub_rangeProjector_mul_le`. -/
theorem specNorm_one_sub_rangeProjector_mul_le (Y : Matrix m p 𝕜) (A : Matrix m n 𝕜) :
    specNorm ((1 - rangeProjector Y) * A) ≤ specNorm A := by
  sorry

/-- The projection residual has Frobenius norm at most that of the matrix.
Port of `NLAlib.frobSq_sub_rangeProjector_mul_le`. -/
theorem frobNorm_one_sub_rangeProjector_mul_le (Y : Matrix m p 𝕜) (A : Matrix m n 𝕜) :
    frobNorm ((1 - rangeProjector Y) * A) ≤ frobNorm A := by
  sorry

/-- **The exact error split.** For any coefficient matrix `X`, the squared Frobenius error of
`B * X` as an approximation of `A` is the squared projection residual plus the squared error
inside the range of `B`. Port of `NLAlib.frobSq_sub_mul_eq`, there for `B` with orthonormal
columns. -/
theorem frobNorm_sub_mul_sq (B : Matrix m p 𝕜) (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    frobNorm (A - B * X) ^ 2 =
      frobNorm ((1 - rangeProjector B) * A) ^ 2 + frobNorm (rangeProjector B * A - B * X) ^ 2 := by
  sorry

/-- **Best approximation in the Frobenius norm.** The projection residual is at most the
residual of any approximation `B * X` with columns in the range of `B`.
[GolubVanLoan2013, §5.3.1]. Port of `NLAlib.frobSq_residual_le_frobSq_sub_mul`. -/
theorem frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul (B : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    frobNorm ((1 - rangeProjector B) * A) ≤ frobNorm (A - B * X) := by
  sorry

/-- **Best approximation in the spectral norm.** The projection residual is at most the residual
of any approximation `B * X` with columns in the range of `B`.
[HalkoMartinssonTropp2011, Proposition 8.5]. -/
theorem specNorm_one_sub_rangeProjector_mul_le_specNorm_sub_mul (B : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    specNorm ((1 - rangeProjector B) * A) ≤ specNorm (A - B * X) := by
  sorry

/-- A larger range gives a smaller projection residual, in spectral norm.
[HalkoMartinssonTropp2011, Proposition 8.5].
Port of `NLAlib.specNorm_sub_rangeProjector_mul_le_of_mul_eq`. -/
theorem specNorm_one_sub_rangeProjector_mul_le_of_range_le {B : Matrix m p 𝕜} {Y : Matrix m l 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) (A : Matrix m n 𝕜) :
    specNorm ((1 - rangeProjector B) * A) ≤ specNorm ((1 - rangeProjector Y) * A) := by
  sorry

/-- A larger range gives a smaller projection residual, in Frobenius norm.
Port of `NLAlib.frobSq_sub_rangeProjector_mul_le_of_mul_eq`. -/
theorem frobNorm_one_sub_rangeProjector_mul_le_of_range_le {B : Matrix m p 𝕜} {Y : Matrix m l 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) (A : Matrix m n 𝕜) :
    frobNorm ((1 - rangeProjector B) * A) ≤ frobNorm ((1 - rangeProjector Y) * A) := by
  sorry

/-- The squared Frobenius norm of the range projector of `A` is the rank of `A`. -/
theorem frobNorm_rangeProjector_sq (A : Matrix m n 𝕜) :
    frobNorm (rangeProjector A) ^ 2 = A.rank := by
  sorry

/-- The trace of the range projector of `A` is the rank of `A`. -/
theorem trace_rangeProjector (A : Matrix m n 𝕜) : (rangeProjector A).trace = A.rank := by
  sorry

end NLAlib
