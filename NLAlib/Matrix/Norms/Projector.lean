/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
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
  refine (specNorm_le_iff zero_le_one).2 fun x => ?_
  rw [one_mul]
  exact hP.norm_toLp_mulVec_le x

/-- A nonzero orthogonal projector has spectral norm one. -/
theorem _root_.IsStarProjection.specNorm_eq_one {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (h : P ≠ 0) : specNorm P = 1 := by
  have hsq := specNorm_conjTranspose_mul_self P
  rw [hP.conjTranspose_eq, hP.mul_self] at hsq
  have h0 : specNorm P ≠ 0 := fun h0 => h (specNorm_eq_zero_iff.1 h0)
  exact mul_left_cancel₀ h0 (by rw [mul_one, ← sq, ← hsq])

/-- Left multiplication by an orthogonal projector does not increase the spectral norm. -/
theorem _root_.IsStarProjection.specNorm_mul_le {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : specNorm (P * A) ≤ specNorm A := by
  exact (NLAlib.specNorm_mul_le P A).trans
    (mul_le_of_le_one_left (specNorm_nonneg A) hP.specNorm_le_one)

/-- Left multiplication by an orthogonal projector does not increase the Frobenius norm.
Port of `NLAlib.frobSq_proj_le`. -/
theorem _root_.IsStarProjection.frobNorm_mul_le {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : frobNorm (P * A) ≤ frobNorm A := by
  exact (frobNorm_mul_le_specNorm_mul_frobNorm P A).trans
    (mul_le_of_le_one_left (frobNorm_nonneg A) hP.specNorm_le_one)

/-- Right multiplication by an orthogonal projector does not increase the spectral norm. -/
theorem _root_.IsStarProjection.specNorm_mul_right_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix n m 𝕜) : specNorm (A * P) ≤ specNorm A := by
  exact (NLAlib.specNorm_mul_le A P).trans
    (mul_le_of_le_one_right (specNorm_nonneg A) hP.specNorm_le_one)

/-- Right multiplication by an orthogonal projector does not increase the Frobenius norm. -/
theorem _root_.IsStarProjection.frobNorm_mul_right_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix n m 𝕜) : frobNorm (A * P) ≤ frobNorm A := by
  exact (frobNorm_mul_le_frobNorm_mul_specNorm A P).trans
    (mul_le_of_le_one_right (frobNorm_nonneg A) hP.specNorm_le_one)

/-- The two parts of a matrix cut out by an orthogonal projector and its complement are
orthogonal in the Frobenius inner product. Port of `NLAlib.frobInner_mul_residual`. -/
theorem _root_.IsStarProjection.frobInner_mul_one_sub_mul [DecidableEq m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A B : Matrix m n 𝕜) :
    frobInner (P * A) ((1 - P) * B) = 0 := by
  rw [frobInner_mul_left, hP.conjTranspose_eq, ← Matrix.mul_assoc, hP.mul_one_sub_self,
    Matrix.zero_mul, frobInner_zero_right]

/-- **Pythagoras** for an orthogonal projector:
`‖A‖_F² = ‖P A‖_F² + ‖(1 - P) A‖_F²`.
Port of `NLAlib.frobSq_eq_frobSq_proj_add_residual`. -/
theorem _root_.IsStarProjection.frobNorm_sq_eq_add [DecidableEq m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) :
    frobNorm A ^ 2 = frobNorm (P * A) ^ 2 + frobNorm ((1 - P) * A) ^ 2 := by
  have h := frobNorm_add_sq_of_frobInner_eq_zero (hP.frobInner_mul_one_sub_mul A A)
  rwa [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul] at h

/-! ### The range projector -/

/-- The trace of the range projector of `A` is the rank of `A`. -/
theorem trace_rangeProjector (A : Matrix m n 𝕜) : (rangeProjector A).trace = A.rank := by
  obtain ⟨Q, hQ, hrange⟩ :=
    exists_hasOrthonormalCols_range_eq (p := Fin A.rank) A (Fintype.card_fin _)
  rw [← rangeProjector_inj.mpr hrange, hQ.rangeProjector_eq, Matrix.trace_mul_comm,
    hQ.conjTranspose_mul_self, Matrix.trace_one, Fintype.card_fin]

/-- The squared Frobenius norm of the range projector of `A` is the rank of `A`. -/
theorem frobNorm_rangeProjector_sq (A : Matrix m n 𝕜) :
    frobNorm (rangeProjector A) ^ 2 = A.rank := by
  rw [frobNorm_sq_eq_re_trace, conjTranspose_rangeProjector, rangeProjector_mul_rangeProjector,
    trace_rangeProjector, RCLike.natCast_re]

/-! ### The projection residual -/

variable [DecidableEq m]

/-- The projection residual has spectral norm at most that of the matrix.
Port of `NLAlib.specNorm_sub_rangeProjector_mul_le`. -/
theorem specNorm_one_sub_rangeProjector_mul_le (Y : Matrix m p 𝕜) (A : Matrix m n 𝕜) :
    specNorm ((1 - rangeProjector Y) * A) ≤ specNorm A := by
  exact (isStarProjection_one_sub_rangeProjector Y).specNorm_mul_le A

/-- The projection residual has Frobenius norm at most that of the matrix.
Port of `NLAlib.frobSq_sub_rangeProjector_mul_le`. -/
theorem frobNorm_one_sub_rangeProjector_mul_le (Y : Matrix m p 𝕜) (A : Matrix m n 𝕜) :
    frobNorm ((1 - rangeProjector Y) * A) ≤ frobNorm A := by
  exact (isStarProjection_one_sub_rangeProjector Y).frobNorm_mul_le A

/-- **The exact error split.** For any coefficient matrix `X`, the squared Frobenius error of
`B * X` as an approximation of `A` is the squared projection residual plus the squared error
inside the range of `B`. Port of `NLAlib.frobSq_sub_mul_eq`, there for `B` with orthonormal
columns. -/
theorem frobNorm_sub_mul_sq (B : Matrix m p 𝕜) (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    frobNorm (A - B * X) ^ 2 =
      frobNorm ((1 - rangeProjector B) * A) ^ 2 + frobNorm (rangeProjector B * A - B * X) ^ 2 := by
  have hPX : rangeProjector B * A - B * X = rangeProjector B * (A - B * X) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, rangeProjector_mul_self]
  have hsplit : A - B * X = (1 - rangeProjector B) * A + rangeProjector B * (A - B * X) := by
    rw [← hPX, one_sub_rangeProjector_mul]
    abel
  have h0 : frobInner ((1 - rangeProjector B) * A) (rangeProjector B * (A - B * X)) = 0 := by
    rw [frobInner_comm]
    exact (isStarProjection_rangeProjector B).frobInner_mul_one_sub_mul _ _
  rw [hPX, ← frobNorm_add_sq_of_frobInner_eq_zero h0, ← hsplit]

omit [Fintype n] in
private theorem one_sub_rangeProjector_mul_sub_mul (B : Matrix m p 𝕜) (A : Matrix m n 𝕜)
    (X : Matrix p n 𝕜) :
    (1 - rangeProjector B) * (A - B * X) = (1 - rangeProjector B) * A := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, one_sub_rangeProjector_mul_self, Matrix.zero_mul,
    sub_zero]

/-- **Best approximation in the Frobenius norm.** The projection residual is at most the
residual of any approximation `B * X` with columns in the range of `B`.
[GolubVanLoan2013, §5.3.1]. Port of `NLAlib.frobSq_residual_le_frobSq_sub_mul`. -/
theorem frobNorm_one_sub_rangeProjector_mul_le_frobNorm_sub_mul (B : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    frobNorm ((1 - rangeProjector B) * A) ≤ frobNorm (A - B * X) := by
  rw [← one_sub_rangeProjector_mul_sub_mul B A X]
  exact frobNorm_one_sub_rangeProjector_mul_le B _

/-- **Best approximation in the spectral norm.** The projection residual is at most the residual
of any approximation `B * X` with columns in the range of `B`.
[HalkoMartinssonTropp2011, Proposition 8.5]. -/
theorem specNorm_one_sub_rangeProjector_mul_le_specNorm_sub_mul (B : Matrix m p 𝕜)
    (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    specNorm ((1 - rangeProjector B) * A) ≤ specNorm (A - B * X) := by
  rw [← one_sub_rangeProjector_mul_sub_mul B A X]
  exact specNorm_one_sub_rangeProjector_mul_le B _

omit [Fintype n] in
private theorem one_sub_rangeProjector_mul_one_sub_rangeProjector_mul {B : Matrix m p 𝕜}
    {Y : Matrix m l 𝕜} (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin)
    (A : Matrix m n 𝕜) :
    (1 - rangeProjector B) * ((1 - rangeProjector Y) * A) = (1 - rangeProjector B) * A := by
  have hmul : (1 - rangeProjector B) * (1 - rangeProjector Y) = 1 - rangeProjector B := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
      rangeProjector_mul_rangeProjector_of_range_le h, sub_self, sub_zero]
  rw [← Matrix.mul_assoc, hmul]

/-- A larger range gives a smaller projection residual, in spectral norm.
[HalkoMartinssonTropp2011, Proposition 8.5].
Port of `NLAlib.specNorm_sub_rangeProjector_mul_le_of_mul_eq`. -/
theorem specNorm_one_sub_rangeProjector_mul_le_of_range_le {B : Matrix m p 𝕜} {Y : Matrix m l 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) (A : Matrix m n 𝕜) :
    specNorm ((1 - rangeProjector B) * A) ≤ specNorm ((1 - rangeProjector Y) * A) := by
  rw [← one_sub_rangeProjector_mul_one_sub_rangeProjector_mul h A]
  exact specNorm_one_sub_rangeProjector_mul_le B _

/-- A larger range gives a smaller projection residual, in Frobenius norm.
Port of `NLAlib.frobSq_sub_rangeProjector_mul_le_of_mul_eq`. -/
theorem frobNorm_one_sub_rangeProjector_mul_le_of_range_le {B : Matrix m p 𝕜} {Y : Matrix m l 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) (A : Matrix m n 𝕜) :
    frobNorm ((1 - rangeProjector B) * A) ≤ frobNorm ((1 - rangeProjector Y) * A) := by
  rw [← one_sub_rangeProjector_mul_one_sub_rangeProjector_mul h A]
  exact frobNorm_one_sub_rangeProjector_mul_le B _

end NLAlib
