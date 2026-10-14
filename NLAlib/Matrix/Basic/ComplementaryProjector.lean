/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Projector

/-!
# The complementary projector

For a matrix `A`, the complementary projector `1 - rangeProjector A` is the orthogonal projector
onto the orthogonal complement of the column space of `A`, the kernel of `Aᴴ`. Applied to a
vector it gives the residual of the best approximation from the column space, and applied to a
matrix it gives the projection residual `(1 - rangeProjector Y) * A`, which has no definition of
its own.

## Main results

* `NLAlib.isStarProjection_one_sub_rangeProjector`: it is an orthogonal projector.
* `NLAlib.one_sub_rangeProjector_mul_self`, `NLAlib.conjTranspose_mul_one_sub_rangeProjector`: it
  annihilates the columns of `A`, on both sides.
* `NLAlib.range_mulVecLin_one_sub_rangeProjector`, `NLAlib.rank_one_sub_rangeProjector_add_rank`:
  its range and its rank.
* `NLAlib.norm_one_sub_rangeProjector_mulVec_le`: the projection is the best approximation.
* `NLAlib.norm_toLp_sq_eq_add_one_sub_rangeProjector`: Pythagoras for a vector and a column space.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}

/-- The complementary projector `1 - rangeProjector A` is a star projection. -/
theorem isStarProjection_one_sub_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) : IsStarProjection (1 - rangeProjector A) :=
  (isStarProjection_rangeProjector A).one_sub

/-- The projection residual of `A` with respect to itself vanishes. -/
@[simp]
theorem one_sub_rangeProjector_mul_self [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) : (1 - rangeProjector A) * A = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_self, sub_self]

/-- The projection residual is orthogonal to the columns of `B`:
`Bᴴ * (1 - rangeProjector B) = 0`. Port of `NLAlib.conjTranspose_mul_residual`. -/
@[simp]
theorem conjTranspose_mul_one_sub_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (B : Matrix m n 𝕜) : Bᴴ * (1 - rangeProjector B) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, conjTranspose_mul_rangeProjector, sub_self]

/-- The projection residual written as a difference. The product on the left is the library's
spelling of the residual; this lemma is for proofs that want the difference. -/
theorem one_sub_rangeProjector_mul [Fintype m] [Fintype n] [DecidableEq m] (Y : Matrix m n 𝕜)
    (A : Matrix m p 𝕜) : (1 - rangeProjector Y) * A = A - rangeProjector Y * A := by
  rw [Matrix.sub_mul, Matrix.one_mul]

/-- The range of the complementary projector of `A` is the kernel of `Aᴴ`: the orthogonal
complement of the column space, expressed without leaving `m → 𝕜`. -/
theorem range_mulVecLin_one_sub_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) :
    LinearMap.range (1 - rangeProjector A).mulVecLin = LinearMap.ker Aᴴ.mulVecLin := by
  ext x
  rw [← (isStarProjection_one_sub_rangeProjector A).mulVec_eq_self_iff, LinearMap.mem_ker,
    Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_self,
    rangeProjector_mulVec_eq_zero_iff]

/-- The rank of the complementary projector `1 - rangeProjector A` and the rank of `A` add up to
the number of rows. -/
theorem rank_one_sub_rangeProjector_add_rank [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) : (1 - rangeProjector A).rank + A.rank = Fintype.card m := by
  have h := LinearMap.finrank_range_add_finrank_ker Aᴴ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [Matrix.rank, range_mulVecLin_one_sub_rangeProjector, ← Matrix.rank_conjTranspose A,
    Matrix.rank, add_comm]
  exact h

/-- **Best approximation.** The projection of `x` onto the column space of `B` is at least as
close to `x`, in Euclidean norm, as any other point `B *ᵥ y` of that space.
[GolubVanLoan2013, §5.3.1]. -/
theorem norm_one_sub_rangeProjector_mulVec_le [Fintype m] [Fintype n] [DecidableEq m]
    (B : Matrix m n 𝕜) (x : m → 𝕜) (y : n → 𝕜) :
    ‖WithLp.toLp 2 ((1 - rangeProjector B) *ᵥ x)‖ ≤ ‖WithLp.toLp 2 (x - B *ᵥ y)‖ := by
  have h : (1 - rangeProjector B) *ᵥ x = (1 - rangeProjector B) *ᵥ (x - B *ᵥ y) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, one_sub_rangeProjector_mul_self,
      Matrix.zero_mulVec, sub_zero]
  rw [h]
  exact (isStarProjection_one_sub_rangeProjector B).norm_toLp_mulVec_le _

/-- **Pythagoras** for a vector and a column space:
`‖x‖² = ‖P x‖² + ‖(1 - P) x‖²` with `P = rangeProjector B`. -/
theorem norm_toLp_sq_eq_add_one_sub_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (B : Matrix m n 𝕜) (x : m → 𝕜) :
    ‖WithLp.toLp 2 x‖ ^ 2 =
      ‖WithLp.toLp 2 (rangeProjector B *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 ((1 - rangeProjector B) *ᵥ x)‖ ^ 2 :=
  (isStarProjection_rangeProjector B).norm_toLp_sq_eq_add x

end NLAlib
