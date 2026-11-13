/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Projector

/-!
# The complementary projector

For a matrix $\mathbf{A}$, the complementary projector $\mathbf{I} - \mathbf{P}_{\mathbf{A}}$, with
$\mathbf{P}_{\mathbf{A}}$ the projector `rangeProjector`, is the orthogonal projector onto the
orthogonal complement of the column space of $\mathbf{A}$, the kernel of $\mathbf{A}^{\mathsf{H}}$.
Applied to a vector it gives the residual of the best approximation from the column space, and
applied to a matrix it gives the projection residual $(\mathbf{I} -
\mathbf{P}_{\mathbf{Y}})\mathbf{A}$, which has no definition of its own.

## Main results

* `NLAlib.isStarProjection_one_sub_rangeProjector`: it is an orthogonal projector.
* `NLAlib.one_sub_rangeProjector_mul_self`, `NLAlib.conjTranspose_mul_one_sub_rangeProjector`: it
  annihilates the columns of $\mathbf{A}$, on both sides.
* `NLAlib.one_sub_rangeProjector_mul_sub_mul`: the residual of $\mathbf{A} - \mathbf{B}\mathbf{X}$
  is the residual of $\mathbf{A}$.
* `NLAlib.range_one_sub_rangeProjector`, `NLAlib.rank_one_sub_rangeProjector_add_rank`:
  its range and its rank.
* `NLAlib.norm_one_sub_rangeProjector_mulVec_le`: the projection is the best approximation.
* `NLAlib.norm_toLp_sq_eq_add_one_sub_rangeProjector`: Pythagoras for a vector and a column space.
* `IsIdempotentElem.trace_mul_add_trace_one_sub_mul_mul_one_sub`: the trace split
  $\operatorname{tr}(\mathbf{P}\mathbf{A}) + \operatorname{tr}((\mathbf{I} - \mathbf{P})\mathbf{A}
  (\mathbf{I} - \mathbf{P})) = \operatorname{tr}\mathbf{A}$ for an idempotent $\mathbf{P}$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}

/-- The complementary projector $\mathbf{I} - \mathbf{P}_{\mathbf{A}}$ is an orthogonal projector
(`IsStarProjection`). -/
theorem isStarProjection_one_sub_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) : IsStarProjection (1 - rangeProjector A) :=
  (isStarProjection_rangeProjector A).one_sub

/-- The projection residual of $\mathbf{A}$ with respect to itself vanishes:
$(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{A} = \mathbf{0}$. -/
@[simp]
theorem one_sub_rangeProjector_mul_self [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) : (1 - rangeProjector A) * A = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_self, sub_self]

/-- The projection residual is orthogonal to the columns of $\mathbf{B}$:
$\mathbf{B}^{\mathsf{H}}(\mathbf{I} - \mathbf{P}_{\mathbf{B}}) = \mathbf{0}$. -/
@[simp]
theorem conjTranspose_mul_one_sub_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (B : Matrix m n 𝕜) : Bᴴ * (1 - rangeProjector B) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, conjTranspose_mul_rangeProjector, sub_self]

/-- The projection residual written as a difference:
$(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A} = \mathbf{A} - \mathbf{P}_{\mathbf{Y}}\mathbf{A}$.
The product on the left is the library's spelling of the residual; this lemma is for proofs that
want the difference. -/
theorem one_sub_rangeProjector_mul [Fintype m] [Fintype n] [DecidableEq m] (Y : Matrix m n 𝕜)
    (A : Matrix m p 𝕜) : (1 - rangeProjector Y) * A = A - rangeProjector Y * A := by
  rw [Matrix.sub_mul, Matrix.one_mul]

/-- The projection residual does not see a matrix with columns in the range:
$(\mathbf{I} - \mathbf{P}_{\mathbf{B}})(\mathbf{A} - \mathbf{B}\mathbf{X}) =
(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{A}$ for every $\mathbf{X}$. -/
theorem one_sub_rangeProjector_mul_sub_mul [Fintype m] [Fintype p] [DecidableEq m]
    (B : Matrix m p 𝕜) (A : Matrix m n 𝕜) (X : Matrix p n 𝕜) :
    (1 - rangeProjector B) * (A - B * X) = (1 - rangeProjector B) * A := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, one_sub_rangeProjector_mul_self, Matrix.zero_mul,
    sub_zero]

/-- The range of the complementary projector $\mathbf{I} - \mathbf{P}_{\mathbf{A}}$ is the kernel
of $\mathbf{A}^{\mathsf{H}}$: the orthogonal complement of the column space, expressed without
leaving `m → 𝕜`. -/
theorem range_one_sub_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) :
    LinearMap.range (1 - rangeProjector A).mulVecLin = LinearMap.ker Aᴴ.mulVecLin := by
  ext x
  rw [← (isStarProjection_one_sub_rangeProjector A).mulVec_eq_self_iff, LinearMap.mem_ker,
    Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_self,
    rangeProjector_mulVec_eq_zero_iff]

/-- The rank of the complementary projector and the rank of $\mathbf{A}$ add up to the number of
rows: $\operatorname{rank}(\mathbf{I} - \mathbf{P}_{\mathbf{A}}) + \operatorname{rank} \mathbf{A}
= \lvert m \rvert$. -/
theorem rank_one_sub_rangeProjector_add_rank [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) : (1 - rangeProjector A).rank + A.rank = Fintype.card m := by
  have h := LinearMap.finrank_range_add_finrank_ker Aᴴ.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [Matrix.rank, range_one_sub_rangeProjector, ← Matrix.rank_conjTranspose A,
    Matrix.rank, add_comm]
  exact h

/-- **Best approximation.** The projection of $\mathbf{x}$ onto the column space of $\mathbf{B}$
is at least as close to $\mathbf{x}$, in Euclidean norm, as any point $\mathbf{B}\mathbf{y}$ of that
space: $\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{x}\| \le \|\mathbf{x} -
\mathbf{B}\mathbf{y}\|$.
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
$\|\mathbf{x}\|^2 = \|\mathbf{P}_{\mathbf{B}}\mathbf{x}\|^2 +
\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{x}\|^2$.
[TrefethenBau1997, Lecture 6]. -/
theorem norm_toLp_sq_eq_add_one_sub_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (B : Matrix m n 𝕜) (x : m → 𝕜) :
    ‖WithLp.toLp 2 x‖ ^ 2 =
      ‖WithLp.toLp 2 (rangeProjector B *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 ((1 - rangeProjector B) *ᵥ x)‖ ^ 2 :=
  (isStarProjection_rangeProjector B).norm_toLp_sq_eq_add x


/-- **The trace split** for an idempotent $\mathbf{P}$ ($\mathbf{P}^2 = \mathbf{P}$, not
necessarily Hermitian) over any commutative ring: for every square $\mathbf{A}$,
$$\operatorname{tr}(\mathbf{P}\mathbf{A}) +
\operatorname{tr}\bigl((\mathbf{I} - \mathbf{P})\mathbf{A}(\mathbf{I} - \mathbf{P})\bigr) =
\operatorname{tr}\mathbf{A}\,,$$
by cyclicity of the trace and $(\mathbf{I} - \mathbf{P})^2 = \mathbf{I} - \mathbf{P}$. With
$\mathbf{P} = \mathbf{P}_{\mathbf{A}\mathbf{S}}$ it splits $\operatorname{tr}\mathbf{A}$ into the
part Hutch++ computes exactly and the compressed residual its probes estimate
(`NLAlib.trace_sub_hutchpp`). [MeyerMuscoMuscoWoodruff2021, §3, proof of Theorem 1]; there for
$\mathbf{P} = \mathbf{Q}\mathbf{Q}^{\mathsf{T}}$ with orthonormal $\mathbf{Q}$. -/
theorem _root_.IsIdempotentElem.trace_mul_add_trace_one_sub_mul_mul_one_sub {R : Type*}
    [CommRing R] [Fintype m] [DecidableEq m] {P : Matrix m m R} (hP : IsIdempotentElem P)
    (A : Matrix m m R) :
    (P * A).trace + ((1 - P) * A * (1 - P)).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, hP.one_sub.eq, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    add_sub_cancel]

end NLAlib
