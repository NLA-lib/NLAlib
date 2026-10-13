/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Order
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.Matrix.Basic.Orthonormal

/-!
# Orthogonal projectors

An orthogonal projector is a matrix `P` with `IsStarProjection P` (Mathlib: idempotent and
self-adjoint). `NLAlib.rangeProjector A` is the orthogonal projector onto the column space
`LinearMap.range A.mulVecLin` of an arbitrary matrix `A`, of any shape and rank. It depends only
on that range.

The projection residual of `A` with respect to `Y` has no definition; it is always written
`(1 - rangeProjector Y) * A`.

## Main definitions

* `NLAlib.rangeProjector`: the orthogonal projector onto the column space of a matrix.

## Main results

* `NLAlib.isStarProjection_rangeProjector`, `NLAlib.rangeProjector_mul_self`,
  `NLAlib.range_mulVecLin_rangeProjector`: the characterising properties.
* `IsStarProjection.eq_rangeProjector`: uniqueness.
* `NLAlib.rangeProjector_mul_eq_self_iff`: `rangeProjector B * Y = Y` iff the range of `Y` is
  inside the range of `B`.
* `NLAlib.HasOrthonormalCols.rangeProjector_eq`: for orthonormal `Q` the projector is `Q * Qᴴ`.
* `NLAlib.rangeProjector_eq_mul_inv_mul_conjTranspose`: the full-column-rank formula.
* `NLAlib.exists_hasOrthonormalCols_range_eq`, `NLAlib.exists_hasOrthonormalCols_range_le`:
  orthonormal bases of a column space.
* `NLAlib.HasOrthonormalCols.exists_fromCols`: orthonormal completion.
* `NLAlib.norm_one_sub_rangeProjector_mulVec_le`: the projection is the best approximation.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Star projections of matrices -/

/-- A matrix is a star projection exactly when it is idempotent and Hermitian. -/
theorem _root_.Matrix.isStarProjection_iff {P : Matrix m m 𝕜} :
    IsStarProjection P ↔ P * P = P ∧ P.IsHermitian := by
  sorry

/-- A star projection is a Hermitian matrix. -/
theorem _root_.IsStarProjection.isHermitian {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    P.IsHermitian := by
  sorry

/-- A star projection squares to itself. -/
theorem _root_.IsStarProjection.mul_self {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    P * P = P := by
  sorry

/-- A star projection equals its conjugate transpose. -/
theorem _root_.IsStarProjection.conjTranspose_eq {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    Pᴴ = P := by
  sorry

/-- A star projection is positive semidefinite. Applied to `hP.one_sub`, this gives `P ≤ 1` in
the Loewner order. -/
theorem _root_.IsStarProjection.posSemidef {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    P.PosSemidef := by
  sorry

/-- A star projection fixes exactly the matrices whose columns lie in its range. -/
theorem _root_.IsStarProjection.mul_eq_self_iff {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {A : Matrix m n 𝕜} :
    P * A = A ↔ LinearMap.range A.mulVecLin ≤ LinearMap.range P.mulVecLin := by
  sorry

/-- A star projection fixes exactly the vectors in its range. -/
theorem _root_.IsStarProjection.mulVec_eq_self_iff {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {x : m → 𝕜} : P *ᵥ x = x ↔ x ∈ LinearMap.range P.mulVecLin := by
  sorry

/-- Two star projections with the same range are equal. -/
theorem _root_.IsStarProjection.eq_of_range_eq {P P' : Matrix m m 𝕜} (hP : IsStarProjection P)
    (hP' : IsStarProjection P')
    (h : LinearMap.range P.mulVecLin = LinearMap.range P'.mulVecLin) : P = P' := by
  sorry

/-- A star projection does not increase the Euclidean norm of a vector. -/
theorem _root_.IsStarProjection.norm_toLp_mulVec_le {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (x : m → 𝕜) : ‖WithLp.toLp 2 (P *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  sorry

/-- For `Q` with orthonormal columns, `Q * Qᴴ` is a star projection.
Port of `NLAlib.mul_conjTranspose_mul_mul_conjTranspose`. -/
theorem HasOrthonormalCols.isStarProjection_mul_conjTranspose [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) : IsStarProjection (Q * Qᴴ) := by
  sorry

/-! ### The range projector -/

open Classical in
/-- The **orthogonal projector onto the column space** of `A`: the matrix of the orthogonal
projection of `EuclideanSpace 𝕜 m` onto `LinearMap.range A.mulVecLin`. Defined for every matrix,
including rank-deficient and empty ones, and equal to `0` for `A = 0`. It depends only on the
range of `A` (`NLAlib.rangeProjector_inj`); for `Q` with orthonormal columns it is `Q * Qᴴ`
(`NLAlib.HasOrthonormalCols.rangeProjector_eq`). [GolubVanLoan2013, §2.5.1]. -/
noncomputable def rangeProjector (A : Matrix m n 𝕜) : Matrix m m 𝕜 :=
  LinearMap.toMatrix' <|
    (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).toLinearMap ∘ₗ
      ((LinearMap.range A.mulVecLin).map
        (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap).starProjection.toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap

/-- The range projector is a star projection: idempotent and Hermitian.
Port of `NLAlib.rangeProjector_isHermitian` and `NLAlib.rangeProjector_isIdempotentElem`. -/
theorem isStarProjection_rangeProjector (A : Matrix m n 𝕜) :
    IsStarProjection (rangeProjector A) := by
  sorry

/-- The range projector is idempotent. -/
@[simp]
theorem rangeProjector_mul_rangeProjector (A : Matrix m n 𝕜) :
    rangeProjector A * rangeProjector A = rangeProjector A := by
  sorry

/-- The range projector is Hermitian. -/
@[simp]
theorem conjTranspose_rangeProjector (A : Matrix m n 𝕜) :
    (rangeProjector A)ᴴ = rangeProjector A := by
  sorry

/-- The range projector of `A` fixes `A`. Port of `NLAlib.rangeProjector_mul`. -/
@[simp]
theorem rangeProjector_mul_self (A : Matrix m n 𝕜) : rangeProjector A * A = A := by
  sorry

/-- `Aᴴ * rangeProjector A = Aᴴ`. -/
@[simp]
theorem conjTranspose_mul_rangeProjector (A : Matrix m n 𝕜) : Aᴴ * rangeProjector A = Aᴴ := by
  sorry

/-- The range of the range projector of `A` is the column space of `A`.
Port of `NLAlib.range_mulVecLin_rangeProjector`. -/
theorem range_mulVecLin_rangeProjector (A : Matrix m n 𝕜) :
    LinearMap.range (rangeProjector A).mulVecLin = LinearMap.range A.mulVecLin := by
  sorry

/-- The range projector of `A` fixes `A *ᵥ y`. -/
@[simp]
theorem rangeProjector_mulVec_mulVec (A : Matrix m n 𝕜) (y : n → 𝕜) :
    rangeProjector A *ᵥ (A *ᵥ y) = A *ᵥ y := by
  sorry

/-- The range projector of `B` fixes exactly the vectors in the column space of `B`. -/
theorem rangeProjector_mulVec_eq_self_iff {B : Matrix m n 𝕜} {x : m → 𝕜} :
    rangeProjector B *ᵥ x = x ↔ x ∈ LinearMap.range B.mulVecLin := by
  sorry

/-- `rangeProjector B * Y = Y` exactly when the column space of `Y` is contained in that of `B`.
Port of `NLAlib.rangeProjector_mul_of_range_le`, there one direction. -/
theorem rangeProjector_mul_eq_self_iff {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜} :
    rangeProjector B * Y = Y ↔ LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin := by
  sorry

/-- The column space of `Y` is contained in that of `B` exactly when `Y = B * C` for some `C`. -/
theorem range_mulVecLin_le_iff_exists_mul {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜} :
    LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin ↔ ∃ C : Matrix n p 𝕜, Y = B * C := by
  sorry

/-- `rangeProjector B * Y = 0` exactly when the columns of `Y` are orthogonal to those of `B`. -/
theorem rangeProjector_mul_eq_zero_iff {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜} :
    rangeProjector B * Y = 0 ↔ Bᴴ * Y = 0 := by
  sorry

/-- A star projection with the same range as `A` is the range projector of `A`. -/
theorem _root_.IsStarProjection.eq_rangeProjector {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {A : Matrix m n 𝕜} (h : LinearMap.range P.mulVecLin = LinearMap.range A.mulVecLin) :
    P = rangeProjector A := by
  sorry

/-- The range projector of a star projection is the projection itself. -/
theorem _root_.IsStarProjection.rangeProjector_eq {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    rangeProjector P = P := by
  sorry

/-- The range projector depends only on the column space. -/
theorem rangeProjector_inj {A : Matrix m n 𝕜} {B : Matrix m p 𝕜} :
    rangeProjector A = rangeProjector B ↔
      LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin := by
  sorry

/-- If the column space of `Y` is inside that of `B`, projecting onto `B` after `Y` is projecting
onto `Y`. Port of `NLAlib.rangeProjector_mul_rangeProjector_of_mul_eq`. -/
theorem rangeProjector_mul_rangeProjector_of_range_le {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector B * rangeProjector Y = rangeProjector Y := by
  sorry

/-- If the column space of `Y` is inside that of `B`, projecting onto `Y` after `B` is projecting
onto `Y`. -/
theorem rangeProjector_mul_rangeProjector_of_range_le' {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector Y * rangeProjector B = rangeProjector Y := by
  sorry

/-- The range projector is monotone: a smaller column space gives a smaller projector in the
Loewner order. -/
theorem rangeProjector_mono {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector Y ≤ rangeProjector B := by
  sorry

/-! ### Special cases -/

/-- The range projector of the zero matrix is zero, for every shape.
Port of `NLAlib.rangeProjector_zero`. -/
@[simp]
theorem rangeProjector_zero : rangeProjector (0 : Matrix m n 𝕜) = 0 := by
  sorry

/-- The range projector of an invertible matrix is the identity. -/
theorem rangeProjector_of_isUnit [DecidableEq m] {A : Matrix m m 𝕜} (hA : IsUnit A) :
    rangeProjector A = 1 := by
  sorry

/-- The range projector of the identity is the identity. -/
@[simp]
theorem rangeProjector_one [DecidableEq m] : rangeProjector (1 : Matrix m m 𝕜) = 1 := by
  sorry

/-- Scaling by a nonzero scalar does not change the range projector. -/
theorem rangeProjector_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix m n 𝕜) :
    rangeProjector (c • A) = rangeProjector A := by
  sorry

/-- Right multiplication by an invertible matrix does not change the range projector. -/
theorem rangeProjector_mul_of_isUnit [DecidableEq n] (A : Matrix m n 𝕜) {B : Matrix n n 𝕜}
    (hB : IsUnit B) : rangeProjector (A * B) = rangeProjector A := by
  sorry

/-- `A * Aᴴ` has the same range projector as `A`. -/
@[simp]
theorem rangeProjector_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    rangeProjector (A * Aᴴ) = rangeProjector A := by
  sorry

/-- For `Q` with orthonormal columns, the range projector is `Q * Qᴴ`.
Port of `NLAlib.rangeProjector_eq_mul_conjTranspose_of_hasOrthonormalCols`. -/
theorem HasOrthonormalCols.rangeProjector_eq [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) : rangeProjector Q = Q * Qᴴ := by
  sorry

/-- With full column rank, the range projector is `A * (Aᴴ * A)⁻¹ * Aᴴ`.
[GolubVanLoan2013, §5.3.1]; the hypothesis is taken as invertibility of the Gram matrix, which
`NLAlib.isUnit_conjTranspose_mul_self_iff` converts to and from injectivity of `A.mulVec`.
Port of `NLAlib.rangeProjector_eq_mul_inv_gram_conjTranspose`. -/
theorem rangeProjector_eq_mul_inv_mul_conjTranspose [DecidableEq n] {A : Matrix m n 𝕜}
    (hA : IsUnit (Aᴴ * A)) : rangeProjector A = A * (Aᴴ * A)⁻¹ * Aᴴ := by
  sorry

/-- The rank of the range projector of `A` is the rank of `A`.
Port of `NLAlib.rank_rangeProjector`. -/
@[simp]
theorem rank_rangeProjector (A : Matrix m n 𝕜) : (rangeProjector A).rank = A.rank := by
  sorry

/-! ### The complementary projector -/

/-- The complementary projector `1 - rangeProjector A` is a star projection. -/
theorem isStarProjection_one_sub_rangeProjector [DecidableEq m] (A : Matrix m n 𝕜) :
    IsStarProjection (1 - rangeProjector A) := by
  sorry

/-- The projection residual of `A` with respect to itself vanishes. -/
@[simp]
theorem one_sub_rangeProjector_mul_self [DecidableEq m] (A : Matrix m n 𝕜) :
    (1 - rangeProjector A) * A = 0 := by
  sorry

/-- The projection residual is orthogonal to the columns of `B`:
`Bᴴ * (1 - rangeProjector B) = 0`. Port of `NLAlib.conjTranspose_mul_residual`. -/
@[simp]
theorem conjTranspose_mul_one_sub_rangeProjector [DecidableEq m] (B : Matrix m n 𝕜) :
    Bᴴ * (1 - rangeProjector B) = 0 := by
  sorry

/-- The projection residual written as a difference. The product on the left is the library's
spelling of the residual; this lemma is for proofs that want the difference. -/
theorem one_sub_rangeProjector_mul [DecidableEq m] (Y : Matrix m n 𝕜) (A : Matrix m p 𝕜) :
    (1 - rangeProjector Y) * A = A - rangeProjector Y * A := by
  sorry

/-- The range of the complementary projector of `A` is the kernel of `Aᴴ`: the orthogonal
complement of the column space, expressed without leaving `m → 𝕜`. -/
theorem range_mulVecLin_one_sub_rangeProjector [DecidableEq m] (A : Matrix m n 𝕜) :
    LinearMap.range (1 - rangeProjector A).mulVecLin = LinearMap.ker Aᴴ.mulVecLin := by
  sorry

/-- **Best approximation.** The projection of `x` onto the column space of `B` is at least as
close to `x`, in Euclidean norm, as any other point `B *ᵥ y` of that space.
[GolubVanLoan2013, §5.3.1]. -/
theorem norm_one_sub_rangeProjector_mulVec_le [DecidableEq m] (B : Matrix m n 𝕜) (x : m → 𝕜)
    (y : n → 𝕜) :
    ‖WithLp.toLp 2 ((1 - rangeProjector B) *ᵥ x)‖ ≤ ‖WithLp.toLp 2 (x - B *ᵥ y)‖ := by
  sorry

/-- **Pythagoras** for a vector and a column space:
`‖x‖² = ‖P x‖² + ‖(1 - P) x‖²` with `P = rangeProjector B`. -/
theorem norm_toLp_sq_eq_add_one_sub_rangeProjector [DecidableEq m] (B : Matrix m n 𝕜)
    (x : m → 𝕜) :
    ‖WithLp.toLp 2 x‖ ^ 2 =
      ‖WithLp.toLp 2 (rangeProjector B *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 ((1 - rangeProjector B) *ᵥ x)‖ ^ 2 := by
  sorry

/-! ### Bridge to Mathlib -/

/-- The range projector is the matrix of Mathlib's `Submodule.starProjection` onto the range of
`Matrix.toEuclideanLin A`. Port of `NLAlib.toEuclideanLin_rangeProjector`. -/
theorem toEuclideanLin_rangeProjector [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) :
    Matrix.toEuclideanLin (rangeProjector A) =
      ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection : _ →ₗ[𝕜] _) := by
  sorry

/-! ### Orthonormal bases and completion -/

/-- **Orthonormal basis of a column space.** For any column index type `p` with as many elements
as the rank of `A`, there is a `Q` with orthonormal columns indexed by `p` and the same column
space as `A`. Port of `NLAlib.hasOrthonormalCols_orthonormalBasisMatrix` and
`NLAlib.range_orthonormalBasisMatrix`, there a definition indexed by `Fin (finrank S)`. -/
theorem exists_hasOrthonormalCols_range_eq [DecidableEq p] (A : Matrix m n 𝕜)
    (h : Fintype.card p = A.rank) :
    ∃ Q : Matrix m p 𝕜, HasOrthonormalCols Q ∧
      LinearMap.range Q.mulVecLin = LinearMap.range A.mulVecLin := by
  sorry

/-- For any column index type `p` with at least `rank A` and at most `card m` elements, there is a
`Q` with orthonormal columns indexed by `p` whose column space contains that of `A`. -/
theorem exists_hasOrthonormalCols_range_le [DecidableEq p] (A : Matrix m n 𝕜)
    (h : A.rank ≤ Fintype.card p) (hp : Fintype.card p ≤ Fintype.card m) :
    ∃ Q : Matrix m p 𝕜, HasOrthonormalCols Q ∧
      LinearMap.range A.mulVecLin ≤ LinearMap.range Q.mulVecLin := by
  sorry

/-- Every star projection is `Q * Qᴴ` for a `Q` with orthonormal columns, indexed by any type
with `rank P` elements. -/
theorem _root_.IsStarProjection.exists_hasOrthonormalCols_mul_conjTranspose_eq [DecidableEq p]
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) (h : Fintype.card p = P.rank) :
    ∃ Q : Matrix m p 𝕜, HasOrthonormalCols Q ∧ Q * Qᴴ = P := by
  sorry

/-- **Orthonormal completion.** A matrix `Q` with orthonormal columns extends, by columns indexed
by any type `p` of the complementary size, to a matrix `fromCols Q Q'` with orthonormal columns.
That matrix has as many rows as columns, so it is unitary up to relabelling:
`HasOrthonormalCols.mul_conjTranspose_self_of_card_eq` gives `Q * Qᴴ + Q' * Q'ᴴ = 1`.
Port of `NLAlib.exists_unitary_complement`. -/
theorem HasOrthonormalCols.exists_fromCols [DecidableEq n] [DecidableEq p] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (h : Fintype.card n + Fintype.card p = Fintype.card m) :
    ∃ Q' : Matrix m p 𝕜, HasOrthonormalCols (Matrix.fromCols Q Q') := by
  sorry

/-- If `fromCols Q Q'` has orthonormal columns and is square up to relabelling, the two
projectors are complementary: `Q * Qᴴ + Q' * Q'ᴴ = 1`. -/
theorem HasOrthonormalCols.mul_conjTranspose_add_mul_conjTranspose [DecidableEq m] [DecidableEq n]
    [DecidableEq p] {Q : Matrix m n 𝕜} {Q' : Matrix m p 𝕜}
    (hQ : HasOrthonormalCols (Matrix.fromCols Q Q'))
    (h : Fintype.card n + Fintype.card p = Fintype.card m) : Q * Qᴴ + Q' * Q'ᴴ = 1 := by
  sorry

end NLAlib
