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
* `NLAlib.norm_one_sub_rangeProjector_mulVec_le`: the projection is the best approximation.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*}

/-! ### Star projections of matrices -/

/-- A matrix is a star projection exactly when it is idempotent and Hermitian. -/
theorem _root_.Matrix.isStarProjection_iff [Fintype m] {P : Matrix m m 𝕜} :
    IsStarProjection P ↔ P * P = P ∧ P.IsHermitian :=
  _root_.isStarProjection_iff P

/-- A star projection is a Hermitian matrix. -/
theorem _root_.IsStarProjection.isHermitian [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) : P.IsHermitian :=
  (Matrix.isStarProjection_iff.mp hP).2

/-- A star projection squares to itself. -/
theorem _root_.IsStarProjection.mul_self [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) : P * P = P :=
  (Matrix.isStarProjection_iff.mp hP).1

/-- A star projection equals its conjugate transpose. -/
theorem _root_.IsStarProjection.conjTranspose_eq [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) : Pᴴ = P :=
  hP.isHermitian

/-- A star projection is positive semidefinite. Applied to `hP.one_sub`, this gives `P ≤ 1` in
the Loewner order. -/
theorem _root_.IsStarProjection.posSemidef [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hP.conjTranspose_eq, hP.mul_self] at h

/-- A star projection fixes exactly the matrices whose columns lie in its range. -/
theorem _root_.IsStarProjection.mul_eq_self_iff [Fintype m] [Fintype n] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {A : Matrix m n 𝕜} :
    P * A = A ↔ LinearMap.range A.mulVecLin ≤ LinearMap.range P.mulVecLin := by
  constructor
  · rintro h _ ⟨x, rfl⟩
    exact ⟨A *ᵥ x, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]⟩
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro x
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hy
    rw [← Matrix.mulVec_mulVec, ← hy, Matrix.mulVec_mulVec, hP.mul_self]

/-- A star projection fixes exactly the vectors in its range. -/
theorem _root_.IsStarProjection.mulVec_eq_self_iff [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {x : m → 𝕜} : P *ᵥ x = x ↔ x ∈ LinearMap.range P.mulVecLin := by
  constructor
  · intro h
    exact ⟨x, h⟩
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP.mul_self]

/-- Two star projections with the same range are equal. -/
theorem _root_.IsStarProjection.eq_of_range_eq [Fintype m] {P P' : Matrix m m 𝕜}
    (hP : IsStarProjection P) (hP' : IsStarProjection P')
    (h : LinearMap.range P.mulVecLin = LinearMap.range P'.mulVecLin) : P = P' := by
  have h1 : P' * P = P := hP'.mul_eq_self_iff.mpr h.le
  have h2 : P * P' = P' := hP.mul_eq_self_iff.mpr h.ge
  have h3 := congrArg Matrix.conjTranspose h1
  rw [Matrix.conjTranspose_mul, hP.conjTranspose_eq, hP'.conjTranspose_eq, h2] at h3
  exact h3.symm

/-- **Pythagoras** for a star projection: `‖x‖² = ‖P x‖² + ‖(1 - P) x‖²`. -/
theorem _root_.IsStarProjection.norm_toLp_sq_eq_add [Fintype m] [DecidableEq m]
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) (x : m → 𝕜) :
    ‖WithLp.toLp 2 x‖ ^ 2 =
      ‖WithLp.toLp 2 (P *ᵥ x)‖ ^ 2 + ‖WithLp.toLp 2 ((1 - P) *ᵥ x)‖ ^ 2 := by
  have hx : WithLp.toLp 2 x = WithLp.toLp 2 (P *ᵥ x) + WithLp.toLp 2 ((1 - P) *ᵥ x) := by
    rw [← WithLp.toLp_add, ← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have h0 : inner 𝕜 (WithLp.toLp 2 (P *ᵥ x)) (WithLp.toLp 2 ((1 - P) *ᵥ x)) = 0 := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hP.conjTranspose_eq,
      hP.mul_one_sub_self, Matrix.zero_mulVec, dotProduct_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [← hx] at h
  rw [sq, sq, sq, h]

/-- A star projection does not increase the Euclidean norm of a vector. -/
theorem _root_.IsStarProjection.norm_toLp_mulVec_le [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (x : m → 𝕜) : ‖WithLp.toLp 2 (P *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  classical
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [hP.norm_toLp_sq_eq_add x]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- For `Q` with orthonormal columns, `Q * Qᴴ` is a star projection.
Port of `NLAlib.mul_conjTranspose_mul_mul_conjTranspose`. -/
theorem HasOrthonormalCols.isStarProjection_mul_conjTranspose [Fintype m] [Fintype n]
    [DecidableEq n] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    IsStarProjection (Q * Qᴴ) := by
  rw [Matrix.isStarProjection_iff]
  exact ⟨by rw [Matrix.mul_assoc, hQ.conjTranspose_mul_cancel_left],
    Matrix.isHermitian_mul_conjTranspose_self Q⟩

/-! ### The range projector -/

open Classical in
/-- The **orthogonal projector onto the column space** of `A`: the matrix of the orthogonal
projection of `EuclideanSpace 𝕜 m` onto `LinearMap.range A.mulVecLin`. Defined for every matrix,
including rank-deficient and empty ones, and equal to `0` for `A = 0`. It depends only on the
range of `A` (`NLAlib.rangeProjector_inj`); for `Q` with orthonormal columns it is `Q * Qᴴ`
(`NLAlib.HasOrthonormalCols.rangeProjector_eq`). [GolubVanLoan2013, §2.5.1]. -/
noncomputable def rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) : Matrix m m 𝕜 :=
  LinearMap.toMatrix' <|
    (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).toLinearMap ∘ₗ
      ((LinearMap.range A.mulVecLin).map
        (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap).starProjection.toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap

/-- The column space of `A` as a subspace of `EuclideanSpace 𝕜 m`. -/
private noncomputable abbrev euclideanRange [Fintype n] (A : Matrix m n 𝕜) :
    Submodule 𝕜 (EuclideanSpace 𝕜 m) :=
  (LinearMap.range A.mulVecLin).map (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap

private theorem toLp_mem_euclideanRange_iff [Fintype n] {A : Matrix m n 𝕜} {x : m → 𝕜} :
    WithLp.toLp 2 x ∈ euclideanRange A ↔ x ∈ LinearMap.range A.mulVecLin :=
  Submodule.mem_map_equiv _

private theorem toEuclideanCLM_rangeProjector [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m n 𝕜) :
    Matrix.toEuclideanCLM (n := m) (𝕜 := 𝕜) (rangeProjector A) =
      (euclideanRange A).starProjection := by
  ext x : 1
  refine WithLp.ofLp_injective 2 ?_
  rw [Matrix.ofLp_toEuclideanCLM, rangeProjector]
  exact @LinearMap.toMatrix'_mulVec 𝕜 _ m m (fun a b => Classical.propDecidable (a = b)) _ _ _

private theorem rangeProjector_mulVec_eq_self_iff_aux [Fintype m] [Fintype n]
    {A : Matrix m n 𝕜} {x : m → 𝕜} :
    rangeProjector A *ᵥ x = x ↔ x ∈ LinearMap.range A.mulVecLin := by
  classical
  rw [← toLp_mem_euclideanRange_iff, ← Submodule.starProjection_eq_self_iff,
    ← toEuclideanCLM_rangeProjector, Matrix.toEuclideanCLM_toLp]
  exact (WithLp.toLp_injective 2).eq_iff.symm

/-- The range projector is a star projection: idempotent and Hermitian.
Port of `NLAlib.rangeProjector_isHermitian` and `NLAlib.rangeProjector_isIdempotentElem`. -/
theorem isStarProjection_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    IsStarProjection (rangeProjector A) := by
  classical
  have h := (isStarProjection_starProjection (U := euclideanRange A)).map
    (Matrix.toEuclideanCLM (n := m) (𝕜 := 𝕜)).symm
  rwa [← toEuclideanCLM_rangeProjector, StarAlgEquiv.symm_apply_apply] at h

/-- The range projector is idempotent. -/
@[simp]
theorem rangeProjector_mul_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    rangeProjector A * rangeProjector A = rangeProjector A :=
  (isStarProjection_rangeProjector A).mul_self

/-- The range projector is Hermitian. -/
@[simp]
theorem conjTranspose_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    (rangeProjector A)ᴴ = rangeProjector A :=
  (isStarProjection_rangeProjector A).conjTranspose_eq

/-- The range of the range projector of `A` is the column space of `A`.
Port of `NLAlib.range_mulVecLin_rangeProjector`. -/
theorem range_mulVecLin_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    LinearMap.range (rangeProjector A).mulVecLin = LinearMap.range A.mulVecLin := by
  ext x
  rw [← (isStarProjection_rangeProjector A).mulVec_eq_self_iff,
    rangeProjector_mulVec_eq_self_iff_aux]

/-- The range projector of `A` fixes `A`. Port of `NLAlib.rangeProjector_mul`. -/
@[simp]
theorem rangeProjector_mul_self [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    rangeProjector A * A = A :=
  (isStarProjection_rangeProjector A).mul_eq_self_iff.mpr (range_mulVecLin_rangeProjector A).ge

/-- `Aᴴ * rangeProjector A = Aᴴ`. -/
@[simp]
theorem conjTranspose_mul_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    Aᴴ * rangeProjector A = Aᴴ := by
  have h := congrArg Matrix.conjTranspose (rangeProjector_mul_self A)
  rwa [Matrix.conjTranspose_mul, conjTranspose_rangeProjector] at h

/-- The range projector of `A` fixes `A *ᵥ y`. -/
theorem rangeProjector_mulVec_mulVec [Fintype m] [Fintype n] (A : Matrix m n 𝕜) (y : n → 𝕜) :
    rangeProjector A *ᵥ (A *ᵥ y) = A *ᵥ y := by
  rw [Matrix.mulVec_mulVec, rangeProjector_mul_self]

/-- The range projector of `B` fixes exactly the vectors in the column space of `B`. -/
theorem rangeProjector_mulVec_eq_self_iff [Fintype m] [Fintype n] {B : Matrix m n 𝕜}
    {x : m → 𝕜} : rangeProjector B *ᵥ x = x ↔ x ∈ LinearMap.range B.mulVecLin :=
  rangeProjector_mulVec_eq_self_iff_aux

/-- `rangeProjector B * Y = Y` exactly when the column space of `Y` is contained in that of `B`.
Port of `NLAlib.rangeProjector_mul_of_range_le`, there one direction. -/
theorem rangeProjector_mul_eq_self_iff [Fintype m] [Fintype n] [Fintype p] {B : Matrix m n 𝕜}
    {Y : Matrix m p 𝕜} :
    rangeProjector B * Y = Y ↔ LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin := by
  rw [(isStarProjection_rangeProjector B).mul_eq_self_iff, range_mulVecLin_rangeProjector]

/-- The column space of `Y` is contained in that of `B` exactly when `Y = B * C` for some `C`. -/
theorem range_mulVecLin_le_iff_exists_mul [Fintype n] [Fintype p] {B : Matrix m n 𝕜}
    {Y : Matrix m p 𝕜} :
    LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin ↔ ∃ C : Matrix n p 𝕜, Y = B * C := by
  constructor
  · intro h
    have hcol : ∀ j, ∃ c : n → 𝕜, B *ᵥ c = Y.col j := fun j => by
      refine h ?_
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨j, rfl⟩
    choose c hc using hcol
    refine ⟨Matrix.of fun i j => c j i, Matrix.ext_col fun j => ?_⟩
    rw [← hc j]
    rfl
  · rintro ⟨C, rfl⟩
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _

private theorem exists_rangeProjector_eq_mul [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    ∃ C : Matrix n m 𝕜, rangeProjector A = A * C :=
  range_mulVecLin_le_iff_exists_mul.mp (range_mulVecLin_rangeProjector A).le

/-- `rangeProjector B * Y = 0` exactly when the columns of `Y` are orthogonal to those of `B`. -/
theorem rangeProjector_mul_eq_zero_iff [Fintype m] [Fintype n] {B : Matrix m n 𝕜}
    {Y : Matrix m p 𝕜} : rangeProjector B * Y = 0 ↔ Bᴴ * Y = 0 := by
  constructor
  · intro h
    rw [← conjTranspose_mul_rangeProjector, Matrix.mul_assoc, h, Matrix.mul_zero]
  · intro h
    obtain ⟨C, hC⟩ := exists_rangeProjector_eq_mul B
    rw [← conjTranspose_rangeProjector, hC, Matrix.conjTranspose_mul, Matrix.mul_assoc, h,
      Matrix.mul_zero]

/-- `rangeProjector B *ᵥ x = 0` exactly when `x` is orthogonal to the columns of `B`. This is the
vector form of `NLAlib.rangeProjector_mul_eq_zero_iff`. -/
theorem rangeProjector_mulVec_eq_zero_iff [Fintype m] [Fintype n] {B : Matrix m n 𝕜}
    {x : m → 𝕜} : rangeProjector B *ᵥ x = 0 ↔ Bᴴ *ᵥ x = 0 := by
  constructor
  · intro h
    rw [← conjTranspose_mul_rangeProjector, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h
    obtain ⟨C, hC⟩ := exists_rangeProjector_eq_mul B
    rw [← conjTranspose_rangeProjector, hC, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]

/-- A star projection with the same range as `A` is the range projector of `A`. -/
theorem _root_.IsStarProjection.eq_rangeProjector [Fintype m] [Fintype n] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {A : Matrix m n 𝕜}
    (h : LinearMap.range P.mulVecLin = LinearMap.range A.mulVecLin) : P = rangeProjector A :=
  hP.eq_of_range_eq (isStarProjection_rangeProjector A)
    (h.trans (range_mulVecLin_rangeProjector A).symm)

/-- The range projector of a star projection is the projection itself. -/
theorem _root_.IsStarProjection.rangeProjector_eq [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) : rangeProjector P = P :=
  (hP.eq_rangeProjector rfl).symm

/-- The range projector depends only on the column space. -/
theorem rangeProjector_inj [Fintype m] [Fintype n] [Fintype p] {A : Matrix m n 𝕜}
    {B : Matrix m p 𝕜} :
    rangeProjector A = rangeProjector B ↔
      LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin := by
  constructor
  · intro h
    rw [← range_mulVecLin_rangeProjector A, h, range_mulVecLin_rangeProjector]
  · intro h
    exact (isStarProjection_rangeProjector A).eq_rangeProjector
      ((range_mulVecLin_rangeProjector A).trans h)

/-- If the column space of `Y` is inside that of `B`, projecting onto `B` after `Y` is projecting
onto `Y`. Port of `NLAlib.rangeProjector_mul_rangeProjector_of_mul_eq`. -/
theorem rangeProjector_mul_rangeProjector_of_range_le [Fintype m] [Fintype n] [Fintype p]
    {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector B * rangeProjector Y = rangeProjector Y := by
  rw [rangeProjector_mul_eq_self_iff, range_mulVecLin_rangeProjector]
  exact h

/-- If the column space of `Y` is inside that of `B`, projecting onto `Y` after `B` is projecting
onto `Y`. -/
theorem rangeProjector_mul_rangeProjector_of_range_le' [Fintype m] [Fintype n] [Fintype p]
    {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector Y * rangeProjector B = rangeProjector Y := by
  have h' := congrArg Matrix.conjTranspose (rangeProjector_mul_rangeProjector_of_range_le h)
  rwa [Matrix.conjTranspose_mul, conjTranspose_rangeProjector, conjTranspose_rangeProjector]
    at h'

/-- The range projector is monotone: a smaller column space gives a smaller projector in the
Loewner order. -/
theorem rangeProjector_mono [Fintype m] [Fintype n] [Fintype p] {B : Matrix m n 𝕜}
    {Y : Matrix m p 𝕜} (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector Y ≤ rangeProjector B := by
  rw [Matrix.le_iff]
  exact ((isStarProjection_rangeProjector Y).sub_of_mul_eq_right
    (isStarProjection_rangeProjector B)
    (rangeProjector_mul_rangeProjector_of_range_le h)).posSemidef

/-! ### Special cases -/

/-- The range projector of the zero matrix is zero, for every shape.
Port of `NLAlib.rangeProjector_zero`. -/
@[simp]
theorem rangeProjector_zero [Fintype m] [Fintype n] : rangeProjector (0 : Matrix m n 𝕜) = 0 := by
  refine ((IsStarProjection.zero (Matrix m m 𝕜)).eq_rangeProjector ?_).symm
  rw [Matrix.mulVecLin_zero, Matrix.mulVecLin_zero, LinearMap.range_zero, LinearMap.range_zero]

/-- The range projector of the identity is the identity. -/
@[simp]
theorem rangeProjector_one [Fintype m] [DecidableEq m] :
    rangeProjector (1 : Matrix m m 𝕜) = 1 :=
  (IsStarProjection.one (Matrix m m 𝕜)).rangeProjector_eq

/-- The range projector of an invertible matrix is the identity. -/
theorem rangeProjector_of_isUnit [Fintype m] [DecidableEq m] {A : Matrix m m 𝕜}
    (hA : IsUnit A) : rangeProjector A = 1 := by
  rw [← rangeProjector_one (𝕜 := 𝕜), rangeProjector_inj, Matrix.mulVecLin_one,
    LinearMap.range_id, LinearMap.range_eq_top, Matrix.coe_mulVecLin]
  exact Matrix.mulVec_surjective_iff_isUnit.mpr hA

/-- Scaling by a nonzero scalar does not change the range projector. -/
theorem rangeProjector_smul [Fintype m] [Fintype n] {c : 𝕜} (hc : c ≠ 0) (A : Matrix m n 𝕜) :
    rangeProjector (c • A) = rangeProjector A := by
  rw [rangeProjector_inj]
  have h : (c • A).mulVecLin = c • A.mulVecLin :=
    LinearMap.ext fun x => Matrix.smul_mulVec c A x
  rw [h, LinearMap.range_smul _ _ hc]

/-- Right multiplication by an invertible matrix does not change the range projector. -/
theorem rangeProjector_mul_of_isUnit [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜)
    {B : Matrix n n 𝕜} (hB : IsUnit B) : rangeProjector (A * B) = rangeProjector A := by
  rw [rangeProjector_inj, Matrix.mulVecLin_mul]
  refine LinearMap.range_comp_of_range_eq_top _ ?_
  rw [LinearMap.range_eq_top, Matrix.coe_mulVecLin]
  exact Matrix.mulVec_surjective_iff_isUnit.mpr hB

/-- `A * Aᴴ` has the same range projector as `A`. -/
@[simp]
theorem rangeProjector_mul_conjTranspose_self [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    rangeProjector (A * Aᴴ) = rangeProjector A := by
  rw [rangeProjector_inj]
  refine Submodule.eq_of_le_of_finrank_eq ?_ (Matrix.rank_self_mul_conjTranspose A)
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- For `Q` with orthonormal columns, the range projector is `Q * Qᴴ`.
Port of `NLAlib.rangeProjector_eq_mul_conjTranspose_of_hasOrthonormalCols`. -/
theorem HasOrthonormalCols.rangeProjector_eq [Fintype m] [Fintype n] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : rangeProjector Q = Q * Qᴴ := by
  rw [← rangeProjector_mul_conjTranspose_self,
    hQ.isStarProjection_mul_conjTranspose.rangeProjector_eq]

/-- With full column rank, the range projector is `A * (Aᴴ * A)⁻¹ * Aᴴ`.
[GolubVanLoan2013, §5.3.1]; the hypothesis is taken as invertibility of the Gram matrix, which
`NLAlib.isUnit_conjTranspose_mul_self_iff` converts to and from injectivity of `A.mulVec`.
Port of `NLAlib.rangeProjector_eq_mul_inv_gram_conjTranspose`. -/
theorem rangeProjector_eq_mul_inv_mul_conjTranspose [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m n 𝕜} (hA : IsUnit (Aᴴ * A)) : rangeProjector A = A * (Aᴴ * A)⁻¹ * Aᴴ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hA
  have hfix : A * (Aᴴ * A)⁻¹ * Aᴴ * A = A := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  have hP : IsStarProjection (A * (Aᴴ * A)⁻¹ * Aᴴ) := by
    rw [Matrix.isStarProjection_iff]
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hfix]
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  refine (hP.eq_rangeProjector (le_antisymm ?_ ?_)).symm
  · rw [Matrix.mul_assoc]
    exact range_mulVecLin_le_iff_exists_mul.mpr ⟨_, rfl⟩
  · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨_, hfix.symm⟩

/-- The rank of the range projector of `A` is the rank of `A`.
Port of `NLAlib.rank_rangeProjector`. -/
@[simp]
theorem rank_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    (rangeProjector A).rank = A.rank := by
  rw [Matrix.rank, range_mulVecLin_rangeProjector, Matrix.rank]

/-! ### The complementary projector -/

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

/-! ### Bridge to Mathlib -/

/-- The range projector is the matrix of Mathlib's `Submodule.starProjection` onto the range of
`Matrix.toEuclideanLin A`. Port of `NLAlib.toEuclideanLin_rangeProjector`. -/
theorem toEuclideanLin_rangeProjector [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n 𝕜) :
    Matrix.toEuclideanLin (rangeProjector A) =
      ((LinearMap.range (Matrix.toEuclideanLin A)).starProjection : _ →ₗ[𝕜] _) := by
  have hS : LinearMap.range (Matrix.toEuclideanLin A) = euclideanRange A := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨A *ᵥ z.ofLp, ⟨z.ofLp, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨WithLp.toLp 2 z, rfl⟩
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanCLM_rangeProjector]
  simp only [hS]

end NLAlib
