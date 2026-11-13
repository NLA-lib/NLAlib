/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Order
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Hermitian
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.Matrix.Basic.Orthonormal

/-!
# Orthogonal projectors

An orthogonal projector is a matrix $\mathbf{P}$ with `IsStarProjection P` (Mathlib: idempotent
and self-adjoint). `NLAlib.rangeProjector A`, written $\mathbf{P}_{\mathbf{A}}$, is the orthogonal
projector onto the column space `LinearMap.range A.mulVecLin` of an arbitrary matrix $\mathbf{A}$,
of any shape and rank. It depends only on that range.

The projection residual of $\mathbf{A}$ with respect to $\mathbf{Y}$ has no definition; it is
always written $(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}$, in Lean
`(1 - rangeProjector Y) * A`. The complementary projector
$\mathbf{I} - \mathbf{P}_{\mathbf{A}}$ is treated in `NLAlib.Matrix.Basic.ComplementaryProjector`.

## Main definitions

* `NLAlib.rangeProjector`: the orthogonal projector onto the column space of a matrix.

## Main results

* `NLAlib.isStarProjection_rangeProjector`, `NLAlib.rangeProjector_mul_self`,
  `NLAlib.range_rangeProjector`: the characterising properties.
* `IsStarProjection.eq_rangeProjector`: uniqueness.
* `NLAlib.rangeProjector_mul_eq_self_iff`: $\mathbf{P}_{\mathbf{B}}\mathbf{Y} = \mathbf{Y}$ iff
  the range of $\mathbf{Y}$ is inside the range of $\mathbf{B}$.
* `NLAlib.HasOrthonormalCols.rangeProjector_eq`: for $\mathbf{Q}$ with orthonormal columns the
  projector is $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$;
  `NLAlib.rangeProjector_eq_mul_conjTranspose_of_mul_conjTranspose_mul_self`, the same for a
  partial isometry.
* `NLAlib.HasOrthonormalCols.rangeProjector_mul`: equivariance,
  $\mathbf{P}_{\mathbf{Q}\mathbf{X}} = \mathbf{Q}\mathbf{P}_{\mathbf{X}}\mathbf{Q}^{\mathsf{H}}$.
* `NLAlib.rangeProjector_eq_mul_inv_mul_conjTranspose`: the full-column-rank formula.
* `NLAlib.toEuclideanLin_rangeProjector`: the bridge to Mathlib's `Submodule.starProjection`.
* `NLAlib.forall_mem_range_star_dotProduct_eq_zero_iff`: orthogonality to a column space as
  $\mathbf{X}^{\mathsf{H}}\mathbf{w} = \mathbf{0}$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*}

/-! ### Star projections of matrices -/

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

/-- A star projection is positive semidefinite. Applied to `hP.one_sub`, this gives
$\mathbf{P} \preceq \mathbf{I}$ in the Loewner order. -/
theorem _root_.IsStarProjection.posSemidef [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hP.conjTranspose_eq, hP.mul_self] at h

/-- A star projection fixes exactly the matrices whose columns lie in its range:
$\mathbf{P}\mathbf{A} = \mathbf{A}$ iff the column space of $\mathbf{A}$ is inside the range of
$\mathbf{P}$. -/
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

/-- **Pythagoras** for a star projection:
$\|\mathbf{x}\|^2 = \|\mathbf{P}\mathbf{x}\|^2 + \|(\mathbf{I} - \mathbf{P})\mathbf{x}\|^2$.
[TrefethenBau1997, Lecture 6]. -/
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

/-- A star projection does not increase the Euclidean norm of a vector:
$\|\mathbf{P}\mathbf{x}\| \le \|\mathbf{x}\|$. -/
theorem _root_.IsStarProjection.norm_toLp_mulVec_le [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (x : m → 𝕜) : ‖WithLp.toLp 2 (P *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  classical
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [hP.norm_toLp_sq_eq_add x]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- For $\mathbf{Q}$ with orthonormal columns, $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ is a star
projection. -/
theorem HasOrthonormalCols.isStarProjection_mul_conjTranspose [Fintype m] [Fintype n]
    [DecidableEq n] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    IsStarProjection (Q * Qᴴ) := by
  rw [Matrix.isStarProjection_iff]
  exact ⟨by rw [Matrix.mul_assoc, hQ.conjTranspose_mul_cancel_left],
    Matrix.isHermitian_mul_conjTranspose_self Q⟩

/-! ### The range projector -/

open Classical in
/-- The **orthogonal projector onto the column space** of $\mathbf{A}$, written
$\mathbf{P}_{\mathbf{A}}$: the matrix of the orthogonal projection of `EuclideanSpace 𝕜 m` onto
`LinearMap.range A.mulVecLin`. Defined for every matrix, including rank-deficient and empty ones,
and equal to $\mathbf{0}$ for $\mathbf{A} = \mathbf{0}$. It depends only on the range of
$\mathbf{A}$ (`NLAlib.rangeProjector_inj`); for $\mathbf{Q}$ with orthonormal columns it is
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ (`NLAlib.HasOrthonormalCols.rangeProjector_eq`).
[GolubVanLoan2013, §2.5.1]. -/
noncomputable def rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) : Matrix m m 𝕜 :=
  LinearMap.toMatrix' <|
    (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).toLinearMap ∘ₗ
      ((LinearMap.range A.mulVecLin).map
        (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap).starProjection.toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap

/-- The column space of $\mathbf{A}$ as a subspace of `EuclideanSpace 𝕜 m`. -/
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

/-- The range projector is a star projection: idempotent and Hermitian. -/
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

/-- The range of $\mathbf{P}_{\mathbf{A}}$ is the column space of $\mathbf{A}$. -/
theorem range_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    LinearMap.range (rangeProjector A).mulVecLin = LinearMap.range A.mulVecLin := by
  ext x
  rw [← (isStarProjection_rangeProjector A).mulVec_eq_self_iff,
    rangeProjector_mulVec_eq_self_iff_aux]

/-- The range projector of $\mathbf{A}$ fixes $\mathbf{A}$:
$\mathbf{P}_{\mathbf{A}}\mathbf{A} = \mathbf{A}$. -/
@[simp]
theorem rangeProjector_mul_self [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    rangeProjector A * A = A :=
  (isStarProjection_rangeProjector A).mul_eq_self_iff.mpr (range_rangeProjector A).ge

/-- $\mathbf{A}^{\mathsf{H}}\mathbf{P}_{\mathbf{A}} = \mathbf{A}^{\mathsf{H}}$. -/
@[simp]
theorem conjTranspose_mul_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    Aᴴ * rangeProjector A = Aᴴ := by
  have h := congrArg Matrix.conjTranspose (rangeProjector_mul_self A)
  rwa [Matrix.conjTranspose_mul, conjTranspose_rangeProjector] at h

/-- The range projector of $\mathbf{A}$ fixes $\mathbf{A}\mathbf{y}$:
$\mathbf{P}_{\mathbf{A}}(\mathbf{A}\mathbf{y}) = \mathbf{A}\mathbf{y}$. -/
theorem rangeProjector_mulVec_mulVec [Fintype m] [Fintype n] (A : Matrix m n 𝕜) (y : n → 𝕜) :
    rangeProjector A *ᵥ (A *ᵥ y) = A *ᵥ y := by
  rw [Matrix.mulVec_mulVec, rangeProjector_mul_self]

/-- The range projector of $\mathbf{B}$ fixes exactly the vectors in the column space of
$\mathbf{B}$. -/
theorem rangeProjector_mulVec_eq_self_iff [Fintype m] [Fintype n] {B : Matrix m n 𝕜}
    {x : m → 𝕜} : rangeProjector B *ᵥ x = x ↔ x ∈ LinearMap.range B.mulVecLin :=
  rangeProjector_mulVec_eq_self_iff_aux

/-- $\mathbf{P}_{\mathbf{B}}\mathbf{Y} = \mathbf{Y}$ exactly when the column space of
$\mathbf{Y}$ is contained in that of $\mathbf{B}$. -/
theorem rangeProjector_mul_eq_self_iff [Fintype m] [Fintype n] [Fintype p] {B : Matrix m n 𝕜}
    {Y : Matrix m p 𝕜} :
    rangeProjector B * Y = Y ↔ LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin := by
  rw [(isStarProjection_rangeProjector B).mul_eq_self_iff, range_rangeProjector]

/-- The column space of $\mathbf{Y}$ is contained in that of $\mathbf{B}$ exactly when
$\mathbf{Y} = \mathbf{B}\mathbf{C}$ for some $\mathbf{C}$. -/
theorem range_le_iff_exists_mul [Fintype n] [Fintype p] {B : Matrix m n 𝕜}
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

/-- Equal column spaces stay equal under a left factor: if $\mathbf{X}$ and $\mathbf{Y}$ have the
same column space, so do $\mathbf{A}\mathbf{X}$ and $\mathbf{A}\mathbf{Y}$. -/
theorem range_mul_eq_of_range_eq {q : Type*} [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n 𝕜) {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : LinearMap.range X.mulVecLin = LinearMap.range Y.mulVecLin) :
    LinearMap.range (A * X).mulVecLin = LinearMap.range (A * Y).mulVecLin := by
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_comp, h]

private theorem exists_rangeProjector_eq_mul [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    ∃ C : Matrix n m 𝕜, rangeProjector A = A * C :=
  range_le_iff_exists_mul.mp (range_rangeProjector A).le

/-- $\mathbf{P}_{\mathbf{B}}\mathbf{Y} = \mathbf{0}$ exactly when the columns of $\mathbf{Y}$
are orthogonal to those of $\mathbf{B}$, $\mathbf{B}^{\mathsf{H}}\mathbf{Y} = \mathbf{0}$. -/
theorem rangeProjector_mul_eq_zero_iff [Fintype m] [Fintype n] {B : Matrix m n 𝕜}
    {Y : Matrix m p 𝕜} : rangeProjector B * Y = 0 ↔ Bᴴ * Y = 0 := by
  constructor
  · intro h
    rw [← conjTranspose_mul_rangeProjector, Matrix.mul_assoc, h, Matrix.mul_zero]
  · intro h
    obtain ⟨C, hC⟩ := exists_rangeProjector_eq_mul B
    rw [← conjTranspose_rangeProjector, hC, Matrix.conjTranspose_mul, Matrix.mul_assoc, h,
      Matrix.mul_zero]

/-- $\mathbf{P}_{\mathbf{B}}\mathbf{x} = \mathbf{0}$ exactly when $\mathbf{x}$ is orthogonal to
the columns of $\mathbf{B}$, $\mathbf{B}^{\mathsf{H}}\mathbf{x} = \mathbf{0}$. This is the vector
form of `NLAlib.rangeProjector_mul_eq_zero_iff`. -/
theorem rangeProjector_mulVec_eq_zero_iff [Fintype m] [Fintype n] {B : Matrix m n 𝕜}
    {x : m → 𝕜} : rangeProjector B *ᵥ x = 0 ↔ Bᴴ *ᵥ x = 0 := by
  constructor
  · intro h
    rw [← conjTranspose_mul_rangeProjector, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h
    obtain ⟨C, hC⟩ := exists_rangeProjector_eq_mul B
    rw [← conjTranspose_rangeProjector, hC, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]

/-- Orthogonality to a column space: a vector $\mathbf{w}$ is orthogonal to every vector of
the column space of $\mathbf{X}$ exactly when $\mathbf{X}^{\mathsf{H}}\mathbf{w} = \mathbf{0}$.
Statements take the right-hand side; this bridge turns it into the quantified form and back. -/
theorem forall_mem_range_star_dotProduct_eq_zero_iff [Fintype m] [Fintype n] {X : Matrix m n 𝕜}
    {w : m → 𝕜} :
    (∀ v ∈ LinearMap.range X.mulVecLin, star v ⬝ᵥ w = 0) ↔ Xᴴ *ᵥ w = 0 := by
  have key : ∀ c : n → 𝕜, star (X *ᵥ c) ⬝ᵥ w = star c ⬝ᵥ (Xᴴ *ᵥ w) := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  constructor
  · intro h
    have h0 := h (X *ᵥ (Xᴴ *ᵥ w)) (LinearMap.mem_range.mpr ⟨_, rfl⟩)
    rw [key] at h0
    exact dotProduct_star_self_eq_zero.mp h0
  · rintro h v ⟨c, rfl⟩
    rw [Matrix.mulVecLin_apply, key, h, dotProduct_zero]

/-- A star projection with the same range as $\mathbf{A}$ is $\mathbf{P}_{\mathbf{A}}$. -/
theorem _root_.IsStarProjection.eq_rangeProjector [Fintype m] [Fintype n] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {A : Matrix m n 𝕜}
    (h : LinearMap.range P.mulVecLin = LinearMap.range A.mulVecLin) : P = rangeProjector A :=
  hP.eq_of_range_eq (isStarProjection_rangeProjector A)
    (h.trans (range_rangeProjector A).symm)

/-- The range projector of a star projection is the projection itself. -/
theorem _root_.IsStarProjection.rangeProjector_eq [Fintype m] {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) : rangeProjector P = P :=
  (hP.eq_rangeProjector rfl).symm

/-- The range projector depends only on the column space:
$\mathbf{P}_{\mathbf{A}} = \mathbf{P}_{\mathbf{B}}$ iff $\mathbf{A}$ and $\mathbf{B}$ have the same
column space. -/
theorem rangeProjector_inj [Fintype m] [Fintype n] [Fintype p] {A : Matrix m n 𝕜}
    {B : Matrix m p 𝕜} :
    rangeProjector A = rangeProjector B ↔
      LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin := by
  constructor
  · intro h
    rw [← range_rangeProjector A, h, range_rangeProjector]
  · intro h
    exact (isStarProjection_rangeProjector A).eq_rangeProjector
      ((range_rangeProjector A).trans h)

/-- If the column space of $\mathbf{Y}$ is inside that of $\mathbf{B}$, projecting onto
$\mathbf{B}$ after $\mathbf{Y}$ is projecting onto $\mathbf{Y}$:
$\mathbf{P}_{\mathbf{B}}\mathbf{P}_{\mathbf{Y}} = \mathbf{P}_{\mathbf{Y}}$. -/
theorem rangeProjector_mul_rangeProjector_of_range_le [Fintype m] [Fintype n] [Fintype p]
    {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector B * rangeProjector Y = rangeProjector Y := by
  rw [rangeProjector_mul_eq_self_iff, range_rangeProjector]
  exact h

/-- If the column space of $\mathbf{Y}$ is inside that of $\mathbf{B}$, projecting onto
$\mathbf{Y}$ after $\mathbf{B}$ is projecting onto $\mathbf{Y}$:
$\mathbf{P}_{\mathbf{Y}}\mathbf{P}_{\mathbf{B}} = \mathbf{P}_{\mathbf{Y}}$. -/
theorem rangeProjector_mul_rangeProjector_of_range_le' [Fintype m] [Fintype n] [Fintype p]
    {B : Matrix m n 𝕜} {Y : Matrix m p 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector Y * rangeProjector B = rangeProjector Y := by
  have h' := congrArg Matrix.conjTranspose (rangeProjector_mul_rangeProjector_of_range_le h)
  rwa [Matrix.conjTranspose_mul, conjTranspose_rangeProjector, conjTranspose_rangeProjector]
    at h'

/-- The range projector is monotone: a smaller column space gives a smaller projector in the
Loewner order, $\mathbf{P}_{\mathbf{Y}} \preceq \mathbf{P}_{\mathbf{B}}$ when the column space of
$\mathbf{Y}$ is inside that of $\mathbf{B}$. -/
theorem rangeProjector_mono [Fintype m] [Fintype n] [Fintype p] {B : Matrix m n 𝕜}
    {Y : Matrix m p 𝕜} (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) :
    rangeProjector Y ≤ rangeProjector B := by
  rw [Matrix.le_iff]
  exact ((isStarProjection_rangeProjector Y).sub_of_mul_eq_right
    (isStarProjection_rangeProjector B)
    (rangeProjector_mul_rangeProjector_of_range_le h)).posSemidef

/-! ### Special cases -/

/-- The range projector of the zero matrix is zero, for every shape. -/
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

/-- $\mathbf{A}\mathbf{A}^{\mathsf{H}}$ has the same range projector as $\mathbf{A}$. -/
@[simp]
theorem rangeProjector_mul_conjTranspose_self [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    rangeProjector (A * Aᴴ) = rangeProjector A := by
  rw [rangeProjector_inj]
  refine Submodule.eq_of_le_of_finrank_eq ?_ (Matrix.rank_self_mul_conjTranspose A)
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/-- For $\mathbf{Q}$ with orthonormal columns,
$\mathbf{P}_{\mathbf{Q}} = \mathbf{Q}\mathbf{Q}^{\mathsf{H}}$. -/
theorem HasOrthonormalCols.rangeProjector_eq [Fintype m] [Fintype n] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : rangeProjector Q = Q * Qᴴ := by
  rw [← rangeProjector_mul_conjTranspose_self,
    hQ.isStarProjection_mul_conjTranspose.rangeProjector_eq]

/-- The projector of a partial isometry: for $\mathbf{Q}$ with
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{Q}$ (orthonormal columns, possibly with
some zero columns), $\mathbf{P}_{\mathbf{Q}} = \mathbf{Q}\mathbf{Q}^{\mathsf{H}}$.
Generalises `NLAlib.HasOrthonormalCols.rangeProjector_eq`. -/
theorem rangeProjector_eq_mul_conjTranspose_of_mul_conjTranspose_mul_self [Fintype m]
    [Fintype n] {Q : Matrix m n 𝕜} (hQ : Q * Qᴴ * Q = Q) : rangeProjector Q = Q * Qᴴ := by
  refine (IsStarProjection.eq_rangeProjector (Matrix.isStarProjection_iff.mpr ⟨?_, ?_⟩) ?_).symm
  · rw [← Matrix.mul_assoc, hQ]
  · exact Matrix.isHermitian_mul_conjTranspose_self _
  · refine le_antisymm ?_ ?_
    · rw [Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _
    · conv_lhs => rw [← hQ, Matrix.mulVecLin_mul]
      exact LinearMap.range_comp_le_range _ _

/-- The projector onto the column space of $\mathbf{Q}\mathbf{X}$, for $\mathbf{Q}$ with
orthonormal columns:
$\mathbf{P}_{\mathbf{Q}\mathbf{X}} = \mathbf{Q}\mathbf{P}_{\mathbf{X}}\mathbf{Q}^{\mathsf{H}}$,
the equivariance of the range projector under an isometry of the ambient space. -/
theorem HasOrthonormalCols.rangeProjector_mul [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) (X : Matrix n p 𝕜) :
    rangeProjector (Q * X) = Q * rangeProjector X * Qᴴ := by
  have hP := isStarProjection_rangeProjector X
  obtain ⟨C, hC⟩ := range_le_iff_exists_mul.mp (range_rangeProjector X).le
  refine (IsStarProjection.eq_rangeProjector (Matrix.isStarProjection_iff.mpr ⟨?_, ?_⟩)
    (le_antisymm ?_ ?_)).symm
  · rw [Matrix.mul_assoc (Q * rangeProjector X), ← Matrix.mul_assoc Qᴴ,
      hQ.conjTranspose_mul_cancel_left, ← Matrix.mul_assoc, Matrix.mul_assoc Q, hP.mul_self]
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP.conjTranspose_eq, Matrix.mul_assoc]
  · refine range_le_iff_exists_mul.mpr ⟨C * Qᴴ, ?_⟩
    rw [hC]
    simp only [Matrix.mul_assoc]
  · refine range_le_iff_exists_mul.mpr ⟨Q * X, ?_⟩
    rw [Matrix.mul_assoc, hQ.conjTranspose_mul_cancel_left, Matrix.mul_assoc,
      rangeProjector_mul_self]

/-- With full column rank, the range projector is
$\mathbf{P}_{\mathbf{A}} =
\mathbf{A}(\mathbf{A}^{\mathsf{H}}\mathbf{A})^{-1}\mathbf{A}^{\mathsf{H}}$.
[GolubVanLoan2013, §5.3.1]; the hypothesis is taken as invertibility of the Gram matrix
$\mathbf{A}^{\mathsf{H}}\mathbf{A}$, which `NLAlib.isUnit_conjTranspose_mul_self_iff` converts to
and from injectivity of $\mathbf{x} \mapsto \mathbf{A}\mathbf{x}$. -/
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
    exact range_le_iff_exists_mul.mpr ⟨_, rfl⟩
  · exact range_le_iff_exists_mul.mpr ⟨_, hfix.symm⟩

/-- $\operatorname{rank} \mathbf{P}_{\mathbf{A}} = \operatorname{rank} \mathbf{A}$. -/
@[simp]
theorem rank_rangeProjector [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    (rangeProjector A).rank = A.rank := by
  rw [Matrix.rank, range_rangeProjector, Matrix.rank]

/-! ### Bridge to Mathlib -/

/-- The range projector is the matrix of Mathlib's `Submodule.starProjection` onto the range of
`Matrix.toEuclideanLin A`. -/
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

/-- The squared norm of the `j`-th column of a real star projection is its `(j, j)` entry. -/
theorem _root_.IsStarProjection.norm_toLp_mulVec_single_sq {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : IsStarProjection P) (j : n) :
    ‖WithLp.toLp 2 (P *ᵥ Pi.single j 1)‖ ^ 2 = P j j := by
  have h := congrFun (congrFun hP.mul_self j) j
  rw [Matrix.mul_apply] at h
  rw [EuclideanSpace.norm_sq_eq, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Real.norm_eq_abs, sq_abs]
  have hsymm : P j i = P i j := by
    simpa only [star_trivial] using hP.isHermitian.apply i j
  rw [hsymm]
  ring


/-- Head mass of a projector: if every column $\mathbf{P}\mathbf{e}_a$ ($a$ in the head)
has head mass at most $c$ times its norm, then
$\sum_a \|\mathbf{P}\mathbf{e}_a\|^2 \le c\,\lvert\kappa\rvert$. -/
theorem _root_.IsStarProjection.sum_head_mass_sq_le {κ r : Type*} [Fintype κ] [Fintype r]
    {P : Matrix (κ ⊕ r) (κ ⊕ r) ℝ} (hP : IsStarProjection P) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a : κ, ∑ b : κ, P (Sum.inl b) (Sum.inl a) ^ 2 ≤ c * ∑ i, P i (Sum.inl a) ^ 2) :
    ∑ a : κ, ∑ i, P i (Sum.inl a) ^ 2 ≤ c * Fintype.card κ := by
  have hsymm : ∀ i j, P j i = P i j := fun i j => by
    have h := congrFun (congrFun hP.conjTranspose_eq j) i
    have h' : P i j = P j i := by simpa [Matrix.conjTranspose_apply] using h
    exact h'.symm
  have hdiag : ∀ a : κ, ∑ i, P i (Sum.inl a) ^ 2 = P (Sum.inl a) (Sum.inl a) := by
    intro a
    have key : ∀ i, P (Sum.inl a) i = P i (Sum.inl a) := fun i => (hsymm (Sum.inl a) i).symm
    have h := congrFun (congrFun hP.mul_self (Sum.inl a)) (Sum.inl a)
    rw [Matrix.mul_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i, sq]
  have hT : ∑ a : κ, ∑ i, P i (Sum.inl a) ^ 2 = ∑ a : κ, P (Sum.inl a) (Sum.inl a) :=
    Finset.sum_congr rfl fun a _ => hdiag a
  have hS2 : ∑ a : κ, ∑ b : κ, P (Sum.inl b) (Sum.inl a) ^ 2
      ≤ c * ∑ a : κ, ∑ i, P i (Sum.inl a) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => h a
  have hsq : ∑ a : κ, P (Sum.inl a) (Sum.inl a) ^ 2
      ≤ ∑ a : κ, ∑ b : κ, P (Sum.inl b) (Sum.inl a) ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.single_le_sum (f := fun b : κ =>
      P (Sum.inl b) (Sum.inl a) ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have hCS : (∑ a : κ, P (Sum.inl a) (Sum.inl a)) ^ 2
      ≤ Fintype.card κ * ∑ a : κ, ∑ b : κ, P (Sum.inl b) (Sum.inl a) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun a : κ => P (Sum.inl a) (Sum.inl a))
    simp only [Finset.card_univ] at this
    exact this.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
  rw [← hT] at hCS
  have hT0 : 0 ≤ ∑ a : κ, ∑ i, P i (Sum.inl a) ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hk : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  rcases hT0.eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hc hk
  · nlinarith [mul_le_mul_of_nonneg_left hS2 hk]


end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*}
  [Fintype n] [Fintype r] [DecidableEq r]
/-- For an orthonormal frame, the range projector of a diagonal matrix times its adjoint
is the diagonal indicator of the nonzero diagonal entries. No printed source. -/
theorem HasOrthonormalCols.rangeProjector_diagonal_mul_conjTranspose
    {V : Matrix n r 𝕜} (hV : HasOrthonormalCols V) (d : r → 𝕜) :
    rangeProjector (Matrix.diagonal d * Vᴴ) =
      Matrix.diagonal (fun i => if d i = 0 then 0 else 1) := by
  set e : r → 𝕜 := fun i => if d i = 0 then 0 else 1
  have hed : Matrix.diagonal e * Matrix.diagonal d = Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [e, hi]
  have hdd : Matrix.diagonal d * Matrix.diagonal d⁻¹ = Matrix.diagonal e := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : d i = 0 <;> simp [e, hi]
  have hP : IsStarProjection (Matrix.diagonal e) := by
    rw [Matrix.isStarProjection_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases hi : d i = 0 <;> simp [e, hi]
    · exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by
        ext i; simp [e])
  rw [← hP.rangeProjector_eq, rangeProjector_inj]
  refine le_antisymm (range_le_iff_exists_mul.mpr ⟨Matrix.diagonal d * Vᴴ, ?_⟩)
    (range_le_iff_exists_mul.mpr ⟨V * Matrix.diagonal d⁻¹, ?_⟩)
  · rw [← Matrix.mul_assoc, hed]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV.conjTranspose_mul_self, Matrix.one_mul, hdd]

end NLAlib
