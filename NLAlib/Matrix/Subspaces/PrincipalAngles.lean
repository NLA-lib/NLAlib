/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import NLAlib.Matrix.Subspaces.ProjectorPair

/-!
# Principal angles between subspaces

The principal angles between the column spaces of two matrices `X` and `Y` are
`NLAlib.principalAngle X Y k`, `k = 0, 1, …`, in non-decreasing order. Their cosines are the
singular values of the product of the two orthogonal projectors; for matrices `U`, `V` with
orthonormal columns these are the singular values of `Uᴴ * V`. The sines are the singular values
of `(1 - rangeProjector X) * rangeProjector Y`. The tangents are the singular values of the
tangent matrix, in `NLAlib.Matrix.Subspaces.Tangent`.

The angle depends only on the column spaces, so `X` and `Y` may be orthonormal frames, arbitrary
bases, or the projectors themselves. Beyond the smaller of the two dimensions the angle is `π / 2`.

Statements about distances between subspaces are made with the matrices, in a norm:
`specNorm ((1 - P) * Q)`, `frobNorm ((1 - P) * Q)`. This file identifies those norms with the
angles.

## Main definitions

* `NLAlib.principalAngle`: the `k`-th principal angle between two column spaces.

## Main results

* `NLAlib.cos_principalAngle`, `NLAlib.HasOrthonormalCols.cos_principalAngle`: cosines.
* `NLAlib.singularValues_one_sub_rangeProjector_mul_rangeProjector`: sines.
* `NLAlib.specNorm_one_sub_rangeProjector_mul_rangeProjector`,
  `NLAlib.specNorm_rangeProjector_sub_rangeProjector`: the largest angle as a distance.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p q r : Type*} [Fintype n] [Fintype p] [Fintype q] [Fintype r]

/-- The **`k`-th principal angle** between the column spaces of `X` and `Y`, `k = 0, 1, …`, in
non-decreasing order: the angle in `[0, π/2]` whose cosine is the `k`-th singular value of the
product of the two orthogonal projectors. For `k` at least the smaller of the two dimensions it
is `π / 2`.
[GolubVanLoan2013, §6.4.3]; [StewartSun1990, §I.5].
Port of `NLAlib.principalAnglesFintype`, there for two frames with the same number of columns. -/
noncomputable def principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) : ℝ :=
  Real.arccos (singularValues (rangeProjector X * rangeProjector Y) k)

/-! ### Basic properties -/

/-- The singular values of a product of two orthogonal projectors are at most one. -/
private theorem singularValues_rangeProjector_mul_rangeProjector_le_one (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) (k : ℕ) : singularValues (rangeProjector X * rangeProjector Y) k ≤ 1 :=
  (singularValues_le_specNorm _ k).trans
    (((isStarProjection_rangeProjector X).specNorm_mul_le _).trans
      (isStarProjection_rangeProjector Y).specNorm_le_one)

/-- Principal angles lie in `[0, π/2]`. Port of `NLAlib.principalAngles_mem_Icc`. -/
theorem principalAngle_mem_Icc (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X Y k ∈ Set.Icc 0 (Real.pi / 2) := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr (singularValues_nonneg _ k)⟩

/-- Principal angles are non-decreasing in the index.
Port of `NLAlib.principalAngles_monotone`. -/
theorem principalAngle_monotone (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) :
    Monotone (principalAngle X Y) := by
  exact fun i j hij => Real.antitone_arccos (singularValues_antitone _ hij)

/-- Principal angles are symmetric in the two subspaces. Port of `NLAlib.principalAngles_comm`. -/
theorem principalAngle_comm (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X Y k = principalAngle Y X k := by
  unfold principalAngle
  rw [← singularValues_conjTranspose, Matrix.conjTranspose_mul, conjTranspose_rangeProjector,
    conjTranspose_rangeProjector]

/-- Principal angles depend only on the column spaces.
Port of `NLAlib.principalAngles_eq_of_range_eq`. -/
theorem principalAngle_congr {X : Matrix n p 𝕜} {X' : Matrix n r 𝕜} {Y : Matrix n q 𝕜}
    {Y' : Matrix n r 𝕜} (hX : LinearMap.range X.mulVecLin = LinearMap.range X'.mulVecLin)
    (hY : LinearMap.range Y.mulVecLin = LinearMap.range Y'.mulVecLin) (k : ℕ) :
    principalAngle X Y k = principalAngle X' Y' k := by
  unfold principalAngle
  rw [rangeProjector_inj.mpr hX, rangeProjector_inj.mpr hY]

/-- The principal angles of a matrix and of its range projector agree. -/
@[simp]
theorem principalAngle_rangeProjector_left (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle (rangeProjector X) Y k = principalAngle X Y k := by
  unfold principalAngle
  rw [(isStarProjection_rangeProjector X).rangeProjector_eq]

/-- The principal angles of a matrix and of its range projector agree. -/
@[simp]
theorem principalAngle_rangeProjector_right (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X (rangeProjector Y) k = principalAngle X Y k := by
  unfold principalAngle
  rw [(isStarProjection_rangeProjector Y).rangeProjector_eq]

/-- Beyond the smaller of the two dimensions the principal angle is `π / 2`. -/
theorem principalAngle_of_rank_le {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜} {k : ℕ}
    (h : min X.rank Y.rank ≤ k) : principalAngle X Y k = Real.pi / 2 := by
  have hr : (rangeProjector X * rangeProjector Y).rank ≤ k := by
    have h1 := Matrix.rank_mul_le (rangeProjector X) (rangeProjector Y)
    rw [rank_rangeProjector, rank_rangeProjector] at h1
    exact h1.trans h
  unfold principalAngle
  rw [(singularValues_eq_zero_iff _).mpr hr, Real.arccos_zero]

/-- The principal angles between a subspace and itself vanish, up to its dimension. -/
theorem principalAngle_self (X : Matrix n p 𝕜) {k : ℕ} (hk : k < X.rank) :
    principalAngle X X k = 0 := by
  unfold principalAngle
  rw [rangeProjector_mul_rangeProjector,
    (isStarProjection_rangeProjector X).singularValues_of_lt_rank (by rwa [rank_rangeProjector]),
    Real.arccos_one]

/-- If the column space of `Y` is inside that of `X`, the principal angles vanish up to the
dimension of the smaller space. Port of `NLAlib.directedSubspaceGap_eq_zero_of_range_le`. -/
theorem principalAngle_eq_zero_of_range_le {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range X.mulVecLin) {k : ℕ} (hk : k < Y.rank) :
    principalAngle X Y k = 0 := by
  have h0 := principalAngle_self Y hk
  unfold principalAngle at h0 ⊢
  rwa [rangeProjector_mul_rangeProjector_of_range_le h, ← rangeProjector_mul_rangeProjector Y]

/-! ### Cosines -/

/-- The cosines of the principal angles are the singular values of the product of the two
projectors. -/
theorem cos_principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.cos (principalAngle X Y k) =
      singularValues (rangeProjector X * rangeProjector Y) k := by
  exact Real.cos_arccos
    (by linarith [singularValues_nonneg (rangeProjector X * rangeProjector Y) k])
    (singularValues_rangeProjector_mul_rangeProjector_le_one X Y k)

/-- **Cosines for orthonormal frames**: the singular values of `Uᴴ * V`.
[GolubVanLoan2013, §6.4.3]. Port of `NLAlib.cos_principalAngles`.
Result: principal-angles -/
theorem HasOrthonormalCols.cos_principalAngle [DecidableEq p] [DecidableEq q]
    {U : Matrix n p 𝕜} {V : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (k : ℕ) :
    Real.cos (principalAngle U V k) = singularValues (Uᴴ * V) k := by
  rw [NLAlib.cos_principalAngle, hU.rangeProjector_eq, hV.rangeProjector_eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc Uᴴ, hU.singularValues_mul_left, hV.singularValues_mul_conjTranspose_right]

/-- Cosines when only the first frame is orthonormal: the singular values of
`Uᴴ * rangeProjector Y`. -/
theorem HasOrthonormalCols.cos_principalAngle_left [DecidableEq p] {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.cos (principalAngle U Y k) = singularValues (Uᴴ * rangeProjector Y) k := by
  rw [NLAlib.cos_principalAngle, hU.rangeProjector_eq, Matrix.mul_assoc,
    hU.singularValues_mul_left]

/-! ### Sines -/

/-- The sine of a principal angle from its cosine. Port of `NLAlib.sin_principalAngles`. -/
theorem sin_principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.sin (principalAngle X Y k) =
      √(1 - singularValues (rangeProjector X * rangeProjector Y) k ^ 2) := by
  exact Real.sin_arccos _

variable [DecidableEq n]

/-- **Sines of the principal angles**: the singular values of
`(1 - rangeProjector X) * rangeProjector Y`, in reverse order:
`σ_i = sin θ_j` for `i + j + 1 = rank Y`.
[GolubVanLoan2013, §2.5.3]; [StewartSun1990, Theorem I.5.5].
Result: principal-angles -/
theorem singularValues_one_sub_rangeProjector_mul_rangeProjector (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) {i j : ℕ} (hij : i + j + 1 = Y.rank) :
    singularValues ((1 - rangeProjector X) * rangeProjector Y) i =
      Real.sin (principalAngle X Y j) := by
  have h := (isStarProjection_rangeProjector Y).sq_singularValues_one_sub_mul
    (isStarProjection_rangeProjector X) (i := i) (j := j) (by rw [rank_rangeProjector, hij])
  rw [sin_principalAngle, ← h, Real.sqrt_sq (singularValues_nonneg _ _)]

/-- Sines for orthonormal frames: the singular values of `(1 - U * Uᴴ) * V`, in reverse order.
Port of `NLAlib.transpose_sinePrincipalAngles_mul_self` and
`NLAlib.specNorm_sinePrincipalAngles_eq_residual`. -/
theorem HasOrthonormalCols.singularValues_one_sub_mul_conjTranspose_mul [DecidableEq p]
    [DecidableEq q]
    {U : Matrix n p 𝕜} {V : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) {i j : ℕ} (hij : i + j + 1 = Fintype.card q) :
    singularValues ((1 - U * Uᴴ) * V) i = Real.sin (principalAngle U V j) := by
  rw [← singularValues_one_sub_rangeProjector_mul_rangeProjector U V (by rw [hV.rank_eq, hij]),
    hU.rangeProjector_eq, hV.rangeProjector_eq, ← Matrix.mul_assoc,
    hV.singularValues_mul_conjTranspose_right]

/-- **The largest principal angle as a distance**: `‖(1 - P_X) P_Y‖₂` is the sine of the largest
principal angle counted up to the dimension of the column space of `Y`.
[GolubVanLoan2013, §2.5.3]. Port of `NLAlib.directedSubspaceGap_eq_sin_principalAngles`.
Result: principal-angles -/
theorem specNorm_one_sub_rangeProjector_mul_rangeProjector (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜)
    {j : ℕ} (hj : j + 1 = Y.rank) :
    specNorm ((1 - rangeProjector X) * rangeProjector Y) = Real.sin (principalAngle X Y j) := by
  rw [← singularValues_zero_eq_specNorm]
  exact singularValues_one_sub_rangeProjector_mul_rangeProjector X Y (by omega)

/-- The Frobenius norm of `(1 - P_X) P_Y` is the root sum of squares of the sines of the
principal angles. Port of `NLAlib.frobNorm_sinePrincipalAngles_eq_residual`. -/
theorem frobNorm_one_sub_rangeProjector_mul_rangeProjector_sq (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) :
    frobNorm ((1 - rangeProjector X) * rangeProjector Y) ^ 2 =
      ∑ j ∈ Finset.range Y.rank, Real.sin (principalAngle X Y j) ^ 2 := by
  have hr : ((1 - rangeProjector X) * rangeProjector Y).rank ≤ Y.rank :=
    (Matrix.rank_mul_le_right _ _).trans (rank_rangeProjector Y).le
  rw [frobNorm_sq_eq_sum_range_singularValues_sq _ hr, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [singularValues_one_sub_rangeProjector_mul_rangeProjector X Y (j := j) (by omega)]

omit [DecidableEq n] in
/-- **The distance between two projectors of equal rank** is the sine of the largest principal
angle. [GolubVanLoan2013, §2.5.3].
Port of `NLAlib.specNorm_sinePrincipalAngles_eq_projector_distance`.
Result: projector-gap -/
theorem specNorm_rangeProjector_sub_rangeProjector {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : X.rank = Y.rank) {j : ℕ} (hj : j + 1 = Y.rank) :
    specNorm (rangeProjector X - rangeProjector Y) = Real.sin (principalAngle X Y j) := by
  classical
  rw [specNorm_sub_comm, (isStarProjection_rangeProjector Y).specNorm_sub_eq_of_rank_eq
    (isStarProjection_rangeProjector X) (by rw [rank_rangeProjector, rank_rangeProjector, h]),
    specNorm_one_sub_rangeProjector_mul_rangeProjector X Y hj]

omit [DecidableEq n] in
/-- For two subspaces of equal dimension,
`‖P_X - P_Y‖_F² = 2 ∑ sin² θ_j`.
Port of `NLAlib.frobSq_projector_distance_eq_two_mul_sinePrincipalAngles`. -/
theorem frobNorm_rangeProjector_sub_rangeProjector_sq {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : X.rank = Y.rank) :
    frobNorm (rangeProjector X - rangeProjector Y) ^ 2 =
      2 * ∑ j ∈ Finset.range Y.rank, Real.sin (principalAngle X Y j) ^ 2 := by
  classical
  rw [frobNorm_sub_comm, (isStarProjection_rangeProjector Y).frobNorm_sub_sq_of_rank_eq
    (isStarProjection_rangeProjector X) (by rw [rank_rangeProjector, rank_rangeProjector, h]),
    frobNorm_one_sub_rangeProjector_mul_rangeProjector_sq]

end NLAlib
