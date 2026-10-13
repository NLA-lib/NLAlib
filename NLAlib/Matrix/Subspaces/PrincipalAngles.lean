/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import NLAlib.Matrix.Subspaces.ProjectorPair
public import NLAlib.Matrix.Spectral.SVD

/-!
# Principal angles between subspaces

The principal angles between the column spaces of two matrices `X` and `Y` are
`NLAlib.principalAngle X Y k`, `k = 0, 1, …`, in non-decreasing order. Their cosines are the
singular values of the product of the two orthogonal projectors; for matrices `U`, `V` with
orthonormal columns these are the singular values of `Uᴴ * V`. The sines are the singular values
of `(1 - rangeProjector X) * rangeProjector Y`, and in the acute case the tangents are the
singular values of `(1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹`.

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
* `NLAlib.HasOrthonormalCols.singularValues_one_sub_mul_mul_inv`: tangents.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p q r : Type*} [Fintype n] [Fintype p] [Fintype q] [Fintype r]
  [DecidableEq n] [DecidableEq p]

/-- The **`k`-th principal angle** between the column spaces of `X` and `Y`, `k = 0, 1, …`, in
non-decreasing order: the angle in `[0, π/2]` whose cosine is the `k`-th singular value of the
product of the two orthogonal projectors. For `k` at least the smaller of the two dimensions it
is `π / 2`.
[GolubVanLoan2013, §6.4.3]; [StewartSun1990, §I.5].
Port of `NLAlib.principalAnglesFintype`, there for two frames with the same number of columns. -/
noncomputable def principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) : ℝ :=
  Real.arccos (singularValues (rangeProjector X * rangeProjector Y) k)

/-! ### Basic properties -/

/-- Principal angles lie in `[0, π/2]`. Port of `NLAlib.principalAngles_mem_Icc`. -/
theorem principalAngle_mem_Icc (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X Y k ∈ Set.Icc 0 (Real.pi / 2) := by
  sorry

/-- Principal angles are non-decreasing in the index.
Port of `NLAlib.principalAngles_monotone`. -/
theorem principalAngle_monotone (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) :
    Monotone (principalAngle X Y) := by
  sorry

/-- Principal angles are symmetric in the two subspaces. Port of `NLAlib.principalAngles_comm`. -/
theorem principalAngle_comm (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X Y k = principalAngle Y X k := by
  sorry

/-- Principal angles depend only on the column spaces.
Port of `NLAlib.principalAngles_eq_of_range_eq`. -/
theorem principalAngle_congr {X : Matrix n p 𝕜} {X' : Matrix n r 𝕜} {Y : Matrix n q 𝕜}
    {Y' : Matrix n r 𝕜} (hX : LinearMap.range X.mulVecLin = LinearMap.range X'.mulVecLin)
    (hY : LinearMap.range Y.mulVecLin = LinearMap.range Y'.mulVecLin) (k : ℕ) :
    principalAngle X Y k = principalAngle X' Y' k := by
  sorry

/-- The principal angles of a matrix and of its range projector agree. -/
@[simp]
theorem principalAngle_rangeProjector_left (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle (rangeProjector X) Y k = principalAngle X Y k := by
  sorry

/-- The principal angles of a matrix and of its range projector agree. -/
@[simp]
theorem principalAngle_rangeProjector_right (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    principalAngle X (rangeProjector Y) k = principalAngle X Y k := by
  sorry

/-- Beyond the smaller of the two dimensions the principal angle is `π / 2`. -/
theorem principalAngle_of_rank_le {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜} {k : ℕ}
    (h : min X.rank Y.rank ≤ k) : principalAngle X Y k = Real.pi / 2 := by
  sorry

/-- The principal angles between a subspace and itself vanish, up to its dimension. -/
theorem principalAngle_self (X : Matrix n p 𝕜) {k : ℕ} (hk : k < X.rank) :
    principalAngle X X k = 0 := by
  sorry

/-- If the column space of `Y` is inside that of `X`, the principal angles vanish up to the
dimension of the smaller space. Port of `NLAlib.directedSubspaceGap_eq_zero_of_range_le`. -/
theorem principalAngle_eq_zero_of_range_le {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range X.mulVecLin) {k : ℕ} (hk : k < Y.rank) :
    principalAngle X Y k = 0 := by
  sorry

/-! ### Cosines -/

/-- The cosines of the principal angles are the singular values of the product of the two
projectors. -/
theorem cos_principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.cos (principalAngle X Y k) =
      singularValues (rangeProjector X * rangeProjector Y) k := by
  sorry

/-- **Cosines for orthonormal frames**: the singular values of `Uᴴ * V`.
[GolubVanLoan2013, §6.4.3]. Port of `NLAlib.cos_principalAngles`.
Result: principal-angles -/
theorem HasOrthonormalCols.cos_principalAngle [DecidableEq q] {U : Matrix n p 𝕜}
    {V : Matrix n q 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (k : ℕ) :
    Real.cos (principalAngle U V k) = singularValues (Uᴴ * V) k := by
  sorry

/-- Cosines when only the first frame is orthonormal: the singular values of
`Uᴴ * rangeProjector Y`. -/
theorem HasOrthonormalCols.cos_principalAngle_left {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.cos (principalAngle U Y k) = singularValues (Uᴴ * rangeProjector Y) k := by
  sorry

/-! ### Sines -/

/-- The sine of a principal angle from its cosine. Port of `NLAlib.sin_principalAngles`. -/
theorem sin_principalAngle (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜) (k : ℕ) :
    Real.sin (principalAngle X Y k) =
      √(1 - singularValues (rangeProjector X * rangeProjector Y) k ^ 2) := by
  sorry

/-- **Sines of the principal angles**: the singular values of
`(1 - rangeProjector X) * rangeProjector Y`, in reverse order:
`σ_i = sin θ_j` for `i + j + 1 = rank Y`.
[GolubVanLoan2013, §2.5.3]; [StewartSun1990, Theorem I.5.5].
Result: principal-angles -/
theorem singularValues_one_sub_rangeProjector_mul_rangeProjector (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) {i j : ℕ} (hij : i + j + 1 = Y.rank) :
    singularValues ((1 - rangeProjector X) * rangeProjector Y) i =
      Real.sin (principalAngle X Y j) := by
  sorry

/-- Sines for orthonormal frames: the singular values of `(1 - U * Uᴴ) * V`, in reverse order.
Port of `NLAlib.transpose_sinePrincipalAngles_mul_self` and
`NLAlib.specNorm_sinePrincipalAngles_eq_residual`. -/
theorem HasOrthonormalCols.singularValues_one_sub_mul_conjTranspose_mul [DecidableEq q]
    {U : Matrix n p 𝕜} {V : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) {i j : ℕ} (hij : i + j + 1 = Fintype.card q) :
    singularValues ((1 - U * Uᴴ) * V) i = Real.sin (principalAngle U V j) := by
  sorry

/-- **The largest principal angle as a distance**: `‖(1 - P_X) P_Y‖₂` is the sine of the largest
principal angle counted up to the dimension of the column space of `Y`.
[GolubVanLoan2013, §2.5.3]. Port of `NLAlib.directedSubspaceGap_eq_sin_principalAngles`.
Result: principal-angles -/
theorem specNorm_one_sub_rangeProjector_mul_rangeProjector (X : Matrix n p 𝕜) (Y : Matrix n q 𝕜)
    {j : ℕ} (hj : j + 1 = Y.rank) :
    specNorm ((1 - rangeProjector X) * rangeProjector Y) = Real.sin (principalAngle X Y j) := by
  sorry

/-- The Frobenius norm of `(1 - P_X) P_Y` is the root sum of squares of the sines of the
principal angles. Port of `NLAlib.frobNorm_sinePrincipalAngles_eq_residual`. -/
theorem frobNorm_one_sub_rangeProjector_mul_rangeProjector_sq (X : Matrix n p 𝕜)
    (Y : Matrix n q 𝕜) :
    frobNorm ((1 - rangeProjector X) * rangeProjector Y) ^ 2 =
      ∑ j ∈ Finset.range Y.rank, Real.sin (principalAngle X Y j) ^ 2 := by
  sorry

/-- **The distance between two projectors of equal rank** is the sine of the largest principal
angle. [GolubVanLoan2013, §2.5.3].
Port of `NLAlib.specNorm_sinePrincipalAngles_eq_projector_distance`.
Result: projector-gap -/
theorem specNorm_rangeProjector_sub_rangeProjector {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : X.rank = Y.rank) {j : ℕ} (hj : j + 1 = Y.rank) :
    specNorm (rangeProjector X - rangeProjector Y) = Real.sin (principalAngle X Y j) := by
  sorry

/-- For two subspaces of equal dimension,
`‖P_X - P_Y‖_F² = 2 ∑ sin² θ_j`.
Port of `NLAlib.frobSq_projector_distance_eq_two_mul_sinePrincipalAngles`. -/
theorem frobNorm_rangeProjector_sub_rangeProjector_sq {X : Matrix n p 𝕜} {Y : Matrix n q 𝕜}
    (h : X.rank = Y.rank) :
    frobNorm (rangeProjector X - rangeProjector Y) ^ 2 =
      2 * ∑ j ∈ Finset.range Y.rank, Real.sin (principalAngle X Y j) ^ 2 := by
  sorry

/-! ### Tangents -/

/-- **The acute case for a frame and a basis with the same number of columns**: `Uᴴ * Y` is
invertible exactly when the largest principal angle is below `π / 2`.
Port of `NLAlib.isUnit_overlap_of_principalAngles_last_lt_pi_div_two`. -/
theorem HasOrthonormalCols.isUnit_conjTranspose_mul_iff {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (Y : Matrix n p 𝕜) {j : ℕ} (hj : j + 1 = Fintype.card p) :
    IsUnit (Uᴴ * Y) ↔ principalAngle U Y j < Real.pi / 2 := by
  sorry

/-- **Tangents of the principal angles.** For `U` with orthonormal columns and any `Y` with the
same number of columns and `Uᴴ * Y` invertible, the singular values of
`(1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹` are the tangents of the principal angles, in reverse order.
[GolubVanLoan2013, §8.2.4 (proof of Theorem 8.2.2)]; [Saad2011, §5.2].
Port of `NLAlib.tan_principalAngles_sq` and `NLAlib.tanThetaMax_eq_tan_principalAngles`.
Result: principal-angles -/
theorem HasOrthonormalCols.singularValues_one_sub_mul_mul_inv {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) {Y : Matrix n p 𝕜} (hY : IsUnit (Uᴴ * Y)) {i j : ℕ}
    (hij : i + j + 1 = Fintype.card p) :
    singularValues ((1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹) i = Real.tan (principalAngle U Y j) := by
  sorry

/-- The tangent of the largest principal angle as a spectral norm.
Port of `NLAlib.specNorm_tangentPrincipalAngles_eq_tan_last`. -/
theorem HasOrthonormalCols.specNorm_one_sub_mul_mul_inv {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) {Y : Matrix n p 𝕜} (hY : IsUnit (Uᴴ * Y)) {j : ℕ}
    (hj : j + 1 = Fintype.card p) :
    specNorm ((1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹) = Real.tan (principalAngle U Y j) := by
  sorry

/-- The tangent matrix does not depend on the basis of the second subspace.
Port of `NLAlib.overlapTangentNorm_mul_right`. -/
theorem one_sub_mul_mul_inv_mul_right (U Y : Matrix n p 𝕜) {R : Matrix p p 𝕜} (hR : IsUnit R) :
    (1 - U * Uᴴ) * (Y * R) * (Uᴴ * (Y * R))⁻¹ = (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹ := by
  sorry

/-- **The tangent of a graph subspace.** If `U` and `W` have orthonormal columns and are mutually
orthogonal, the singular values of `F` are the tangents of the principal angles between the
column spaces of `U` and of `U + W * F`.
[Saad2011, §5.1]. Port of `NLAlib.subspaceTangent_range_graph_eq_specNorm`. -/
theorem HasOrthonormalCols.singularValues_eq_tan_principalAngle_add_mul [DecidableEq q]
    {U : Matrix n p 𝕜} {W : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hW : HasOrthonormalCols W) (hUW : Uᴴ * W = 0) (F : Matrix q p 𝕜) {i j : ℕ}
    (hij : i + j + 1 = Fintype.card p) :
    singularValues F i = Real.tan (principalAngle U (U + W * F) j) := by
  sorry

end NLAlib
