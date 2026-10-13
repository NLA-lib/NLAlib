/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Spectral.SVD
public import NLAlib.Matrix.Subspaces.ProjectorPair

/-!
# Principal angles between subspaces

The principal angles between the column spaces of two matrices `X` and `Y` are
`NLAlib.principalAngle X Y k`, `k = 0, 1, …`, in non-decreasing order. Their cosines are the
singular values of the product of the two orthogonal projectors; for matrices `U`, `V` with
orthonormal columns these are the singular values of `Uᴴ * V`. The sines are the singular values
of `(1 - rangeProjector X) * rangeProjector Y`, and in the acute case the tangents are the
singular values of the tangent matrix `NLAlib.tangentMatrix U Y = (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹`.

The angle depends only on the column spaces, so `X` and `Y` may be orthonormal frames, arbitrary
bases, or the projectors themselves. Beyond the smaller of the two dimensions the angle is `π / 2`.

Statements about distances between subspaces are made with the matrices, in a norm:
`specNorm ((1 - P) * Q)`, `frobNorm ((1 - P) * Q)`. This file identifies those norms with the
angles.

## Main definitions

* `NLAlib.principalAngle`: the `k`-th principal angle between two column spaces.
* `NLAlib.tangentMatrix`: the matrix whose singular values are the tangents.

## Main results

* `NLAlib.cos_principalAngle`, `NLAlib.HasOrthonormalCols.cos_principalAngle`: cosines.
* `NLAlib.singularValues_one_sub_rangeProjector_mul_rangeProjector`: sines.
* `NLAlib.specNorm_one_sub_rangeProjector_mul_rangeProjector`,
  `NLAlib.specNorm_rangeProjector_sub_rangeProjector`: the largest angle as a distance.
* `NLAlib.tangentMatrix`, `NLAlib.HasOrthonormalCols.singularValues_tangentMatrix`: tangents.
* `NLAlib.HasOrthonormalCols.exists_frobNorm_sub_mul_sq_le`: aligning two frames.
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

/-- The singular values of an orthogonal projector are `1` up to its rank. -/
private theorem singularValues_eq_one_of_isStarProjection {P : Matrix n n 𝕜}
    (hP : IsStarProjection P) {k : ℕ} (hk : k < P.rank) : singularValues P k = 1 := by
  classical
  have h := hP.sq_singularValues_one_sub_mul hP (i := P.rank - 1 - k) (j := k) (by omega)
  rw [hP.one_sub_mul_self, singularValues_zero, hP.mul_self, Pi.zero_apply] at h
  refine (sq_eq_sq₀ (singularValues_nonneg P k) zero_le_one).mp ?_
  linarith

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
  rw [rangeProjector_mul_rangeProjector, singularValues_eq_one_of_isStarProjection
    (isStarProjection_rangeProjector X) (by rwa [rank_rangeProjector]), Real.arccos_one]

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

/-! ### Tangents -/

variable [DecidableEq p]

/-- The **tangent matrix** of a basis `Y` relative to a frame `U` with the same number of
columns: `(1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹`. When `U` has orthonormal columns and `Uᴴ * Y` is
invertible, its singular values are the tangents of the principal angles between the two column
spaces, and it depends only on the column space of `Y`. It is `0` when `Uᴴ * Y` is singular.
[GolubVanLoan2013, §8.2.4]; [Saad2011, §5.2].
Port of `NLAlib.overlapTangentNorm` and `NLAlib.tangentPrincipalAngles`, as a matrix. -/
noncomputable def tangentMatrix (U Y : Matrix n p 𝕜) : Matrix n p 𝕜 :=
  (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹

/-- The tangent matrix unfolded. -/
theorem tangentMatrix_def (U Y : Matrix n p 𝕜) :
    tangentMatrix U Y = (1 - U * Uᴴ) * Y * (Uᴴ * Y)⁻¹ :=
  rfl

/-- The tangent matrix does not depend on the basis of the second subspace.
Port of `NLAlib.overlapTangentNorm_mul_right`. -/
@[simp]
theorem tangentMatrix_mul_right (U Y : Matrix n p 𝕜) {R : Matrix p p 𝕜} (hR : IsUnit R) :
    tangentMatrix U (Y * R) = tangentMatrix U Y := by
  have hR' : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR
  rw [tangentMatrix, tangentMatrix, ← Matrix.mul_assoc Uᴴ, Matrix.mul_inv_rev,
    ← Matrix.mul_assoc _ Y R, Matrix.mul_assoc _ R, ← Matrix.mul_assoc R,
    Matrix.mul_nonsing_inv R hR', Matrix.one_mul]

/-- The tangent matrix vanishes when `Uᴴ * Y` is singular.
Port of `NLAlib.overlapTangentNorm_eq_zero_of_not_isUnit`. -/
theorem tangentMatrix_of_not_isUnit {U Y : Matrix n p 𝕜} (h : ¬ IsUnit (Uᴴ * Y)) :
    tangentMatrix U Y = 0 := by
  rw [tangentMatrix, Matrix.nonsing_inv_apply_not_isUnit _
    (fun hd => h ((Matrix.isUnit_iff_isUnit_det _).mpr hd)), Matrix.mul_zero]

/-- The tangent matrix in terms of a complement frame: if `U * Uᴴ + W * Wᴴ = 1` with `W`
orthonormal, then `tangentMatrix U Y` and `Wᴴ * Y * (Uᴴ * Y)⁻¹` have the same singular values.
Port of `NLAlib.overlapTangentNorm_eq_specNorm_transpose_mul_mul`. -/
theorem singularValues_tangentMatrix_eq_of_mul_conjTranspose_add_eq_one [DecidableEq q]
    {U : Matrix n p 𝕜} {W : Matrix n q 𝕜} (hW : HasOrthonormalCols W)
    (h : U * Uᴴ + W * Wᴴ = 1) (Y : Matrix n p 𝕜) :
    singularValues (tangentMatrix U Y) = singularValues (Wᴴ * Y * (Uᴴ * Y)⁻¹) := by
  rw [tangentMatrix, Matrix.mul_assoc, Matrix.mul_assoc Wᴴ,
    singularValues_conjTranspose_mul_eq_of_mul_conjTranspose_add_eq_one hW h]

omit [DecidableEq n] in
/-- **The acute case for a frame and a basis with the same number of columns**: `Uᴴ * Y` is
invertible exactly when the largest principal angle is below `π / 2`.
Port of `NLAlib.isUnit_overlap_of_principalAngles_last_lt_pi_div_two`. -/
theorem HasOrthonormalCols.isUnit_conjTranspose_mul_iff {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (Y : Matrix n p 𝕜) {j : ℕ} (hj : j + 1 = Fintype.card p) :
    IsUnit (Uᴴ * Y) ↔ principalAngle U Y j < Real.pi / 2 := by
  have hrank : (rangeProjector U * rangeProjector Y).rank = (Uᴴ * Y).rank := by
    rw [hU.rangeProjector_eq, Matrix.mul_assoc, hU.rank_mul]
    refine le_antisymm ?_ ?_
    · rw [← mul_pinv, ← Matrix.mul_assoc]
      exact Matrix.rank_mul_le_left _ _
    · have hY : Uᴴ * Y = Uᴴ * rangeProjector Y * Y := by
        rw [Matrix.mul_assoc, rangeProjector_mul_self]
      rw [hY]
      exact Matrix.rank_mul_le_left _ _
  unfold principalAngle
  rw [Real.arccos_lt_pi_div_two, singularValues_pos_iff, hrank]
  constructor
  · intro h
    rw [Matrix.rank_of_isUnit _ h]
    omega
  · intro h
    have hr : (Uᴴ * Y).rank = Fintype.card p :=
      le_antisymm (Matrix.rank_le_card_width _) (by omega)
    exact Matrix.mulVec_injective_iff_isUnit.mp (mulVec_injective_iff_rank_eq.mpr hr)

/-- **Tangents of the principal angles.** For `U` with orthonormal columns and any `Y` with the
same number of columns and `Uᴴ * Y` invertible, the singular values of `tangentMatrix U Y` are
the tangents of the principal angles, in reverse order.
[GolubVanLoan2013, §8.2.4 (proof of Theorem 8.2.2)]; [Saad2011, §5.2].
Port of `NLAlib.tan_principalAngles_sq` and `NLAlib.tanThetaMax_eq_tan_principalAngles`.
Result: principal-angles -/
theorem HasOrthonormalCols.singularValues_tangentMatrix {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) {Y : Matrix n p 𝕜} (hY : IsUnit (Uᴴ * Y)) {i j : ℕ}
    (hij : i + j + 1 = Fintype.card p) :
    singularValues (tangentMatrix U Y) i = Real.tan (principalAngle U Y j) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix n p 𝕜, Z = Y * (Uᴴ * Y)⁻¹ := ⟨_, rfl⟩
  have hUZ : Uᴴ * Z = 1 := by
    rw [hZ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hY)]
  have hZU : Zᴴ * U = 1 := by
    have h := congrArg Matrix.conjTranspose hUZ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] at h
  have hT : tangentMatrix U Y = Z - U := by
    rw [tangentMatrix, Matrix.mul_assoc, ← hZ, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
      hUZ, Matrix.mul_one]
  have hgram : Zᴴ * Z =
      (tangentMatrix U Y)ᴴ * tangentMatrix U Y + (1 : ℝ) • (1 : Matrix p p 𝕜) := by
    rw [hT, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hUZ, hZU,
      hU.conjTranspose_mul_self, one_smul]
    abel
  have hsq : singularValues Z i ^ 2 = singularValues (tangentMatrix U Y) i ^ 2 + 1 := by
    rw [sq_singularValues, sq_singularValues, hgram,
      (Matrix.isHermitian_conjTranspose_mul_self _).eigenvalue_add_smul_one 1 (by omega)]
  have hZinj : Function.Injective Z.mulVec := fun x y hxy => by
    have h := congrArg (Uᴴ *ᵥ ·) hxy
    simpa only [Matrix.mulVec_mulVec, hUZ, Matrix.one_mulVec] using h
  have hpinv : pinv Z = Uᴴ * rangeProjector Y := by
    rw [← rangeProjector_mul_of_isUnit Y (Matrix.isUnit_nonsing_inv_iff.mpr hY), ← hZ, ← mul_pinv,
      ← Matrix.mul_assoc, hUZ, Matrix.one_mul]
  have hcos : Real.cos (principalAngle U Y j) = (singularValues Z i)⁻¹ := by
    rw [hU.cos_principalAngle_left, ← hpinv]
    exact singularValues_pinv Z (by rw [mulVec_injective_iff_rank_eq.mp hZinj]; omega)
  have ht := singularValues_nonneg (tangentMatrix U Y) i
  have hs : 0 < singularValues Z i := by
    have := singularValues_nonneg Z i
    nlinarith
  have hsin : √(1 - (singularValues Z i)⁻¹ ^ 2) =
      singularValues (tangentMatrix U Y) i / singularValues Z i := by
    have h1 : 1 - (singularValues Z i)⁻¹ ^ 2 =
        (singularValues (tangentMatrix U Y) i / singularValues Z i) ^ 2 := by
      field_simp
      linarith
    rw [h1, Real.sqrt_sq (div_nonneg ht hs.le)]
  rw [Real.tan_eq_sin_div_cos, sin_principalAngle, ← NLAlib.cos_principalAngle, hcos, hsin]
  field_simp

/-- The tangent of the largest principal angle as a spectral norm.
Port of `NLAlib.specNorm_tangentPrincipalAngles_eq_tan_last`. -/
theorem HasOrthonormalCols.specNorm_tangentMatrix {U : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) {Y : Matrix n p 𝕜} (hY : IsUnit (Uᴴ * Y)) {j : ℕ}
    (hj : j + 1 = Fintype.card p) :
    specNorm (tangentMatrix U Y) = Real.tan (principalAngle U Y j) := by
  rw [← singularValues_zero_eq_specNorm]
  exact hU.singularValues_tangentMatrix hY (by omega)

/-- **The tangent matrix of a graph subspace.** If `U` and `W` have orthonormal columns and are
mutually orthogonal, the tangent matrix of `U + W * F` relative to `U` is `W * F`: its singular
values are those of `F`. [Saad2011, §5.1].
Port of `NLAlib.subspaceTangent_range_graph_eq_specNorm`. -/
theorem HasOrthonormalCols.tangentMatrix_add_mul {U : Matrix n p 𝕜} {W : Matrix n q 𝕜}
    (hU : HasOrthonormalCols U) (hUW : Uᴴ * W = 0) (F : Matrix q p 𝕜) :
    tangentMatrix U (U + W * F) = W * F := by
  have h1 : Uᴴ * (U + W * F) = 1 := by
    rw [Matrix.mul_add, hU.conjTranspose_mul_self, ← Matrix.mul_assoc, hUW, Matrix.zero_mul,
      add_zero]
  rw [tangentMatrix, h1, inv_one, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, h1, Matrix.mul_one, add_sub_cancel_left]

omit [DecidableEq n] in
/-- The singular values of `F` are the tangents of the principal angles between the column spaces
of `U` and of the graph `U + W * F`. [Saad2011, §5.1]. -/
theorem HasOrthonormalCols.singularValues_eq_tan_principalAngle_add_mul [DecidableEq q]
    {U : Matrix n p 𝕜} {W : Matrix n q 𝕜} (hU : HasOrthonormalCols U)
    (hW : HasOrthonormalCols W) (hUW : Uᴴ * W = 0) (F : Matrix q p 𝕜) {i j : ℕ}
    (hij : i + j + 1 = Fintype.card p) :
    singularValues F i = Real.tan (principalAngle U (U + W * F) j) := by
  classical
  have h1 : IsUnit (Uᴴ * (U + W * F)) := by
    rw [Matrix.mul_add, hU.conjTranspose_mul_self, ← Matrix.mul_assoc, hUW, Matrix.zero_mul,
      add_zero]
    exact isUnit_one
  have h := hU.singularValues_tangentMatrix h1 hij
  rwa [hU.tangentMatrix_add_mul hUW, hW.singularValues_mul_left] at h

/-! ### Aligning two frames -/

/-- There is a unitary `T` for which the Gram matrix of `U - V * T` is at most twice that of
`(1 - V * Vᴴ) * U` in the Loewner order. With a singular value decomposition
`Vᴴ * U = W₁ * D * W₂ᴴ` and `T = W₁ * W₂ᴴ`, the two Gram matrices are `2 (1 - W₂ D W₂ᴴ)` and
`1 - W₂ D² W₂ᴴ`, and `D - D²` is positive semidefinite. -/
private theorem exists_conjTranspose_sub_mul_mul_sub_mul_le {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    ∃ T : Matrix p p 𝕜, HasOrthonormalCols T ∧
      (U - V * T)ᴴ * (U - V * T) ≤
        (2 : ℝ) • (((1 - V * Vᴴ) * U)ᴴ * ((1 - V * Vᴴ) * U)) := by
  obtain ⟨W₁, W₂, h⟩ := exists_isSVD (Vᴴ * U) (k := Fintype.card p)
    (Matrix.rank_le_card_width _) le_rfl le_rfl
  obtain ⟨d, hd⟩ : ∃ d : Fin (Fintype.card p) → ℝ,
    d = fun i : Fin (Fintype.card p) => singularValues (Vᴴ * U) i := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin (Fintype.card p)) (Fin (Fintype.card p)) 𝕜,
    D = Matrix.diagonal fun i => ((d i : ℝ) : 𝕜) := ⟨_, rfl⟩
  have h1 := h.hasOrthonormalCols_left.conjTranspose_mul_self
  have h2 : W₂ * W₂ᴴ = 1 :=
    h.hasOrthonormalCols_right.mul_conjTranspose_self_of_card_eq (Fintype.card_fin _).symm
  have hDH : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp only [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal]
  have hVU : Vᴴ * U = W₁ * D * W₂ᴴ := by rw [hD, hd]; exact h.eq
  have hUV : Uᴴ * V = W₂ * D * W₁ᴴ := by
    have h' := congrArg Matrix.conjTranspose hVU
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDH,
      ← Matrix.mul_assoc] at h'
  have hT : (W₁ * W₂ᴴ)ᴴ * (W₁ * W₂ᴴ) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc W₁ᴴ, h1, Matrix.one_mul, h2]
  refine ⟨W₁ * W₂ᴴ, hT, ?_⟩
  have hgram : (U - V * (W₁ * W₂ᴴ))ᴴ * (U - V * (W₁ * W₂ᴴ)) =
      (2 : ℝ) • (1 - W₂ * D * W₂ᴴ) := by
    have e1 : Uᴴ * (V * (W₁ * W₂ᴴ)) = W₂ * D * W₂ᴴ := by
      rw [← Matrix.mul_assoc, hUV, Matrix.mul_assoc (W₂ * D), ← Matrix.mul_assoc W₁ᴴ, h1,
        Matrix.one_mul]
    have e2 : (V * (W₁ * W₂ᴴ))ᴴ * U = W₂ * D * W₂ᴴ := by
      have hH : (W₂ * D * W₂ᴴ)ᴴ = W₂ * D * W₂ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, hDH, Matrix.mul_assoc]
      have h' := congrArg Matrix.conjTranspose e1
      rw [hH] at h'
      rw [← h', Matrix.conjTranspose_mul Uᴴ, Matrix.conjTranspose_conjTranspose]
    have e3 : (V * (W₁ * W₂ᴴ))ᴴ * (V * (W₁ * W₂ᴴ)) = 1 := by
      rw [hV.conjTranspose_mul_mul, hT]
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      hU.conjTranspose_mul_self, e1, e2, e3, two_smul]
    abel
  have hres : ((1 - V * Vᴴ) * U)ᴴ * ((1 - V * Vᴴ) * U) = 1 - W₂ * (D * D) * W₂ᴴ := by
    have hP := hV.isStarProjection_mul_conjTranspose.one_sub
    have e4 : W₂ * D * W₁ᴴ * (W₁ * D * W₂ᴴ) = W₂ * (D * D) * W₂ᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc W₁ᴴ, h1, Matrix.one_mul]
    rw [Matrix.conjTranspose_mul, hP.conjTranspose_eq, Matrix.mul_assoc,
      ← Matrix.mul_assoc (1 - V * Vᴴ), hP.mul_self, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_sub, hU.conjTranspose_mul_self, Matrix.mul_assoc V, ← Matrix.mul_assoc Uᴴ, hUV,
      hVU, e4]
  have hE : (2 : ℝ) • (1 - W₂ * (D * D) * W₂ᴴ) - (2 : ℝ) • (1 - W₂ * D * W₂ᴴ) =
      W₂ * ((2 : ℝ) • (D - D * D)) * W₂ᴴ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, ← smul_sub]
    congr 1
    abel
  have hdiag : (2 : ℝ) • (D - D * D) =
      Matrix.diagonal fun i => ((2 * (d i * (1 - d i)) : ℝ) : 𝕜) := by
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub, ← Matrix.diagonal_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul, RCLike.ofReal_sub,
      RCLike.ofReal_one, RCLike.ofReal_ofNat]
    ring
  rw [Matrix.le_iff, hgram, hres, hE, hdiag]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same (Matrix.PosSemidef.diagonal fun i => ?_) W₂
  have h0 : 0 ≤ d i := by rw [hd]; exact singularValues_nonneg _ _
  have h1 : d i ≤ 1 := by
    rw [hd]
    exact (singularValues_le_specNorm _ _).trans
      ((hV.specNorm_conjTranspose_mul_le U).trans hU.specNorm_le_one)
  exact RCLike.ofReal_nonneg.mpr (mul_nonneg zero_le_two (mul_nonneg h0 (sub_nonneg.mpr h1)))

/-- **Aligning two frames.** For frames `U`, `V` with the same number of columns there is a
unitary `T` with `‖U - V T‖_F² ≤ 2 ‖(1 - V Vᴴ) U‖_F²`: after the best rotation, the frames are as
close as the subspaces. [StewartSun1990, Theorem II.4.11 context]. -/
theorem HasOrthonormalCols.exists_frobNorm_sub_mul_sq_le {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    ∃ T : Matrix p p 𝕜, HasOrthonormalCols T ∧
      frobNorm (U - V * T) ^ 2 ≤ 2 * frobNorm ((1 - V * Vᴴ) * U) ^ 2 := by
  obtain ⟨T, hT, hle⟩ := exists_conjTranspose_sub_mul_mul_sub_mul_le hU hV
  refine ⟨T, hT, ?_⟩
  have h := (Matrix.le_iff.mp hle).re_trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, map_sub, RCLike.smul_re, ← frobNorm_sq_eq_re_trace,
    ← frobNorm_sq_eq_re_trace] at h
  linarith

/-- Aligning two frames, in the spectral norm: there is a unitary `T` with
`‖U - V T‖₂² ≤ 2 ‖(1 - V Vᴴ) U‖₂²`. -/
theorem HasOrthonormalCols.exists_specNorm_sub_mul_sq_le {U V : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) :
    ∃ T : Matrix p p 𝕜, HasOrthonormalCols T ∧
      specNorm (U - V * T) ^ 2 ≤ 2 * specNorm ((1 - V * Vᴴ) * U) ^ 2 := by
  obtain ⟨T, hT, hle⟩ := exists_conjTranspose_sub_mul_mul_sub_mul_le hU hV
  refine ⟨T, hT, ?_⟩
  have h := (Matrix.posSemidef_conjTranspose_mul_self (U - V * T)).specNorm_le_specNorm_of_le hle
  rwa [specNorm_real_smul, specNorm_conjTranspose_mul_self, specNorm_conjTranspose_mul_self,
    abs_of_nonneg zero_le_two] at h

end NLAlib
