/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2
public import NLAlib.Matrix.Basic.Orthonormal

/-!
# Plane rotations

`NLAlib.planeRotation u v c s` rotates the plane spanned by two orthonormal vectors `u`, `v` by
the angle with cosine `c` and sine `s`, and fixes the orthogonal complement of that plane. With
`u`, `v` standard basis vectors it is a Givens rotation.

## Main definitions

* `NLAlib.planeRotation`: `1 + (c - 1) (u uᴴ + v vᴴ) + s (u vᴴ - v uᴴ)`.

## Main results

* `NLAlib.hasOrthonormalCols_planeRotation`: a plane rotation is unitary.
* `NLAlib.planeRotation_mulVec`: its action on a vector.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [DecidableEq n]

/-- The **plane rotation** in the plane of `u` and `v` with cosine `c` and sine `s`:
`1 + (c - 1) (u uᴴ + v vᴴ) + s (u vᴴ - v uᴴ)`. It is a rotation when `u`, `v` are orthonormal
and `c ^ 2 + s ^ 2 = 1`; for other arguments it is just this matrix.
[GolubVanLoan2013, §5.1.8] for `u`, `v` standard basis vectors (Givens rotations).
Port of `NLAlib.planeRotation`, there over `ℝ`. -/
def planeRotation (u v : n → 𝕜) (c s : ℝ) : Matrix n n 𝕜 :=
  1 + ((c : 𝕜) - 1) • (Matrix.vecMulVec u (star u) + Matrix.vecMulVec v (star v)) +
    (s : 𝕜) • (Matrix.vecMulVec u (star v) - Matrix.vecMulVec v (star u))

/-- The action of a plane rotation on a vector. Port of `NLAlib.planeRotation_mulVec`. -/
theorem planeRotation_mulVec [Fintype n] (u v x : n → 𝕜) (c s : ℝ) :
    planeRotation u v c s *ᵥ x =
      x + ((c : 𝕜) - 1) • ((star u ⬝ᵥ x) • u + (star v ⬝ᵥ x) • v) +
        (s : 𝕜) • ((star v ⬝ᵥ x) • u - (star u ⬝ᵥ x) • v) := by
  simp only [planeRotation, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

/-- The rotation by angle zero is the identity. -/
@[simp]
theorem planeRotation_one_zero (u v : n → 𝕜) : planeRotation u v 1 0 = 1 := by
  rw [planeRotation, RCLike.ofReal_one, sub_self, zero_smul, RCLike.ofReal_zero, zero_smul,
    add_zero, add_zero]

/-- The conjugate transpose of a plane rotation is the rotation by the opposite angle. -/
theorem conjTranspose_planeRotation (u v : n → 𝕜) (c s : ℝ) :
    (planeRotation u v c s)ᴴ = planeRotation u v c (-s) := by
  simp only [planeRotation, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.conjTranspose_vecMulVec,
    star_star, star_sub, star_one, RCLike.star_def, RCLike.conj_ofReal, RCLike.ofReal_neg,
    neg_smul, smul_sub]
  abel

omit [DecidableEq n] in
private theorem star_dotProduct_self_of_norm_toLp_eq_one [Fintype n] {u : n → 𝕜}
    (hu : ‖WithLp.toLp 2 u‖ = 1) : star u ⬝ᵥ u = 1 := by
  rw [EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, hu, one_pow, RCLike.ofReal_one]

/-- A plane rotation sends `u` to `c u - s v`, for orthonormal `u`, `v`. -/
theorem planeRotation_mulVec_left [Fintype n] {u v : n → 𝕜} (hu : ‖WithLp.toLp 2 u‖ = 1)
    (huv : star u ⬝ᵥ v = 0) (c s : ℝ) :
    planeRotation u v c s *ᵥ u = (c : 𝕜) • u - (s : 𝕜) • v := by
  have hvu : star v ⬝ᵥ u = 0 := by rw [Matrix.star_dotProduct, huv, star_zero]
  rw [planeRotation_mulVec, star_dotProduct_self_of_norm_toLp_eq_one hu, hvu]
  simp only [one_smul, zero_smul, add_zero, zero_sub, smul_neg, sub_smul]
  abel

/-- A plane rotation sends `v` to `s u + c v`, for orthonormal `u`, `v`. -/
theorem planeRotation_mulVec_right [Fintype n] {u v : n → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1)
    (huv : star u ⬝ᵥ v = 0) (c s : ℝ) :
    planeRotation u v c s *ᵥ v = (s : 𝕜) • u + (c : 𝕜) • v := by
  rw [planeRotation_mulVec, star_dotProduct_self_of_norm_toLp_eq_one hv, huv]
  simp only [one_smul, zero_smul, zero_add, sub_zero, sub_smul]
  abel

/-- A plane rotation fixes every vector orthogonal to `u` and `v`. -/
theorem planeRotation_mulVec_of_orthogonal [Fintype n] {u v x : n → 𝕜}
    (hux : star u ⬝ᵥ x = 0) (hvx : star v ⬝ᵥ x = 0) (c s : ℝ) :
    planeRotation u v c s *ᵥ x = x := by
  rw [planeRotation_mulVec, hux, hvx, zero_smul, zero_smul, add_zero, sub_self, smul_zero,
    smul_zero, add_zero, add_zero]

/-- **A plane rotation is unitary**, for orthonormal `u`, `v` and `c ^ 2 + s ^ 2 = 1`.
Port of `NLAlib.hasOrthonormalCols_planeRotation`, there over `ℝ`. -/
theorem hasOrthonormalCols_planeRotation [Fintype n] {u v : n → 𝕜}
    (hu : ‖WithLp.toLp 2 u‖ = 1) (hv : ‖WithLp.toLp 2 v‖ = 1) (huv : star u ⬝ᵥ v = 0)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) : HasOrthonormalCols (planeRotation u v c s) := by
  have hu := star_dotProduct_self_of_norm_toLp_eq_one hu
  have hv := star_dotProduct_self_of_norm_toLp_eq_one hv
  have hvu : star v ⬝ᵥ u = 0 := by rw [Matrix.star_dotProduct, huv, star_zero]
  rw [HasOrthonormalCols, conjTranspose_planeRotation]
  let P := Matrix.vecMulVec u (star u) + Matrix.vecMulVec v (star v)
  let K := Matrix.vecMulVec u (star v) - Matrix.vecMulVec v (star u)
  have hPP : P * P = P := by
    simp only [P, Matrix.add_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, huv, hvu, one_smul, zero_smul, Matrix.vecMulVec_zero, add_zero, zero_add]
  have hPK : P * K = K := by
    simp only [P, K, Matrix.add_mul, Matrix.mul_sub, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, huv, hvu, one_smul, zero_smul, Matrix.vecMulVec_zero]
    abel
  have hKP : K * P = K := by
    simp only [P, K, Matrix.sub_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, huv, hvu, one_smul, zero_smul, Matrix.vecMulVec_zero]
    abel
  have hKK : K * K = -P := by
    simp only [P, K, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul_vecMulVec,
      hu, hv, huv, hvu, one_smul, zero_smul, Matrix.vecMulVec_zero, sub_zero, zero_sub]
    abel
  have hcoef : ((c : 𝕜) - 1) * ((c : 𝕜) - 1) + 2 * ((c : 𝕜) - 1) + (s : 𝕜) * (s : 𝕜) = 0 := by
    have h : (c : 𝕜) ^ 2 + (s : 𝕜) ^ 2 = 1 := by
      exact_mod_cast congrArg (RCLike.ofReal (K := 𝕜)) hcs
    linear_combination h
  change (1 + ((c : 𝕜) - 1) • P + ((-s : ℝ) : 𝕜) • K) * (1 + ((c : 𝕜) - 1) • P + (s : 𝕜) • K) = 1
  simp only [RCLike.ofReal_neg, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, hPP, hPK, hKP, hKK, smul_neg, neg_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
  linear_combination hcoef * P i j

/-- The rational parametrisation of the circle: `c = (1 - t²) / (1 + t²)` and
`s = 2 t / (1 + t²)` satisfy `c ^ 2 + s ^ 2 = 1`.
Port of `NLAlib.sq_rational_rotation_coefficients`. -/
theorem sq_div_add_sq_div_one_add_sq (t : ℝ) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

end NLAlib
