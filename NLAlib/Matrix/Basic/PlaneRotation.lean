/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

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

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **plane rotation** in the plane of `u` and `v` with cosine `c` and sine `s`:
`1 + (c - 1) (u uᴴ + v vᴴ) + s (u vᴴ - v uᴴ)`. It is a rotation when `u`, `v` are orthonormal
and `c ^ 2 + s ^ 2 = 1`; for other arguments it is just this matrix.
[GolubVanLoan2013, §5.1.8] for `u`, `v` standard basis vectors (Givens rotations).
Port of `NLAlib.planeRotation`, there over `ℝ`. -/
def planeRotation (u v : n → 𝕜) (c s : ℝ) : Matrix n n 𝕜 :=
  1 + ((c : 𝕜) - 1) • (Matrix.vecMulVec u (star u) + Matrix.vecMulVec v (star v)) +
    (s : 𝕜) • (Matrix.vecMulVec u (star v) - Matrix.vecMulVec v (star u))

/-- The action of a plane rotation on a vector. Port of `NLAlib.planeRotation_mulVec`. -/
theorem planeRotation_mulVec (u v x : n → 𝕜) (c s : ℝ) :
    planeRotation u v c s *ᵥ x =
      x + ((c : 𝕜) - 1) • ((star u ⬝ᵥ x) • u + (star v ⬝ᵥ x) • v) +
        (s : 𝕜) • ((star v ⬝ᵥ x) • u - (star u ⬝ᵥ x) • v) := by
  sorry

/-- The rotation by angle zero is the identity. -/
@[simp]
theorem planeRotation_one_zero (u v : n → 𝕜) : planeRotation u v 1 0 = 1 := by
  sorry

/-- The conjugate transpose of a plane rotation is the rotation by the opposite angle. -/
theorem conjTranspose_planeRotation (u v : n → 𝕜) (c s : ℝ) :
    (planeRotation u v c s)ᴴ = planeRotation u v c (-s) := by
  sorry

/-- A plane rotation sends `u` to `c u - s v`, for orthonormal `u`, `v`. -/
theorem planeRotation_mulVec_left {u v : n → 𝕜} (hu : ‖WithLp.toLp 2 u‖ = 1)
    (huv : star u ⬝ᵥ v = 0) (c s : ℝ) :
    planeRotation u v c s *ᵥ u = (c : 𝕜) • u - (s : 𝕜) • v := by
  sorry

/-- A plane rotation sends `v` to `s u + c v`, for orthonormal `u`, `v`. -/
theorem planeRotation_mulVec_right {u v : n → 𝕜} (hv : ‖WithLp.toLp 2 v‖ = 1)
    (huv : star u ⬝ᵥ v = 0) (c s : ℝ) :
    planeRotation u v c s *ᵥ v = (s : 𝕜) • u + (c : 𝕜) • v := by
  sorry

/-- A plane rotation fixes every vector orthogonal to `u` and `v`. -/
theorem planeRotation_mulVec_of_orthogonal {u v x : n → 𝕜} (hux : star u ⬝ᵥ x = 0)
    (hvx : star v ⬝ᵥ x = 0) (c s : ℝ) : planeRotation u v c s *ᵥ x = x := by
  sorry

/-- **A plane rotation is unitary**, for orthonormal `u`, `v` and `c ^ 2 + s ^ 2 = 1`.
Port of `NLAlib.hasOrthonormalCols_planeRotation`, there over `ℝ`. -/
theorem hasOrthonormalCols_planeRotation {u v : n → 𝕜} (hu : ‖WithLp.toLp 2 u‖ = 1)
    (hv : ‖WithLp.toLp 2 v‖ = 1) (huv : star u ⬝ᵥ v = 0) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    HasOrthonormalCols (planeRotation u v c s) := by
  sorry

/-- The rational parametrisation of the circle: `c = (1 - t²) / (1 + t²)` and
`s = 2 t / (1 + t²)` satisfy `c ^ 2 + s ^ 2 = 1`.
Port of `NLAlib.sq_rational_rotation_coefficients`. -/
theorem sq_div_add_sq_div_one_add_sq (t : ℝ) :
    ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 + (2 * t / (1 + t ^ 2)) ^ 2 = 1 := by
  sorry

end NLAlib
