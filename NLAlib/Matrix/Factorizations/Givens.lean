/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR

/-!
# Givens rotations

The Givens rotation `NLAlib.givens i j c s` acts on the coordinates `i` and `j` by the matrix
`[[c, s], [-s̄, c̄]]` and fixes the others. It is unitary when `|c|² + |s|² = 1`, and for every
vector there is a rotation that clears coordinate `j` into coordinate `i`.

## Main definitions

* `NLAlib.givens`: the rotation in the coordinate plane `(i, j)`.

## Main results

* `NLAlib.hasOrthonormalCols_givens`: unitarity.
* `NLAlib.givens_mulVec_apply_left`, `…_right`, `…_of_ne`: the action on a vector.
* `NLAlib.exists_givens_mulVec_apply_eq_zero`: clearing an entry.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype n] [DecidableEq n]

/-- The **Givens rotation** in the coordinate plane `(i, j)`: the identity outside rows and
columns `i`, `j`, and `[[c, s], [-s̄, c̄]]` on them.
[GolubVanLoan2013, §5.1.8]. Port of `NLAlib.givens`, there over `ℝ`. -/
def givens (i j : n) (c s : 𝕜) : Matrix n n 𝕜 :=
  1 + (c - 1) • Matrix.single i i 1 + (star c - 1) • Matrix.single j j 1 +
    s • Matrix.single i j 1 - star s • Matrix.single j i 1

/-- The trivial rotation is the identity. -/
@[simp]
theorem givens_one_zero (i j : n) : givens i j (1 : 𝕜) 0 = 1 := by
  sorry

/-- Coordinate `i` of a rotated vector. Port of `NLAlib.givens_mulVec_apply_left`. -/
theorem givens_mulVec_apply_left {i j : n} (hij : i ≠ j) (c s : 𝕜) (x : n → 𝕜) :
    (givens i j c s *ᵥ x) i = c * x i + s * x j := by
  sorry

/-- Coordinate `j` of a rotated vector. Port of `NLAlib.givens_mulVec_apply_right`. -/
theorem givens_mulVec_apply_right {i j : n} (hij : i ≠ j) (c s : 𝕜) (x : n → 𝕜) :
    (givens i j c s *ᵥ x) j = -star s * x i + star c * x j := by
  sorry

/-- The other coordinates of a rotated vector are unchanged.
Port of `NLAlib.givens_mulVec_apply_of_ne`. -/
theorem givens_mulVec_apply_of_ne {i j a : n} (hai : a ≠ i) (haj : a ≠ j) (c s : 𝕜)
    (x : n → 𝕜) : (givens i j c s *ᵥ x) a = x a := by
  sorry

/-- Left multiplication by a rotation changes only rows `i` and `j`. -/
theorem givens_mul_apply_of_ne {i j a : n} (hai : a ≠ i) (haj : a ≠ j) (c s : 𝕜)
    (A : Matrix n m 𝕜) (b : m) : (givens i j c s * A) a b = A a b := by
  sorry

/-- Right multiplication by a rotation changes only columns `i` and `j`. -/
theorem mul_givens_apply_of_ne [Fintype m] {i j b : n} (hbi : b ≠ i) (hbj : b ≠ j) (c s : 𝕜)
    (A : Matrix m n 𝕜) (a : m) : (A * givens i j c s) a b = A a b := by
  sorry

/-- The conjugate transpose of a rotation is the inverse rotation.
Port of `NLAlib.transpose_givens`. -/
theorem conjTranspose_givens (i j : n) (c s : 𝕜) :
    (givens i j c s)ᴴ = givens i j (star c) (-s) := by
  sorry

/-- **A Givens rotation is unitary** when `|c|² + |s|² = 1`.
Port of `NLAlib.hasOrthonormalCols_givens`. -/
theorem hasOrthonormalCols_givens {i j : n} (hij : i ≠ j) {c s : 𝕜}
    (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) : HasOrthonormalCols (givens i j c s) := by
  sorry

/-- A unitary Givens rotation times its conjugate transpose is the identity.
Port of `NLAlib.givens_mul_transpose_self`. -/
theorem givens_mul_conjTranspose_self {i j : n} (hij : i ≠ j) {c s : 𝕜}
    (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) : givens i j c s * (givens i j c s)ᴴ = 1 := by
  sorry

/-- The determinant of a unitary Givens rotation is one. -/
theorem det_givens {i j : n} (hij : i ≠ j) {c s : 𝕜} (hcs : ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1) :
    (givens i j c s).det = 1 := by
  sorry

/-- **Clearing an entry.** For every vector `x` and `i ≠ j` there is a unitary Givens rotation
that sends coordinate `j` to zero and coordinate `i` to `√(|x i|² + |x j|²)`.
Port of `NLAlib.givensRotation_transpose_mulVec_apply_right` and `…_left`, there over `ℝ`. -/
theorem exists_givens_mulVec_apply_eq_zero {i j : n} (hij : i ≠ j) (x : n → 𝕜) :
    ∃ c s : 𝕜, ‖c‖ ^ 2 + ‖s‖ ^ 2 = 1 ∧ (givens i j c s *ᵥ x) j = 0 ∧
      (givens i j c s *ᵥ x) i = ((√(‖x i‖ ^ 2 + ‖x j‖ ^ 2) : ℝ) : 𝕜) := by
  sorry

end NLAlib
