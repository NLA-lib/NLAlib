/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Matrix.Basic.QuadForm

/-!
# Positive semidefinite block matrices and Schur complements

Criteria for a Hermitian block matrix `fromBlocks A B Bᴴ C` to be positive semidefinite or
positive definite. The Schur complement has no definition: with `A` invertible it is Mathlib's
`C - Bᴴ * A⁻¹ * B`, and in general it is `C - Xᴴ * A * X` for any solution `X` of `A * X = B`,
which does not depend on the solution. Mathlib has the determinant and inverse of a block matrix
and the semidefinite criterion for positive definite `A` (`Matrix.PosSemidef.fromBlocks₁₁`).

## Main results

* `NLAlib.posSemidef_fromBlocks_iff_exists`: Albert's criterion, without the pseudoinverse.
* `NLAlib.quadForm_fromBlocks_eq_add`: completing the square.
* `NLAlib.posDef_fromBlocks_iff`: the positive definite criterion.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- **Completing the square** in a Hermitian block matrix. If `A` is Hermitian and `A * X = B`,
the quadratic form of `fromBlocks A B Bᴴ C` at `(y, x)` is the quadratic form of `A` at
`y + X x` plus the quadratic form of `C - Xᴴ * A * X` at `x`.
Port of `NLAlib.dotProduct_fromBlocks_eq_generalizedSchurComplement_square`, there with
`X = A⁺ B`. -/
theorem quadForm_fromBlocks_eq_add {A : Matrix m m 𝕜} {B X : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hX : A * X = B) (y : m → 𝕜) (x : n → 𝕜) :
    quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim y x) =
      quadForm A (y + X *ᵥ x) + quadForm (C - Xᴴ * A * X) x := by
  sorry

/-- For Hermitian `A`, the matrix `Xᴴ * A * X` is the same for every solution `X` of
`A * X = B`. -/
theorem conjTranspose_mul_mul_eq_of_mul_eq {A : Matrix m m 𝕜} {B X Y : Matrix m n 𝕜}
    (hA : A.IsHermitian) (hX : A * X = B) (hY : A * Y = B) : Xᴴ * A * X = Yᴴ * A * Y := by
  sorry

/-- In a positive semidefinite block matrix, the kernel of the leading block `A` is contained in
the kernel of `Bᴴ`. Port of `NLAlib.conjTranspose_mulVec_eq_zero_of_fromBlocks_posSemidef`. -/
theorem conjTranspose_mulVec_eq_zero_of_posSemidef_fromBlocks {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    {z : m → 𝕜} (hz : A *ᵥ z = 0) : Bᴴ *ᵥ z = 0 := by
  sorry

/-- In a positive semidefinite block matrix, the columns of the off-diagonal block `B` lie in the
column space of the leading block `A`.
Port of `NLAlib.one_sub_mul_moorePenroseInverse_mul_eq_zero_of_fromBlocks_posSemidef`. -/
theorem range_mulVecLin_le_of_posSemidef_fromBlocks {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin := by
  sorry

/-- **Albert's criterion.** The block matrix `fromBlocks A B Bᴴ C` is positive semidefinite
exactly when `A` is, the equation `A * X = B` has a solution, and `C - Xᴴ * A * X` is positive
semidefinite for one such solution (equivalently for all,
`NLAlib.conjTranspose_mul_mul_eq_of_mul_eq`).
[HornJohnson2013, Theorem 7.7.9]; stated there with the pseudoinverse solution `X = A⁺ B` and the
range condition `A A⁺ B = B`, here with any solution, so that no pseudoinverse is needed.
Port of `NLAlib.posSemidef_fromBlocks_iff`.
Result: schur-complement-psd, albert-theorem -/
theorem posSemidef_fromBlocks_iff_exists {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      A.PosSemidef ∧ ∃ X : Matrix m n 𝕜, A * X = B ∧ (C - Xᴴ * A * X).PosSemidef := by
  sorry

/-- If the block matrix is positive semidefinite, then for every solution `X` of `A * X = B` the
Schur complement `C - Xᴴ * A * X` is positive semidefinite.
Port of `NLAlib.generalizedSchurComplement_nonneg`. -/
theorem posSemidef_sub_conjTranspose_mul_mul_of_posSemidef_fromBlocks {A : Matrix m m 𝕜}
    {B X : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (hX : A * X = B) : (C - Xᴴ * A * X).PosSemidef := by
  sorry

/-- **The Schur complement as a partial minimum.** In a positive semidefinite block matrix, with
`A * X = B`, the quadratic form of `C - Xᴴ * A * X` at `x` is a lower bound for the quadratic
form of the block matrix at `(y, x)`, for every `y`. Equality holds at `y = -X x`
(`NLAlib.quadForm_fromBlocks_eq_add`).
Port of `NLAlib.dotProduct_generalizedSchurComplement_mulVec_le`.
Result: schur-complement-variational -/
theorem quadForm_sub_conjTranspose_mul_mul_le {A : Matrix m m 𝕜} {B X : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) (hX : A * X = B)
    (y : m → 𝕜) (x : n → 𝕜) :
    quadForm (C - Xᴴ * A * X) x ≤ quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim y x) := by
  sorry

/-- The Schur complement of a positive semidefinite leading block is below `C` in the Loewner
order. Port of `NLAlib.generalizedSchurComplement_le`. -/
theorem sub_conjTranspose_mul_mul_le {A : Matrix m m 𝕜} (hA : A.PosSemidef) (X : Matrix m n 𝕜)
    (C : Matrix n n 𝕜) : C - Xᴴ * A * X ≤ C := by
  sorry

/-- **Positive definite block matrices.** `fromBlocks A B Bᴴ C` is positive definite exactly when
`A` and the Schur complement `C - Bᴴ * A⁻¹ * B` are.
[HornJohnson2013, Theorem 7.7.7].
Result: schur-complement-pd -/
theorem posDef_fromBlocks_iff [DecidableEq m] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔ A.PosDef ∧ (C - Bᴴ * A⁻¹ * B).PosDef := by
  sorry

end NLAlib
