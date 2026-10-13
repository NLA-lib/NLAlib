/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import NLAlib.Matrix.Basic.SchurComplement
public import NLAlib.Matrix.Norms.Loewner

/-!
# Positive semidefinite block matrices

Criteria for a Hermitian block matrix `fromBlocks A B Bᴴ C` to be positive semidefinite that do
not need an inverse: the Cauchy–Schwarz test on the off-diagonal block, the factorisation
`B = A^{1/2} X C^{1/2}` with a contraction `X`, and the special cases with identity or equal
diagonal blocks. The Schur complement criteria are in `NLAlib.Matrix.Basic.SchurComplement` and
`NLAlib.Matrix.Pseudoinverse.GeneralizedSchur`.

## Main results

* `Matrix.PosSemidef.norm_sq_star_dotProduct_mulVec_le`: Cauchy–Schwarz for a positive
  semidefinite form.
* `NLAlib.posSemidef_fromBlocks_iff_forall_norm_sq_le`: the bilinear test.
* `NLAlib.posSemidef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt`: the contraction factor.
* `NLAlib.posSemidef_fromBlocks_one_iff_specNorm_le_one`.
* `NLAlib.posSemidef_fromBlocks_self_iff`: equal diagonal blocks.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Cauchy–Schwarz -/

/-- **Cauchy–Schwarz for a positive semidefinite form**: `|xᴴ A y|² ≤ (xᴴ A x) (yᴴ A y)`.
[HornJohnson2013, §7.7].
Port of `NLAlib.sq_bilinear_le_quadForm_mul_of_posSemidef`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.norm_sq_star_dotProduct_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (x y : n → 𝕜) :
    ‖star x ⬝ᵥ A *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm A y) := by
  sorry

/-- The quadratic form of a Hermitian block matrix:
`(x, y)ᴴ [A B; Bᴴ C] (x, y) = xᴴ A x + 2 re (xᴴ B y) + yᴴ C y`, for the real parts.
Port of `NLAlib.quadForm_fromBlocks`, there over `ℝ`. -/
theorem re_quadForm_fromBlocks (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n n 𝕜)
    (x : m → 𝕜) (y : n → 𝕜) :
    RCLike.re (quadForm (Matrix.fromBlocks A B Bᴴ C) (Sum.elim x y)) =
      RCLike.re (quadForm A x) + 2 * RCLike.re (star x ⬝ᵥ B *ᵥ y) +
        RCLike.re (quadForm C y) := by
  sorry

/-! ### The bilinear test -/

/-- If a Hermitian block matrix is positive semidefinite, its off-diagonal block satisfies the
Cauchy–Schwarz bound `|xᴴ B y|² ≤ (xᴴ A x) (yᴴ C y)`.
[HornJohnson2013, Theorem 7.7.7].
Port of `NLAlib.sq_bilinear_le_quadForm_mul_of_fromBlocks_posSemidef`, there over `ℝ`. -/
theorem norm_sq_star_dotProduct_mulVec_le_of_posSemidef_fromBlocks {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef)
    (x : m → 𝕜) (y : n → 𝕜) :
    ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm C y) := by
  sorry

/-- **The bilinear test.** For positive semidefinite `A` and `C`, the block matrix
`fromBlocks A B Bᴴ C` is positive semidefinite exactly when
`|xᴴ B y|² ≤ (xᴴ A x) (yᴴ C y)` for all `x`, `y`.
[HornJohnson2013, Theorem 7.7.7].
Port of `NLAlib.posSemidef_fromBlocks_iff_bilinear_tests`, there over `ℝ`.
Result: block-positivity -/
theorem posSemidef_fromBlocks_iff_forall_norm_sq_le {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      ∀ (x : m → 𝕜) (y : n → 𝕜),
        ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 ≤ RCLike.re (quadForm A x) * RCLike.re (quadForm C y) := by
  sorry

/-! ### Contraction factors -/

/-- `[1 X; Xᴴ 1]` is positive semidefinite exactly when `‖X‖₂ ≤ 1`.
[HornJohnson2013, §7.7].
Port of `NLAlib.posSemidef_identity_fromBlocks_iff_specNorm_le_one`, there over `ℝ`. -/
theorem posSemidef_fromBlocks_one_iff_specNorm_le_one (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks 1 X Xᴴ 1).PosSemidef ↔ specNorm X ≤ 1 := by
  sorry

/-- `[1 X; Xᴴ 1]` is positive definite exactly when `‖X‖₂ < 1`.
Port of `NLAlib.posDef_identity_fromBlocks_iff_specNorm_lt_one`, there over `ℝ`. -/
theorem posDef_fromBlocks_one_iff_specNorm_lt_one (X : Matrix m n 𝕜) :
    (Matrix.fromBlocks 1 X Xᴴ 1).PosDef ↔ specNorm X < 1 := by
  sorry

/-- **The contraction factor.** For positive semidefinite `A` and `C`, the block matrix
`fromBlocks A B Bᴴ C` is positive semidefinite exactly when `B = A^{1/2} X C^{1/2}` for some
contraction `X`.
[HornJohnson2013, Theorem 7.7.9].
Port of `NLAlib.posSemidef_fromBlocks_iff_exists_sqrt_contraction_factor`, there over `ℝ`.
Result: block-positivity -/
theorem posSemidef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt {A : Matrix m m 𝕜}
    {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    (Matrix.fromBlocks A B Bᴴ C).PosSemidef ↔
      ∃ X : Matrix m n 𝕜, specNorm X ≤ 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C := by
  sorry

/-- For positive definite `A` and any `X`, `[A X; Xᴴ Xᴴ A⁻¹ X]` is positive semidefinite.
Port of `NLAlib.fromBlocks_inverse_gram_posSemidef`. -/
theorem posSemidef_fromBlocks_conjTranspose_mul_inv_mul {A : Matrix m m 𝕜} (hA : A.PosDef)
    (X : Matrix m n 𝕜) : (Matrix.fromBlocks A X Xᴴ (Xᴴ * A⁻¹ * X)).PosSemidef := by
  sorry

/-! ### Equal diagonal blocks -/

/-- **Equal diagonal blocks.** `[A B; B A]` is positive semidefinite exactly when `-A ≤ B ≤ A`.
[HornJohnson2013, §7.7].
Port of `NLAlib.posSemidef_equal_diagonal_fromBlocks_iff_le`, there for positive semidefinite `B`
over `ℝ`. -/
theorem posSemidef_fromBlocks_self_iff {A B : Matrix n n 𝕜} :
    (Matrix.fromBlocks A B B A).PosSemidef ↔ -A ≤ B ∧ B ≤ A := by
  sorry

/-- For Hermitian `B`, the bound `-A ≤ B ≤ A` is the quadratic-form bound
`|xᴴ B x| ≤ xᴴ A x`. Port of `NLAlib.abs_quadForm_le_iff_neg_le_and_le`, there over `ℝ`. -/
theorem neg_le_and_le_iff_forall_abs_re_quadForm_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    -A ≤ B ∧ B ≤ A ↔ ∀ x : n → 𝕜, |RCLike.re (quadForm B x)| ≤ RCLike.re (quadForm A x) := by
  sorry

end NLAlib
