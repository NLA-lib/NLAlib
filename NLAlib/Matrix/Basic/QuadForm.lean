/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Matrix.Order

/-!
# Quadratic forms and Rayleigh quotients of matrices

`NLAlib.quadForm A z` is the `𝕜`-valued quadratic form `star z ⬝ᵥ (A *ᵥ z)`, the expression in
which Mathlib states positive semidefiniteness. For a Hermitian `A` it is real, and the real
consumers (variational characterisations of eigenvalues, energy norms) take `RCLike.re` of it.
`NLAlib.rayleighQuotient A x` is the real quotient `re (quadForm A x) / ‖x‖ ^ 2`.

## Main definitions

* `NLAlib.quadForm`: the quadratic form `zᴴ A z`.
* `NLAlib.rayleighQuotient`: the Rayleigh quotient `re (xᴴ A x) / ‖x‖²`, zero at `x = 0`.

## Main results

* `NLAlib.posSemidef_iff_quadForm_nonneg`: positive semidefiniteness through `quadForm`.
* `Matrix.IsHermitian.coe_re_quadForm`: the quadratic form of a Hermitian matrix is real.
* `Matrix.IsHermitian.ext_quadForm`: a Hermitian matrix is determined by its quadratic form.
* `NLAlib.re_quadForm_le_re_quadForm_of_le`: monotonicity in the Loewner order.
* `NLAlib.rayleighQuotient_eq_toEuclideanCLM`: the bridge to
  `ContinuousLinearMap.rayleighQuotient`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- The quadratic form `zᴴ A z` of a square matrix, `𝕜`-valued: `star z ⬝ᵥ (A *ᵥ z)`. This is the
expression in Mathlib's dot-product characterisation of `Matrix.PosSemidef`. For Hermitian `A` the
value is real (`Matrix.IsHermitian.coe_re_quadForm`). -/
def quadForm (A : Matrix n n 𝕜) (z : n → 𝕜) : 𝕜 :=
  star z ⬝ᵥ (A *ᵥ z)

/-- `quadForm A z` unfolds to `star z ⬝ᵥ (A *ᵥ z)`. -/
theorem quadForm_def (A : Matrix n n 𝕜) (z : n → 𝕜) : quadForm A z = star z ⬝ᵥ (A *ᵥ z) :=
  rfl

/-- The quadratic form as a double sum over entries. Port of `NLAlib.quadForm_eq_sum_mul_mul`. -/
theorem quadForm_eq_sum (A : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm A z = ∑ i, ∑ j, star (z i) * A i j * z j := by
  sorry

/-! ### Dependence on the matrix -/

/-- The quadratic form of the zero matrix is zero. -/
@[simp]
theorem quadForm_zero_left (z : n → 𝕜) : quadForm (0 : Matrix n n 𝕜) z = 0 := by
  sorry

/-- The quadratic form is additive in the matrix. -/
theorem quadForm_add_left (A B : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm (A + B) z = quadForm A z + quadForm B z := by
  sorry

/-- The quadratic form commutes with subtraction of matrices. -/
theorem quadForm_sub_left (A B : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm (A - B) z = quadForm A z - quadForm B z := by
  sorry

/-- The quadratic form commutes with negation of the matrix. -/
theorem quadForm_neg_left (A : Matrix n n 𝕜) (z : n → 𝕜) : quadForm (-A) z = -quadForm A z := by
  sorry

/-- The quadratic form is homogeneous in the matrix. -/
theorem quadForm_smul_left (c : 𝕜) (A : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm (c • A) z = c * quadForm A z := by
  sorry

/-- The quadratic form of the identity is the squared Euclidean norm. -/
theorem quadForm_one [DecidableEq n] (z : n → 𝕜) :
    quadForm (1 : Matrix n n 𝕜) z = ((‖WithLp.toLp 2 z‖ ^ 2 : ℝ) : 𝕜) := by
  sorry

/-- The quadratic form of a diagonal matrix is the weighted sum of squared moduli. -/
theorem quadForm_diagonal [DecidableEq n] (d : n → 𝕜) (z : n → 𝕜) :
    quadForm (Matrix.diagonal d) z = ∑ i, d i * ((‖z i‖ ^ 2 : ℝ) : 𝕜) := by
  sorry

/-- The quadratic form of the rank-one matrix `b bᴴ` is `|bᴴ z|²`.
Port of `NLAlib.quadForm_vecMulVec_star_self`. -/
theorem quadForm_vecMulVec_star (b z : n → 𝕜) :
    quadForm (Matrix.vecMulVec b (star b)) z = ((‖star b ⬝ᵥ z‖ ^ 2 : ℝ) : 𝕜) := by
  sorry

/-- The quadratic form of a compression `Wᴴ A W` at `v` is that of `A` at `W v`.
Port of `NLAlib.quadForm_conjTranspose_mul_mul`. -/
theorem quadForm_conjTranspose_mul_mul (A : Matrix m m 𝕜) (W : Matrix m n 𝕜) (v : n → 𝕜) :
    quadForm (Wᴴ * A * W) v = quadForm A (W *ᵥ v) := by
  sorry

/-- The quadratic form of a Gram matrix `Aᴴ A` at `z` is `‖A z‖²`.
Port of `NLAlib.quadForm_conjTranspose_mul_self`. -/
theorem quadForm_conjTranspose_mul_self (A : Matrix m n 𝕜) (z : n → 𝕜) :
    quadForm (Aᴴ * A) z = ((‖WithLp.toLp 2 (A *ᵥ z)‖ ^ 2 : ℝ) : 𝕜) := by
  sorry

/-- Conjugating the quadratic form is the quadratic form of the conjugate transpose. -/
theorem star_quadForm (A : Matrix n n 𝕜) (z : n → 𝕜) : star (quadForm A z) = quadForm Aᴴ z := by
  sorry

/-! ### Dependence on the vector -/

/-- The quadratic form vanishes at the zero vector. -/
@[simp]
theorem quadForm_zero_right (A : Matrix n n 𝕜) : quadForm A 0 = 0 := by
  sorry

/-- The quadratic form scales by `|c|²` under scaling of the vector: `star c * c * quadForm A z`.
Port of `NLAlib.quadForm_smul`. -/
theorem quadForm_smul_right (A : Matrix n n 𝕜) (c : 𝕜) (z : n → 𝕜) :
    quadForm A (c • z) = star c * c * quadForm A z := by
  sorry

/-- The quadratic form is even: `quadForm A (-z) = quadForm A z`. -/
@[simp]
theorem quadForm_neg_right (A : Matrix n n 𝕜) (z : n → 𝕜) : quadForm A (-z) = quadForm A z := by
  sorry

/-- The polar expansion of the quadratic form of a sum of vectors. Port of `NLAlib.quadForm_add`. -/
theorem quadForm_add_right (A : Matrix n n 𝕜) (x y : n → 𝕜) :
    quadForm A (x + y) =
      quadForm A x + star x ⬝ᵥ (A *ᵥ y) + star y ⬝ᵥ (A *ᵥ x) + quadForm A y := by
  sorry

/-! ### Hermitian and positive semidefinite matrices -/

/-- The quadratic form of a Hermitian matrix is real: it is the coercion of its real part.
Port of `Matrix.IsHermitian.ofReal_re_quadForm`. -/
theorem _root_.Matrix.IsHermitian.coe_re_quadForm {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (z : n → 𝕜) : (RCLike.re (quadForm A z) : 𝕜) = quadForm A z := by
  sorry

/-- The quadratic form of a Hermitian matrix has zero imaginary part. -/
theorem _root_.Matrix.IsHermitian.im_quadForm {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (z : n → 𝕜) : RCLike.im (quadForm A z) = 0 := by
  sorry

/-- For Hermitian `A`, the two cross terms of the polar expansion are conjugate.
Port of `Matrix.IsHermitian.star_dotProduct_mulVec_comm`. -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_mulVec_comm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x y : n → 𝕜) :
    star y ⬝ᵥ (A *ᵥ x) = star (star x ⬝ᵥ (A *ᵥ y)) := by
  sorry

/-- The real polar expansion for a Hermitian matrix:
`re (quadForm A (x + y)) = re (quadForm A x) + 2 * re (xᴴ A y) + re (quadForm A y)`. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_add {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (x y : n → 𝕜) :
    RCLike.re (quadForm A (x + y)) =
      RCLike.re (quadForm A x) + 2 * RCLike.re (star x ⬝ᵥ (A *ᵥ y)) +
        RCLike.re (quadForm A y) := by
  sorry

/-- **Polarisation.** Two Hermitian matrices with the same quadratic form are equal. -/
theorem _root_.Matrix.IsHermitian.ext_quadForm {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : ∀ z, quadForm A z = quadForm B z) : A = B := by
  sorry

/-- The quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem _root_.Matrix.PosSemidef.quadForm_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (z : n → 𝕜) : 0 ≤ quadForm A z := by
  sorry

/-- The real part of the quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem _root_.Matrix.PosSemidef.re_quadForm_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (z : n → 𝕜) : 0 ≤ RCLike.re (quadForm A z) := by
  sorry

/-- The quadratic form of a positive definite matrix is positive away from zero. -/
theorem _root_.Matrix.PosDef.quadForm_pos {A : Matrix n n 𝕜} (hA : A.PosDef) {z : n → 𝕜}
    (hz : z ≠ 0) : 0 < quadForm A z := by
  sorry

/-- The real part of the quadratic form of a positive definite matrix is positive away from
zero. -/
theorem _root_.Matrix.PosDef.re_quadForm_pos {A : Matrix n n 𝕜} (hA : A.PosDef) {z : n → 𝕜}
    (hz : z ≠ 0) : 0 < RCLike.re (quadForm A z) := by
  sorry

/-- A matrix is positive semidefinite exactly when it is Hermitian with nonnegative quadratic
form. -/
theorem posSemidef_iff_quadForm_nonneg {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ ∀ z, 0 ≤ quadForm A z := by
  sorry

/-- A matrix is positive definite exactly when it is Hermitian with quadratic form positive away
from zero. -/
theorem posDef_iff_quadForm_pos {A : Matrix n n 𝕜} :
    A.PosDef ↔ A.IsHermitian ∧ ∀ z, z ≠ 0 → 0 < quadForm A z := by
  sorry

/-- The quadratic form is monotone in the Loewner order. -/
theorem quadForm_le_quadForm_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) (z : n → 𝕜) :
    quadForm A z ≤ quadForm B z := by
  sorry

/-- The real part of the quadratic form is monotone in the Loewner order. -/
theorem re_quadForm_le_re_quadForm_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) (z : n → 𝕜) :
    RCLike.re (quadForm A z) ≤ RCLike.re (quadForm B z) := by
  sorry

/-- For Hermitian matrices, the Loewner order is the pointwise order of the real quadratic
forms. -/
theorem _root_.Matrix.IsHermitian.le_iff_re_quadForm_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ ∀ z, RCLike.re (quadForm A z) ≤ RCLike.re (quadForm B z) := by
  sorry

/-! ### Rayleigh quotient -/

/-- The **Rayleigh quotient** `re (xᴴ A x) / ‖x‖²` of a square matrix at a vector. Real-valued;
its value at `x = 0` is `0`. For Hermitian `A` nothing is lost by taking the real part. -/
noncomputable def rayleighQuotient (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (quadForm A x) / ‖WithLp.toLp 2 x‖ ^ 2

/-- `rayleighQuotient A x` unfolds to `re (quadForm A x) / ‖x‖ ^ 2`. -/
theorem rayleighQuotient_def (A : Matrix n n 𝕜) (x : n → 𝕜) :
    rayleighQuotient A x = RCLike.re (quadForm A x) / ‖WithLp.toLp 2 x‖ ^ 2 :=
  rfl

/-- The Rayleigh quotient at the zero vector is zero. -/
@[simp]
theorem rayleighQuotient_zero_right (A : Matrix n n 𝕜) : rayleighQuotient A 0 = 0 := by
  sorry

/-- At a unit vector the Rayleigh quotient is the real part of the quadratic form. -/
theorem rayleighQuotient_of_norm_eq_one (A : Matrix n n 𝕜) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) : rayleighQuotient A x = RCLike.re (quadForm A x) := by
  sorry

/-- The Rayleigh quotient is invariant under nonzero scaling of the vector. -/
theorem rayleighQuotient_smul (A : Matrix n n 𝕜) {c : 𝕜} (hc : c ≠ 0) (x : n → 𝕜) :
    rayleighQuotient A (c • x) = rayleighQuotient A x := by
  sorry

/-- The real part of the quadratic form is the Rayleigh quotient times the squared norm. -/
theorem re_quadForm_eq_rayleighQuotient_mul (A : Matrix n n 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm A x) = rayleighQuotient A x * ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

/-- The Rayleigh quotient at an eigenvector is the real part of the eigenvalue. -/
theorem rayleighQuotient_of_mulVec_eq_smul {A : Matrix n n 𝕜} {x : n → 𝕜} {c : 𝕜}
    (h : A *ᵥ x = c • x) (hx : x ≠ 0) : rayleighQuotient A x = RCLike.re c := by
  sorry

/-- The Rayleigh quotient of a matrix is Mathlib's `ContinuousLinearMap.rayleighQuotient` of the
operator it defines on Euclidean space. -/
theorem rayleighQuotient_eq_toEuclideanCLM [DecidableEq n] (A : Matrix n n 𝕜) (x : n → 𝕜) :
    rayleighQuotient A x =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) A).rayleighQuotient (WithLp.toLp 2 x) := by
  sorry

end NLAlib
