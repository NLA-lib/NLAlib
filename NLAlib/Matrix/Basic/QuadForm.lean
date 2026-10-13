/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Matrix.Order
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

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

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype n]

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
  simp only [quadForm, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### Dependence on the matrix -/

/-- The quadratic form of the zero matrix is zero. -/
@[simp]
theorem quadForm_zero_left (z : n → 𝕜) : quadForm (0 : Matrix n n 𝕜) z = 0 := by
  rw [quadForm, Matrix.zero_mulVec, dotProduct_zero]

/-- The quadratic form is additive in the matrix. -/
theorem quadForm_add_left (A B : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm (A + B) z = quadForm A z + quadForm B z := by
  simp only [quadForm, Matrix.add_mulVec, dotProduct_add]

/-- The quadratic form commutes with subtraction of matrices. -/
theorem quadForm_sub_left (A B : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm (A - B) z = quadForm A z - quadForm B z := by
  simp only [quadForm, Matrix.sub_mulVec, dotProduct_sub]

/-- The quadratic form commutes with negation of the matrix. -/
theorem quadForm_neg_left (A : Matrix n n 𝕜) (z : n → 𝕜) : quadForm (-A) z = -quadForm A z := by
  simp only [quadForm, Matrix.neg_mulVec, dotProduct_neg]

/-- The quadratic form is homogeneous in the matrix. -/
theorem quadForm_smul_left (c : 𝕜) (A : Matrix n n 𝕜) (z : n → 𝕜) :
    quadForm (c • A) z = c * quadForm A z := by
  simp only [quadForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The quadratic form of the identity is the squared Euclidean norm. -/
theorem quadForm_one [DecidableEq n] (z : n → 𝕜) :
    quadForm (1 : Matrix n n 𝕜) z = ((‖WithLp.toLp 2 z‖ ^ 2 : ℝ) : 𝕜) := by
  rw [quadForm, Matrix.one_mulVec, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq]

/-- The real quadratic form of a real multiple of the identity, written with the real scalar
action, is that multiple of the squared Euclidean norm. -/
theorem re_quadForm_real_smul_one [DecidableEq n] (a : ℝ) (x : n → 𝕜) :
    RCLike.re (quadForm (a • (1 : Matrix n n 𝕜)) x) = a * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left, quadForm_one,
    RCLike.re_ofReal_mul, RCLike.ofReal_re]

/-- The quadratic form of a diagonal matrix is the weighted sum of squared moduli. -/
theorem quadForm_diagonal [DecidableEq n] (d : n → 𝕜) (z : n → 𝕜) :
    quadForm (Matrix.diagonal d) z = ∑ i, d i * ((‖z i‖ ^ 2 : ℝ) : 𝕜) := by
  simp only [quadForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]

/-- The quadratic form of the rank-one matrix `b bᴴ` is `|bᴴ z|²`.
Port of `NLAlib.quadForm_vecMulVec_star_self`. -/
theorem quadForm_vecMulVec_star (b z : n → 𝕜) :
    quadForm (Matrix.vecMulVec b (star b)) z = ((‖star b ⬝ᵥ z‖ ^ 2 : ℝ) : 𝕜) := by
  rw [quadForm, Matrix.vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul,
    Matrix.star_dotProduct z b, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]

/-- The quadratic form of a compression `Wᴴ A W` at `v` is that of `A` at `W v`.
Port of `NLAlib.quadForm_conjTranspose_mul_mul`. -/
theorem quadForm_conjTranspose_mul_mul [Fintype m] (A : Matrix m m 𝕜) (W : Matrix m n 𝕜)
    (v : n → 𝕜) : quadForm (Wᴴ * A * W) v = quadForm A (W *ᵥ v) := by
  rw [quadForm, quadForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (star v) Wᴴ, Matrix.star_mulVec]

/-- The quadratic form of a Gram matrix `Aᴴ A` at `z` is `‖A z‖²`.
Port of `NLAlib.quadForm_conjTranspose_mul_self`. -/
theorem quadForm_conjTranspose_mul_self [Fintype m] (A : Matrix m n 𝕜) (z : n → 𝕜) :
    quadForm (Aᴴ * A) z = ((‖WithLp.toLp 2 (A *ᵥ z)‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, Matrix.star_mulVec, quadForm,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

/-- Conjugating the quadratic form is the quadratic form of the conjugate transpose. -/
theorem star_quadForm (A : Matrix n n 𝕜) (z : n → 𝕜) : star (quadForm A z) = quadForm Aᴴ z := by
  rw [quadForm, quadForm, Matrix.star_dotProduct, Matrix.star_mulVec, star_star,
    Matrix.dotProduct_mulVec]

/-! ### Dependence on the vector -/

/-- The quadratic form vanishes at the zero vector. -/
@[simp]
theorem quadForm_zero_right (A : Matrix n n 𝕜) : quadForm A 0 = 0 := by
  rw [quadForm, Matrix.mulVec_zero, dotProduct_zero]

/-- The quadratic form scales by `|c|²` under scaling of the vector: `star c * c * quadForm A z`.
Port of `NLAlib.quadForm_smul`. -/
theorem quadForm_smul_right (A : Matrix n n 𝕜) (c : 𝕜) (z : n → 𝕜) :
    quadForm A (c • z) = star c * c * quadForm A z := by
  simp only [quadForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

/-- The quadratic form is even: `quadForm A (-z) = quadForm A z`. -/
@[simp]
theorem quadForm_neg_right (A : Matrix n n 𝕜) (z : n → 𝕜) : quadForm A (-z) = quadForm A z := by
  simp only [quadForm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]

/-- The polar expansion of the quadratic form of a sum of vectors. Port of `NLAlib.quadForm_add`. -/
theorem quadForm_add_right (A : Matrix n n 𝕜) (x y : n → 𝕜) :
    quadForm A (x + y) =
      quadForm A x + star x ⬝ᵥ (A *ᵥ y) + star y ⬝ᵥ (A *ᵥ x) + quadForm A y := by
  simp only [quadForm, star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  ring

/-! ### Hermitian and positive semidefinite matrices -/

omit [Fintype n] in
/-- A real multiple of the identity, written with the real scalar action, is Hermitian. This is
the side condition for comparing a matrix with `a • 1` through
`Matrix.IsHermitian.le_iff_re_quadForm_le`. -/
theorem isHermitian_real_smul_one [DecidableEq n] (a : ℝ) :
    (a • (1 : Matrix n n 𝕜)).IsHermitian :=
  Matrix.isHermitian_one.smul (IsSelfAdjoint.all a)

/-- The quadratic form of a Hermitian matrix is real: it is the coercion of its real part.
Port of `Matrix.IsHermitian.ofReal_re_quadForm`. -/
theorem _root_.Matrix.IsHermitian.coe_re_quadForm {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (z : n → 𝕜) : (RCLike.re (quadForm A z) : 𝕜) = quadForm A z := by
  rw [← RCLike.conj_eq_iff_re, ← RCLike.star_def, star_quadForm, hA.eq]

/-- The quadratic form of a Hermitian matrix has zero imaginary part. -/
theorem _root_.Matrix.IsHermitian.im_quadForm {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (z : n → 𝕜) : RCLike.im (quadForm A z) = 0 := by
  exact hA.im_star_dotProduct_mulVec_self z

/-- For Hermitian `A`, the two cross terms of the polar expansion are conjugate.
Port of `Matrix.IsHermitian.star_dotProduct_mulVec_comm`. -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_mulVec_comm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x y : n → 𝕜) :
    star y ⬝ᵥ (A *ᵥ x) = star (star x ⬝ᵥ (A *ᵥ y)) := by
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, ← Matrix.dotProduct_mulVec,
    hA.eq]

/-- The real polar expansion for a Hermitian matrix:
`re (quadForm A (x + y)) = re (quadForm A x) + 2 * re (xᴴ A y) + re (quadForm A y)`. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_add {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (x y : n → 𝕜) :
    RCLike.re (quadForm A (x + y)) =
      RCLike.re (quadForm A x) + 2 * RCLike.re (star x ⬝ᵥ (A *ᵥ y)) +
        RCLike.re (quadForm A y) := by
  rw [quadForm_add_right, hA.star_dotProduct_mulVec_comm x y]
  simp only [map_add, RCLike.star_def, RCLike.conj_re]
  ring

/-- **Polarisation.** Two Hermitian matrices with the same quadratic form are equal. -/
theorem _root_.Matrix.IsHermitian.ext_quadForm {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : ∀ z, quadForm A z = quadForm B z) : A = B := by
  classical
  rw [← sub_eq_zero]
  have hD : (Matrix.toEuclideanLin (A - B)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (hA.sub hB)
  refine Matrix.toEuclideanLin.map_eq_zero_iff.mp (hD.inner_map_self_eq_zero.mp fun x => ?_)
  have hx : quadForm (A - B) x.ofLp = 0 := by rw [quadForm_sub_left, h, sub_self]
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply,
    dotProduct_comm, Matrix.star_dotProduct, ← quadForm_def, hx, star_zero]

/-- The quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem _root_.Matrix.PosSemidef.quadForm_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (z : n → 𝕜) : 0 ≤ quadForm A z := by
  exact hA.dotProduct_mulVec_nonneg z

/-- The real part of the quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem _root_.Matrix.PosSemidef.re_quadForm_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (z : n → 𝕜) : 0 ≤ RCLike.re (quadForm A z) := by
  exact (RCLike.nonneg_iff.mp (hA.quadForm_nonneg z)).1

/-- The quadratic form of a positive definite matrix is positive away from zero. -/
theorem _root_.Matrix.PosDef.quadForm_pos {A : Matrix n n 𝕜} (hA : A.PosDef) {z : n → 𝕜}
    (hz : z ≠ 0) : 0 < quadForm A z := by
  exact hA.dotProduct_mulVec_pos hz

/-- The real part of the quadratic form of a positive definite matrix is positive away from
zero. -/
theorem _root_.Matrix.PosDef.re_quadForm_pos {A : Matrix n n 𝕜} (hA : A.PosDef) {z : n → 𝕜}
    (hz : z ≠ 0) : 0 < RCLike.re (quadForm A z) := by
  exact (RCLike.pos_iff.mp (hA.quadForm_pos hz)).1

/-- A matrix is positive semidefinite exactly when it is Hermitian with nonnegative quadratic
form. -/
theorem posSemidef_iff_quadForm_nonneg {A : Matrix n n 𝕜} :
    A.PosSemidef ↔ A.IsHermitian ∧ ∀ z, 0 ≤ quadForm A z := by
  exact Matrix.posSemidef_iff_dotProduct_mulVec

/-- A matrix is positive definite exactly when it is Hermitian with quadratic form positive away
from zero. -/
theorem posDef_iff_quadForm_pos {A : Matrix n n 𝕜} :
    A.PosDef ↔ A.IsHermitian ∧ ∀ z, z ≠ 0 → 0 < quadForm A z := by
  exact Matrix.posDef_iff_dotProduct_mulVec

/-- The quadratic form is monotone in the Loewner order. -/
theorem quadForm_le_quadForm_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) (z : n → 𝕜) :
    quadForm A z ≤ quadForm B z := by
  rw [← sub_nonneg, ← quadForm_sub_left]
  exact (Matrix.le_iff.mp h).quadForm_nonneg z

/-- The real part of the quadratic form is monotone in the Loewner order. -/
theorem re_quadForm_le_re_quadForm_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) (z : n → 𝕜) :
    RCLike.re (quadForm A z) ≤ RCLike.re (quadForm B z) := by
  exact (RCLike.le_iff_re_im.mp (quadForm_le_quadForm_of_le h z)).1

/-- For Hermitian matrices, the Loewner order is the pointwise order of the real quadratic
forms. -/
theorem _root_.Matrix.IsHermitian.le_iff_re_quadForm_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ ∀ z, RCLike.re (quadForm A z) ≤ RCLike.re (quadForm B z) := by
  refine ⟨fun h z => re_quadForm_le_re_quadForm_of_le h z, fun h => ?_⟩
  rw [Matrix.le_iff, posSemidef_iff_quadForm_nonneg]
  refine ⟨hB.sub hA, fun z => ?_⟩
  rw [quadForm_sub_left, sub_nonneg, ← hA.coe_re_quadForm, ← hB.coe_re_quadForm,
    RCLike.ofReal_le_ofReal]
  exact h z

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
  rw [rayleighQuotient, quadForm_zero_right, map_zero, zero_div]

/-- At a unit vector the Rayleigh quotient is the real part of the quadratic form. -/
theorem rayleighQuotient_of_norm_eq_one (A : Matrix n n 𝕜) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) : rayleighQuotient A x = RCLike.re (quadForm A x) := by
  rw [rayleighQuotient, hx, one_pow, div_one]

/-- The Rayleigh quotient is invariant under nonzero scaling of the vector. -/
theorem rayleighQuotient_smul (A : Matrix n n 𝕜) {c : 𝕜} (hc : c ≠ 0) (x : n → 𝕜) :
    rayleighQuotient A (c • x) = rayleighQuotient A x := by
  rw [rayleighQuotient, rayleighQuotient, quadForm_smul_right, RCLike.star_def, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, WithLp.toLp_smul, norm_smul, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))

/-- The real part of the quadratic form is the Rayleigh quotient times the squared norm. -/
theorem re_quadForm_eq_rayleighQuotient_mul (A : Matrix n n 𝕜) (x : n → 𝕜) :
    RCLike.re (quadForm A x) = rayleighQuotient A x * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [quadForm_zero_right, rayleighQuotient_zero_right, map_zero, zero_mul]
  · rw [rayleighQuotient, div_mul_cancel₀]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hx))

/-- The Rayleigh quotient at an eigenvector is the real part of the eigenvalue. -/
theorem rayleighQuotient_of_mulVec_eq_smul {A : Matrix n n 𝕜} {x : n → 𝕜} {c : 𝕜}
    (h : A *ᵥ x = c • x) (hx : x ≠ 0) : rayleighQuotient A x = RCLike.re c := by
  have hx' : ‖WithLp.toLp 2 x‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hx))
  rw [rayleighQuotient, quadForm, h, dotProduct_smul, smul_eq_mul,
    EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, RCLike.re_mul_ofReal]
  exact mul_div_cancel_right₀ _ hx'

/-- The Rayleigh quotient of a matrix is Mathlib's `ContinuousLinearMap.rayleighQuotient` of the
operator it defines on Euclidean space. -/
theorem rayleighQuotient_eq_toEuclideanCLM [DecidableEq n] (A : Matrix n n 𝕜) (x : n → 𝕜) :
    rayleighQuotient A x =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) A).rayleighQuotient (WithLp.toLp 2 x) := by
  rw [rayleighQuotient, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, Matrix.toEuclideanCLM_toLp,
    EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct, Matrix.star_dotProduct, RCLike.star_def,
    RCLike.conj_re, quadForm]

end NLAlib
