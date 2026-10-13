/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Compare

/-!
# Norm bounds as Loewner inequalities

A spectral norm bound on a matrix `T` is a Loewner inequality on its Gram matrix, and for a
Hermitian matrix it is a two-sided Loewner inequality on the matrix itself. These are the forms
in which matrix concentration inequalities conclude and in which a subspace embedding is stated,
so the lemmas here are the bridge between those layers and `specNorm`.

A scalar multiple of the identity in a Loewner inequality is always written with the real scalar
action, `(a : ℝ) • (1 : Matrix n n 𝕜)`.

## Main results

* `NLAlib.conjTranspose_mul_self_le_smul_one_iff`, `NLAlib.smul_one_le_conjTranspose_mul_self_iff`:
  an upper or lower Loewner bound on `Tᴴ * T` is a bound on `‖T x‖ ^ 2` for every `x`.
* `NLAlib.specNorm_sq_le_iff_conjTranspose_mul_self_le`: the upper bound in terms of `specNorm`.
* `NLAlib.mul_specNorm_sq_le_of_smul_one_le`, `NLAlib.mul_frobNorm_sq_le_of_smul_one_le`: a factor
  bounded below cannot shrink a norm by more than its lower bound.
* `Matrix.IsHermitian.specNorm_le_iff`: for Hermitian `A`, `specNorm A ≤ c` iff
  `-(c • 1) ≤ A ≤ c • 1`.
* `Matrix.PosSemidef.specNorm_le_specNorm_of_le`: the spectral norm is monotone on the positive
  semidefinite cone.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Quadratic forms -/

/-- The quadratic form is bounded by the spectral norm: `|zᴴ A z| ≤ specNorm A * ‖z‖ ^ 2`.
Port of `NLAlib.abs_re_star_dotProduct_mulVec_le_specNorm`. -/
theorem norm_quadForm_le (A : Matrix n n 𝕜) (z : n → 𝕜) :
    ‖quadForm A z‖ ≤ specNorm A * ‖WithLp.toLp 2 z‖ ^ 2 := by
  sorry

/-- The real part of the quadratic form is bounded by the spectral norm. -/
theorem abs_re_quadForm_le (A : Matrix n n 𝕜) (z : n → 𝕜) :
    |RCLike.re (quadForm A z)| ≤ specNorm A * ‖WithLp.toLp 2 z‖ ^ 2 := by
  sorry

/-! ### Gram matrices -/

/-- An upper Loewner bound on the Gram matrix of `T` is an upper bound on `‖T x‖ ^ 2`. -/
theorem conjTranspose_mul_self_le_smul_one_iff [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ} :
    Tᴴ * T ≤ a • (1 : Matrix n n 𝕜) ↔
      ∀ x, ‖WithLp.toLp 2 (T *ᵥ x)‖ ^ 2 ≤ a * ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

/-- A lower Loewner bound on the Gram matrix of `T` is a lower bound on `‖T x‖ ^ 2`. This is the
form in which a one-sided subspace embedding is used vector by vector.
Port of the hypothesis of `NLAlib.mul_specNorm_le_specNorm_mul_of_mulVec_sq_le`. -/
theorem smul_one_le_conjTranspose_mul_self_iff [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ} :
    a • (1 : Matrix n n 𝕜) ≤ Tᴴ * T ↔
      ∀ x, a * ‖WithLp.toLp 2 x‖ ^ 2 ≤ ‖WithLp.toLp 2 (T *ᵥ x)‖ ^ 2 := by
  sorry

/-- The squared spectral norm of `T` is at most `a ≥ 0` exactly when `Tᴴ * T ≤ a • 1`. -/
theorem specNorm_sq_le_iff_conjTranspose_mul_self_le [DecidableEq n] {T : Matrix m n 𝕜} {a : ℝ}
    (ha : 0 ≤ a) : specNorm T ^ 2 ≤ a ↔ Tᴴ * T ≤ a • (1 : Matrix n n 𝕜) := by
  sorry

/-- The Gram matrix is below the squared spectral norm times the identity. -/
theorem conjTranspose_mul_self_le_specNorm_sq_smul_one [DecidableEq n] (T : Matrix m n 𝕜) :
    Tᴴ * T ≤ (specNorm T ^ 2) • (1 : Matrix n n 𝕜) := by
  sorry

/-- A factor `T` with `Tᴴ * T ≤ a • 1` enlarges the squared spectral norm by at most `a`. -/
theorem specNorm_mul_sq_le_of_conjTranspose_mul_self_le [DecidableEq m] {T : Matrix l m 𝕜}
    {a : ℝ} (h : Tᴴ * T ≤ a • (1 : Matrix m m 𝕜)) (X : Matrix m n 𝕜) :
    specNorm (T * X) ^ 2 ≤ a * specNorm X ^ 2 := by
  sorry

/-- A factor `T` with `a • 1 ≤ Tᴴ * T` shrinks the squared spectral norm by at most `a`.
Port of `NLAlib.mul_specNorm_le_specNorm_mul_of_mulVec_sq_le`, there over `ℝ` with the
hypothesis as a raw condition on vectors and the bound unsquared. -/
theorem mul_specNorm_sq_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    a * specNorm X ^ 2 ≤ specNorm (T * X) ^ 2 := by
  sorry

/-- A factor `T` with `Tᴴ * T ≤ a • 1` enlarges the squared Frobenius norm by at most `a`. -/
theorem frobNorm_mul_sq_le_of_conjTranspose_mul_self_le [DecidableEq m] {T : Matrix l m 𝕜}
    {a : ℝ} (h : Tᴴ * T ≤ a • (1 : Matrix m m 𝕜)) (X : Matrix m n 𝕜) :
    frobNorm (T * X) ^ 2 ≤ a * frobNorm X ^ 2 := by
  sorry

/-- A factor `T` with `a • 1 ≤ Tᴴ * T` shrinks the squared Frobenius norm by at most `a`.
Port of `NLAlib.mul_frobSq_le_frobSq_mul_of_mulVec_sq_le`. -/
theorem mul_frobNorm_sq_le_of_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {a : ℝ}
    (h : a • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    a * frobNorm X ^ 2 ≤ frobNorm (T * X) ^ 2 := by
  sorry

/-- The unsquared form of `NLAlib.mul_specNorm_sq_le_of_smul_one_le`, for a lower bound written
as a square. -/
theorem mul_specNorm_le_of_sq_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {c : ℝ}
    (hc : 0 ≤ c) (h : (c ^ 2) • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    c * specNorm X ≤ specNorm (T * X) := by
  sorry

/-! ### Hermitian matrices -/

/-- A Hermitian matrix is below its spectral norm times the identity. -/
theorem _root_.Matrix.IsHermitian.le_specNorm_smul_one [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A ≤ specNorm A • (1 : Matrix n n 𝕜) := by
  sorry

/-- A Hermitian matrix is above minus its spectral norm times the identity. -/
theorem _root_.Matrix.IsHermitian.neg_specNorm_smul_one_le [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : -(specNorm A • (1 : Matrix n n 𝕜)) ≤ A := by
  sorry

/-- The upper half of `Matrix.IsHermitian.specNorm_le_iff`. -/
theorem _root_.Matrix.IsHermitian.le_smul_one_of_specNorm_le [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (h : specNorm A ≤ c) : A ≤ c • (1 : Matrix n n 𝕜) := by
  sorry

/-- The lower half of `Matrix.IsHermitian.specNorm_le_iff`. -/
theorem _root_.Matrix.IsHermitian.neg_smul_one_le_of_specNorm_le [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} (h : specNorm A ≤ c) :
    -(c • (1 : Matrix n n 𝕜)) ≤ A := by
  sorry

/-- A Hermitian matrix sandwiched between `-(c • 1)` and `c • 1` has spectral norm at most `c`,
for `c ≥ 0`. This is how a two-sided eigenvalue bound becomes a norm bound. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_of_le_smul_one [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (h₁ : -(c • (1 : Matrix n n 𝕜)) ≤ A)
    (h₂ : A ≤ c • (1 : Matrix n n 𝕜)) : specNorm A ≤ c := by
  sorry

/-- For a Hermitian matrix and `c ≥ 0`, `specNorm A ≤ c` exactly when `-(c • 1) ≤ A ≤ c • 1`.
[HornJohnson2013, §7.7]. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ -(c • (1 : Matrix n n 𝕜)) ≤ A ∧ A ≤ c • (1 : Matrix n n 𝕜) := by
  sorry

/-- For a Hermitian matrix and `c ≥ 0`, `specNorm A ≤ c` exactly when the real quadratic form is
bounded by `c * ‖x‖ ^ 2`. Port of `NLAlib.specNorm_le_iff_abs_dotProduct_mulVec_le`, there over
`ℝ`. -/
theorem _root_.Matrix.IsHermitian.specNorm_le_iff_abs_re_quadForm_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ ∀ x, |RCLike.re (quadForm A x)| ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

/-- The spectral norm of a Hermitian matrix is attained by its quadratic form at a unit vector.
Port of `NLAlib.exists_unit_abs_quadForm_eq_specNorm`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.exists_norm_eq_one_and_abs_re_quadForm_eq_specNorm [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 ∧ |RCLike.re (quadForm A x)| = specNorm A := by
  sorry

/-! ### Positive semidefinite matrices -/

/-- For a positive semidefinite matrix and `c ≥ 0`, `specNorm A ≤ c` exactly when
`A ≤ c • 1`. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ A ≤ c • (1 : Matrix n n 𝕜) := by
  sorry

/-- The spectral norm is monotone on the positive semidefinite cone. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_specNorm_of_le {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≤ B) : specNorm A ≤ specNorm B := by
  sorry

/-- The spectral norm of a positive semidefinite matrix is at most the real part of its
trace. -/
theorem _root_.Matrix.PosSemidef.specNorm_le_re_trace {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    specNorm A ≤ RCLike.re A.trace := by
  sorry

end NLAlib
