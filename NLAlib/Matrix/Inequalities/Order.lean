/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.Weyl
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Consequences of the Loewner order

Monotonicity of the trace, the determinant and the inverse in the Loewner order, with their
equality cases; invariance of the order under congruence; compressions of inverses; spectral
equivalence `a • M ≤ A ≤ b • M`, which is how the quality of a preconditioner `M` is stated, with
its consequence for the condition number of the preconditioned matrix and its description through
the spectrum of `M⁻¹ * A` (the generalized eigenvalues of the pair).

## Main results

* `NLAlib.re_trace_le_re_trace_of_le`, `NLAlib.eq_of_le_of_re_trace_eq`.
* `Matrix.PosSemidef.re_det_le_re_det_of_le`, `Matrix.PosDef.eq_of_le_of_det_eq`.
* `NLAlib.conjTranspose_mul_mul_le_conjTranspose_mul_mul_iff`: congruence by an invertible matrix.
* `Matrix.PosDef.inv_le_inv_of_le`: the inverse is order-reversing.
* `Matrix.PosDef.inv_conjTranspose_mul_mul_le`: the inverse of a compression.
* `NLAlib.conditionNumber_conjTranspose_mul_mul_le_div`: the condition number of a preconditioned
  matrix.
* `Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset`: spectral equivalence through the
  generalized eigenvalues.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Trace and determinant -/

/-- The trace is monotone in the Loewner order. Port of `NLAlib.trace_le_of_le`. -/
theorem re_trace_le_re_trace_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) :
    RCLike.re A.trace ≤ RCLike.re B.trace := by
  sorry

/-- Loewner-ordered matrices with the same trace are equal.
Port of `NLAlib.trace_eq_iff_of_le`. -/
theorem eq_of_le_of_re_trace_eq {A B : Matrix n n 𝕜} (h : A ≤ B)
    (ht : RCLike.re A.trace = RCLike.re B.trace) : A = B := by
  sorry

/-- The determinant of a Hermitian matrix is real. -/
theorem _root_.Matrix.IsHermitian.det_eq_re_det {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.det = ((RCLike.re A.det : ℝ) : 𝕜) := by
  sorry

/-- **The determinant is monotone on positive semidefinite matrices.**
[HornJohnson2013, Corollary 7.7.4]. Port of `NLAlib.det_le_det_of_posSemidef_le`. -/
theorem _root_.Matrix.PosSemidef.re_det_le_re_det_of_le {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≤ B) : RCLike.re A.det ≤ RCLike.re B.det := by
  sorry

/-- Equality in the monotonicity of the determinant: if `B ≤ A` with `A` positive definite, `B`
positive semidefinite and `det B = det A`, then `B = A`.
[HornJohnson2013, Corollary 7.7.4]. Port of `NLAlib.det_eq_iff_eq_of_posSemidef_le_posDef`. -/
theorem _root_.Matrix.PosDef.eq_of_le_of_det_eq {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosSemidef) (h : B ≤ A) (hdet : B.det = A.det) : B = A := by
  sorry

/-! ### Congruence and inverses -/

/-- **Congruence by an invertible matrix preserves and reflects the Loewner order.**
Port of `NLAlib.congruence_le_congruence_iff`. -/
theorem conjTranspose_mul_mul_le_conjTranspose_mul_mul_iff {A B S : Matrix n n 𝕜}
    (hS : IsUnit S) : Sᴴ * A * S ≤ Sᴴ * B * S ↔ A ≤ B := by
  sorry

/-- **The inverse is order-reversing** on positive definite matrices.
[HornJohnson2013, Corollary 7.7.4]. -/
theorem _root_.Matrix.PosDef.inv_le_inv_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  sorry

/-- The inverse of a positive definite matrix is bounded by the reciprocal of a lower bound:
`a • 1 ≤ A` with `0 < a` gives `A⁻¹ ≤ a⁻¹ • 1`. -/
theorem inv_le_inv_smul_one_of_smul_one_le {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (h : a • (1 : Matrix n n 𝕜) ≤ A) : A⁻¹ ≤ a⁻¹ • (1 : Matrix n n 𝕜) := by
  sorry

/-- **The inverse of a compression is at most the compression of the inverse**:
`(Vᴴ A V)⁻¹ ≤ Vᴴ A⁻¹ V` for positive definite `A` and `V` with orthonormal columns.
[HornJohnson2013, Theorem 7.7.8 context].
Port of `NLAlib.inv_compression_le_compression_inv`. -/
theorem _root_.Matrix.PosDef.inv_conjTranspose_mul_mul_le {A : Matrix m m 𝕜} (hA : A.PosDef)
    {V : Matrix m n 𝕜} (hV : HasOrthonormalCols V) : (Vᴴ * A * V)⁻¹ ≤ Vᴴ * A⁻¹ * V := by
  sorry

/-- The inverse of a principal submatrix is at most the principal submatrix of the inverse.
[HornJohnson2013, Theorem 7.7.8]. Port of `NLAlib.inv_submatrix_le_submatrix_inv`. -/
theorem _root_.Matrix.PosDef.inv_submatrix_le {A : Matrix m m 𝕜} (hA : A.PosDef) {f : n → m}
    (hf : Function.Injective f) : (A.submatrix f f)⁻¹ ≤ A⁻¹.submatrix f f := by
  sorry

/-! ### Comparison with the identity -/

/-- A positive semidefinite matrix is at most the identity exactly when its spectral norm is at
most one. Port of `NLAlib.le_one_iff_specNorm_le_one_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.le_one_iff_specNorm_le_one {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : A ≤ 1 ↔ specNorm A ≤ 1 := by
  sorry

/-- For positive semidefinite `A`, `1 - A` is positive definite exactly when `‖A‖₂ < 1`.
Port of `NLAlib.posDef_one_sub_iff_specNorm_lt_one_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.posDef_one_sub_iff_specNorm_lt_one {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : (1 - A).PosDef ↔ specNorm A < 1 := by
  sorry

/-! ### Spectral equivalence -/

/-- A Hermitian matrix between `a • 1` and `b • 1` with `0 < a` has condition number at most
`b / a`. -/
theorem conditionNumber_le_div_of_smul_one_le_of_le_smul_one {A : Matrix n n 𝕜} {a b : ℝ}
    (ha : 0 < a) (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) :
    conditionNumber A ≤ b / a := by
  sorry

/-- **Spectral equivalence, lower half, after a change of variables.** If `Cᴴ * M * C = 1`
(for instance `C = M^{-1/2}`, or the inverse of a Cholesky factor), then `a • M ≤ A` exactly when
`a • 1 ≤ Cᴴ * A * C`. -/
theorem smul_le_iff_smul_one_le_conjTranspose_mul_mul {A M C : Matrix n n 𝕜}
    (hC : Cᴴ * M * C = 1) {a : ℝ} : a • M ≤ A ↔ a • (1 : Matrix n n 𝕜) ≤ Cᴴ * A * C := by
  sorry

/-- Spectral equivalence, upper half, after a change of variables: if `Cᴴ * M * C = 1`, then
`A ≤ b • M` exactly when `Cᴴ * A * C ≤ b • 1`. -/
theorem le_smul_iff_conjTranspose_mul_mul_le_smul_one {A M C : Matrix n n 𝕜}
    (hC : Cᴴ * M * C = 1) {b : ℝ} : A ≤ b • M ↔ Cᴴ * A * C ≤ b • (1 : Matrix n n 𝕜) := by
  sorry

/-- **The condition number of a preconditioned matrix.** If `a • M ≤ A ≤ b • M` with `0 < a` and
`Cᴴ * M * C = 1`, the symmetrically preconditioned matrix `Cᴴ * A * C` has condition number at
most `b / a`. This is the statement that conjugate gradient rates consume.
Result: preconditioned-condition-number -/
theorem conditionNumber_conjTranspose_mul_mul_le_div {A M C : Matrix n n 𝕜}
    (hC : Cᴴ * M * C = 1) {a b : ℝ} (ha : 0 < a) (h₁ : a • M ≤ A) (h₂ : A ≤ b • M) :
    conditionNumber (Cᴴ * A * C) ≤ b / a := by
  sorry

/-! ### Generalized eigenvalues -/

/-- **Spectral equivalence through generalized eigenvalues.** For positive definite `A` and
Hermitian `B`, `a • A ≤ B ≤ b • A` exactly when the spectrum of `A⁻¹ * B` lies in `[a, b]`.
[HornJohnson2013, Theorem 7.6.4 context].
Port of `NLAlib.loewner_sandwich_iff_relative_spectrum_subset`, there over `ℝ`.
Result: relative-spectrum -/
theorem _root_.Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) (a b : ℝ) :
    a • A ≤ B ∧ B ≤ b • A ↔ spectrum ℝ (A⁻¹ * B) ⊆ Set.Icc a b := by
  sorry

/-- The upper half: `B ≤ b • A` exactly when the spectrum of `A⁻¹ * B` is at most `b`.
Port of `NLAlib.le_smul_iff_relative_spectrum_upper`. -/
theorem _root_.Matrix.PosDef.le_smul_iff_forall_spectrum_le {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) (b : ℝ) :
    B ≤ b • A ↔ ∀ z ∈ spectrum ℝ (A⁻¹ * B), z ≤ b := by
  sorry

/-- The lower half: `a • A ≤ B` exactly when the spectrum of `A⁻¹ * B` is at least `a`.
Port of `NLAlib.smul_le_iff_relative_spectrum_lower`. -/
theorem _root_.Matrix.PosDef.smul_le_iff_forall_le_spectrum {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) (a : ℝ) :
    a • A ≤ B ↔ ∀ z ∈ spectrum ℝ (A⁻¹ * B), a ≤ z := by
  sorry

/-- The generalized eigenvalues of a positive definite pair are real: the spectrum of
`A⁻¹ * B` over `𝕜` consists of real numbers when `A` is positive definite and `B` Hermitian. -/
theorem _root_.Matrix.PosDef.spectrum_inv_mul_subset_range_ofReal {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    spectrum 𝕜 (A⁻¹ * B) ⊆ Set.range (fun r : ℝ => (r : 𝕜)) := by
  sorry

/-- `B² ≤ A²` exactly when `‖B A⁻¹‖₂ ≤ 1`, for positive definite `A` and Hermitian `B`.
Port of `NLAlib.sq_le_sq_iff_relative_specNorm_le_one`. -/
theorem _root_.Matrix.PosDef.sq_le_sq_iff_specNorm_mul_inv_le_one {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) : B ^ 2 ≤ A ^ 2 ↔ specNorm (B * A⁻¹) ≤ 1 := by
  sorry

end NLAlib
