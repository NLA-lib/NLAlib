/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.OperatorMonotone
public import NLAlib.Matrix.Inequalities.Determinant

/-!
# The logarithm of the determinant and the trace of the inverse

For a positive definite matrix, `log det A = tr log A`. The function `A ↦ log det A` is strictly
concave on positive definite matrices, `log det (1 + A) ≤ tr A`, and `A ↦ tr A⁻¹` is strictly
convex. These are the objective functions of D-optimal and A-optimal experimental design and the
potential functions of barrier arguments.

Determinants of Hermitian matrices are written `RCLike.re A.det`.

## Main results

* `Matrix.PosDef.log_re_det_eq_re_trace_cfc_log`: `log det A = tr log A`.
* `Matrix.PosSemidef.log_re_det_one_add_le_re_trace`: `log det (1 + A) ≤ tr A`.
* `NLAlib.strictConcaveOn_log_re_det`: strict concavity of `log det`.
* `NLAlib.strictConvexOn_re_trace_inv`: strict convexity of `tr A⁻¹`.
* `Matrix.PosDef.inv_smul_add_smul_le`: the inverse is operator convex.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive definite matrices form a convex set. Port of `NLAlib.convex_setOf_posDef`. -/
theorem convex_setOf_posDef : Convex ℝ {A : Matrix n n 𝕜 | A.PosDef} := by
  sorry

/-- The positive semidefinite matrices form a convex set. -/
theorem convex_setOf_posSemidef : Convex ℝ {A : Matrix n n 𝕜 | A.PosSemidef} := by
  sorry

/-! ### The determinant through the eigenvalues -/

/-- The determinant of a function of a Hermitian matrix is the product over the eigenvalues. -/
theorem _root_.Matrix.IsHermitian.re_det_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    RCLike.re (cfc f A).det = ∏ i ∈ Finset.range (Fintype.card n), f (eigenvalue A i) := by
  sorry

/-- **`log det A = tr log A`** for positive definite `A`. -/
theorem _root_.Matrix.PosDef.log_re_det_eq_re_trace_cfc_log {A : Matrix n n 𝕜} (hA : A.PosDef) :
    Real.log (RCLike.re A.det) = RCLike.re (cfc Real.log A).trace := by
  sorry

/-- `det (exp A) = exp (tr A)` for Hermitian `A`. -/
theorem _root_.Matrix.IsHermitian.re_det_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re (NormedSpace.exp A).det = Real.exp (RCLike.re A.trace) := by
  sorry

/-- **`log det (1 + A) ≤ tr A`** for positive semidefinite `A`. This is the inequality behind the
elliptical potential lemma and volume-based pivoting arguments. -/
theorem _root_.Matrix.PosSemidef.log_re_det_one_add_le_re_trace {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : Real.log (RCLike.re (1 + A).det) ≤ RCLike.re A.trace := by
  sorry

/-- `1 + tr A ≤ det (1 + A)` for positive semidefinite `A`. -/
theorem _root_.Matrix.PosSemidef.one_add_re_trace_le_re_det_one_add {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : 1 + RCLike.re A.trace ≤ RCLike.re (1 + A).det := by
  sorry

/-! ### Concavity of the logarithm of the determinant -/

/-- **The weighted geometric mean of determinants** is at most the determinant of the weighted
mean: `det A ^ a · det B ^ b ≤ det (a A + b B)` for positive definite `A`, `B` and weights
`a + b = 1`. [HornJohnson2013, Theorem 7.6.6 context].
Port of `NLAlib.det_rpow_mul_le_det_smul_add`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.re_det_rpow_mul_re_det_rpow_le {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    RCLike.re A.det ^ a * RCLike.re B.det ^ b ≤ RCLike.re (a • A + b • B).det := by
  sorry

/-- **`log det` is strictly concave** on the positive definite matrices.
[HornJohnson2013, Theorem 7.6.6]. Port of `NLAlib.strictConcaveOn_log_det`, there over `ℝ`.
Result: log-det-concavity -/
theorem strictConcaveOn_log_re_det :
    StrictConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef} fun A => Real.log (RCLike.re A.det) := by
  sorry

/-- Equality in the concavity of `log det` holds only at `A = B`.
Port of `NLAlib.log_det_smul_add_eq_iff`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.log_re_det_smul_add_smul_eq_iff {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Real.log (RCLike.re (a • A + b • B).det) =
        a * Real.log (RCLike.re A.det) + b * Real.log (RCLike.re B.det) ↔ A = B := by
  sorry

/-! ### The inverse -/

/-- **The inverse is operator convex** on positive definite matrices:
`(a A + b B)⁻¹ ≤ a A⁻¹ + b B⁻¹`. [Bhatia1997, Exercise V.1.15 context]. -/
theorem _root_.Matrix.PosDef.inv_smul_add_smul_le {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A + b • B)⁻¹ ≤ a • A⁻¹ + b • B⁻¹ := by
  sorry

/-- **`tr A⁻¹` is strictly convex** on the positive definite matrices.
Port of `NLAlib.strictConvexOn_trace_inv`, there over `ℝ`.
Result: trace-inverse-convexity -/
theorem strictConvexOn_re_trace_inv :
    StrictConvexOn ℝ {A : Matrix n n 𝕜 | A.PosDef} fun A => RCLike.re A⁻¹.trace := by
  sorry

end NLAlib
