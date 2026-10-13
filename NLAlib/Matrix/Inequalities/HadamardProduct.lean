/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.Hadamard
public import NLAlib.Matrix.Inequalities.Determinant

/-!
# Inequalities for the Hadamard product

Mathlib has the Schur product theorem (`Matrix.PosSemidef.hadamard`). This file adds what follows
from it: monotonicity of the Hadamard product in the Loewner order, lower bounds for its smallest
eigenvalue, the bound of its spectral norm, the inequality between the inverse of a Hadamard
product and the Hadamard product of the inverses, and Oppenheim's determinant inequality.

## Main results

* `Matrix.PosSemidef.hadamard_le_hadamard_of_le`: monotonicity.
* `Matrix.PosSemidef.smul_diagonal_le_hadamard`: a lower bound from a lower bound of one factor.
* `NLAlib.specNorm_hadamard_le`: `‖A ⊙ B‖₂ ≤ ‖A‖₂ ‖B‖₂`.
* `Matrix.PosDef.inv_hadamard_le_hadamard_inv`, `Matrix.PosDef.one_le_hadamard_inv`.
* `Matrix.PosSemidef.re_det_mul_prod_re_diag_le_re_det_hadamard`: Oppenheim's inequality.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-! ### Norms -/

/-- **The spectral norm is submultiplicative for the Hadamard product**:
`‖A ⊙ B‖₂ ≤ ‖A‖₂ ‖B‖₂`. [HornJohnson1991, Theorem 5.5.1]. -/
theorem specNorm_hadamard_le (A B : Matrix m n 𝕜) :
    specNorm (A ⊙ B) ≤ specNorm A * specNorm B := by
  sorry

/-- The Frobenius norm is submultiplicative for the Hadamard product. -/
theorem frobNorm_hadamard_le (A B : Matrix m n 𝕜) :
    frobNorm (A ⊙ B) ≤ frobNorm A * frobNorm B := by
  sorry

/-! ### Order -/

/-- **The Hadamard product with a positive semidefinite matrix is monotone.**
[HornJohnson1991, §5.2]. Port of `NLAlib.hadamard_le_hadamard_of_posSemidef_left`, there over
`ℝ`. -/
theorem _root_.Matrix.PosSemidef.hadamard_le_hadamard_of_le {A B C : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : B ≤ C) : A ⊙ B ≤ A ⊙ C := by
  sorry

/-- A two-sided bound is preserved by Hadamard products, upper half: if `-A ≤ B ≤ A` and
`-C ≤ D ≤ C` then `B ⊙ D ≤ A ⊙ C`.
Port of `NLAlib.hadamard_le_hadamard_of_neg_le_of_le`, there over `ℝ`. -/
theorem hadamard_le_hadamard_of_neg_le_of_le {A B C D : Matrix n n 𝕜} (hAB : -A ≤ B)
    (hBA : B ≤ A) (hCD : -C ≤ D) (hDC : D ≤ C) : B ⊙ D ≤ A ⊙ C := by
  sorry

/-- A two-sided bound is preserved by Hadamard products, lower half: `-(A ⊙ C) ≤ B ⊙ D`.
Port of `NLAlib.neg_hadamard_le_hadamard_of_neg_le_of_le`, there over `ℝ`. -/
theorem neg_hadamard_le_hadamard_of_neg_le_of_le {A B C D : Matrix n n 𝕜} (hAB : -A ≤ B)
    (hBA : B ≤ A) (hCD : -C ≤ D) (hDC : D ≤ C) : -(A ⊙ C) ≤ B ⊙ D := by
  sorry

/-- **A lower bound for a Hadamard product.** If `a • 1 ≤ A` and `B` is positive semidefinite,
then `a • diagonal (diag B) ≤ A ⊙ B`. In particular the smallest eigenvalue of `A ⊙ B` is at
least `λ_min(A) · min_i B i i`. [HornJohnson1991, Theorem 5.3.4]. -/
theorem _root_.Matrix.PosSemidef.smul_diagonal_le_hadamard {A B : Matrix n n 𝕜} {a : ℝ}
    (hB : B.PosSemidef) (hA : a • (1 : Matrix n n 𝕜) ≤ A) :
    a • Matrix.diagonal (fun i => B i i) ≤ A ⊙ B := by
  sorry

/-- The upper companion: if `A ≤ b • 1` and `B` is positive semidefinite then
`A ⊙ B ≤ b • diagonal (diag B)`. -/
theorem _root_.Matrix.PosSemidef.hadamard_le_smul_diagonal {A B : Matrix n n 𝕜} {b : ℝ}
    (hB : B.PosSemidef) (hA : A ≤ b • (1 : Matrix n n 𝕜)) :
    A ⊙ B ≤ b • Matrix.diagonal (fun i => B i i) := by
  sorry

/-- The Hadamard product of a positive definite matrix with a positive semidefinite matrix with
positive diagonal is positive definite. [HornJohnson1991, Theorem 5.2.1].
Port of `NLAlib.posDef_hadamard_of_posDef_of_diag_pos`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.hadamard_of_forall_diag_pos {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosSemidef) (hdiag : ∀ i, 0 < RCLike.re (B i i)) : (A ⊙ B).PosDef := by
  sorry

/-! ### Inverses -/

/-- **The inverse of a Hadamard product is at most the Hadamard product of the inverses.**
[HornJohnson1991, Theorem 5.4.3 context].
Port of `NLAlib.inv_hadamard_le_hadamard_inv`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.inv_hadamard_le_hadamard_inv {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosDef) : (A ⊙ B)⁻¹ ≤ A⁻¹ ⊙ B⁻¹ := by
  sorry

/-- **Fiedler's inequality**: `1 ≤ A ⊙ A⁻¹` for positive definite `A`.
[HornJohnson1991, Theorem 5.4.3]. Port of `NLAlib.one_le_hadamard_inv`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.one_le_hadamard_inv {A : Matrix n n 𝕜} (hA : A.PosDef) :
    1 ≤ A ⊙ A⁻¹ := by
  sorry

/-! ### Determinants -/

/-- **Oppenheim's inequality**: `det A · ∏ B i i ≤ det (A ⊙ B)` for positive semidefinite `A`,
`B`. [HornJohnson2013, Theorem 7.8.16].
Port of `NLAlib.det_mul_prod_diag_le_det_hadamard`, there over `ℝ`.
Result: oppenheim-inequality -/
theorem _root_.Matrix.PosSemidef.re_det_mul_prod_re_diag_le_re_det_hadamard {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det * ∏ i, RCLike.re (B i i) ≤ RCLike.re (A ⊙ B).det := by
  sorry

/-- The determinant of a Hadamard product dominates the product of the determinants:
`det A · det B ≤ det (A ⊙ B)`. [HornJohnson2013, Theorem 7.8.16]. -/
theorem _root_.Matrix.PosSemidef.re_det_mul_re_det_le_re_det_hadamard {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det * RCLike.re B.det ≤ RCLike.re (A ⊙ B).det := by
  sorry

end NLAlib
