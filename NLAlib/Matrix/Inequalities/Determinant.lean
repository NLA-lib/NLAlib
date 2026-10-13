/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Matrix.Basic.SchurComplement

/-!
# Determinant inequalities for positive semidefinite matrices

Hadamard's inequality (in its positive semidefinite form and in its column-norm form), Fischer's
inequality for a block matrix, the Hadamard–Fischer (Koteljanskii) inequality for principal
minors on overlapping index sets, and Minkowski's inequality: `A ↦ (det A)^(1/n)` is concave on
positive definite matrices. Determinants of Hermitian matrices are real; the inequalities are stated for
`RCLike.re (det A)`.

## Main results

* `Matrix.PosSemidef.re_det_le_prod_re_diag`, `NLAlib.norm_det_le_prod_norm_col`: Hadamard.
* `NLAlib.re_det_fromBlocks_le_of_posSemidef`: Fischer.
* `NLAlib.principalMinor`, `NLAlib.sum_principalMinor`: principal minors.
* `Matrix.PosSemidef.re_principalMinor_union_mul_inter_le`: Hadamard–Fischer (Koteljanskii).
* `Matrix.PosDef.re_det_rpow_add_le`, `NLAlib.concaveOn_re_det_rpow`: Minkowski.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Hadamard's inequality -/

/-- **Hadamard's inequality.** The determinant of a positive semidefinite matrix is at most the
product of its diagonal entries.
[HornJohnson2013, Theorem 7.8.1]. Port of `NLAlib.det_le_prod_diag_of_posSemidef`, there over
`ℝ`.
Result: hadamard-determinant-inequality -/
theorem _root_.Matrix.PosSemidef.re_det_le_prod_re_diag {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    RCLike.re A.det ≤ ∏ i, RCLike.re (A i i) := by
  sorry

/-- Equality in Hadamard's inequality for a positive definite matrix holds exactly for diagonal
matrices. [HornJohnson2013, Theorem 7.8.1].
Port of `NLAlib.det_eq_prod_diag_iff_isDiag_of_posDef`, there over `ℝ`. -/
theorem _root_.Matrix.PosDef.re_det_eq_prod_re_diag_iff {A : Matrix n n 𝕜} (hA : A.PosDef) :
    RCLike.re A.det = ∏ i, RCLike.re (A i i) ↔ A.IsDiag := by
  sorry

/-- **Hadamard's inequality, column form.** The modulus of the determinant of a square matrix is
at most the product of the Euclidean norms of its columns.
[HornJohnson2013, Corollary 7.8.3]. Port of `NLAlib.abs_det_le_prod_column_norm`, there over `ℝ`.
Result: hadamard-determinant-inequality -/
theorem norm_det_le_prod_norm_col (B : Matrix n n 𝕜) :
    ‖B.det‖ ≤ ∏ i, ‖WithLp.toLp 2 (B.col i)‖ := by
  sorry

/-! ### Fischer's inequality -/

/-- **Fischer's inequality.** The determinant of a positive semidefinite block matrix is at most
the product of the determinants of its diagonal blocks.
[HornJohnson2013, Theorem 7.8.5].
Port of `NLAlib.det_fromBlocks_le_mul_det_of_posSemidef`, there over `ℝ`.
Result: fischer-inequality -/
theorem re_det_fromBlocks_le_of_posSemidef {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosSemidef) :
    RCLike.re (Matrix.fromBlocks A B Bᴴ C).det ≤ RCLike.re A.det * RCLike.re C.det := by
  sorry

/-- Equality in Fischer's inequality for a positive definite block matrix holds exactly when the
off-diagonal block vanishes.
Port of `NLAlib.det_fromBlocks_eq_mul_det_iff_of_posDef`, there over `ℝ`. -/
theorem re_det_fromBlocks_eq_iff_of_posDef {A : Matrix m m 𝕜} {B : Matrix m n 𝕜}
    {C : Matrix n n 𝕜} (h : (Matrix.fromBlocks A B Bᴴ C).PosDef) :
    RCLike.re (Matrix.fromBlocks A B Bᴴ C).det = RCLike.re A.det * RCLike.re C.det ↔ B = 0 := by
  sorry

/-! ### Principal minors and the Hadamard–Fischer inequality -/

/-- The **principal minor** of a square matrix on an index set: the determinant of the principal
submatrix with rows and columns in `s`. The minor on the empty set is `1`.
[HornJohnson2013, §0.7.1]. Port of `NLAlib.principalMinor`, there for real matrices. -/
def principalMinor {R : Type*} [CommRing R] (A : Matrix n n R) (s : Finset n) : R :=
  (A.submatrix (Subtype.val : ↥s → n) Subtype.val).det

/-- The principal minor on the empty set is one. -/
@[simp]
theorem principalMinor_empty {R : Type*} [CommRing R] (A : Matrix n n R) :
    principalMinor A ∅ = 1 := by
  sorry

/-- The principal minor on a single index is the diagonal entry. -/
@[simp]
theorem principalMinor_singleton {R : Type*} [CommRing R] (A : Matrix n n R) (i : n) :
    principalMinor A {i} = A i i := by
  sorry

/-- The principal minor on all indices is the determinant. -/
@[simp]
theorem principalMinor_univ {R : Type*} [CommRing R] (A : Matrix n n R) :
    principalMinor A Finset.univ = A.det := by
  sorry

/-- **The sum of all principal minors is `det (1 + A)`.** This is the normalising constant of a
determinantal point process with kernel `A`. [HornJohnson2013, §1.2 context]. -/
theorem sum_principalMinor {R : Type*} [CommRing R] (A : Matrix n n R) :
    ∑ s : Finset n, principalMinor A s = (1 + A).det := by
  sorry

/-- The principal minors of a positive semidefinite matrix are nonnegative.
Port of `NLAlib.principalMinor_nonneg`. -/
theorem _root_.Matrix.PosSemidef.re_principalMinor_nonneg {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (s : Finset n) : 0 ≤ RCLike.re (principalMinor A s) := by
  sorry

/-- The principal minors of a positive definite matrix are positive.
Port of `NLAlib.principalMinor_pos`. -/
theorem _root_.Matrix.PosDef.re_principalMinor_pos {A : Matrix n n 𝕜} (hA : A.PosDef)
    (s : Finset n) : 0 < RCLike.re (principalMinor A s) := by
  sorry

/-- **The Hadamard–Fischer inequality** (Koteljanskii). For a positive semidefinite matrix and
index sets `s`, `t`, `A[s ∪ t] · A[s ∩ t] ≤ A[s] · A[t]` for the principal minors.
[HornJohnson2013, Theorem 7.8.9].
Port of `NLAlib.det_principal_union_mul_inter_le_of_posSemidef`, there over `ℝ`.
Result: koteljanskii-inequality -/
theorem _root_.Matrix.PosSemidef.re_principalMinor_union_mul_inter_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (s t : Finset n) :
    RCLike.re (principalMinor A (s ∪ t)) * RCLike.re (principalMinor A (s ∩ t)) ≤
      RCLike.re (principalMinor A s) * RCLike.re (principalMinor A t) := by
  sorry

/-! ### Minkowski's inequality -/

/-- **Minkowski's determinant inequality.** For positive semidefinite `A`, `B` of size `N ≥ 1`,
`(det A)^(1/N) + (det B)^(1/N) ≤ (det (A + B))^(1/N)`.
[HornJohnson2013, Theorem 7.8.21].
Port of `NLAlib.det_rpow_inv_card_add_le`, there over `ℝ` for positive definite matrices.
Result: minkowski-determinant-inequality -/
theorem _root_.Matrix.PosSemidef.re_det_rpow_add_le [Nonempty n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ + RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (A + B).det ^ (Fintype.card n : ℝ)⁻¹ := by
  sorry

/-- `A ↦ (det A)^(1/N)` is concave on the positive definite matrices.
[HornJohnson2013, Theorem 7.8.21]. Port of `NLAlib.concaveOn_det_rpow_inv_card`. -/
theorem concaveOn_re_det_rpow [Nonempty n] :
    ConcaveOn ℝ {A : Matrix n n 𝕜 | A.PosDef}
      fun A => RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ := by
  sorry

/-- The determinant is superadditive on positive semidefinite matrices of positive size:
`det A + det B ≤ det (A + B)`. [HornJohnson2013, §7.8]. -/
theorem _root_.Matrix.PosSemidef.re_det_add_le [Nonempty n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef)
    (hB : B.PosSemidef) : RCLike.re A.det + RCLike.re B.det ≤ RCLike.re (A + B).det := by
  sorry

end NLAlib
