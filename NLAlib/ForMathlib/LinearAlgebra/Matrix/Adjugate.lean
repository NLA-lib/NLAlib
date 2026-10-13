/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Determinants under single-entry updates and reindexing

Facts about `Matrix.det` and `Matrix.adjugate` that Mathlib does not yet have. Upstream
candidates for `Mathlib.LinearAlgebra.Matrix.Adjugate` and
`Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.

## Main results

* `Matrix.det_add_single`: changing one entry of a matrix changes its determinant by the entry's
  cofactor times the change, with no invertibility hypothesis.
* `Matrix.adjugate_apply_self_congr`: a diagonal cofactor depends only on the entries outside its
  row and column.
* `Matrix.det_submatrix_equiv_equiv`: reindexing rows and columns by two different bijections
  changes the determinant by the sign of their relative permutation.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- Adding `a` to the `(i, j)` entry of `A` adds `a` times the `(i, j)` cofactor, which is
`A.adjugate j i`, to the determinant. No invertibility is assumed.
Port of `NLAlib.det_add_single_diagonal`, there over `ℝ` and for a diagonal entry. -/
theorem det_add_single (A : Matrix n n R) (i j : n) (a : R) :
    (A + single i j a).det = A.det + a * A.adjugate j i := by
  sorry

/-- A diagonal cofactor depends only on the entries outside its row and column.
Port of `NLAlib.det_updateCol_single_eq_of_complement_eq`, there over `ℝ`. -/
theorem adjugate_apply_self_congr {A B : Matrix n n R} (i : n)
    (h : ∀ a b, a ≠ i → b ≠ i → A a b = B a b) : A.adjugate i i = B.adjugate i i := by
  sorry

/-- Reindexing the rows by `er` and the columns by `ec` multiplies the determinant by the sign
of the permutation `ec.trans er.symm`. With `er = ec` this is `Matrix.det_submatrix_equiv_self`.
Port of `NLAlib.det_submatrix_equiv_eq_sign_mul`, there over `ℝ`. -/
theorem det_submatrix_equiv_equiv (A : Matrix n n R) (er ec : m ≃ n) :
    (A.submatrix er ec).det = (Equiv.Perm.sign (ec.trans er.symm) : ℤ) * A.det := by
  sorry

end Matrix
