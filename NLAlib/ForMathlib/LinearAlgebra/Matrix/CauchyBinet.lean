/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Order.Hom.PowersetCard

/-!
# The Cauchy–Binet formula and compound matrices

The determinant of a product of rectangular matrices as a sum over maximal square selections,
and the compound matrix of all `k × k` minors with its multiplicativity. Upstream candidate for
`Mathlib.LinearAlgebra.Matrix.Determinant`.

The Cauchy–Binet formula is stated without choosing an enumeration of each index subset: the
term for a subset `s` is the determinant of the product of the two rectangular selections, which
are indexed by `s` itself. `Matrix.det_mul_eq_det_submatrix_mul_det_submatrix` turns such a term
into a product of two minors along any equivalence. Compound matrices need a sign convention, so
they are defined for linearly ordered index types, with minors taken in increasing order.

## Main definitions

* `Matrix.compound k A`: the `k`-th compound matrix of `A`, indexed by `Set.powersetCard`.

## Main results

* `Matrix.det_mul_eq_sum_powersetCard`: the Cauchy–Binet formula.
* `Matrix.det_conjTranspose_mul_self_eq_sum_powersetCard`: a Gram determinant is the sum of the
  Gram determinants of the maximal row selections.
* `Matrix.compound_mul`: compound matrices are multiplicative.
-/

@[expose] public section

open scoped Matrix

namespace Matrix

variable {R : Type*} [CommRing R] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- The determinant of a product `A * B` of an `m × n` and an `n × m` matrix, when `m` and `n`
are in bijection, is the product of the determinants of the two matrices made square along the
bijection. -/
theorem det_mul_eq_det_submatrix_mul_det_submatrix [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R) (B : Matrix n m R) (e : m ≃ n) :
    (A * B).det = (A.submatrix id e).det * (B.submatrix e id).det := by
  sorry

/-- **The Cauchy–Binet formula.** For `A` of size `m × n` and `B` of size `n × m`, the
determinant of `A * B` is the sum, over the subsets `s` of the middle index with as many elements
as `m`, of the determinant of the product of the columns `s` of `A` with the rows `s` of `B`.
When `n` has fewer elements than `m` the sum is empty and the determinant is zero.
[HornJohnson2013, §0.8.7]; stated there with each term as a product of two minors, which is
`Matrix.det_mul_eq_det_submatrix_mul_det_submatrix` applied to an enumeration of `s`. Here over
any commutative ring and any finite index types.
Port of `NLAlib.det_mul_eq_sum_det_submatrix_mul_det_submatrix`.
Result: cauchy-binet -/
theorem det_mul_eq_sum_powersetCard [DecidableEq m] [DecidableEq n] (A : Matrix m n R)
    (B : Matrix n m R) :
    (A * B).det = ∑ s ∈ (Finset.univ : Finset n).powersetCard (Fintype.card m),
      (A.submatrix id (Subtype.val : s → n) * B.submatrix (Subtype.val : s → n) id).det := by
  sorry

/-- A Gram determinant is the sum of the Gram determinants of the maximal row selections:
`det (Aᴴ * A) = ∑ s, det (A_sᴴ * A_s)`, over the sets `s` of rows with as many elements as `A`
has columns. Over `ℝ` or `ℂ` each term is the squared absolute value of a maximal minor.
[HornJohnson2013, §0.8.7]. Port of `NLAlib.det_conjTranspose_mul_self_eq_sum_norm_sq` and
`NLAlib.det_transpose_mul_self_eq_sum_det_sq`.
Result: cauchy-binet -/
theorem det_conjTranspose_mul_self_eq_sum_powersetCard [StarRing R] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n R) :
    (Aᴴ * A).det = ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n),
      ((A.submatrix (Subtype.val : s → m) id)ᴴ * A.submatrix (Subtype.val : s → m) id).det := by
  sorry

section Compound

variable [LinearOrder l] [LinearOrder m] [LinearOrder n]

/-- The `k`-th **compound matrix** of `A`: the matrix of all `k × k` minors of `A`, indexed by the
`k`-element subsets of the row and column index types, each minor taken with its rows and columns
in increasing order. [HornJohnson2013, §0.8.1]. -/
noncomputable def compound (k : ℕ) (A : Matrix m n R) :
    Matrix (Set.powersetCard m k) (Set.powersetCard n k) R :=
  of fun s t =>
    (A.submatrix (fun i => (Set.powersetCard.orderIsoOfFin s i : m))
      (fun j => (Set.powersetCard.orderIsoOfFin t j : n))).det

/-- An entry of the compound matrix is the minor on the two subsets, in increasing order. -/
theorem compound_apply (k : ℕ) (A : Matrix m n R) (s : Set.powersetCard m k)
    (t : Set.powersetCard n k) :
    compound k A s t =
      (A.submatrix (fun i => (Set.powersetCard.orderIsoOfFin s i : m))
        (fun j => (Set.powersetCard.orderIsoOfFin t j : n))).det := by
  sorry

/-- **Multiplicativity of compound matrices.** `compound k (A * B) = compound k A * compound k B`,
the Cauchy–Binet formula for every `k × k` minor of a product.
[HornJohnson2013, §0.8.1 and §0.8.7]. Port of `NLAlib.compoundMatrix_mul`.
Result: cauchy-binet -/
theorem compound_mul (k : ℕ) (A : Matrix l m R) (B : Matrix m n R) :
    compound k (A * B) = compound k A * compound k B := by
  sorry

/-- The compound of the identity is the identity. Port of `NLAlib.compoundMatrix_one`. -/
@[simp]
theorem compound_one (k : ℕ) : compound k (1 : Matrix n n R) = 1 := by
  sorry

/-- Compound matrices commute with transposition. -/
theorem compound_transpose (k : ℕ) (A : Matrix m n R) :
    compound k Aᵀ = (compound k A)ᵀ := by
  sorry

/-- Compound matrices commute with the conjugate transpose.
Port of `NLAlib.compoundMatrix_conjTranspose`. -/
theorem compound_conjTranspose [StarRing R] (k : ℕ) (A : Matrix m n R) :
    compound k Aᴴ = (compound k A)ᴴ := by
  sorry

end Compound

end Matrix
