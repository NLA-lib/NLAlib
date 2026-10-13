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
open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {l m n : Type*}

section CauchyBinet

variable [Fintype m] [Fintype n]

/-- The determinant of a product `A * B` of an `m × n` and an `n × m` matrix, when `m` and `n`
are in bijection, is the product of the determinants of the two matrices made square along the
bijection. -/
theorem det_mul_eq_det_submatrix_mul_det_submatrix [DecidableEq m]
    (A : Matrix m n R) (B : Matrix n m R) (e : m ≃ n) :
    (A * B).det = (A.submatrix id e).det * (B.submatrix e id).det := by
  rw [← det_mul, submatrix_mul_equiv, submatrix_id_id]

private theorem coeff_card_det_one_add_X_smul [DecidableEq m] (M : Matrix m m R) :
    (det (1 + (X : R[X]) • M.map C)).coeff (Fintype.card m) = M.det := by
  rw [coeff_det_one_add_X_smul_eq_sum_minors, ← Finset.card_univ, Finset.powersetCard_self,
    Finset.sum_singleton]
  exact det_submatrix_equiv_self (Equiv.subtypeUnivEquiv Finset.mem_univ) M

/-- **The Cauchy–Binet formula.** For `A` of size `m × n` and `B` of size `n × m`, the
determinant of `A * B` is the sum, over the subsets `s` of the middle index with as many elements
as `m`, of the determinant of the product of the columns `s` of `A` with the rows `s` of `B`.
When `n` has fewer elements than `m` the sum is empty and the determinant is zero.
[HornJohnson2013, §0.8.7]; stated there with each term as a product of two minors, which is
`Matrix.det_mul_eq_det_submatrix_mul_det_submatrix` applied to an enumeration of `s`. Here over
any commutative ring and any finite index types.
Port of `NLAlib.det_mul_eq_sum_det_submatrix_mul_det_submatrix`.
Result: cauchy-binet -/
theorem det_mul_eq_sum_powersetCard [DecidableEq m] (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ s ∈ (Finset.univ : Finset n).powersetCard (Fintype.card m),
      (A.submatrix id (Subtype.val : s → n) * B.submatrix (Subtype.val : s → n) id).det := by
  classical
  have h := congrArg (fun p : R[X] => p.coeff (Fintype.card m))
    (det_one_add_mul_comm ((X : R[X]) • A.map C) (B.map C))
  simp only [smul_mul, Matrix.mul_smul, ← Matrix.map_mul] at h
  rw [coeff_card_det_one_add_X_smul, coeff_det_one_add_X_smul_eq_sum_minors] at h
  rw [h]
  refine Finset.sum_congr rfl fun s hs => ?_
  let e : m ≃ s := Fintype.equivOfCardEq
    ((Fintype.card_coe s).trans (Finset.mem_powersetCard.mp hs).2).symm
  rw [det_mul_eq_det_submatrix_mul_det_submatrix _ _ e, mul_comm, ← det_mul,
    ← submatrix_mul _ _ _ _ _ Function.bijective_id, det_submatrix_equiv_self,
    ← submatrix_mul _ _ _ _ _ Function.bijective_id]

/-- A Gram determinant is the sum of the Gram determinants of the maximal row selections:
`det (Aᴴ * A) = ∑ s, det (A_sᴴ * A_s)`, over the sets `s` of rows with as many elements as `A`
has columns. Over `ℝ` or `ℂ` each term is the squared absolute value of a maximal minor.
[HornJohnson2013, §0.8.7]. Port of `NLAlib.det_conjTranspose_mul_self_eq_sum_norm_sq` and
`NLAlib.det_transpose_mul_self_eq_sum_det_sq`.
Result: cauchy-binet -/
theorem det_conjTranspose_mul_self_eq_sum_powersetCard [StarRing R] [DecidableEq n]
    (A : Matrix m n R) :
    (Aᴴ * A).det = ∑ s ∈ (Finset.univ : Finset m).powersetCard (Fintype.card n),
      ((A.submatrix (Subtype.val : s → m) id)ᴴ * A.submatrix (Subtype.val : s → m) id).det := by
  rw [det_mul_eq_sum_powersetCard]
  simp only [conjTranspose_submatrix]

end CauchyBinet

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
        (fun j => (Set.powersetCard.orderIsoOfFin t j : n))).det :=
  rfl

/-- **Multiplicativity of compound matrices.** `compound k (A * B) = compound k A * compound k B`,
the Cauchy–Binet formula for every `k × k` minor of a product.
[HornJohnson2013, §0.8.1 and §0.8.7]. Port of `NLAlib.compoundMatrix_mul`.
Result: cauchy-binet -/
theorem compound_mul [Fintype m] (k : ℕ) (A : Matrix l m R) (B : Matrix m n R) :
    compound k (A * B) = compound k A * compound k B := by
  ext s t
  rw [mul_apply, compound_apply, submatrix_mul _ _ _ id _ Function.bijective_id,
    det_mul_eq_sum_powersetCard, Fintype.card_fin,
    Finset.sum_subtype (p := (· ∈ Set.powersetCard m k)) _ (fun u => by simp)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [det_mul_eq_det_submatrix_mul_det_submatrix _ _ (Set.powersetCard.orderIsoOfFin u).toEquiv]
  rfl

/-- The compound of the identity is the identity. Port of `NLAlib.compoundMatrix_one`. -/
@[simp]
theorem compound_one (k : ℕ) : compound k (1 : Matrix n n R) = 1 := by
  ext s t
  rw [compound_apply]
  obtain rfl | hst := eq_or_ne s t
  · have h : Function.Injective fun i => (Set.powersetCard.orderIsoOfFin s i : n) :=
      Subtype.val_injective.comp (Set.powersetCard.orderIsoOfFin s).injective
    rw [submatrix_one _ h, det_one, one_apply_eq]
  · obtain ⟨a, has, hat⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne s t).mp hst
    rw [one_apply_ne hst]
    refine det_eq_zero_of_row_eq_zero ((Set.powersetCard.orderIsoOfFin s).symm ⟨a, has⟩)
      fun j => ?_
    rw [submatrix_apply, OrderIso.apply_symm_apply, one_apply_ne]
    rintro rfl
    exact hat (Set.powersetCard.orderIsoOfFin t j).2

/-- Compound matrices commute with transposition. -/
theorem compound_transpose (k : ℕ) (A : Matrix m n R) :
    compound k Aᵀ = (compound k A)ᵀ := by
  ext s t
  rw [transpose_apply, compound_apply, compound_apply, ← transpose_submatrix, det_transpose]

/-- Compound matrices commute with the conjugate transpose.
Port of `NLAlib.compoundMatrix_conjTranspose`. -/
theorem compound_conjTranspose [StarRing R] (k : ℕ) (A : Matrix m n R) :
    compound k Aᴴ = (compound k A)ᴴ := by
  ext s t
  rw [conjTranspose_apply, compound_apply, compound_apply, ← conjTranspose_submatrix,
    det_conjTranspose]

end Compound

end Matrix
