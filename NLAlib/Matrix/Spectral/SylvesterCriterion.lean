/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import NLAlib.Matrix.Spectral.Inertia
public import NLAlib.Matrix.Spectral.Schur

/-!
# Sylvester's criterion and principal minors

A Hermitian matrix is positive definite exactly when its leading principal minors
`principalMinor A (Finset.Iic i)` are positive, and positive semidefinite exactly when all its
principal minors are nonnegative. The coefficients of the characteristic polynomial are the
signed sums of the principal minors of each order, which are the elementary symmetric functions
of the eigenvalues.

## Main results

* `NLAlib.posDef_iff_forall_re_principalMinor_Iic_pos`: Sylvester's criterion.
* `NLAlib.posSemidef_iff_forall_re_principalMinor_nonneg`.
* `NLAlib.charpoly_coeff_eq_sum_principalMinor`: coefficients of the characteristic polynomial.
* `NLAlib.sum_principalMinor_eq_sum_prod_of_charpoly_eq`: elementary symmetric functions of the
  eigenvalues.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Positive definiteness -/

/-- **Sylvester's criterion.** A Hermitian matrix is positive definite exactly when its leading
principal minors are positive. [HornJohnson2013, Theorem 7.2.5].
Port of `NLAlib.posDef_iff_leadingMinor_pos`, there over `ℝ` on `Fin n`.
Result: sylvester-criterion -/
theorem posDef_iff_forall_re_principalMinor_Iic_pos [LinearOrder n] [LocallyFiniteOrderBot n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i, 0 < RCLike.re (principalMinor A (Finset.Iic i)) := by
  sorry

/-- Sylvester's criterion with trailing principal minors.
Port of `NLAlib.posDef_iff_trailingMinor_pos`. -/
theorem posDef_iff_forall_re_principalMinor_Ici_pos [LinearOrder n] [LocallyFiniteOrderTop n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i, 0 < RCLike.re (principalMinor A (Finset.Ici i)) := by
  sorry

/-- A Hermitian matrix with positive proper leading principal minors and nonnegative
determinant is positive semidefinite.
Port of `NLAlib.posSemidef_of_leadingMinor_pos_and_det_nonneg`. -/
theorem posSemidef_of_forall_re_principalMinor_Iio_pos [LinearOrder n]
    [LocallyFiniteOrderBot n] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : ∀ i, 0 < RCLike.re (principalMinor A (Finset.Iio i))) (hdet : 0 ≤ RCLike.re A.det) :
    A.PosSemidef := by
  sorry

/-- **A Hermitian matrix is positive semidefinite exactly when all its principal minors are
nonnegative.** Leading minors do not suffice. [HornJohnson2013, Theorem 7.2.5].
Port of `NLAlib.posSemidef_iff_principal_minors_nonneg`, there over `ℝ`. -/
theorem posSemidef_iff_forall_re_principalMinor_nonneg {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.PosSemidef ↔ ∀ s : Finset n, 0 ≤ RCLike.re (principalMinor A s) := by
  sorry

/-! ### The characteristic polynomial -/

/-- **The coefficients of the characteristic polynomial are signed sums of principal minors**:
the coefficient of `X ^ j` is `(-1) ^ k` times the sum of the principal minors of order `k`,
where `k + j` is the size. [HornJohnson2013, Theorem 1.2.16].
Port of `NLAlib.signed_charpoly_coeff_eq_sum_principal_minors`, there over `ℝ`. -/
theorem charpoly_coeff_eq_sum_principalMinor {R : Type*} [CommRing R] (A : Matrix n n R)
    {k j : ℕ} (h : k + j = Fintype.card n) :
    A.charpoly.coeff j =
      (-1) ^ k * ∑ s ∈ Finset.powersetCard k Finset.univ, principalMinor A s := by
  sorry

/-- **The sum of the principal minors of order `k` is the `k`-th elementary symmetric function
of the eigenvalues.** [HornJohnson2013, Theorem 1.2.16].
Port of `NLAlib.sum_det_principal_minors_eq_sum_prod_of_diagonalization`. -/
theorem sum_principalMinor_eq_sum_prod_of_charpoly_eq {K : Type*} [Field K] {A : Matrix n n K}
    {d : n → K} (hd : A.charpoly = ∏ i, (X - C (d i))) (k : ℕ) :
    ∑ s ∈ Finset.powersetCard k Finset.univ, principalMinor A s =
      ∑ s ∈ Finset.powersetCard k (Finset.univ : Finset n), ∏ i ∈ s, d i := by
  sorry

/-- A Hermitian matrix is positive semidefinite exactly when the coefficients of its
characteristic polynomial alternate in sign.
Port of `NLAlib.posSemidef_iff_signed_charpoly_coeff_nonneg`, there over `ℝ`. -/
theorem posSemidef_iff_forall_re_charpoly_coeff_nonneg {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    A.PosSemidef ↔
      ∀ k j, k + j = Fintype.card n → 0 ≤ (-1) ^ k * RCLike.re (A.charpoly.coeff j) := by
  sorry

end NLAlib
