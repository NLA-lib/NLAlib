/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Inequalities.Determinant

/-!
# Principal minors of positive semidefinite matrices

For a positive semidefinite matrix, the products of all principal minors
(`NLAlib.principalMinor`) of a given size satisfy Szász's chain of inequalities, which
interpolates between `det A` and Hadamard's bound `∏ A i i`.

## Main results

* `Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase`: a minor against its sub-minors of one
  size less.
* `Matrix.PosSemidef.prod_re_principalMinor_succ_pow_le`: Szász's inequality.
* `NLAlib.principalMinor_erase_univ_eq`: complementary minors and the diagonal of the
  inverse.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Complementary minors and the inverse.** For an invertible matrix, the principal minor on
the complement of an index `i` is `det A · (A⁻¹) i i`.
[HornJohnson2013, §0.8.4]. Port of
`NLAlib.det_principal_complement_singleton_eq_det_mul_inv_diag`. -/
theorem principalMinor_erase_univ_eq {K : Type*} [Field K] {A : Matrix n n K} (hA : IsUnit A)
    (i : n) : principalMinor A (Finset.univ.erase i) = A.det * A⁻¹ i i := by
  sorry

/-- **A minor against its sub-minors.** For a positive semidefinite matrix and a nonempty index
set `t` with `k + 1` elements, `A[t] ^ k ≤ ∏ i ∈ t, A[t \ {i}]`.
[HornJohnson2013, Theorem 7.8.11 (step)].
Port of `NLAlib.principalMinor_pow_pred_le_prod_erase`, there over `ℝ` for positive definite
matrices. -/
theorem _root_.Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {t : Finset n} {k : ℕ} (hk : t.card = k + 1) :
    RCLike.re (principalMinor A t) ^ k ≤ ∏ i ∈ t, RCLike.re (principalMinor A (t.erase i)) := by
  sorry

/-- **Szász's inequality.** Let `P k` be the product of all principal minors of size `k` of a
positive semidefinite matrix of size `N`. Then
`P (k + 1) ^ k ≤ P k ^ (N - k)`, stated with `k + d = N`.
[HornJohnson2013, Theorem 7.8.11].
Port of `NLAlib.principalMinorProduct_succ_pow_le_of_posSemidef`, there over `ℝ`.
Result: szasz-inequality -/
theorem _root_.Matrix.PosSemidef.prod_re_principalMinor_succ_pow_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {k d : ℕ} (hkd : k + d = Fintype.card n) :
    (∏ s ∈ Finset.univ.powersetCard (k + 1), RCLike.re (principalMinor A s)) ^ k ≤
      (∏ s ∈ Finset.univ.powersetCard k, RCLike.re (principalMinor A s)) ^ d := by
  sorry

/-- The case `k + 1 = N` of Szász's inequality: `det A ^ (N - 1) ≤ ∏ i, A[univ \ {i}]`.
[HornJohnson2013, Theorem 7.8.11].
Port of `NLAlib.det_pow_card_pred_le_prod_complement_singleton`. -/
theorem _root_.Matrix.PosSemidef.re_det_pow_le_prod_re_principalMinor_erase {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    RCLike.re A.det ^ k ≤ ∏ i, RCLike.re (principalMinor A (Finset.univ.erase i)) := by
  sorry

end NLAlib
