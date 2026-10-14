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
interpolates between `det A` and Hadamard's bound `∏ A i i`. The determinant of a compression
`Vᴴ * A * V` by a matrix with orthonormal columns, of which a principal minor is the case of a
coordinate selection, is at most the product of the leading eigenvalues.

## Main results

* `Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase`: a minor against its sub-minors of one
  size less.
* `Matrix.PosSemidef.prod_re_principalMinor_succ_pow_le`: Szász's inequality.
* `NLAlib.principalMinor_erase_univ_eq_adjugate`, `NLAlib.principalMinor_erase_univ_eq`:
  complementary minors as the diagonal of the adjugate and of the inverse.
* `Matrix.PosSemidef.re_det_conjTranspose_mul_mul_le_prod_range_eigenvalue`: the determinant of a
  compression against the leading eigenvalues.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **A complementary minor is a diagonal entry of the adjugate.** Over any commutative ring, the
principal minor on the complement of an index `i` is `A.adjugate i i`.
[HornJohnson2013, §0.8.2]. -/
theorem principalMinor_erase_univ_eq_adjugate {R : Type*} [CommRing R] (A : Matrix n n R)
    (i : n) : principalMinor A (Finset.univ.erase i) = A.adjugate i i := by
  rw [Matrix.adjugate_apply, principalMinor, ← Matrix.det_piecewise_one_eq_submatrix_det]
  congr 1
  ext a b
  by_cases ha : a = i
  · subst ha
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · simp [ha]

/-- **Complementary minors and the inverse.** For an invertible matrix, the principal minor on
the complement of an index `i` is `det A · (A⁻¹) i i`.
[HornJohnson2013, §0.8.4]. Port of
`NLAlib.det_principal_complement_singleton_eq_det_mul_inv_diag`. -/
theorem principalMinor_erase_univ_eq {K : Type*} [Field K] {A : Matrix n n K} (hA : IsUnit A)
    (i : n) : principalMinor A (Finset.univ.erase i) = A.det * A⁻¹ i i := by
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hdet, one_mul, principalMinor_erase_univ_eq_adjugate]

/-- The case of the whole index set of `Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase`,
for a positive definite matrix: Hadamard's inequality for the inverse. -/
private theorem re_det_pow_le_prod_erase_of_posDef {A : Matrix n n 𝕜} (hA : A.PosDef) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    RCLike.re A.det ^ k ≤ ∏ i, RCLike.re (principalMinor A (Finset.univ.erase i)) := by
  have hd : 0 < RCLike.re A.det := (RCLike.pos_iff.mp hA.det_pos).1
  have hinv : RCLike.re A⁻¹.det = (RCLike.re A.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hA.isHermitian.det_eq_re_det,
      ← RCLike.ofReal_inv, RCLike.ofReal_re, RCLike.ofReal_re]
  have hterm (i : n) : RCLike.re (principalMinor A (Finset.univ.erase i)) =
      RCLike.re A.det * RCLike.re (A⁻¹ i i) := by
    rw [principalMinor_erase_univ_eq hA.isUnit, hA.isHermitian.det_eq_re_det,
      RCLike.re_ofReal_mul, RCLike.ofReal_re]
  simp only [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hk]
  calc RCLike.re A.det ^ k = RCLike.re A.det ^ (k + 1) * RCLike.re A⁻¹.det := by
        rw [hinv, pow_succ, mul_assoc, mul_inv_cancel₀ hd.ne', mul_one]
    _ ≤ RCLike.re A.det ^ (k + 1) * ∏ i, RCLike.re (A⁻¹ i i) :=
        mul_le_mul_of_nonneg_left hA.inv.posSemidef.re_det_le_prod_re_diag (pow_pos hd _).le

/-- The case of the whole index set of `Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase`,
by continuity from the positive definite case. -/
private theorem re_det_pow_le_prod_erase {A : Matrix n n 𝕜} (hA : A.PosSemidef) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    RCLike.re A.det ^ k ≤ ∏ i, RCLike.re (principalMinor A (Finset.univ.erase i)) :=
  Matrix.PosSemidef.le_of_forall_posDef_le
    (f := fun A : Matrix n n 𝕜 => RCLike.re A.det ^ k)
    (g := fun A : Matrix n n 𝕜 => ∏ i, RCLike.re
      (A.submatrix (Subtype.val : ↥(Finset.univ.erase i) → n) Subtype.val).det)
    (by fun_prop) (by fun_prop) (fun _ hM => re_det_pow_le_prod_erase_of_posDef hM hk) hA

omit [Fintype n] in
/-- **A minor against its sub-minors.** For a positive semidefinite matrix and a nonempty index
set `t` with `k + 1` elements, `A[t] ^ k ≤ ∏ i ∈ t, A[t \ {i}]`.
[HornJohnson2013, Theorem 7.8.11 (step)].
Port of `NLAlib.principalMinor_pow_pred_le_prod_erase`, there over `ℝ` for positive definite
matrices. -/
theorem _root_.Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {t : Finset n} {k : ℕ} (hk : t.card = k + 1) :
    RCLike.re (principalMinor A t) ^ k ≤ ∏ i ∈ t, RCLike.re (principalMinor A (t.erase i)) := by
  have h := re_det_pow_le_prod_erase (hA.submatrix (Subtype.val : ↥t → n)) (k := k)
    (by rw [Fintype.card_coe, hk])
  have he (i : ↥t) : principalMinor (A.submatrix (Subtype.val : ↥t → n) Subtype.val)
      (Finset.univ.erase i) = principalMinor A (t.erase i) := by
    rw [principalMinor, Matrix.submatrix_submatrix]
    refine det_submatrix_eq_principalMinor A
      (Subtype.val_injective.comp Subtype.val_injective) (Set.ext fun x => ?_)
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff,
      Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y.2, fun h => (Finset.mem_erase.mp hy).1 (Subtype.ext h)⟩
    · rintro ⟨hxt, hx⟩
      exact ⟨⟨⟨x, hxt⟩, by simpa [Subtype.ext_iff] using hx⟩, rfl⟩
  simp only [he] at h
  rw [Finset.prod_coe_sort t fun i => RCLike.re (principalMinor A (t.erase i))] at h
  exact h

/-- Multiplying a function over every one-element deletion of every subset with `k + 1`
elements counts each subset with `k` elements once for each element outside it. -/
private theorem prod_powersetCard_prod_erase {M : Type*} [CommMonoid M] (f : Finset n → M)
    {k d : ℕ} (hkd : k + d = Fintype.card n) :
    ∏ t ∈ Finset.univ.powersetCard (k + 1), ∏ i ∈ t, f (t.erase i) =
      (∏ s ∈ Finset.univ.powersetCard k, f s) ^ d := by
  have hprod : ∏ u ∈ (Finset.univ.powersetCard (k + 1)).sigma (fun t : Finset n => t),
      f (u.1.erase u.2) =
      ∏ v ∈ (Finset.univ.powersetCard k).sigma (fun s : Finset n => Finset.univ \ s), f v.1 := by
    refine Finset.prod_bij' (fun u _ => ⟨u.1.erase u.2, u.2⟩)
      (fun v _ => ⟨insert v.2 v.1, v.2⟩) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨ht, hi⟩ := Finset.mem_sigma.mp hu
      have hcard := (Finset.mem_powersetCard.mp ht).2
      refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · rw [Finset.card_erase_of_mem hi, hcard, Nat.add_sub_cancel]
      · simp
    · intro v hv
      obtain ⟨hs, hi⟩ := Finset.mem_sigma.mp hv
      have hcard := (Finset.mem_powersetCard.mp hs).2
      have hnot : v.2 ∉ v.1 := (Finset.mem_sdiff.mp hi).2
      refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
        Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hnot, hcard]
    · intro u hu
      exact Sigma.ext (Finset.insert_erase (Finset.mem_sigma.mp hu).2) HEq.rfl
    · intro v hv
      exact Sigma.ext
        (Finset.erase_insert (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hv).2).2) HEq.rfl
    · intro u _
      rfl
  rw [Finset.prod_sigma', hprod, Finset.prod_sigma, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun s hs => ?_
  change ∏ _i ∈ Finset.univ \ s, f s = _
  rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ,
    (Finset.mem_powersetCard.mp hs).2, ← hkd, Nat.add_sub_cancel_left]

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
  rw [← Finset.prod_pow, ← prod_powersetCard_prod_erase _ hkd]
  exact Finset.prod_le_prod (fun s _ => pow_nonneg (hA.re_principalMinor_nonneg s) k)
    fun s hs => hA.re_principalMinor_pow_le_prod_erase (Finset.mem_powersetCard.mp hs).2

/-- The case `k + 1 = N` of Szász's inequality: `det A ^ (N - 1) ≤ ∏ i, A[univ \ {i}]`.
[HornJohnson2013, Theorem 7.8.11].
Port of `NLAlib.det_pow_card_pred_le_prod_complement_singleton`. -/
theorem _root_.Matrix.PosSemidef.re_det_pow_le_prod_re_principalMinor_erase {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    RCLike.re A.det ^ k ≤ ∏ i, RCLike.re (principalMinor A (Finset.univ.erase i)) :=
  re_det_pow_le_prod_erase hA hk

/-! ### Compressions -/

omit [DecidableEq n] in
/-- **The determinant of a compression is at most the product of the leading eigenvalues.** For
positive semidefinite `A` and `V` with orthonormal columns indexed by `p`,
`det (Vᴴ A V) ≤ λ_0(A) ⋯ λ_{card p - 1}(A)`, eigenvalues non-increasing. With no columns both
sides are `1`.
[HornJohnson2013, Corollary 4.3.37]; a consequence of the Poincaré separation theorem.
Port of `NLAlib.det_transpose_mul_mul_le_prod_eigenvalues₀`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.re_det_conjTranspose_mul_mul_le_prod_range_eigenvalue
    {p : Type*} [Fintype p] [DecidableEq p] {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {V : Matrix n p 𝕜} (hV : HasOrthonormalCols V) :
    RCLike.re (Vᴴ * A * V).det ≤ ∏ i ∈ Finset.range (Fintype.card p), eigenvalue A i := by
  have hB : (Vᴴ * A * V).PosSemidef := hA.conjTranspose_mul_mul_same V
  rw [hB.isHermitian.det_eq_prod_range_eigenvalue, RCLike.ofReal_re]
  exact Finset.prod_le_prod (fun i _ => hB.eigenvalue_nonneg i) fun i hi =>
    hA.isHermitian.eigenvalue_conjTranspose_mul_mul_le hV (Finset.mem_range.mp hi)

end NLAlib
