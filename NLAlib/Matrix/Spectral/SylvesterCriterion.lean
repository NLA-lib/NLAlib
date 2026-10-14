/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import NLAlib.Matrix.Spectral.InertiaElimination
public import NLAlib.Matrix.Spectral.Schur

/-!
# Sylvester's criterion and principal minors

A Hermitian matrix is positive definite exactly when its leading principal minors `principalMinor A
(Finset.Iic i)` are positive, and positive semidefinite exactly when all its principal minors are
nonnegative. The coefficients of the characteristic polynomial are the signed sums of the principal
minors of each order (Mathlib's `Matrix.charpoly_coeff_eq_sum_minors` in the vocabulary of
`principalMinor`), which are the elementary symmetric functions of the eigenvalues.

## Main results

* `Matrix.IsHermitian.posDef_iff_forall_re_principalMinor_Iic_pos`: Sylvester's criterion.
* `Matrix.IsHermitian.posSemidef_iff_forall_re_principalMinor_nonneg`.
* `NLAlib.charpoly_coeff_eq_sum_principalMinor`: coefficients of the characteristic polynomial.
* `NLAlib.IsEigenvalueListing.sum_principalMinor_eq`: elementary symmetric functions of the
  eigenvalues.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [DecidableEq n]

/-! ### Positive definiteness -/

/-- **Bordering.** If a principal submatrix with one row and column fewer is positive definite,
the sign of the determinant decides whether the Hermitian matrix is positive definite or
positive semidefinite: by interlacing all eigenvalues but the smallest are positive. -/
private theorem posDef_and_posSemidef_of_posDef_submatrix [Fintype n] {p : Type*} [Fintype p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {s : p → n} (hs : Function.Injective s)
    (hcard : Fintype.card p + 1 = Fintype.card n) (hB : (A.submatrix s s).PosDef) :
    (0 < RCLike.re A.det → A.PosDef) ∧ (0 ≤ RCLike.re A.det → A.PosSemidef) := by
  have hpos : ∀ k < Fintype.card p, 0 < eigenvalue A k := fun k hk =>
    ((hA.submatrix s).posDef_iff_eigenvalue_pos.mp hB k hk).trans_le
      (hA.eigenvalue_submatrix_le hs hk)
  have hdet : RCLike.re A.det =
      (∏ k ∈ Finset.range (Fintype.card p), eigenvalue A k) * eigenvalue A (Fintype.card p) := by
    rw [hA.det_eq_prod_range_eigenvalue, RCLike.ofReal_re, ← hcard, Finset.prod_range_succ]
  have hprod : 0 < ∏ k ∈ Finset.range (Fintype.card p), eigenvalue A k :=
    Finset.prod_pos fun k hk => hpos k (Finset.mem_range.mp hk)
  constructor
  · intro h
    rw [hA.posDef_iff_eigenvalue_pos]
    intro k hk
    rcases Nat.lt_or_ge k (Fintype.card p) with hk' | hk'
    · exact hpos k hk'
    · obtain rfl : k = Fintype.card p := by omega
      rw [hdet] at h
      exact (pos_iff_pos_of_mul_pos h).mp hprod
  · intro h
    rw [hA.posSemidef_iff_eigenvalue_nonneg]
    intro k
    rcases lt_trichotomy k (Fintype.card p) with hk' | rfl | hk'
    · exact (hpos k hk').le
    · rw [hdet] at h
      exact nonneg_of_mul_nonneg_right h hprod
    · exact (eigenvalue_of_card_le A (by omega)).ge

omit [DecidableEq n] in
/-- A nonempty initial segment `Iio i` of a finite linear order is `Iic j` for its largest
element `j`. -/
private theorem exists_Iio_eq_Iic [LinearOrder n] [LocallyFiniteOrderBot n] {i : n}
    (h : (Finset.Iio i).Nonempty) : ∃ j < i, Finset.Iio i = Finset.Iic j := by
  refine ⟨(Finset.Iio i).max' h, Finset.mem_Iio.mp (Finset.max'_mem _ h), ?_⟩
  ext x
  rw [Finset.mem_Iio, Finset.mem_Iic]
  exact ⟨fun hx => Finset.le_max' _ _ (Finset.mem_Iio.mpr hx),
    fun hx => hx.trans_lt (Finset.mem_Iio.mp (Finset.max'_mem _ h))⟩

/-- With positive proper leading principal minors, every proper leading principal submatrix is
positive definite. -/
private theorem posDef_submatrix_Iio [Finite n] [LinearOrder n] [LocallyFiniteOrderBot n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : ∀ i, 0 < RCLike.re (principalMinor A (Finset.Iio i))) (i : n) :
    (A.submatrix (Subtype.val : ↥(Finset.Iio i) → n) Subtype.val).PosDef := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rcases (Finset.Iio i).eq_empty_or_nonempty with hempty | hne
    · refine (hA.submatrix _).posDef_iff_eigenvalue_pos.mpr fun k hk => absurd hk ?_
      rw [Fintype.card_coe, hempty, Finset.card_empty]
      exact Nat.not_lt_zero k
    · obtain ⟨j, hj, hij⟩ := exists_Iio_eq_Iic hne
      have hsub : ∀ x : ↥(Finset.Iio j), x.1 ∈ Finset.Iio i := fun x =>
        Finset.mem_Iio.mpr ((Finset.mem_Iio.mp x.2).trans hj)
      have hcard : Fintype.card ↥(Finset.Iio j) + 1 = Fintype.card ↥(Finset.Iio i) := by
        rw [Fintype.card_coe, Fintype.card_coe, hij, ← Finset.Iio_insert,
          Finset.card_insert_of_notMem Finset.notMem_Iio_self]
      have hB : ((A.submatrix (Subtype.val : ↥(Finset.Iio i) → n) Subtype.val).submatrix
          (fun x : ↥(Finset.Iio j) => (⟨x.1, hsub x⟩ : ↥(Finset.Iio i)))
          fun x => ⟨x.1, hsub x⟩).PosDef := ih j hj
      exact (posDef_and_posSemidef_of_posDef_submatrix (hA.submatrix _)
        (s := fun x : ↥(Finset.Iio j) => (⟨x.1, hsub x⟩ : ↥(Finset.Iio i)))
        (fun x y hxy => Subtype.ext (congrArg (fun z : ↥(Finset.Iio i) => z.1) hxy)) hcard
        hB).1 (h i)

/-- With positive proper leading principal minors, the sign of the determinant decides between
positive definite and positive semidefinite. -/
private theorem posDef_and_posSemidef_of_forall_re_principalMinor_Iio_pos [Fintype n]
    [LinearOrder n] [LocallyFiniteOrderBot n] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : ∀ i, 0 < RCLike.re (principalMinor A (Finset.Iio i))) :
    (0 < RCLike.re A.det → A.PosDef) ∧ (0 ≤ RCLike.re A.det → A.PosSemidef) := by
  cases isEmpty_or_nonempty n
  · have hP : A.PosDef := hA.posDef_iff_eigenvalue_pos.mpr fun k hk =>
      absurd hk (by rw [Fintype.card_eq_zero]; exact Nat.not_lt_zero k)
    exact ⟨fun _ => hP, fun _ => hP.posSemidef⟩
  · have ht : ∀ x : n, x ≤ Finset.univ.max' Finset.univ_nonempty := fun x =>
      Finset.le_max' _ _ (Finset.mem_univ x)
    refine posDef_and_posSemidef_of_posDef_submatrix hA
      (s := (Subtype.val : ↥(Finset.Iio (Finset.univ.max' Finset.univ_nonempty)) → n))
      Subtype.val_injective ?_ (posDef_submatrix_Iio hA h _)
    rw [Fintype.card_coe, ← Finset.card_insert_of_notMem Finset.notMem_Iio_self,
      Finset.Iio_insert, ← Finset.card_univ]
    exact congrArg Finset.card (Finset.eq_univ_of_forall fun x => Finset.mem_Iic.mpr (ht x))

/-- **Sylvester's criterion.** A Hermitian matrix is positive definite exactly when its leading
principal minors are positive. [HornJohnson2013, Theorem 7.2.5].
Port of `NLAlib.posDef_iff_leadingMinor_pos`, there over `ℝ` on `Fin n`.
Result: sylvester-criterion -/
theorem _root_.Matrix.IsHermitian.posDef_iff_forall_re_principalMinor_Iic_pos
    [Finite n] [LinearOrder n] [LocallyFiniteOrderBot n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i, 0 < RCLike.re (principalMinor A (Finset.Iic i)) := by
  cases nonempty_fintype n
  refine ⟨fun h i => h.re_principalMinor_pos _, fun h => ?_⟩
  have hIio : ∀ i, 0 < RCLike.re (principalMinor A (Finset.Iio i)) := fun i => by
    rcases (Finset.Iio i).eq_empty_or_nonempty with hempty | hne
    · rw [hempty, principalMinor_empty, RCLike.one_re]
      exact one_pos
    · obtain ⟨j, -, hij⟩ := exists_Iio_eq_Iic hne
      rw [hij]
      exact h j
  refine (posDef_and_posSemidef_of_forall_re_principalMinor_Iio_pos hA hIio).1 ?_
  cases isEmpty_or_nonempty n
  · rw [Matrix.det_isEmpty, RCLike.one_re]
    exact one_pos
  · have ht : Finset.Iic (Finset.univ.max' (Finset.univ_nonempty (α := n))) = Finset.univ :=
      Finset.eq_univ_of_forall fun x => Finset.mem_Iic.mpr (Finset.le_max' _ _ (Finset.mem_univ x))
    rw [← principalMinor_univ, ← ht]
    exact h _

/-- Sylvester's criterion with trailing principal minors.
Port of `NLAlib.posDef_iff_trailingMinor_pos`. -/
theorem _root_.Matrix.IsHermitian.posDef_iff_forall_re_principalMinor_Ici_pos
    [Finite n] [LinearOrder n] [LocallyFiniteOrderTop n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ i, 0 < RCLike.re (principalMinor A (Finset.Ici i)) := by
  refine ⟨fun h i => h.re_principalMinor_pos _, fun h => ?_⟩
  have hB : (A.submatrix (OrderDual.ofDual : nᵒᵈ → n) OrderDual.ofDual).PosDef := by
    rw [(hA.submatrix _).posDef_iff_forall_re_principalMinor_Iic_pos]
    intro i
    rw [principalMinor, Matrix.submatrix_submatrix, det_submatrix_eq_principalMinor A
      (OrderDual.ofDual.injective.comp Subtype.val_injective)
      (s := Finset.Ici (OrderDual.ofDual i))]
    · exact h _
    · ext x
      simp only [Set.mem_range, Function.comp_apply, Subtype.exists, Finset.mem_Iic,
        Finset.coe_Ici, Set.mem_Ici]
      exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨OrderDual.toDual x, hx, rfl⟩⟩
  exact hB.submatrix (e := (OrderDual.toDual : n → nᵒᵈ)) OrderDual.toDual.injective

/-- A Hermitian matrix with positive proper leading principal minors and nonnegative
determinant is positive semidefinite.
Port of `NLAlib.posSemidef_of_leadingMinor_pos_and_det_nonneg`. -/
theorem _root_.Matrix.IsHermitian.posSemidef_of_forall_re_principalMinor_Iio_pos [Fintype n]
    [LinearOrder n] [LocallyFiniteOrderBot n] {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (h : ∀ i, 0 < RCLike.re (principalMinor A (Finset.Iio i))) (hdet : 0 ≤ RCLike.re A.det) :
    A.PosSemidef :=
  (posDef_and_posSemidef_of_forall_re_principalMinor_Iio_pos hA h).2 hdet

/-! ### The characteristic polynomial -/

/-- **The coefficients of the characteristic polynomial are signed sums of principal minors**:
the coefficient of `X ^ j` is `(-1) ^ k` times the sum of the principal minors of order `k`,
where `k + j` is the size. [HornJohnson2013, Theorem 1.2.16].
Port of `NLAlib.signed_charpoly_coeff_eq_sum_principal_minors`, there over `ℝ`. -/
theorem charpoly_coeff_eq_sum_principalMinor [Fintype n] {R : Type*} [CommRing R] (A : Matrix n n R)
    {k j : ℕ} (h : k + j = Fintype.card n) :
    A.charpoly.coeff j =
      (-1) ^ k * ∑ s ∈ Finset.powersetCard k Finset.univ, principalMinor A s := by
  obtain rfl : j = Fintype.card n - k := by omega
  exact Matrix.charpoly_coeff_eq_sum_minors A k (by omega)

/-- **The sum of the principal minors of order `k` is the `k`-th elementary symmetric function
of the eigenvalues.** [HornJohnson2013, Theorem 1.2.16].
Port of `NLAlib.sum_det_principal_minors_eq_sum_prod_of_diagonalization`. -/
theorem IsEigenvalueListing.sum_principalMinor_eq [Fintype n] {K : Type*} [Field K]
    {A : Matrix n n K} {d : n → K} (hd : IsEigenvalueListing A d) (k : ℕ) :
    ∑ s ∈ Finset.powersetCard k Finset.univ, principalMinor A s =
      ∑ s ∈ Finset.powersetCard k (Finset.univ : Finset n), ∏ i ∈ s, d i := by
  rcases le_or_gt k (Fintype.card n) with hk | hk
  · have h1 := charpoly_coeff_eq_sum_principalMinor A (k := k) (j := Fintype.card n - k)
      (by omega)
    have h2 := charpoly_coeff_eq_sum_principalMinor (Matrix.diagonal d) (k := k)
      (j := Fintype.card n - k) (by omega)
    rw [Matrix.charpoly_diagonal, ← isEigenvalueListing_iff.mp hd, h1] at h2
    refine (((isUnit_one.neg).pow k).mul_left_cancel h2).trans
      (Finset.sum_congr rfl fun s _ => ?_)
    rw [principalMinor, Matrix.submatrix_diagonal _ _ Subtype.val_injective, Matrix.det_diagonal]
    exact Finset.prod_coe_sort s d
  · rw [Finset.powersetCard_eq_empty.mpr (by rwa [Finset.card_univ]), Finset.sum_empty,
      Finset.sum_empty]

/-! ### Positive semidefiniteness -/

/-- The signed coefficients of the characteristic polynomial, as sums of real parts of
principal minors. -/
private theorem neg_one_pow_mul_re_charpoly_coeff [Fintype n] (A : Matrix n n 𝕜) {k j : ℕ}
    (h : k + j = Fintype.card n) :
    (-1) ^ k * RCLike.re (A.charpoly.coeff j) =
      ∑ s ∈ Finset.powersetCard k Finset.univ, RCLike.re (principalMinor A s) := by
  have hre : ∀ z : 𝕜, RCLike.re ((-1) ^ k * z) = (-1) ^ k * RCLike.re z := fun z => by
    rw [← RCLike.ofReal_one, ← RCLike.ofReal_neg, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul]
  rw [charpoly_coeff_eq_sum_principalMinor A h, hre, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_mul, map_sum]

/-- A monic real polynomial of degree `N` whose coefficients have the signs of those of
`(X + 1) ^ N` evaluated at `-X` does not vanish at a negative number. -/
private theorem neg_one_pow_mul_eval_neg_pos {p : ℝ[X]} {N : ℕ} (hdeg : p.natDegree = N)
    (hp : p.Monic) (hcoeff : ∀ k j, k + j = N → 0 ≤ (-1) ^ k * p.coeff j) {t : ℝ}
    (ht : 0 < t) : 0 < (-1) ^ N * p.eval (-t) := by
  have hterm : ∀ k j, k + j = N →
      (-1 : ℝ) ^ N * (p.coeff j * (-t) ^ j) = (-1) ^ k * p.coeff j * t ^ j := by
    intro k j hkj
    have h1 : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [← hkj, pow_add, neg_pow t j]
    linear_combination (-1 : ℝ) ^ k * p.coeff j * t ^ j * h1
  rw [Polynomial.eval_eq_sum_range, hdeg, Finset.mul_sum]
  refine Finset.sum_pos' (fun j hj => ?_) ⟨N, Finset.mem_range.mpr N.lt_succ_self, ?_⟩
  · have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [hterm (N - j) j (by omega)]
    exact mul_nonneg (hcoeff (N - j) j (by omega)) (pow_nonneg ht.le _)
  · rw [hterm 0 N (zero_add N), pow_zero, one_mul, ← hdeg, hp.coeff_natDegree, one_mul]
    exact pow_pos ht _

/-- A Hermitian matrix is positive semidefinite exactly when the coefficients of its
characteristic polynomial alternate in sign.
Port of `NLAlib.posSemidef_iff_signed_charpoly_coeff_nonneg`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.posSemidef_iff_forall_re_charpoly_coeff_nonneg [Fintype n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.PosSemidef ↔
      ∀ k j, k + j = Fintype.card n → 0 ≤ (-1) ^ k * RCLike.re (A.charpoly.coeff j) := by
  constructor
  · intro h k j hkj
    rw [neg_one_pow_mul_re_charpoly_coeff A hkj]
    exact Finset.sum_nonneg fun s _ => h.re_principalMinor_nonneg s
  · intro h
    rw [hA.posSemidef_iff_eigenvalues_nonneg]
    intro i
    by_contra hneg
    have hmap : A.charpoly = (∏ i, (X - C (hA.eigenvalues i))).map (algebraMap ℝ 𝕜) := by
      rw [hA.charpoly_eq, Polynomial.map_prod]
      exact Finset.prod_congr rfl fun i _ => by
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    have hcoeff : ∀ k j, k + j = Fintype.card n →
        0 ≤ (-1) ^ k * (∏ i, (X - C (hA.eigenvalues i))).coeff j := by
      intro k j hkj
      have h1 := h k j hkj
      rwa [hmap, Polynomial.coeff_map, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_re] at h1
    have hdeg : (∏ i, (X - C (hA.eigenvalues i))).natDegree = Fintype.card n := by
      rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ]
    have hpos := neg_one_pow_mul_eval_neg_pos hdeg (Polynomial.monic_prod_X_sub_C _ _) hcoeff
      (neg_pos.mpr (not_le.mp hneg))
    rw [neg_neg, Polynomial.eval_prod,
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self]), mul_zero] at hpos
    exact lt_irrefl _ hpos

/-- **A Hermitian matrix is positive semidefinite exactly when all its principal minors are
nonnegative.** Leading minors do not suffice. [HornJohnson2013, Theorem 7.2.5].
Port of `NLAlib.posSemidef_iff_principal_minors_nonneg`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.posSemidef_iff_forall_re_principalMinor_nonneg [Finite n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ s : Finset n, 0 ≤ RCLike.re (principalMinor A s) := by
  cases nonempty_fintype n
  refine ⟨fun h s => h.re_principalMinor_nonneg s, fun h => ?_⟩
  rw [hA.posSemidef_iff_forall_re_charpoly_coeff_nonneg]
  intro k j hkj
  rw [neg_one_pow_mul_re_charpoly_coeff A hkj]
  exact Finset.sum_nonneg fun s _ => h s

end NLAlib
