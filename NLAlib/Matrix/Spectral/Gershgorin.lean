/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import NLAlib.Matrix.Spectral.Schur

/-!
# Gershgorin discs and diagonal dominance

Mathlib has Gershgorin's circle theorem (`eigenvalue_mem_ball`) and the nonsingularity of strictly
diagonally dominant matrices (`det_ne_zero_of_sum_row_lt_diag`). This file states the circle
theorem for the spectrum, by rows and by columns, and its consequences: a Hermitian diagonally
dominant matrix with positive diagonal is positive definite, a matrix whose diagonal dominates
in real part has its eigenvalues in the right half plane, an irreducibly diagonally dominant
matrix is nonsingular (Taussky), and a union of discs disjoint from the others contains as many
eigenvalues as discs.

The off-diagonal row sum is `gershgorinRadius A i`, as in Mathlib.

## Main definitions

* `NLAlib.gershgorinRadius`: the off-diagonal row sum.

## Main results

* `NLAlib.exists_norm_sub_le_sum_of_mem_spectrum`: the circle theorem for the spectrum.
* `Matrix.IsHermitian.posDef_of_forall_sum_lt_re`: diagonal dominance gives positive
  definiteness.
* `NLAlib.re_pos_of_mem_spectrum_of_forall_sum_lt_re`.
* `NLAlib.det_ne_zero_of_isIrreducible_of_forall_sum_le`: Taussky's theorem.
* `NLAlib.card_roots_charpoly_filter_mem_iUnion_closedBall`: counting eigenvalues in a union of
  discs.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **Gershgorin radius** of row `i`: the sum of the moduli of the off-diagonal entries of
the row. The radius of column `j` is `gershgorinRadius Aᵀ j`. [HornJohnson2013, §6.1].
Port of `NLAlib.gershgorinRowRadius`. -/
def gershgorinRadius (A : Matrix n n 𝕜) (i : n) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, ‖A i j‖

/-- The Gershgorin radius unfolded, in the spelling of Mathlib's `eigenvalue_mem_ball`. -/
theorem gershgorinRadius_def (A : Matrix n n 𝕜) (i : n) :
    gershgorinRadius A i = ∑ j ∈ Finset.univ.erase i, ‖A i j‖ :=
  rfl

/-- The Gershgorin radius is nonnegative. Port of `NLAlib.gershgorinRowRadius_nonneg`. -/
theorem gershgorinRadius_nonneg (A : Matrix n n 𝕜) (i : n) : 0 ≤ gershgorinRadius A i :=
  Finset.sum_nonneg fun j _ => norm_nonneg (A i j)

/-! ### The circle theorem -/

/-- **Gershgorin's circle theorem**, by rows: every eigenvalue lies in a disc centred at a
diagonal entry with radius the off-diagonal row sum. [HornJohnson2013, Theorem 6.1.1].
Port of `NLAlib.exists_mem_gershgorinRowDisc_of_mem_spectrum`. -/
theorem exists_norm_sub_le_sum_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ i, ‖μ - A i i‖ ≤ gershgorinRadius A i := by
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hμ
  exact ⟨i, mem_closedBall_iff_norm.mp hi⟩

/-- Gershgorin's circle theorem, by columns.
Port of `NLAlib.exists_mem_gershgorinColumnDisc_of_mem_spectrum`. -/
theorem exists_norm_sub_le_sum_col_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ j, ‖μ - A j j‖ ≤ gershgorinRadius Aᵀ j := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, ← Matrix.charpoly_transpose,
    ← Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ
  exact exists_norm_sub_le_sum_of_mem_spectrum hμ

/-- Every eigenvalue is at most a row sum in absolute value.
Port of `NLAlib.exists_norm_le_row_sum_of_mem_spectrum`. -/
theorem exists_norm_le_sum_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ i, ‖μ‖ ≤ ∑ j, ‖A i j‖ := by
  obtain ⟨i, hi⟩ := exists_norm_sub_le_sum_of_mem_spectrum hμ
  refine ⟨i, ?_⟩
  calc ‖μ‖ = ‖(μ - A i i) + A i i‖ := by rw [sub_add_cancel]
    _ ≤ ‖μ - A i i‖ + ‖A i i‖ := norm_add_le _ _
    _ ≤ gershgorinRadius A i + ‖A i i‖ := by gcongr
    _ = ∑ j, ‖A i j‖ := Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- Every eigenvalue is at most a weighted row sum in absolute value, for any positive weights.
[HornJohnson2013, Corollary 6.1.6].
Port of `NLAlib.spectralRadius_le_max_weighted_row_sum`. -/
theorem exists_norm_le_weighted_sum_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) {p : n → ℝ} (hp : ∀ i, 0 < p i) :
    ∃ i, ‖μ‖ ≤ (p i)⁻¹ * ∑ j, p j * ‖A i j‖ := by
  have hpi : ∀ i, ((p i : ℝ) : 𝕜) ≠ 0 := fun i => RCLike.ofReal_ne_zero.mpr (hp i).ne'
  have hHD : Matrix.diagonal (fun i => ((p i : ℝ) : 𝕜)⁻¹) *
      Matrix.diagonal (fun i => ((p i : ℝ) : 𝕜)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [inv_mul_cancel₀ (hpi _), Matrix.diagonal_one]
  have hμ' : μ ∈ spectrum 𝕜 (Matrix.diagonal (fun i => ((p i : ℝ) : 𝕜)⁻¹) * A *
      Matrix.diagonal (fun i => ((p i : ℝ) : 𝕜))) := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      mul_eq_one_comm.mp hHD, Matrix.one_mul, ← Matrix.mem_spectrum_iff_isRoot_charpoly]
    exact hμ
  obtain ⟨i, hi⟩ := exists_norm_le_sum_of_mem_spectrum hμ'
  refine ⟨i, hi.trans_eq ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, norm_inv, RCLike.norm_ofReal,
    RCLike.norm_ofReal, abs_of_pos (hp i), abs_of_pos (hp j)]
  ring

/-! ### Diagonal dominance -/

/-- Every eigenvalue has real part at least the real part of a diagonal entry minus the radius
of its row. -/
private theorem exists_re_sub_le_re_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : ∃ i, RCLike.re (A i i) - gershgorinRadius A i ≤ RCLike.re μ := by
  obtain ⟨i, hi⟩ := exists_norm_sub_le_sum_of_mem_spectrum hμ
  refine ⟨i, ?_⟩
  have h := (RCLike.re_le_norm (A i i - μ)).trans ((norm_sub_rev _ _).trans_le hi)
  rw [map_sub] at h
  linarith

/-- Every eigenvalue of a Hermitian matrix is at least a diagonal entry minus the radius of its
row. -/
private theorem exists_re_sub_le_eigenvalue {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k < Fintype.card n) :
    ∃ i, RCLike.re (A i i) - gershgorinRadius A i ≤ eigenvalue A k := by
  have h := spectrum.algebraMap_mem 𝕜 (hA.eigenvalue_mem_spectrum hk)
  obtain ⟨i, hi⟩ := exists_re_sub_le_re_of_mem_spectrum h
  exact ⟨i, by simpa using hi⟩

/-- **A Hermitian strictly diagonally dominant matrix with positive diagonal is positive
definite.** [HornJohnson2013, Theorem 6.1.10].
Port of `NLAlib.posDef_of_isHermitian_of_row_radius_lt_diag`, there over `ℝ`. -/
theorem _root_.Matrix.IsHermitian.posDef_of_forall_sum_lt_re {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ i, gershgorinRadius A i < RCLike.re (A i i)) :
    A.PosDef := by
  rw [hA.posDef_iff_eigenvalue_pos]
  intro k hk
  obtain ⟨i, hi⟩ := exists_re_sub_le_eigenvalue hA hk
  linarith [h i]

/-- A Hermitian weakly diagonally dominant matrix with nonnegative diagonal is positive
semidefinite. -/
theorem _root_.Matrix.IsHermitian.posSemidef_of_forall_sum_le_re {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (h : ∀ i, gershgorinRadius A i ≤ RCLike.re (A i i)) :
    A.PosSemidef := by
  rw [hA.posSemidef_iff_eigenvalue_nonneg]
  intro k
  rcases lt_or_ge k (Fintype.card n) with hk | hk
  · obtain ⟨i, hi⟩ := exists_re_sub_le_eigenvalue hA hk
    linarith [h i]
  · rw [eigenvalue_of_card_le A hk]

/-- **A matrix whose diagonal dominates in real part has its eigenvalues in the open right half
plane.** [HornJohnson2013, Theorem 6.1.10].
Port of `NLAlib.re_pos_of_mem_spectrum_of_row_radius_lt_re_diag`. -/
theorem re_pos_of_mem_spectrum_of_forall_sum_lt_re {A : Matrix n n 𝕜}
    (h : ∀ i, gershgorinRadius A i < RCLike.re (A i i)) {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : 0 < RCLike.re μ := by
  obtain ⟨i, hi⟩ := exists_re_sub_le_re_of_mem_spectrum hμ
  linarith [h i]

/-- At a coordinate of a null vector, the diagonal term is at most the weighted sum of the
off-diagonal terms. -/
private theorem norm_mul_norm_le_sum_of_mulVec_eq_zero {A : Matrix n n 𝕜} {v : n → 𝕜}
    (hv : A *ᵥ v = 0) (i : n) :
    ‖A i i‖ * ‖v i‖ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖ * ‖v j‖ := by
  have hsum : ∑ j ∈ Finset.univ.erase i, A i j * v j = -(A i i * v i) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    have hrow : ∑ j, A i j * v j = 0 := congrFun hv i
    rw [hrow, zero_sub]
  calc ‖A i i‖ * ‖v i‖ = ‖-(A i i * v i)‖ := by rw [norm_neg, norm_mul]
    _ = ‖∑ j ∈ Finset.univ.erase i, A i j * v j‖ := congrArg norm hsum.symm
    _ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j * v j‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul]

/-- Under weak diagonal dominance, the largest modulus of a coordinate of a null vector
propagates along every nonzero entry of the matrix. -/
private theorem norm_eq_of_mulVec_eq_zero_of_apply_ne_zero {A : Matrix n n 𝕜} {v : n → 𝕜}
    {M : ℝ} (hv : A *ᵥ v = 0) (hweak : ∀ i, gershgorinRadius A i ≤ ‖A i i‖)
    (hmax : ∀ i, ‖v i‖ ≤ M) {i j : n} (hi : ‖v i‖ = M) (hij : A i j ≠ 0) : ‖v j‖ = M := by
  by_cases heq : j = i
  · rw [heq, hi]
  have hM : 0 ≤ M := hi ▸ norm_nonneg (v i)
  have hbound := norm_mul_norm_le_sum_of_mulVec_eq_zero hv i
  rw [hi] at hbound
  have hsum : ∑ k ∈ Finset.univ.erase i, ‖A i k‖ * ‖v k‖ =
      ∑ k ∈ Finset.univ.erase i, ‖A i k‖ * M := by
    refine le_antisymm (Finset.sum_le_sum fun k _ => by gcongr; exact hmax k) ?_
    rw [← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (hweak i) hM).trans hbound
  have hzero : ∑ k ∈ Finset.univ.erase i, ‖A i k‖ * (M - ‖v k‖) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← hsum, sub_self]
  have hterm : ‖A i j‖ * (M - ‖v j‖) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (norm_nonneg _) (sub_nonneg.mpr (hmax k))).mp hzero j
        (Finset.mem_erase.mpr ⟨heq, Finset.mem_univ _⟩)
  linarith [(mul_eq_zero.mp hterm).resolve_left (norm_ne_zero_iff.mpr hij)]

/-- **Taussky's theorem.** An irreducible weakly diagonally dominant matrix with one strictly
dominant row is nonsingular. [HornJohnson2013, Corollary 6.2.27].
Port of `NLAlib.det_ne_zero_of_irreducible_weak_diagonal_dominance`. -/
theorem det_ne_zero_of_isIrreducible_of_forall_sum_le {A : Matrix n n 𝕜}
    (hI : (A.map fun x => ‖x‖).IsIrreducible)
    (hweak : ∀ i, gershgorinRadius A i ≤ ‖A i i‖)
    (hstrict : ∃ i, gershgorinRadius A i < ‖A i i‖) : A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨s, hs⟩ := hstrict
  have : Nonempty n := ⟨s⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => ‖v i‖
  have hmax : ∀ j, ‖v j‖ ≤ ‖v i‖ := fun j =>
    hi ▸ Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ j)
  have hpos : 0 < ‖v i‖ := by
    by_contra! h
    exact hvne (funext fun j => norm_le_zero_iff.mp ((hmax j).trans h))
  let _ : Quiver n := Matrix.toQuiver (A.map fun x => ‖x‖)
  obtain ⟨p, -⟩ := hI.connected i s
  have hpath : ∀ {j : n} (_ : Quiver.Path i j), ‖v j‖ = ‖v i‖ := by
    intro j q
    induction q with
    | nil => rfl
    | cons q e ih =>
      exact norm_eq_of_mulVec_eq_zero_of_apply_ne_zero hAv hweak hmax ih
        (norm_pos_iff.mp e.down)
  have hbound := norm_mul_norm_le_sum_of_mulVec_eq_zero hAv s
  rw [hpath p] at hbound
  have hsum : ∑ j ∈ Finset.univ.erase s, ‖A s j‖ * ‖v j‖ ≤ gershgorinRadius A s * ‖v i‖ := by
    rw [gershgorinRadius, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by gcongr; exact hmax j
  exact (hbound.trans hsum).not_gt (mul_lt_mul_of_pos_right hs hpos)

/-- A Hermitian irreducible weakly diagonally dominant matrix with positive diagonal and one
strictly dominant row is positive definite. [HornJohnson2013, Corollary 6.2.27].
Port of `NLAlib.posDef_of_isHermitian_of_irreducible_weak_diagonal_dominance`. -/
theorem _root_.Matrix.IsHermitian.posDef_of_isIrreducible_of_forall_sum_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hI : (A.map fun x => ‖x‖).IsIrreducible)
    (hweak : ∀ i, gershgorinRadius A i ≤ RCLike.re (A i i))
    (hstrict : ∃ i, gershgorinRadius A i < RCLike.re (A i i)) : A.PosDef := by
  have hnorm : ∀ i, ‖A i i‖ = RCLike.re (A i i) := fun i => by
    have h : ((RCLike.re (A i i) : ℝ) : 𝕜) = A i i :=
      RCLike.conj_eq_iff_re.mp (hA.apply i i)
    rw [← h, RCLike.norm_ofReal, RCLike.ofReal_re,
      abs_of_nonneg ((gershgorinRadius_nonneg A i).trans (h ▸ hweak i))]
  have hdet : A.det ≠ 0 := det_ne_zero_of_isIrreducible_of_forall_sum_le hI
    (fun i => (hnorm i).symm ▸ hweak i) (hstrict.imp fun i hi => (hnorm i).symm ▸ hi)
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hpsd := hA.posSemidef_of_forall_sum_le_re hweak
  rw [hA.posDef_iff_eigenvalue_pos]
  intro k hk
  refine lt_of_le_of_ne (hpsd.eigenvalue_nonneg k) fun h0 => ?_
  exact spectrum.zero_notMem ℝ hunit (h0 ▸ hA.eigenvalue_mem_spectrum hk)

/-! ### Counting eigenvalues -/

open Classical in
/-- The number of roots of the characteristic polynomial in a set, read off a listing. -/
private theorem card_filter_roots_charpoly {A : Matrix n n ℂ} {d : n → ℂ}
    (hd : IsEigenvalueListing A d) (K : Set ℂ) :
    Multiset.card (A.charpoly.roots.filter fun z => z ∈ K) =
      (Finset.univ.filter fun i => d i ∈ K).card := by
  have hroots : A.charpoly.roots = Finset.univ.val.map d := by
    rw [hd, ← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map d), Multiset.map_map]
    rfl
  rw [hroots, ← Multiset.countP_eq_card_filter, Multiset.countP_map]
  rfl

/-- The values at `card n + 1` points determine the characteristic polynomial among the
products of `card n` monic linear factors. -/
private theorem isEigenvalueListing_of_forall_eval_eq {A : Matrix n n ℂ} {d : n → ℂ}
    (h : ∀ j : Fin (Fintype.card n + 1), A.charpoly.eval (j : ℂ) = ∏ i, ((j : ℂ) - d i)) :
    IsEigenvalueListing A d := by
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq A.charpoly (∏ i, (X - C (d i)))
    (f := fun j : Fin (Fintype.card n + 1) => ((j : ℕ) : ℂ))
    (fun i j hij => Fin.ext (Nat.cast_injective hij)) (fun j => ?_) ?_
  · simpa only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] using h j
  · simp only [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
      Finset.card_univ, max_self, Fintype.card_fin, Nat.lt_succ_self]

open Classical in
/-- For a continuous family of matrices whose spectra stay in the union of two disjoint compact
sets, the set of parameters with a given number of eigenvalues in the first set is closed: it is
the preimage of a compact set of value vectors of products of linear factors. -/
private theorem isClosed_setOf_card_filter_roots_eq {Ω : Type*} [TopologicalSpace Ω]
    {A : Ω → Matrix n n ℂ} (hA : Continuous A) {K L : Set ℂ} (hK : IsCompact K)
    (hL : IsCompact L) (hdisj : Disjoint K L) (hspec : ∀ t, spectrum ℂ (A t) ⊆ K ∪ L) (r : ℕ) :
    IsClosed {t | Multiset.card ((A t).charpoly.roots.filter fun z => z ∈ K) = r} := by
  let F : (n → ℂ) → Fin (Fintype.card n + 1) → ℂ := fun z j => ∏ i, (((j : ℕ) : ℂ) - z i)
  let G : Ω → Fin (Fintype.card n + 1) → ℂ := fun t j => (A t).charpoly.eval ((j : ℕ) : ℂ)
  let box : Finset n → Set (n → ℂ) := fun s => {z | ∀ i, z i ∈ if i ∈ s then K else L}
  have hF : Continuous F := by fun_prop
  have hG : Continuous G := by
    refine continuous_pi fun j => ?_
    simp only [G, Matrix.eval_charpoly]
    exact (continuous_const.sub hA).matrix_det
  have hbox : ∀ s, IsCompact (box s) := fun s =>
    isCompact_pi_infinite fun i => by split_ifs <;> assumption
  have hC : IsCompact (⋃ s : {s : Finset n // s.card = r}, F '' box s.val) :=
    isCompact_iUnion fun s => (hbox s.val).image hF
  have hfilter : ∀ (s : Finset n) (z : n → ℂ), z ∈ box s →
      (Finset.univ.filter fun i => z i ∈ K) = s := by
    intro s z hz
    ext i
    rw [Finset.mem_filter_univ]
    by_cases hi : i ∈ s
    · exact iff_of_true (by simpa only [hi, if_true] using hz i) hi
    · have hzi : z i ∈ L := by simpa only [hi, if_false] using hz i
      exact iff_of_false (fun hk => Set.disjoint_left.mp hdisj hk hzi) hi
  have heq : {t | Multiset.card ((A t).charpoly.roots.filter fun z => z ∈ K) = r} =
      G ⁻¹' ⋃ s : {s : Finset n // s.card = r}, F '' box s.val := by
    ext t
    refine ⟨fun ht => ?_, fun ht => ?_⟩
    · obtain ⟨z, hz⟩ := exists_isEigenvalueListing (A t)
      have hzbox : z ∈ box (Finset.univ.filter fun i => z i ∈ K) := by
        intro i
        by_cases hi : z i ∈ K
        · simp only [Finset.mem_filter_univ, hi, if_true]
        · have hmem : z i ∈ spectrum ℂ (A t) := hz.spectrum_eq_range ▸ Set.mem_range_self i
          simpa only [Finset.mem_filter_univ, hi, if_false] using (hspec t hmem).resolve_left hi
      have hval : F z = G t := by
        funext j
        change ∏ i, (((j : ℕ) : ℂ) - z i) = (A t).charpoly.eval ((j : ℕ) : ℂ)
        rw [isEigenvalueListing_iff.mp hz, Polynomial.eval_prod]
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact Set.mem_iUnion.mpr
        ⟨⟨_, (card_filter_roots_charpoly hz K).symm.trans ht⟩, z, hzbox, hval⟩
    · obtain ⟨s, z, hz, hval⟩ := Set.mem_iUnion.mp ht
      have hlist : IsEigenvalueListing (A t) z :=
        isEigenvalueListing_of_forall_eval_eq fun j => (congrFun hval j).symm
      rw [Set.mem_ofPred_eq, card_filter_roots_charpoly hlist K, hfilter s.val z hz]
      exact s.property
  rw [heq]
  exact hC.isClosed.preimage hG

open Classical in
/-- Along a continuous family of matrices over a preconnected space whose spectra stay in the
union of two disjoint compact sets, the number of eigenvalues in the first set is constant. -/
private theorem card_filter_roots_eq_of_preconnected {Ω : Type*} [TopologicalSpace Ω]
    [PreconnectedSpace Ω] {A : Ω → Matrix n n ℂ} (hA : Continuous A) {K L : Set ℂ}
    (hK : IsCompact K) (hL : IsCompact L) (hdisj : Disjoint K L)
    (hspec : ∀ t, spectrum ℂ (A t) ⊆ K ∪ L) (s t : Ω) :
    Multiset.card ((A s).charpoly.roots.filter fun z => z ∈ K) =
      Multiset.card ((A t).charpoly.roots.filter fun z => z ∈ K) := by
  have hclosed := isClosed_setOf_card_filter_roots_eq hA hK hL hdisj hspec
  have hle : ∀ x, Multiset.card ((A x).charpoly.roots.filter fun z => z ∈ K) <
      Fintype.card n + 1 := by
    intro x
    obtain ⟨z, hz⟩ := exists_isEigenvalueListing (A x)
    rw [card_filter_roots_charpoly hz K, Nat.lt_succ_iff]
    exact Finset.card_le_univ _
  have hcomp : {x | Multiset.card ((A x).charpoly.roots.filter fun z => z ∈ K) =
        Multiset.card ((A s).charpoly.roots.filter fun z => z ∈ K)}ᶜ =
      ⋃ j : {j : Fin (Fintype.card n + 1) //
          (j : ℕ) ≠ Multiset.card ((A s).charpoly.roots.filter fun z => z ∈ K)},
        {x | Multiset.card ((A x).charpoly.roots.filter fun z => z ∈ K) = (j.val : ℕ)} := by
    ext x
    refine ⟨fun hx => Set.mem_iUnion.mpr ⟨⟨⟨_, hle x⟩, hx⟩, rfl⟩, fun hx => ?_⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rw [Set.mem_compl_iff, Set.mem_ofPred_eq, show _ = (j.val : ℕ) from hj]
    exact j.property
  have hopen : IsOpen {x | Multiset.card ((A x).charpoly.roots.filter fun z => z ∈ K) =
      Multiset.card ((A s).charpoly.roots.filter fun z => z ∈ K)} := by
    rw [← isClosed_compl_iff, hcomp]
    exact isClosed_iUnion_of_finite fun j => hclosed j.val
  exact (isPreconnected_univ.subset_isClopen ⟨hclosed _, hopen⟩ ⟨s, Set.mem_univ s, rfl⟩
    (Set.mem_univ t)).symm

open Classical in
/-- **A union of Gershgorin discs disjoint from the remaining discs contains exactly as many
eigenvalues, with multiplicity, as it has discs.** [HornJohnson2013, Theorem 6.1.1].
Port of `NLAlib.charpolyRootCountIn_gershgorinRowUnion_eq_card`. -/
theorem card_roots_charpoly_filter_mem_iUnion_closedBall (A : Matrix n n ℂ) (I : Finset n)
    (h : Disjoint (⋃ i ∈ I, Metric.closedBall (A i i) (gershgorinRadius A i))
      (⋃ i ∈ Iᶜ, Metric.closedBall (A i i) (gershgorinRadius A i))) :
    Multiset.card (A.charpoly.roots.filter fun z =>
      z ∈ ⋃ i ∈ I, Metric.closedBall (A i i) (gershgorinRadius A i)) = I.card := by
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let H : Set.Icc (0 : ℝ) 1 → Matrix n n ℂ := fun t =>
    Matrix.diagonal A.diag + ((t : ℝ) : ℂ) • (A - Matrix.diagonal A.diag)
  have hH : Continuous H := by fun_prop
  have hdiag : ∀ t i, H t i i = A i i := fun t i => by
    simp only [H, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.diagonal_apply_eq, Matrix.diag_apply, sub_self, smul_zero, add_zero]
  have hradius : ∀ t i, gershgorinRadius (H t) i = t * gershgorinRadius A i := by
    intro t i
    rw [gershgorinRadius, gershgorinRadius, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    simp only [H, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.diagonal_apply_ne _ hij, zero_add, sub_zero, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  have hmem : ∀ (J : Finset n) (i : n), i ∈ J →
      A i i ∈ ⋃ i ∈ J, Metric.closedBall (A i i) (gershgorinRadius A i) := fun J i hi =>
    Set.mem_biUnion hi (Metric.mem_closedBall_self (gershgorinRadius_nonneg A i))
  have hspec : ∀ t, spectrum ℂ (H t) ⊆
      (⋃ i ∈ I, Metric.closedBall (A i i) (gershgorinRadius A i)) ∪
        ⋃ i ∈ Iᶜ, Metric.closedBall (A i i) (gershgorinRadius A i) := by
    intro t μ hμ
    obtain ⟨i, hi⟩ := exists_norm_sub_le_sum_of_mem_spectrum hμ
    rw [hdiag, hradius] at hi
    have hball : μ ∈ Metric.closedBall (A i i) (gershgorinRadius A i) :=
      mem_closedBall_iff_norm.mpr
        (hi.trans (mul_le_of_le_one_left (gershgorinRadius_nonneg A i) t.property.2))
    by_cases hiI : i ∈ I
    · exact Or.inl (Set.mem_biUnion hiI hball)
    · exact Or.inr (Set.mem_biUnion (Finset.mem_compl.mpr hiI) hball)
  have hcompact : ∀ J : Finset n,
      IsCompact (⋃ i ∈ J, Metric.closedBall (A i i) (gershgorinRadius A i)) := fun J =>
    J.finite_toSet.isCompact_biUnion fun i _ => isCompact_closedBall _ _
  have hcount := card_filter_roots_eq_of_preconnected hH (hcompact I) (hcompact Iᶜ) h hspec
    ⟨1, by norm_num⟩ ⟨0, by norm_num⟩
  have hH₀ : H ⟨0, by norm_num⟩ = Matrix.diagonal A.diag := by simp [H]
  have hH₁ : H ⟨1, by norm_num⟩ = A := by simp [H]
  have hlist : IsEigenvalueListing (Matrix.diagonal A.diag) fun i => A i i :=
    Matrix.charpoly_diagonal A.diag
  rw [hH₁, hH₀, card_filter_roots_charpoly hlist] at hcount
  rw [hcount]
  congr 1
  ext i
  rw [Finset.mem_filter_univ]
  refine ⟨fun hi => ?_, hmem I i⟩
  by_contra hiI
  exact Set.disjoint_left.mp h hi (hmem Iᶜ i (Finset.mem_compl.mpr hiI))

end NLAlib
