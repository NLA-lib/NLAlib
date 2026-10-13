/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Majorization.Schur
public import NLAlib.Matrix.Basic.PlaneRotation
public import NLAlib.Matrix.Subspaces.Frames

/-!
# The Schur–Horn theorem

Schur's theorem says that the diagonal of a Hermitian matrix is majorized by its eigenvalues
(`NLAlib.Matrix.Majorization.Schur`). Horn's converse: every real vector majorized by `λ` is the
diagonal of a real symmetric matrix with eigenvalues `λ`. Together they describe the set of
diagonals of the unitary orbit of a Hermitian matrix.

## Main results

* `NLAlib.exists_hasOrthonormalCols_diag_eq_of_majorized`: Horn's theorem.
* `NLAlib.majorized_iff_exists_hasOrthonormalCols_diag_eq`: the Schur–Horn theorem.
* `Matrix.IsHermitian.majorized_iff_exists_diag_conj_eq`: for the orbit of a Hermitian matrix.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The diagonal of `Q * diagonal λ * Qᴴ` is the image of `λ` under the matrix of squared moduli
of the entries of `Q`. Port of `NLAlib.diagonal_conjugation_eq_sq_mulVec`, there over `ℝ`. -/
theorem re_mul_diagonal_mul_conjTranspose_apply_self (Q : Matrix n n 𝕜) (lam : n → ℝ) (i : n) :
    RCLike.re ((Q * Matrix.diagonal (fun j => ((lam j : ℝ) : 𝕜)) * Qᴴ) i i) =
      ((Matrix.of fun i j => ‖Q i j‖ ^ 2) *ᵥ lam) i := by
  rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, RCLike.star_def, map_sum,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_right_comm, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

/-! ### Transfers between two entries of a vector -/

/-- `transfer y i j δ` lowers the entry `i` of `y` by `δ` and raises the entry `j` by `δ`. -/
private def transfer {ι : Type*} [DecidableEq ι] (y : ι → ℝ) (i j : ι) (δ : ℝ) : ι → ℝ :=
  fun k => y k - (if k = i then δ else 0) + if k = j then δ else 0

private theorem sum_transfer {ι : Type*} [DecidableEq ι] (y : ι → ℝ) (i j : ι) (δ : ℝ)
    (t : Finset ι) :
    ∑ k ∈ t, transfer y i j δ k =
      ∑ k ∈ t, y k - (if i ∈ t then δ else 0) + if j ∈ t then δ else 0 := by
  simp only [transfer, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']

private theorem transfer_of_ne {ι : Type*} [DecidableEq ι] (y : ι → ℝ) {i j k : ι} (hi : k ≠ i)
    (hj : k ≠ j) (δ : ℝ) : transfer y i j δ k = y k := by
  simp only [transfer, if_neg hi, if_neg hj, sub_zero, add_zero]

private theorem transfer_self {ι : Type*} [DecidableEq ι] (y : ι → ℝ) (i : ι) (δ : ℝ) :
    transfer y i i δ = y := by
  ext k
  simp only [transfer, sub_add_cancel]

private theorem transfer_apply_left {ι : Type*} [DecidableEq ι] (y : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (δ : ℝ) : transfer y i j δ i = y i - δ := by
  simp only [transfer, if_true, if_neg hij, add_zero]

/-- Transferring the difference of two entries exchanges them. -/
private theorem transfer_sub_eq_comp_swap {ι : Type*} [DecidableEq ι] (y : ι → ℝ) (p i : ι) :
    transfer y p i (y p - y i) = y ∘ Equiv.swap p i := by
  ext k
  obtain rfl | hpi := eq_or_ne p i
  · rw [transfer_self, Equiv.swap_self, Equiv.coe_refl, Function.comp_id]
  obtain rfl | hkp := eq_or_ne k p
  · rw [transfer_apply_left y hpi, Function.comp_apply, Equiv.swap_apply_left, sub_sub_cancel]
  obtain rfl | hki := eq_or_ne k i
  · simp only [transfer, if_neg hkp, if_true, sub_zero, add_sub_cancel, Function.comp_apply,
      Equiv.swap_apply_right]
  · rw [transfer_of_ne y hkp hki, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hkp hki]

/-! ### Majorization under relabelling and restriction -/

private theorem majorized_comp_equiv_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {x y : ι → ℝ}
    (e : κ ≃ ι) : Majorized (x ∘ e) (y ∘ e) ↔ Majorized x y := by
  have hsum (z : ι → ℝ) : ∑ k, (z ∘ e) k = ∑ k, z k := Equiv.sum_comp e z
  refine ⟨fun h => ⟨fun k => ?_, ?_⟩, fun h => ⟨fun k => ?_, ?_⟩⟩
  · have hk := h.weaklyMajorized k
    rwa [sumLargest_comp_equiv, sumLargest_comp_equiv] at hk
  · have hs := h.sum_eq
    rwa [hsum, hsum] at hs
  · rw [sumLargest_comp_equiv, sumLargest_comp_equiv]
    exact h.weaklyMajorized k
  · rw [hsum, hsum]
    exact h.sum_eq

/-- Two vectors that agree outside an index set are majorized exactly when their restrictions to
the set are. -/
private theorem majorized_subtype_iff {ι : Type*} [Fintype ι] {x y : ι → ℝ} {s : Finset ι}
    (h : ∀ k ∉ s, x k = y k) :
    Majorized (fun k : s => x k) (fun k : s => y k) ↔ Majorized x y := by
  classical
  simp only [majorized_iff_forall_sum_convex_le]
  refine forall₂_congr fun φ _ => ?_
  have hc : ∑ k ∈ sᶜ, φ (x k) = ∑ k ∈ sᶜ, φ (y k) :=
    Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_compl.mp hk)]
  rw [Finset.sum_coe_sort s fun k => φ (x k), Finset.sum_coe_sort s fun k => φ (y k),
    ← Finset.sum_add_sum_compl s fun k => φ (x k), ← Finset.sum_add_sum_compl s fun k => φ (y k),
    hc, add_le_add_iff_right]

private theorem exists_equiv_antitone_comp {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, Antitone (a ∘ e) := by
  classical
  refine ⟨(Tuple.sort fun j => -a ((Fintype.equivFin ι).symm j)).trans (Fintype.equivFin ι).symm,
    fun i j hij => ?_⟩
  have h := Tuple.monotone_sort (fun j => -a ((Fintype.equivFin ι).symm j)) hij
  simpa only [Function.comp_apply, neg_le_neg_iff, Equiv.trans_apply] using h

/-! ### A transfer between adjacent entries of a sorted vector -/

private theorem sumLargest_succ_of_antitone {N : ℕ} {y : Fin N → ℝ} (hy : Antitone y)
    (i : Fin N) : sumLargest y (i + 1) = sumLargest y i + y i := by
  have h (k : Fin N) : (if (k : ℕ) < i + 1 then y k else 0) =
      (if (k : ℕ) < i then y k else 0) + if k = i then y k else 0 := by
    obtain hlt | heq | hgt := lt_trichotomy (k : ℕ) i
    · rw [if_pos (Nat.lt_succ_of_lt hlt), if_pos hlt, if_neg (Fin.ne_of_val_ne hlt.ne), add_zero]
    · rw [if_pos (heq ▸ Nat.lt_succ_self _), if_neg (heq ▸ lt_irrefl _), if_pos (Fin.ext heq),
        zero_add]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (Fin.ne_of_val_ne hgt.ne'), add_zero]
  rw [sumLargest_eq_sum_of_antitone hy, sumLargest_eq_sum_of_antitone hy]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The first `r` entries of a transfer of a sorted vector bound its `r` largest entries from
below. -/
private theorem sumLargest_sub_add_le_sumLargest_transfer {N : ℕ} {y : Fin N → ℝ}
    (hy : Antitone y) (i j : Fin N) (δ : ℝ) (r : ℕ) :
    sumLargest y r - (if (i : ℕ) < r then δ else 0) + (if (j : ℕ) < r then δ else 0) ≤
      sumLargest (transfer y i j δ) r := by
  have hcard : (Finset.univ.filter fun k : Fin N => (k : ℕ) < r).card =
      min r (Fintype.card (Fin N)) := by
    rw [Fin.card_filter_val_lt, Fintype.card_fin, min_comm]
  refine le_of_eq_of_le ?_ (sum_le_sumLargest_of_card_eq _ hcard)
  rw [sum_transfer, sumLargest_eq_sum_of_antitone hy, Finset.sum_filter]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Transfer between adjacent entries.** If `x` is majorized by a sorted vector `y`, it is
still majorized after the entry `y i` is replaced by any entry `x p` of `x` and the difference is
added to the next entry of `y`. -/
private theorem majorized_transfer_of_antitone {N : ℕ} {x y : Fin N → ℝ} (hy : Antitone y)
    (h : Majorized x y) (p : Fin N) {i j : Fin N} (hij : (j : ℕ) = i + 1) :
    Majorized x (transfer y i j (y i - x p)) := by
  refine ⟨weaklyMajorized_iff_forall_sum_le.mpr fun s => ?_, ?_⟩
  · have hG := sumLargest_sub_add_le_sumLargest_transfer hy i j (y i - x p) s.card
    have hxy := (sum_le_sumLargest x s).trans (h.weaklyMajorized s.card)
    have hsi := sumLargest_succ_of_antitone hy i
    by_cases hr : s.card = i + 1
    · by_cases hp : p ∈ s
      · have h1 := (sum_le_sumLargest x (s.erase p)).trans (h.weaklyMajorized _)
        rw [Finset.card_erase_of_mem hp, hr, Nat.add_sub_cancel] at h1
        rw [hr, if_pos (Nat.lt_succ_self _), if_neg (by omega), hsi] at hG
        have h2 := Finset.add_sum_erase s x hp
        rw [hr]
        linarith
      · have h1 := (sum_le_sumLargest x (insert p s)).trans (h.weaklyMajorized _)
        rw [Finset.card_insert_of_notMem hp, Finset.sum_insert hp, hr] at h1
        have hsj := sumLargest_succ_of_antitone hy j
        rw [hij] at hsj
        have hjT : j ∉ Finset.univ.filter fun k : Fin N => (k : ℕ) < i := by
          rw [Finset.mem_filter, hij]
          omega
        have hiT : i ∉ insert j (Finset.univ.filter fun k : Fin N => (k : ℕ) < i) := by
          rw [Finset.mem_insert, Finset.mem_filter, Fin.ext_iff]
          omega
        have hcard : (insert j (Finset.univ.filter fun k : Fin N => (k : ℕ) < i)).card =
            min s.card (Fintype.card (Fin N)) := by
          rw [Finset.card_insert_of_notMem hjT, Fin.card_filter_val_lt, hr, Fintype.card_fin,
            min_eq_right i.isLt.le, min_eq_left i.isLt]
        have h2 := sum_le_sumLargest_of_card_eq (transfer y i j (y i - x p)) hcard
        rw [sum_transfer, if_neg hiT, if_pos (Finset.mem_insert_self _ _), Finset.sum_insert hjT,
          Finset.sum_filter, ← sumLargest_eq_sum_of_antitone hy] at h2
        linarith
    · have hiff : (i : ℕ) < s.card ↔ (j : ℕ) < s.card := by omega
      by_cases hlt : (i : ℕ) < s.card
      · rw [if_pos hlt, if_pos (hiff.mp hlt)] at hG
        linarith
      · rw [if_neg hlt, if_neg (mt hiff.mpr hlt)] at hG
        linarith
  · have hsum := sum_transfer y i j (y i - x p) Finset.univ
    rw [if_pos (Finset.mem_univ i), if_pos (Finset.mem_univ j), sub_add_cancel] at hsum
    rw [hsum, h.sum_eq]

/-- An entry of a vector majorized by a sorted vector `y` lies between two adjacent entries of
`y`, or equals one. -/
private theorem exists_le_and_le_of_antitone {N : ℕ} {x y : Fin N → ℝ} (hy : Antitone y)
    (h : Majorized x y) (p : Fin N) :
    ∃ i j : Fin N, (i = j ∨ (j : ℕ) = i + 1) ∧ y j ≤ x p ∧ x p ≤ y i := by
  have hN : 0 < N := p.pos
  have h0 : (⟨0, hN⟩ : Fin N) ∈ Finset.univ.filter fun k : Fin N => x p ≤ y k := by
    have h1 := (sum_le_sumLargest x {p}).trans (h.weaklyMajorized _)
    have h2 := sumLargest_succ_of_antitone hy ⟨0, hN⟩
    rw [Finset.sum_singleton, Finset.card_singleton] at h1
    rw [zero_add, sumLargest_zero, zero_add] at h2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h1.trans_eq h2⟩
  obtain ⟨i, hiS, hmax⟩ := Finset.exists_maximal ⟨_, h0⟩
  have hi : x p ≤ y i := (Finset.mem_filter.mp hiS).2
  by_cases hlast : (i : ℕ) + 1 < N
  · refine ⟨i, ⟨i + 1, hlast⟩, Or.inr rfl, le_of_not_ge fun hcon => ?_, hi⟩
    have hle := hmax (Finset.mem_filter.mpr ⟨Finset.mem_univ (⟨i + 1, hlast⟩ : Fin N), hcon⟩)
      (Fin.le_def.mpr (Nat.le_succ _))
    exact absurd (Fin.le_def.mp hle) (Nat.not_succ_le_self _)
  · refine ⟨i, i, Or.inl rfl, ?_, hi⟩
    have h1 := h.sum_sub_sumLargest_le_sum {p} (d := i) (by
      rw [Finset.card_singleton, Fintype.card_fin]
      omega)
    have h2 := sumLargest_succ_of_antitone hy i
    have h3 := sumLargest_of_card_le y (k := i + 1) (by
      rw [Fintype.card_fin]
      omega)
    rw [Finset.sum_singleton] at h1
    linarith

private theorem exists_majorized_transfer_of_antitone {N : ℕ} {x y : Fin N → ℝ}
    (hy : Antitone y) (h : Majorized x y) (p : Fin N) :
    ∃ i j : Fin N, y j ≤ x p ∧ x p ≤ y i ∧ Majorized x (transfer y i j (y i - x p)) := by
  obtain ⟨i, j, hij | hij, hj, hi⟩ := exists_le_and_le_of_antitone hy h p
  · subst hij
    exact ⟨i, i, hj, hi, by rwa [transfer_self]⟩
  · exact ⟨i, j, hj, hi, majorized_transfer_of_antitone hy h p hij⟩


/-- If `x` is majorized by `y` and agrees with it outside an index set `s`, then for every `p` in
`s` a transfer between two entries of `y` in `s` puts the value `x p` on the diagonal, keeping
`x` majorized. -/
private theorem exists_majorized_transfer {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι → ℝ}
    (h : Majorized x y) {s : Finset ι} (hs : ∀ k ∉ s, x k = y k) {p : ι} (hp : p ∈ s) :
    ∃ i ∈ s, ∃ j ∈ s, y j ≤ x p ∧ x p ≤ y i ∧ Majorized x (transfer y i j (y i - x p)) := by
  obtain ⟨e, he⟩ := exists_equiv_antitone_comp fun k : s => y k
  have h' := (majorized_comp_equiv_iff e).mpr ((majorized_subtype_iff hs).mpr h)
  obtain ⟨i, j, hj, hi, hmaj⟩ := exists_majorized_transfer_of_antitone he h' (e.symm ⟨p, hp⟩)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hj hi hmaj
  refine ⟨e i, (e i).2, e j, (e j).2, hj, hi, ?_⟩
  have hT : transfer ((fun k : s => y k) ∘ e) i j (y (e i) - x p) =
      (fun k : s => transfer y (e i) (e j) (y (e i) - x p) k) ∘ e := by
    ext k
    simp only [transfer, Function.comp_apply, ← Subtype.ext_iff, e.apply_eq_iff_eq]
  rw [hT, majorized_comp_equiv_iff e] at hmaj
  refine (majorized_subtype_iff fun k hk => ?_).mp hmaj
  have hki : k ≠ e i := fun hki => hk (hki ▸ (e i).2)
  have hkj : k ≠ e j := fun hkj => hk (hkj ▸ (e j).2)
  rw [transfer_of_ne y hki hkj, hs k hk]

/-! ### Plane rotations in two coordinates -/

omit [Fintype n] in
private theorem planeRotation_single_apply {i j : n} (hij : i ≠ j) (c s : ℝ) (k : n) :
    planeRotation (Pi.single i (1 : ℝ)) (Pi.single j 1) c s k =
      if k = i then c • Pi.single i 1 + s • Pi.single j 1
      else if k = j then (-s) • Pi.single i 1 + c • Pi.single j 1
      else Pi.single k 1 := by
  ext l
  by_cases hki : k = i <;> by_cases hkj : k = j
  · exact (hij (hki.symm.trans hkj)).elim
  · subst k
    simp [planeRotation, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.one_apply, hij, eq_comm]
    split_ifs <;> ring
  · subst k
    simp [planeRotation, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.one_apply, hij, eq_comm]
    split_ifs <;> ring
  · simp [planeRotation, Matrix.vecMulVec_apply, Pi.single_apply, hki, hkj,
      Matrix.one_apply, eq_comm]

/-- Conjugating a real symmetric matrix by a rotation in the coordinates `i`, `j` transfers
between the diagonal entries `i` and `j` and fixes the other diagonal entries.
Port of `NLAlib.planeRotation_single_conjugation_diag`. -/
private theorem diag_planeRotation_single_mul_mul {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {i j : n} (hij : i ≠ j) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (planeRotation (Pi.single i 1) (Pi.single j 1) c s * A *
      (planeRotation (Pi.single i 1) (Pi.single j 1) c s)ᴴ).diag =
      transfer A.diag i j (-(2 * c * s * A i j + s ^ 2 * (A j j - A i i))) := by
  ext k
  have hji : A j i = A i j := hA.apply i j
  rw [Matrix.diag_apply, Matrix.mul_mul_apply, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_transpose, planeRotation_single_apply hij]
  by_cases hki : k = i
  · subst k
    simp only [ite_true, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, single_dotProduct, Matrix.mulVec_single_one,
      one_mul, smul_eq_mul, Matrix.col_apply, hji, transfer_apply_left _ hij, Matrix.diag_apply]
    linear_combination A i i * hcs
  · by_cases hkj : k = j
    · subst k
      simp only [if_neg hki, ite_true, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
        dotProduct_add, smul_dotProduct, dotProduct_smul, single_dotProduct,
        Matrix.mulVec_single_one, one_mul, smul_eq_mul, Matrix.col_apply, hji, transfer,
        Matrix.diag_apply, sub_zero]
      linear_combination A j j * hcs
    · rw [if_neg hki, if_neg hkj, transfer_of_ne _ hki hkj, Matrix.mulVec_single_one,
        single_one_dotProduct, Matrix.col_apply, Matrix.diag_apply]

/-- For a real symmetric matrix and any value `t` between two of its diagonal entries, a
rotation in those two coordinates puts `t` in the first of the two diagonal positions. -/
private theorem exists_hasOrthonormalCols_diag_eq_transfer {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (i j : n) {t : ℝ} (ht : t ∈ Set.uIcc (A i i) (A j j)) :
    ∃ R : Matrix n n ℝ, HasOrthonormalCols R ∧
      (R * A * Rᴴ).diag = transfer A.diag i j (A i i - t) := by
  obtain rfl | hij := eq_or_ne i j
  · exact ⟨1, hasOrthonormalCols_one, by
      rw [transfer_self, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]⟩
  let f : ℝ → ℝ := fun θ =>
    A i i + (2 * Real.cos θ * Real.sin θ * A i j + Real.sin θ ^ 2 * (A j j - A i i))
  have hf : Continuous f := by fun_prop
  have h0 : f 0 = A i i := by simp [f]
  have h1 : f (Real.pi / 2) = A j j := by simp [f]
  obtain ⟨θ, -, hθ⟩ := intermediate_value_uIcc (a := 0) (b := Real.pi / 2) hf.continuousOn
    (by rwa [h0, h1])
  refine ⟨planeRotation (Pi.single i 1) (Pi.single j 1) (Real.cos θ) (Real.sin θ),
    hasOrthonormalCols_planeRotation ?_ ?_ ?_ (Real.cos_sq_add_sin_sq θ), ?_⟩
  · sorry
  · sorry
  · sorry
  · rw [diag_planeRotation_single_mul_mul hA hij (Real.cos_sq_add_sin_sq θ)]
    congr 1
    linarith

end NLAlib
