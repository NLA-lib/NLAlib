/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Matrix.Spectral.RankOneUpdate

/-!
# The converses of interlacing

Every sequence that interlaces the eigenvalues of a Hermitian matrix is the spectrum of a
rank-one update of it, and of a bordering of it by one row and one column. After a unitary
diagonalisation the characteristic polynomial of the update is given by the secular equation,
and the weights that produce the prescribed roots are the residues of a partial fraction
expansion, which interlacing makes nonnegative.

## Main results

* `Matrix.IsHermitian.exists_eigenvalue_add_vecMulVec_star_eq`: the converse of interlacing for a
  rank-one update.
* `Matrix.IsHermitian.exists_eigenvalue_fromBlocks_eq`: the converse of Cauchy interlacing.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Partial fractions -/

/-- Interpolation at distinct nodes `d i`, `i ∈ s`: the monic polynomial with roots `β i` is the
one with roots `d i` minus a combination of the polynomials that omit one node, with the
residues as coefficients. -/
private theorem prod_X_sub_C_eq_sub_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) {d : ι → ℝ}
    (β : ι → ℝ) (hd : Set.InjOn d s) :
    ∏ i ∈ s, (X - C (β i)) = ∏ i ∈ s, (X - C (d i)) -
      ∑ i ∈ s, C ((β i - d i) * ∏ j ∈ s.erase i, ((d i - β j) / (d i - d j))) *
        ∏ j ∈ s.erase i, (X - C (d j)) := by
  refine Polynomial.eq_of_degree_sub_lt_of_eval_index_eq s hd ?_ fun k hk => ?_
  · have hdeg : ∀ (c : ι → ℝ) (t : Finset ι),
        (∏ i ∈ t, (X - C (c i))).degree = (t.card : WithBot ℕ) := fun c t => by
        rw [Polynomial.degree_eq_natDegree (monic_prod_X_sub_C c t).ne_zero,
          natDegree_finsetProd_X_sub_C_eq_card]
    have h1 : (∏ i ∈ s, (X - C (β i)) - ∏ i ∈ s, (X - C (d i))).degree <
        (s.card : WithBot ℕ) := by
      have h := Polynomial.degree_sub_lt_left ((hdeg β s).trans (hdeg d s).symm)
        (monic_prod_X_sub_C β s).ne_zero
        ((monic_prod_X_sub_C β s).leadingCoeff.trans (monic_prod_X_sub_C d s).leadingCoeff.symm)
      rwa [hdeg β s] at h
    have h2 : (∑ i ∈ s, C ((β i - d i) * ∏ j ∈ s.erase i, ((d i - β j) / (d i - d j))) *
        ∏ j ∈ s.erase i, (X - C (d j))).degree < (s.card : WithBot ℕ) := by
      refine (Polynomial.degree_sum_le _ _).trans_lt
        ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i hi => ?_)
      refine ((Polynomial.degree_mul_le _ _).trans
        (add_le_add Polynomial.degree_C_le le_rfl)).trans_lt ?_
      rw [zero_add, hdeg d, Finset.card_erase_of_mem hi]
      exact_mod_cast Nat.sub_lt (Finset.card_pos.mpr ⟨i, hi⟩) one_pos
    rw [sub_sub_eq_add_sub, add_sub_right_comm]
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt h1 h2)
  · have hz : ∏ i ∈ s, (d k - d i) = 0 := Finset.prod_eq_zero hk (sub_self _)
    simp only [eval_sub, eval_prod, eval_finsetSum, eval_mul, eval_X, eval_C]
    rw [hz, zero_sub,
      Finset.sum_eq_single_of_mem k hk fun i _ hik => by
        have h0 : ∏ j ∈ s.erase i, (d k - d j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hik, hk⟩) (sub_self _)
        rw [h0, mul_zero],
      mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun j hj => div_mul_cancel₀ _ (sub_ne_zero.mpr fun h =>
        Finset.ne_of_mem_erase hj (hd (Finset.mem_of_mem_erase hj) hk h.symm)),
      ← Finset.mul_prod_erase s _ hk]
    ring

/-- **Partial fractions under interlacing.** If `β` interlaces `d` from above, in the order
given by an injective ranking `r` of the indices, the monic polynomial with roots `β` is the one
with roots `d` minus a nonnegative combination of the polynomials that omit one root. Repeated
values of `d` are allowed: only the first index of each group of equal values gets a nonzero
weight. -/
private theorem exists_nonneg_prod_X_sub_C_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ι → ℕ} (hr : Function.Injective r) {d β : ι → ℝ} (hd : ∀ i j, r i ≤ r j → d j ≤ d i)
    (h₁ : ∀ i, d i ≤ β i) (h₂ : ∀ i j, r i < r j → β j ≤ d i) :
    ∃ ω : ι → ℝ, (∀ i, 0 ≤ ω i) ∧ ∏ i, (X - C (β i)) =
      ∏ i, (X - C (d i)) - ∑ i, C (ω i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  let R : Finset ι := Finset.univ.filter fun i => ∀ j, r j < r i → d j ≠ d i
  have hmem : ∀ i, i ∈ R ↔ ∀ j, r j < r i → d j ≠ d i := fun i => by
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ i)]
  have hinj : Set.InjOn d R := by
    intro i hi k hk hik
    rcases lt_trichotomy (r i) (r k) with h | h | h
    · exact absurd hik ((hmem k).mp hk i h)
    · exact hr h
    · exact absurd hik.symm ((hmem i).mp hi k h)
  have hβ : ∀ i, i ∉ R → β i = d i := by
    intro i hi
    rw [hmem] at hi
    push Not at hi
    obtain ⟨j, hj, hji⟩ := hi
    exact le_antisymm ((h₂ j i hj).trans hji.le) (h₁ i)
  have hprod : ∀ i ∈ R, ∏ j ∈ Finset.univ.erase i, (X - C (d j)) =
      (∏ j ∈ R.erase i, (X - C (d j))) * ∏ j ∈ Rᶜ, (X - C (d j)) := by
    intro i hi
    have hdisj : Disjoint (R.erase i) Rᶜ :=
      Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_compl.mp hx' (Finset.mem_of_mem_erase hx)
    rw [← Finset.prod_union hdisj]
    refine Finset.prod_congr (Finset.ext fun x => ?_) fun _ _ => rfl
    rw [Finset.mem_erase, Finset.mem_union, Finset.mem_erase, Finset.mem_compl,
      and_iff_left (Finset.mem_univ x)]
    by_cases hx : x ∈ R
    · exact ⟨fun h => Or.inl ⟨h, hx⟩, fun h => h.elim (fun h' => h'.1) fun h' => absurd hx h'⟩
    · exact ⟨fun _ => Or.inr hx, fun _ hxi => hx (hxi ▸ hi)⟩
  refine ⟨fun i => (β i - d i) * ∏ j ∈ R.erase i, ((d i - β j) / (d i - d j)), fun i => ?_, ?_⟩
  · refine mul_nonneg (sub_nonneg.mpr (h₁ i)) (Finset.prod_nonneg fun j hj => ?_)
    rcases lt_or_gt_of_ne (fun h => Finset.ne_of_mem_erase hj (hr h) : r j ≠ r i) with h | h
    · exact div_nonneg_of_nonpos (sub_nonpos.mpr ((hd j i h.le).trans (h₁ j)))
        (sub_nonpos.mpr (hd j i h.le))
    · exact div_nonneg (sub_nonneg.mpr (h₂ i j h)) (sub_nonneg.mpr (hd i j h.le))
  · rw [← Finset.prod_mul_prod_compl R fun i => X - C (β i),
      ← Finset.prod_mul_prod_compl R fun i => X - C (d i),
      Finset.prod_congr rfl fun i (hi : i ∈ Rᶜ) => by rw [hβ i (Finset.mem_compl.mp hi)],
      prod_X_sub_C_eq_sub_sum R β hinj, sub_mul, Finset.sum_mul]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ R) fun i _ hi => by
      simp only [hβ i hi, sub_self, zero_mul, C_0]]
    exact Finset.sum_congr rfl fun i hi => by rw [hprod i hi, mul_assoc]

/-- Multiplying the secular polynomial by a linear factor gives the polynomial of an arrowhead
matrix: this turns the weights of a rank-one update into those of a bordering. -/
private theorem mul_prod_sub_sum_eq {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (d ω : ι → R) (c : R) :
    (X - C c) *
        (∏ i, (X - C (d i)) - ∑ i, C (ω i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j))) =
      (X - C (c + ∑ i, ω i)) * ∏ i, (X - C (d i)) -
        ∑ i, C (ω i * (d i - c)) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := by
  have hterm : ∀ i, (X - C c) * (C (ω i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j))) =
      C (ω i) * ∏ j, (X - C (d j)) +
        C (ω i * (d i - c)) * ∏ j ∈ Finset.univ.erase i, (X - C (d j)) := fun i => by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => X - C (d j)) (Finset.mem_univ i), C_mul,
      C_sub]
    ring
  rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
    ← Finset.sum_mul, C_add, map_sum]
  ring

/-! ### Eigenvalues from the characteristic polynomial -/

/-- A Hermitian matrix whose characteristic polynomial is `∏ (X - β i)` for a non-increasing
`β` has the eigenvalues `β`. -/
private theorem eigenvalue_eq_of_charpoly_eq_prod {p : Type*} [Fintype p] [DecidableEq p]
    {q : ℕ} (hq : Fintype.card p = q) {M : Matrix p p 𝕜} (hM : M.IsHermitian) {β : Fin q → ℝ}
    (hβ : Antitone β) (hchar : M.charpoly = ∏ i, (X - C ((β i : ℝ) : 𝕜))) (i : Fin q) :
    eigenvalue M i = β i := by
  subst hq
  have hsort := hM.sort_roots_charpoly_eq_eigenvalues₀
  rw [hchar, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hsort
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_def, RCLike.ofReal_re] at hsort
  have hl : List.ofFn hM.eigenvalues₀ = List.ofFn β := by
    rw [← hsort]
    simp_rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hβ.sortedGE_ofFn
  rw [hM.eigenvalue_eq_eigenvalues₀ i, List.ofFn_injective hl]

omit [DecidableEq n] in
/-- A sequence that interlaces the eigenvalues from above is non-increasing. -/
private theorem antitone_of_interlacing {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : ℕ → ℝ}
    {q : ℕ} (hq : q ≤ Fintype.card n + 1)
    (h₁ : ∀ i, i < Fintype.card n → eigenvalue A i ≤ b i)
    (h₂ : ∀ i, i + 1 < q → b (i + 1) ≤ eigenvalue A i) : Antitone fun j : Fin q => b j := by
  intro j k hjk
  rcases eq_or_lt_of_le (Fin.le_def.mp hjk) with h | h
  · exact (congrArg b h).ge
  · obtain ⟨m, hm⟩ : ∃ m, (k : ℕ) = m + 1 := ⟨k - 1, by omega⟩
    have hk := k.isLt
    change b k ≤ b j
    rw [hm]
    exact ((h₂ m (by omega)).trans (hA.eigenvalue_le_eigenvalue (by omega) (by omega))).trans
      (h₁ j (by omega))

/-- **The weights of the secular equation.** If `b` interlaces the eigenvalues of a Hermitian
matrix from above, the polynomial with roots `b` is the secular polynomial of the eigenvalues
with nonnegative weights. -/
private theorem exists_nonneg_prod_X_sub_C_eigenvalues_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : ℕ → ℝ} (h₁ : ∀ i, i < Fintype.card n → eigenvalue A i ≤ b i)
    (h₂ : ∀ i, i + 1 < Fintype.card n → b (i + 1) ≤ eigenvalue A i) :
    ∃ ω : n → ℝ, (∀ x, 0 ≤ ω x) ∧
      ∏ j : Fin (Fintype.card n), (X - C ((b j : ℝ) : 𝕜)) =
        ∏ x, (X - C ((hA.eigenvalues x : ℝ) : 𝕜)) -
          ∑ x, C ((ω x : ℝ) : 𝕜) *
            ∏ y ∈ Finset.univ.erase x, (X - C ((hA.eigenvalues y : ℝ) : 𝕜)) := by
  obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
  have hd : ∀ x y, (e x : ℕ) ≤ e y → hA.eigenvalues y ≤ hA.eigenvalues x := fun x y hxy => by
    rw [he, he]
    exact hA.eigenvalue_le_eigenvalue hxy (e y).isLt
  have hh₂ : ∀ x y, (e x : ℕ) < e y → b (e y) ≤ hA.eigenvalues x := fun x y hxy => by
    obtain ⟨k, hk⟩ : ∃ k, (e y : ℕ) = k + 1 := ⟨e y - 1, by omega⟩
    have hy := (e y).isLt
    rw [he, hk]
    exact (h₂ k (by omega)).trans (hA.eigenvalue_le_eigenvalue (by omega) (by omega))
  obtain ⟨ω, hω, h⟩ := exists_nonneg_prod_X_sub_C_eq (r := fun x => (e x : ℕ))
    (fun x y hxy => e.injective (Fin.ext hxy)) hd (β := fun x => b (e x))
    (fun x => by rw [he]; exact h₁ _ (e x).isLt) hh₂
  refine ⟨ω, hω, ?_⟩
  have h' := congrArg (Polynomial.map (algebraMap ℝ 𝕜)) h
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_sum, Polynomial.map_mul, RCLike.algebraMap_eq_ofReal] at h'
  rw [← h']
  exact (Fintype.prod_equiv e (fun x => X - C ((b (e x) : ℝ) : 𝕜))
    (fun j => X - C ((b j : ℝ) : 𝕜)) fun x => rfl).symm

/-- A unitary diagonalisation of a Hermitian matrix indexed by its own index type. -/
private theorem exists_eq_mul_diagonal_eigenvalues_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ P : Matrix n n 𝕜, HasOrthonormalCols P ∧
      A = P * Matrix.diagonal (fun x => ((hA.eigenvalues x : ℝ) : 𝕜)) * Pᴴ := by
  refine ⟨hA.eigenvectorUnitary, hA.hasOrthonormalCols_eigenvectorUnitary, ?_⟩
  have h := hA.spectral_theorem
  rwa [Unitary.conjStarAlgAut_apply] at h

/-! ### The converses -/

omit [DecidableEq n] in
/-- **The converse of interlacing for a rank-one update.** If `b` interlaces the eigenvalues of
the Hermitian matrix `A` from above, `λ_i ≤ b_i` and `b_{i+1} ≤ λ_i`, there is a vector `z` such
that `A + z zᴴ` has eigenvalues `b`. [HornJohnson2013, Theorem 4.3.26].
Port of `NLAlib.exists_add_vecMulVec_charpoly_of_interlacing`, there over `ℝ`.
Result: interlacing-converse -/
theorem _root_.Matrix.IsHermitian.exists_eigenvalue_add_vecMulVec_star_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : ℕ → ℝ} (h₁ : ∀ i, i < Fintype.card n → eigenvalue A i ≤ b i)
    (h₂ : ∀ i, i + 1 < Fintype.card n → b (i + 1) ≤ eigenvalue A i) :
    ∃ z : n → 𝕜, ∀ i, i < Fintype.card n →
      eigenvalue (A + Matrix.vecMulVec z (star z)) i = b i := by
  classical
  obtain ⟨ω, hω, hpoly⟩ := exists_nonneg_prod_X_sub_C_eigenvalues_eq hA h₁ h₂
  obtain ⟨P, hP, hAP⟩ := exists_eq_mul_diagonal_eigenvalues_mul hA
  obtain ⟨w, hww⟩ : ∃ w : n → 𝕜, ∀ x, w x * star (w x) = ((ω x : ℝ) : 𝕜) :=
    ⟨fun x => ((√(ω x) : ℝ) : 𝕜), fun x => by
      rw [RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, Real.mul_self_sqrt (hω x)]⟩
  refine ⟨P *ᵥ w, fun i hi => ?_⟩
  have hsim : A + Matrix.vecMulVec (P *ᵥ w) (star (P *ᵥ w)) =
      P * (Matrix.diagonal (fun x => ((hA.eigenvalues x : ℝ) : 𝕜)) +
        Matrix.vecMulVec w (star w)) * Pᴴ := by
    rw [Matrix.mul_add, Matrix.add_mul, ← hAP, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.star_mulVec]
  have hchar : (A + Matrix.vecMulVec (P *ᵥ w) (star (P *ᵥ w))).charpoly =
      ∏ j : Fin (Fintype.card n), (X - C ((b j : ℝ) : 𝕜)) := by
    rw [hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hP.conjTranspose_mul_self,
      Matrix.one_mul, charpoly_diagonal_add_vecMulVec, hpoly]
    simp only [Pi.star_apply, hww]
  exact eigenvalue_eq_of_charpoly_eq_prod rfl
    (hA.add (Matrix.posSemidef_vecMulVec_self_star _).isHermitian)
    (antitone_of_interlacing hA (Nat.le_succ _) h₁ h₂) hchar ⟨i, hi⟩

omit [DecidableEq n] in
/-- **The converse of Cauchy interlacing.** If `b_0 ≥ … ≥ b_n` interlaces the eigenvalues of the
Hermitian matrix `A` of size `n`, `b_{i+1} ≤ λ_i ≤ b_i`, there is a bordering of `A` by one row
and column with eigenvalues `b`. [HornJohnson2013, Theorem 4.3.21].
Port of `NLAlib.exists_bordered_charpoly_of_interlacing`, there over `ℝ`.
Result: interlacing-converse -/
theorem _root_.Matrix.IsHermitian.exists_eigenvalue_fromBlocks_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : ℕ → ℝ} (h₁ : ∀ i, i < Fintype.card n → eigenvalue A i ≤ b i)
    (h₂ : ∀ i, i < Fintype.card n → b (i + 1) ≤ eigenvalue A i) :
    ∃ (z : n → 𝕜) (a : ℝ), ∀ i, i < Fintype.card n + 1 →
      eigenvalue (Matrix.fromBlocks A (Matrix.replicateCol Unit z)
        (Matrix.replicateRow Unit (star z)) (Matrix.of fun _ _ => ((a : ℝ) : 𝕜))) i = b i := by
  classical
  obtain ⟨ω, hω, hpoly⟩ :=
    exists_nonneg_prod_X_sub_C_eigenvalues_eq hA h₁ fun i hi => h₂ i (by omega)
  obtain ⟨P, hP, hAP⟩ := exists_eq_mul_diagonal_eigenvalues_mul hA
  have hlast : ∀ x, b (Fintype.card n) ≤ hA.eigenvalues x := fun x => by
    obtain ⟨e, he⟩ := hA.exists_equiv_eigenvalue_eq
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card n = k + 1 := ⟨Fintype.card n - 1, by
      have := (e x).isLt
      omega⟩
    have hx := (e x).isLt
    rw [he, congrArg b hk]
    exact (h₂ k (by omega)).trans (hA.eigenvalue_le_eigenvalue (by omega) (by omega))
  obtain ⟨w, hww⟩ : ∃ w : n → 𝕜, ∀ x, w x * star (w x) =
      ((ω x : ℝ) : 𝕜) * (((hA.eigenvalues x : ℝ) : 𝕜) - ((b (Fintype.card n) : ℝ) : 𝕜)) :=
    ⟨fun x => ((√(ω x * (hA.eigenvalues x - b (Fintype.card n))) : ℝ) : 𝕜), fun x => by
      rw [RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
        Real.mul_self_sqrt (mul_nonneg (hω x) (sub_nonneg.mpr (hlast x))), RCLike.ofReal_mul,
        RCLike.ofReal_sub]⟩
  refine ⟨P *ᵥ w, b (Fintype.card n) + ∑ x, ω x, fun i hi => ?_⟩
  have hQ : (Matrix.fromBlocks P 0 0 (1 : Matrix Unit Unit 𝕜))ᴴ * Matrix.fromBlocks P 0 0 1 =
      1 := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, hP.conjTranspose_mul_self,
      Matrix.fromBlocks_one]
  have hsim : Matrix.fromBlocks A (Matrix.replicateCol Unit (P *ᵥ w))
        (Matrix.replicateRow Unit (star (P *ᵥ w)))
        (Matrix.of fun _ _ => ((b (Fintype.card n) + ∑ x, ω x : ℝ) : 𝕜)) =
      Matrix.fromBlocks P 0 0 (1 : Matrix Unit Unit 𝕜) *
        Matrix.fromBlocks (Matrix.diagonal fun x => ((hA.eigenvalues x : ℝ) : 𝕜))
          (Matrix.replicateCol Unit w) (Matrix.replicateRow Unit (star w))
          (Matrix.of fun _ _ => ((b (Fintype.card n) + ∑ x, ω x : ℝ) : 𝕜)) *
        (Matrix.fromBlocks P 0 0 (1 : Matrix Unit Unit 𝕜))ᴴ := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    rw [← hAP, ← Matrix.replicateCol_mulVec, Matrix.star_mulVec, Matrix.replicateRow_vecMul]
  have hchar : (Matrix.fromBlocks A (Matrix.replicateCol Unit (P *ᵥ w))
      (Matrix.replicateRow Unit (star (P *ᵥ w)))
      (Matrix.of fun _ _ => ((b (Fintype.card n) + ∑ x, ω x : ℝ) : 𝕜))).charpoly =
      ∏ j : Fin (Fintype.card n + 1), (X - C ((b j : ℝ) : 𝕜)) := by
    rw [hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQ, Matrix.one_mul,
      charpoly_fromBlocks_diagonal_replicateCol, Fin.prod_univ_castSucc, mul_comm (∏ i, _) _]
    simp only [Fin.val_castSucc, Fin.val_last, Pi.star_apply, hww]
    rw [hpoly, mul_prod_sub_sum_eq, RCLike.ofReal_add, RCLike.ofReal_sum]
  have hM : (Matrix.fromBlocks A (Matrix.replicateCol Unit (P *ᵥ w))
      (Matrix.replicateRow Unit (star (P *ᵥ w)))
      (Matrix.of fun _ _ => ((b (Fintype.card n) + ∑ x, ω x : ℝ) : 𝕜))).IsHermitian := by
    exact Matrix.IsHermitian.fromBlocks hA (Matrix.conjTranspose_replicateCol _)
      (Matrix.ext fun _ _ => RCLike.conj_ofReal _)
  exact eigenvalue_eq_of_charpoly_eq_prod (by rw [Fintype.card_sum, Fintype.card_unit]) hM
    (antitone_of_interlacing hA le_rfl h₁ fun i hi => h₂ i (by omega)) hchar ⟨i, hi⟩

end NLAlib
