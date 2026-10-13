/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Fin.Tuple.Sort
public import NLAlib.ForMathlib.Algebra.BigOperators.AbelSummation
public import NLAlib.Matrix.Majorization.Basic

/-!
# Majorization, doubly stochastic matrices and convex functions

The Hardy–Littlewood–Pólya characterisations of majorization: `x` is majorized by `y` exactly
when `x = D y` for a doubly stochastic matrix `D`, exactly when `x` lies in the convex hull of the
permutations of `y`, and exactly when `∑ φ (x i) ≤ ∑ φ (y i)` for every convex `φ`. Weak
majorization is characterised by monotone convex functions.

## Main results

* `NLAlib.majorized_iff_exists_doublyStochastic`: Hardy–Littlewood–Pólya.
* `NLAlib.majorized_iff_mem_convexHull_permutations`: Rado.
* `NLAlib.Majorized.sum_convex_le`, `NLAlib.majorized_iff_forall_sum_convex_le`: Karamata.
* `NLAlib.Majorized.le_of_convexOn_of_comp_perm`: symmetric convex functions are Schur-convex.
* `NLAlib.WeaklyMajorized.sum_monotone_convex_le`,
  `NLAlib.weaklyMajorized_iff_forall_sum_monotone_convex_le`: Tomić–Weyl and its converse.
* `NLAlib.WeaklyMajorized.exists_le_majorized`: weak majorization is domination followed by
  majorization.
-/

@[expose] public section

open scoped Matrix Pointwise

namespace NLAlib

variable {ι : Type*} [Fintype ι]

/-! ### Thresholds and weighted sums -/

private theorem exists_card_eq_min_and_forall_le (x : ι → ℝ) (k : ℕ) :
    ∃ t : Finset ι, t.card = min k (Fintype.card ι) ∧ (∀ i ∈ t, ∀ j ∉ t, x j ≤ x i) ∧
      ∑ i ∈ t, x i = sumLargest x k := by
  classical
  obtain ⟨t, ht, hsum⟩ := exists_card_eq_min_and_sum_eq_sumLargest x k
  refine ⟨t, ht, fun i hi j hj => ?_, hsum⟩
  by_contra hlt
  rw [not_le] at hlt
  have hj' : j ∉ t.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  have hcard : (insert j (t.erase i)).card = min k (Fintype.card ι) := by
    rw [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hi, ← ht]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have h := sum_le_sumLargest_of_card_eq x hcard
  rw [Finset.sum_insert hj', ← hsum, ← Finset.add_sum_erase t x hi] at h
  linarith

/-- A set carrying the `k` largest entries, with a value `c` separating its entries from the
others. -/
private theorem exists_threshold (x : ι → ℝ) (k : ℕ) :
    ∃ (t : Finset ι) (c : ℝ), t.card = min k (Fintype.card ι) ∧ (∀ i ∈ t, c ≤ x i) ∧
      (∀ j ∉ t, x j ≤ c) ∧ ∑ i ∈ t, x i = sumLargest x k := by
  obtain ⟨t, ht, hle, hsum⟩ := exists_card_eq_min_and_forall_le x k
  obtain hne | hne := t.eq_empty_or_nonempty
  · obtain hι | hι := isEmpty_or_nonempty ι
    · exact ⟨t, 0, ht, fun i => isEmptyElim i, fun j => isEmptyElim j, hsum⟩
    · refine ⟨t, Finset.univ.sup' Finset.univ_nonempty x, ht, fun i hi => ?_,
        fun j _ => Finset.le_sup' x (Finset.mem_univ j), hsum⟩
      rw [hne] at hi
      exact absurd hi (Finset.notMem_empty i)
  · refine ⟨t, t.inf' hne x, ht, fun i hi => Finset.inf'_le x hi, fun j hj => ?_, hsum⟩
    obtain ⟨i, hi, hmin⟩ := Finset.exists_mem_eq_inf' hne x
    rw [hmin]
    exact hle i hi j hj

/-- A weight vector with entries in `[0, 1]` and total `k` picks out at most the sum of the `k`
largest entries. Port of `NLAlib.sum_mul_le_sumLargest`. -/
theorem sum_mul_le_sumLargest (x w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) {k : ℕ}
    (hk : ∑ i, w i = k) : ∑ i, x i * w i ≤ sumLargest x k := by
  classical
  obtain ⟨t, c, ht, htc, hct, hsum⟩ := exists_threshold x k
  have hkcard : k ≤ Fintype.card ι := by
    have h : ∑ i, w i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hw1 i
    rw [hk, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  rw [min_eq_left hkcard] at ht
  have hterm (i : ι) : (x i - c) * w i ≤ if i ∈ t then x i - c else 0 := by
    split_ifs with hi
    · exact mul_le_of_le_one_right (sub_nonneg.mpr (htc i hi)) (hw1 i)
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hct i hi)) (hw0 i)
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  have hl : ∑ i, (x i - c) * w i = ∑ i, x i * w i - c * k := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hk]
  have hr : (∑ i, if i ∈ t then x i - c else 0) = sumLargest x k - c * k := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib, Finset.sum_const, ht,
      hsum, nsmul_eq_mul, mul_comm]
  rw [hl, hr] at h
  linarith

/-- The image of a vector under a doubly stochastic matrix is majorized by the vector.
[HornJohnson2013, Theorem 4.3.49].
Port of `NLAlib.majorized_mulVec_of_doublyStochastic`. -/
theorem majorized_mulVec_of_mem_doublyStochastic [DecidableEq ι] (y : ι → ℝ) {D : Matrix ι ι ℝ}
    (hD : D ∈ doublyStochastic ℝ ι) : Majorized (D *ᵥ y) y := by
  refine ⟨weaklyMajorized_iff_forall_sum_le.mpr fun s => ?_,
    sum_mulVec_of_mem_doublyStochastic hD⟩
  have hw0 (j : ι) : 0 ≤ ∑ i ∈ s, D i j :=
    Finset.sum_nonneg fun i _ => nonneg_of_mem_doublyStochastic hD
  have hw1 (j : ι) : ∑ i ∈ s, D i j ≤ 1 := by
    rw [← sum_col_of_mem_doublyStochastic hD j]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      fun i _ _ => nonneg_of_mem_doublyStochastic hD
  have hw : ∑ j, ∑ i ∈ s, D i j = (s.card : ℝ) := by
    rw [Finset.sum_comm]
    simp only [sum_row_of_mem_doublyStochastic hD, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum : ∑ i ∈ s, (D *ᵥ y) i = ∑ j, y j * ∑ i ∈ s, D i j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsum]
  exact sum_mul_le_sumLargest y _ hw0 hw1 hw

/-! ### Pairing with a weight vector -/

/-- Extension by zero of a family on `Fin N` to a sequence. -/
private noncomputable def extendFin {N : ℕ} (g : Fin N → ℝ) (i : ℕ) : ℝ :=
  if h : i < N then g ⟨i, h⟩ else 0

private theorem extendFin_val {N : ℕ} (g : Fin N → ℝ) (j : Fin N) : extendFin g j = g j := by
  rw [extendFin, dif_pos j.isLt]

private theorem sum_range_extendFin {N : ℕ} (g : Fin N → ℝ) {k : ℕ} (hk : k ≤ N) :
    ∑ i ∈ Finset.range k, extendFin g i = ∑ j : Fin N, if (j : ℕ) < k then g j else 0 := by
  have h := Fin.sum_univ_eq_sum_range (fun i => if i < k then extendFin g i else 0) N
  simp only [extendFin_val] at h
  rw [h, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- Abel summation on `Fin N`: a non-increasing weight preserves domination of the partial sums,
when the totals agree or the weight is nonnegative. -/
private theorem sum_mul_le_sum_mul_of_antitone {N : ℕ} {a b c : Fin N → ℝ} (ha : Antitone a)
    (hp : ∀ k ≤ N, (∑ i : Fin N, if (i : ℕ) < k then b i else 0) ≤
      ∑ i : Fin N, if (i : ℕ) < k then c i else 0)
    (hc : ∑ i, b i = ∑ i, c i ∨ ∀ i, 0 ≤ a i) : ∑ i, a i * b i ≤ ∑ i, a i * c i := by
  have ha' : AntitoneOn (extendFin a) (Set.Iio N) := fun i hi j hj hij => by
    rw [extendFin, extendFin, dif_pos (Set.mem_Iio.mp hi), dif_pos (Set.mem_Iio.mp hj)]
    exact ha (Fin.mk_le_mk.mpr hij)
  have hp' (k : ℕ) (hk : k ≤ N) :
      ∑ i ∈ Finset.range k, extendFin b i ≤ ∑ i ∈ Finset.range k, extendFin c i := by
    rw [sum_range_extendFin b hk, sum_range_extendFin c hk]
    exact hp k hk
  have hfull (g : Fin N → ℝ) :
      ∑ i ∈ Finset.range N, extendFin a i * extendFin g i = ∑ j, a j * g j := by
    rw [← Fin.sum_univ_eq_sum_range fun i => extendFin a i * extendFin g i]
    simp only [extendFin_val]
  have htot (g : Fin N → ℝ) : ∑ i ∈ Finset.range N, extendFin g i = ∑ j, g j := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [extendFin_val]
  rw [← hfull b, ← hfull c]
  obtain hc | hc := hc
  · exact Finset.sum_range_mul_le_sum_range_mul_of_antitoneOn_of_sum_eq ha' hp'
      (by rw [htot, htot, hc])
  · exact Finset.sum_range_mul_le_sum_range_mul_of_antitoneOn_of_nonneg ha' hp' fun i hi => by
      rw [extendFin, dif_pos hi]
      exact hc _

private theorem exists_equiv_antitone (a : ι → ℝ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, Antitone (a ∘ e) := by
  classical
  refine ⟨(Tuple.sort fun j => -a ((Fintype.equivFin ι).symm j)).trans (Fintype.equivFin ι).symm,
    fun i j hij => ?_⟩
  have h := Tuple.monotone_sort (fun j => -a ((Fintype.equivFin ι).symm j)) hij
  simpa only [Function.comp_apply, neg_le_neg_iff, Equiv.trans_apply] using h

/-- The pairing of a weight vector with a weakly majorized vector is at most its pairing with a
permutation of the majorizing vector, when the totals agree or the weight is nonnegative. -/
private theorem exists_perm_sum_mul_le_aux {x y : ι → ℝ} (h : WeaklyMajorized x y) (a : ι → ℝ)
    (hc : ∑ i, x i = ∑ i, y i ∨ ∀ i, 0 ≤ a i) :
    ∃ σ : Equiv.Perm ι, ∑ i, a i * x i ≤ ∑ i, a i * y (σ i) := by
  obtain ⟨e₁, ha⟩ := exists_equiv_antitone a
  obtain ⟨e₂, hy⟩ := exists_equiv_antitone y
  refine ⟨e₁.symm.trans e₂, ?_⟩
  have h1 : ∑ i, a i * x i = ∑ j, (a ∘ e₁) j * (x ∘ e₁) j :=
    (Equiv.sum_comp e₁ fun i => a i * x i).symm
  have h2 : ∑ i, a i * y ((e₁.symm.trans e₂) i) = ∑ j, (a ∘ e₁) j * (y ∘ e₂) j := by
    rw [← Equiv.sum_comp e₁]
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [h1, h2]
  refine sum_mul_le_sum_mul_of_antitone ha (fun k _ => ?_) ?_
  · rw [← sumLargest_eq_sum_of_antitone hy, sumLargest_comp_equiv, ← Finset.sum_filter]
    refine le_trans ?_ (h k)
    refine (sum_le_sumLargest_of_card_eq (x ∘ e₁) ?_).trans_eq (sumLargest_comp_equiv x e₁ k)
    rw [Fin.card_filter_val_lt, Fintype.card_fin, min_comm]
  · obtain hc | hc := hc
    · exact Or.inl ((Equiv.sum_comp e₁ x).trans (hc.trans (Equiv.sum_comp e₂ y).symm))
    · exact Or.inr fun j => hc _

/-- **Rearrangement through majorization.** If `x` is majorized by `y` then for every weight
vector `a` there is a permutation `σ` with `∑ a i * x i ≤ ∑ a i * y (σ i)`.
Port of `NLAlib.Majorized.exists_perm_sum_mul_le`. -/
theorem Majorized.exists_perm_sum_mul_le {x y : ι → ℝ} (h : Majorized x y) (a : ι → ℝ) :
    ∃ σ : Equiv.Perm ι, ∑ i, a i * x i ≤ ∑ i, a i * y (σ i) := by
  exact exists_perm_sum_mul_le_aux h.weaklyMajorized a (Or.inl h.sum_eq)

/-- **Rearrangement through weak majorization.** If `x` is weakly majorized by `y` then for every
nonnegative weight vector `a` there is a permutation `σ` with `∑ a i * x i ≤ ∑ a i * y (σ i)`.
The majorized case, with no sign condition on `a`, is `NLAlib.Majorized.exists_perm_sum_mul_le`. -/
theorem WeaklyMajorized.exists_perm_sum_mul_le {x y : ι → ℝ} (h : WeaklyMajorized x y)
    {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    ∃ σ : Equiv.Perm ι, ∑ i, a i * x i ≤ ∑ i, a i * y (σ i) := by
  exact exists_perm_sum_mul_le_aux h a (Or.inr ha)

/-! ### Hardy–Littlewood–Pólya and Rado -/

/-- A continuous linear functional on `ι → ℝ` is a pairing with a weight vector. -/
private theorem exists_forall_apply_eq_sum_mul (f : StrongDual ℝ (ι → ℝ)) :
    ∃ a : ι → ℝ, ∀ z, f z = ∑ i, a i * z i := by
  classical
  refine ⟨fun i => f fun j => if i = j then 1 else 0, fun z => ?_⟩
  have h := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) z
  simp only [smul_eq_mul, ContinuousLinearMap.coe_coe] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem Majorized.mem_convexHull_permutations {x y : ι → ℝ} (h : Majorized x y) :
    x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) := by
  by_contra hx
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    ((Set.finite_range fun σ : Equiv.Perm ι => y ∘ σ).isClosed_convexHull ℝ) hx
  obtain ⟨a, ha⟩ := exists_forall_apply_eq_sum_mul f
  obtain ⟨σ, hσ⟩ := h.exists_perm_sum_mul_le a
  have hlt := hu _ (subset_convexHull ℝ _ ⟨σ, rfl⟩)
  have hle : f x ≤ f (y ∘ σ) := by
    rw [ha x, ha (y ∘ σ)]
    exact hσ
  linarith

/-- Birkhoff's theorem transported along `D ↦ D *ᵥ y`. -/
private theorem mem_convexHull_permutations_iff_exists_doublyStochastic [DecidableEq ι]
    {x y : ι → ℝ} : x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) ↔
      ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x := by
  let F : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ) := (Matrix.mulVecBilin ℝ ℝ).flip y
  have him : F '' {σ.permMatrix ℝ | σ : Equiv.Perm ι} =
      Set.range fun σ : Equiv.Perm ι => y ∘ σ := by
    ext z
    constructor
    · rintro ⟨D, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, (Matrix.permMatrix_mulVec ..).symm⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨σ.permMatrix ℝ, ⟨σ, rfl⟩, Matrix.permMatrix_mulVec ..⟩
  rw [← him, ← F.image_convexHull, ← doublyStochastic_eq_convexHull_permMatrix]
  rfl

/-- **Rado's theorem.** `x` is majorized by `y` exactly when `x` lies in the convex hull of the
permutations of `y`. [HornJohnson2013, Theorem 4.3.49].
Port of `NLAlib.majorized_iff_mem_convexHull_permutations`.
Result: majorization-convex-hull -/
theorem majorized_iff_mem_convexHull_permutations {x y : ι → ℝ} :
    Majorized x y ↔ x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) := by
  classical
  refine ⟨fun h => h.mem_convexHull_permutations, fun h => ?_⟩
  obtain ⟨D, hD, rfl⟩ := mem_convexHull_permutations_iff_exists_doublyStochastic.mp h
  exact majorized_mulVec_of_mem_doublyStochastic y hD

/-- **Hardy–Littlewood–Pólya.** `x` is majorized by `y` exactly when `x = D y` for some doubly
stochastic matrix `D`. [HornJohnson2013, Theorem 4.3.49].
Port of `NLAlib.majorized_iff_exists_doublyStochastic`.
Result: hardy-littlewood-polya -/
theorem majorized_iff_exists_doublyStochastic [DecidableEq ι] {x y : ι → ℝ} :
    Majorized x y ↔ ∃ D ∈ doublyStochastic ℝ ι, D *ᵥ y = x := by
  rw [majorized_iff_mem_convexHull_permutations,
    mem_convexHull_permutations_iff_exists_doublyStochastic]

/-! ### Convex functions -/

/-- **Karamata's inequality.** If `x` is majorized by `y` and `φ` is convex, then
`∑ φ (x i) ≤ ∑ φ (y i)`. [HornJohnson2013, Theorem 4.3.50].
Port of `NLAlib.Majorized.sum_convex_le`.
Result: karamata-inequality -/
theorem Majorized.sum_convex_le {x y : ι → ℝ} (h : Majorized x y) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) : ∑ i, φ (x i) ≤ ∑ i, φ (y i) := by
  classical
  obtain ⟨D, hD, rfl⟩ := majorized_iff_exists_doublyStochastic.mp h
  calc ∑ i, φ ((D *ᵥ y) i) ≤ ∑ i, ∑ j, D i j * φ (y j) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := hφ.map_sum_le (t := Finset.univ) (w := fun j => D i j) (p := y)
          (fun j _ => nonneg_of_mem_doublyStochastic hD) (sum_row_of_mem_doublyStochastic hD i)
          fun j _ => Set.mem_univ (y j)
        simpa only [Matrix.mulVec, dotProduct, smul_eq_mul] using hi
    _ = ∑ j, φ (y j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hD j, one_mul]

/-- **Schur-convexity of symmetric convex functions.** If `x` is majorized by `y` and
`Φ : (ι → ℝ) → ℝ` is convex and invariant under permutations of the coordinates, then
`Φ x ≤ Φ y`. Karamata's inequality is the separable case `Φ z = ∑ i, φ (z i)`.
[HornJohnson2013, Theorem 4.3.49 with Birkhoff's theorem 8.7.2]; [Bhatia1997, Theorem II.3.3]. -/
theorem Majorized.le_of_convexOn_of_comp_perm {x y : ι → ℝ} (h : Majorized x y)
    {Φ : (ι → ℝ) → ℝ} (hΦ : ConvexOn ℝ Set.univ Φ)
    (hperm : ∀ (z : ι → ℝ) (σ : Equiv.Perm ι), Φ (z ∘ σ) = Φ z) : Φ x ≤ Φ y := by
  obtain ⟨z, ⟨σ, rfl⟩, hz⟩ := hΦ.exists_ge_of_mem_convexHull (Set.subset_univ _)
    (majorized_iff_mem_convexHull_permutations.mp h)
  exact hz.trans_eq (hperm y σ)

private theorem convexOn_max_sub (a : ℝ) : ConvexOn ℝ Set.univ fun u : ℝ => max (u - a) 0 := by
  have h : ConvexOn ℝ Set.univ fun u : ℝ => u - a :=
    (convexOn_id convex_univ).sub (concaveOn_const a convex_univ)
  exact h.sup (convexOn_const 0 convex_univ)

private theorem sumLargest_le_mul_add_sum_max_sub (x : ι → ℝ) (k : ℕ) (a : ℝ) :
    sumLargest x k ≤ (min k (Fintype.card ι) : ℕ) * a + ∑ i, max (x i - a) 0 := by
  refine sumLargest_le fun s hs => ?_
  have h1 : ∑ i ∈ s, x i = s.card * a + ∑ i ∈ s, (x i - a) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have h2 : ∑ i ∈ s, (x i - a) ≤ ∑ i ∈ s, max (x i - a) 0 :=
    Finset.sum_le_sum fun i _ => le_max_left _ _
  have h3 : ∑ i ∈ s, max (x i - a) 0 ≤ ∑ i, max (x i - a) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun i _ _ => le_max_right _ _
  rw [h1, hs]
  linarith

private theorem weaklyMajorized_of_forall_sum_max_sub_le {x y : ι → ℝ}
    (h : ∀ a : ℝ, ∑ i, max (x i - a) 0 ≤ ∑ i, max (y i - a) 0) : WeaklyMajorized x y := by
  classical
  intro k
  obtain ⟨t, c, ht, htc, hct, hsum⟩ := exists_threshold y k
  have hterm (i : ι) : max (y i - c) 0 = if i ∈ t then y i - c else 0 := by
    split_ifs with hi
    · exact max_eq_left (sub_nonneg.mpr (htc i hi))
    · exact max_eq_right (sub_nonpos.mpr (hct i hi))
  have hy : ∑ i, max (y i - c) 0 = sumLargest y k - (min k (Fintype.card ι) : ℕ) * c := by
    simp only [hterm]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib, Finset.sum_const, ht,
      hsum, nsmul_eq_mul]
  have hx := sumLargest_le_mul_add_sum_max_sub x k c
  have hc := h c
  linarith

/-- Majorization is characterised by convex functions.
Port of `NLAlib.majorized_iff_sum_convex_le`. -/
theorem majorized_iff_forall_sum_convex_le {x y : ι → ℝ} :
    Majorized x y ↔ ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → ∑ i, φ (x i) ≤ ∑ i, φ (y i) := by
  refine ⟨fun h φ hφ => h.sum_convex_le hφ, fun h =>
    ⟨weaklyMajorized_of_forall_sum_max_sub_le fun a => h _ (convexOn_max_sub a), ?_⟩⟩
  have hpos := h id (convexOn_id convex_univ)
  have hneg := h (fun u => -u) (concaveOn_id convex_univ).neg
  simp only [id_eq, Finset.sum_neg_distrib, neg_le_neg_iff] at hpos hneg
  exact le_antisymm hpos hneg

/-! ### Weak majorization -/

private theorem WeaklyMajorized.mem_convexHull_add_Iic {x y : ι → ℝ} (h : WeaklyMajorized x y) :
    x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) + Set.Iic (0 : ι → ℝ) := by
  classical
  have hclosed : IsClosed
      (convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) + Set.Iic (0 : ι → ℝ)) :=
    isClosed_Iic.add_left_of_isCompact
      ((Set.finite_range fun σ : Equiv.Perm ι => y ∘ σ).isCompact_convexHull ℝ)
  have hconvex : Convex ℝ
      (convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) + Set.Iic (0 : ι → ℝ)) :=
    (convex_convexHull ℝ _).add (convex_Iic _)
  have hmem (σ : Equiv.Perm ι) : y ∘ σ ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm ι => y ∘ σ) :=
    subset_convexHull ℝ _ ⟨σ, rfl⟩
  by_contra hx
  obtain ⟨f, u, hu, hux⟩ := geometric_hahn_banach_closed_point hconvex hclosed hx
  obtain ⟨a, ha⟩ := exists_forall_apply_eq_sum_mul f
  have hperm (σ : Equiv.Perm ι) : f (y ∘ σ) < u := by
    have hlt := hu _ (Set.add_mem_add (hmem σ) (Set.mem_Iic.mpr (le_refl (0 : ι → ℝ))))
    rwa [add_zero] at hlt
  have ha0 (i : ι) : 0 ≤ a i := by
    by_contra hi
    rw [not_le] at hi
    have hfy : f y < u := hperm (Equiv.refl ι)
    have hsingle : f (Pi.single i 1) = a i := by
      rw [ha]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have ht : 0 ≤ (u - f y) / (-a i) :=
      div_nonneg (sub_nonneg.mpr hfy.le) (neg_nonneg.mpr hi.le)
    have hw : (-((u - f y) / (-a i))) • Pi.single i (1 : ℝ) ≤ (0 : ι → ℝ) :=
      smul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Pi.single_nonneg.mpr zero_le_one)
    have hlt := hu _ (Set.add_mem_add (hmem (Equiv.refl ι)) (Set.mem_Iic.mpr hw))
    have hcancel : (u - f y) / (-a i) * (-a i) = u - f y :=
      div_mul_cancel₀ _ (neg_pos.mpr hi).ne'
    rw [map_add, map_smul, hsingle, smul_eq_mul] at hlt
    have hfy' : f (y ∘ Equiv.refl ι) = f y := rfl
    linarith
  obtain ⟨σ, hσ⟩ := h.exists_perm_sum_mul_le ha0
  have hle : f x ≤ f (y ∘ σ) := by
    rw [ha x, ha (y ∘ σ)]
    exact hσ
  linarith [hperm σ]

/-- A weakly majorized vector lies below a majorized one: `x ≤ z` entrywise with `z` majorized
by `y`. Port of `NLAlib.WeaklyMajorized.exists_le_majorized`. -/
theorem WeaklyMajorized.exists_le_majorized {x y : ι → ℝ} (h : WeaklyMajorized x y) :
    ∃ z : ι → ℝ, x ≤ z ∧ Majorized z y := by
  obtain ⟨z, hz, w, hw, rfl⟩ := h.mem_convexHull_add_Iic
  exact ⟨z, add_le_of_nonpos_right hw, majorized_iff_mem_convexHull_permutations.mpr hz⟩

/-- If `x` is weakly majorized by `y` and `Φ : (ι → ℝ) → ℝ` is convex, monotone and invariant
under permutations of the coordinates, then `Φ x ≤ Φ y`. This is the form in which symmetric
gauge functions consume weak majorization. [Bhatia1997, Theorem II.3.3 and Example II.3.5]. -/
theorem WeaklyMajorized.le_of_convexOn_of_monotone_of_comp_perm {x y : ι → ℝ}
    (h : WeaklyMajorized x y) {Φ : (ι → ℝ) → ℝ} (hΦ : ConvexOn ℝ Set.univ Φ) (hmono : Monotone Φ)
    (hperm : ∀ (z : ι → ℝ) (σ : Equiv.Perm ι), Φ (z ∘ σ) = Φ z) : Φ x ≤ Φ y := by
  obtain ⟨z, hxz, hzy⟩ := h.exists_le_majorized
  exact (hmono hxz).trans (hzy.le_of_convexOn_of_comp_perm hΦ hperm)

/-- **Tomić–Weyl.** If `x` is weakly majorized by `y` and `φ` is monotone and convex, then
`∑ φ (x i) ≤ ∑ φ (y i)`. [HornJohnson1991, Theorem 3.3.14 context].
Port of `NLAlib.WeaklyMajorized.sum_monotone_convex_le`.
Result: tomic-weyl-inequality -/
theorem WeaklyMajorized.sum_monotone_convex_le {x y : ι → ℝ} (h : WeaklyMajorized x y)
    {φ : ℝ → ℝ} (hφm : Monotone φ) (hφ : ConvexOn ℝ Set.univ φ) :
    ∑ i, φ (x i) ≤ ∑ i, φ (y i) := by
  obtain ⟨z, hxz, hzy⟩ := h.exists_le_majorized
  exact (Finset.sum_le_sum fun i _ => hφm (hxz i)).trans (hzy.sum_convex_le hφ)

/-- Weak majorization is characterised by the hinge functions `u ↦ max (u - a) 0`.
Port of `NLAlib.weaklyMajorized_iff_sum_max_sub_le`. -/
theorem weaklyMajorized_iff_forall_sum_max_sub_le {x y : ι → ℝ} :
    WeaklyMajorized x y ↔ ∀ a : ℝ, ∑ i, max (x i - a) 0 ≤ ∑ i, max (y i - a) 0 := by
  refine ⟨fun h a => h.sum_monotone_convex_le (fun u v huv => ?_) (convexOn_max_sub a),
    weaklyMajorized_of_forall_sum_max_sub_le⟩
  exact max_le_max (sub_le_sub_right huv a) le_rfl

/-- Weak majorization is characterised by monotone convex functions: `x` is weakly majorized by
`y` exactly when `∑ φ (x i) ≤ ∑ φ (y i)` for every monotone convex `φ`. The forward direction
is `NLAlib.WeaklyMajorized.sum_monotone_convex_le`; the converse tests the hinge functions
`u ↦ max (u - a) 0`, as in `NLAlib.weaklyMajorized_iff_forall_sum_max_sub_le`. -/
theorem weaklyMajorized_iff_forall_sum_monotone_convex_le {x y : ι → ℝ} :
    WeaklyMajorized x y ↔
      ∀ φ : ℝ → ℝ, Monotone φ → ConvexOn ℝ Set.univ φ → ∑ i, φ (x i) ≤ ∑ i, φ (y i) := by
  refine ⟨fun h φ hφm hφ => h.sum_monotone_convex_le hφm hφ, fun h =>
    weaklyMajorized_of_forall_sum_max_sub_le fun a => h _ (fun u v huv => ?_) (convexOn_max_sub a)⟩
  exact max_le_max (sub_le_sub_right huv a) le_rfl

/-! ### Transport plans -/

/-- A doubly stochastic transport plan costs at least as much as the best permutation.
Port of `NLAlib.exists_perm_sum_le_doublyStochastic_cost`. -/
theorem exists_perm_sum_le_sum_mul_of_mem_doublyStochastic [DecidableEq ι] (C : Matrix ι ι ℝ)
    {W : Matrix ι ι ℝ} (hW : W ∈ doublyStochastic ℝ ι) :
    ∃ σ : Equiv.Perm ι, ∑ i, C i (σ i) ≤ ∑ i, ∑ j, W i j * C i j := by
  let f : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun X := ∑ i, ∑ j, X i j * C i j
      map_add' X Y := by simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' c X := by
        simp only [RingHom.id_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc,
          Finset.mul_sum] }
  have hconv : W ∈ convexHull ℝ {σ.permMatrix ℝ | σ : Equiv.Perm ι} := by
    rwa [← doublyStochastic_eq_convexHull_permMatrix]
  obtain ⟨P, ⟨σ, rfl⟩, hP⟩ := (f.concaveOn convex_univ).exists_le_of_mem_convexHull
    (Set.subset_univ _) hconv
  refine ⟨σ, ?_⟩
  simpa only [f, Equiv.Perm.permMatrix, LinearMap.coe_mk, AddHom.coe_mk, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] using hP

end NLAlib
