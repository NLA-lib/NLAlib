/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Interval.Set.Basic

/-!
# Majorization of real vectors

For real vectors `x y : ι → ℝ` on a finite index type, `NLAlib.Majorized x y` says that `x` is
majorized by `y`: for every `k` the sum of the `k` largest entries of `x` is at most that of `y`,
and the total sums agree. `NLAlib.WeaklyMajorized x y` drops the equality of the totals.

The vectors need not be sorted: `NLAlib.sumLargest x k` is the largest sum of `k` entries of `x`,
defined as a maximum over index sets, with no sorting and no chosen enumeration. For a sequence
that is already non-increasing, such as the eigenvalues or singular values of a matrix, it is the
partial sum (`NLAlib.sumLargest_fin_eq_sum_range`), and majorization is the family of partial-sum
inequalities (`NLAlib.weaklyMajorized_fin_iff_sum_range_le`). Statements about spectra are given
in that partial-sum form; the predicates are for unsorted vectors and for the general theory.

## Main definitions

* `NLAlib.sumLargest`: the sum of the `k` largest entries.
* `NLAlib.WeaklyMajorized`, `NLAlib.Majorized`: weak majorization and majorization.

## Main results

* `NLAlib.sum_le_sumLargest`, `NLAlib.sumLargest_le`,
  `NLAlib.exists_card_eq_and_sum_eq_sumLargest`: `sumLargest` is the maximum over index sets of
  size `k`.
* `NLAlib.sumLargest_add_le`: subadditivity.
* `NLAlib.convexOn_sumLargest_abs`: the sum of the `k` largest absolute values is convex.
* `NLAlib.sumLargest_eq_sum_of_forall_le`: an index set whose entries dominate all the others
  attains the maximum.
* `NLAlib.sumLargest_fin_eq_sum_range`, `NLAlib.sum_le_sum_range_card_of_antitone`: partial sums
  of a non-increasing sequence.
* `NLAlib.weaklyMajorized_iff_forall_sum_le`: weak majorization tested on arbitrary index sets.
* `NLAlib.Majorized.trans`, `NLAlib.Majorized.comp_equiv_left`,
  `NLAlib.WeaklyMajorized.comp_equiv_left`: order properties and invariance under permutations.
* `NLAlib.majorized_comp_equiv_iff`: invariance under relabelling both vectors.
* `NLAlib.exists_equiv_antitone_comp`, `NLAlib.sumLargest_succ_of_antitone`: sorting a vector,
  and the partial sums of a sorted one.
-/

@[expose] public section

namespace NLAlib

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### The sum of the largest entries -/

/-- The **sum of the `k` largest entries** of a real vector: the maximum of `∑ i ∈ s, x i` over
index sets `s` with `min k (card ι)` elements. For `k` at least the number of entries it is the
total sum. No sorting is involved.
[HornJohnson2013, §4.3.47]. Port of `NLAlib.sumLargest`, there through a sorting equivalence. -/
noncomputable def sumLargest (x : ι → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.powersetCard (min k (Fintype.card ι))).sup'
    (Finset.powersetCard_nonempty.mpr (by simp)) fun s => ∑ i ∈ s, x i

/-- A sum over an index set with `min k (card ι)` elements is at most the sum of the `k` largest
entries. This is the form of `sum_le_sumLargest` for a `k` that is not syntactically a
cardinality. -/
theorem sum_le_sumLargest_of_card_eq (x : ι → ℝ) {s : Finset ι} {k : ℕ}
    (hs : s.card = min k (Fintype.card ι)) : ∑ i ∈ s, x i ≤ sumLargest x k := by
  exact Finset.le_sup' (fun s => ∑ i ∈ s, x i)
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hs⟩)

/-- A bound on every sum over `min k (card ι)` indices bounds the sum of the `k` largest
entries. -/
theorem sumLargest_le {x : ι → ℝ} {k : ℕ} {c : ℝ}
    (h : ∀ s : Finset ι, s.card = min k (Fintype.card ι) → ∑ i ∈ s, x i ≤ c) :
    sumLargest x k ≤ c := by
  exact Finset.sup'_le _ _ fun s hs => h s (Finset.mem_powersetCard.mp hs).2

/-- The maximum defining `sumLargest` is attained, for every `k`, on an index set with
`min k (card ι)` elements. -/
theorem exists_card_eq_min_and_sum_eq_sumLargest (x : ι → ℝ) (k : ℕ) :
    ∃ s : Finset ι, s.card = min k (Fintype.card ι) ∧ ∑ i ∈ s, x i = sumLargest x k := by
  have hne : (Finset.univ.powersetCard (min k (Fintype.card ι)) : Finset (Finset ι)).Nonempty :=
    Finset.powersetCard_nonempty.mpr (by simp)
  obtain ⟨s, hs, h⟩ := Finset.exists_mem_eq_sup' hne fun s : Finset ι => ∑ i ∈ s, x i
  exact ⟨s, (Finset.mem_powersetCard.mp hs).2, h.symm⟩

/-- The maximum defining `sumLargest` is attained.
Port of `NLAlib.isGreatest_sumLargest`. -/
theorem exists_card_eq_and_sum_eq_sumLargest (x : ι → ℝ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    ∃ s : Finset ι, s.card = k ∧ ∑ i ∈ s, x i = sumLargest x k := by
  obtain ⟨s, hs, h⟩ := exists_card_eq_min_and_sum_eq_sumLargest x k
  exact ⟨s, hs.trans (min_eq_left hk), h⟩

/-- Truncating `k` at the number of entries does not change `sumLargest`. -/
@[simp]
theorem sumLargest_min_card (x : ι → ℝ) (k : ℕ) :
    sumLargest x (min k (Fintype.card ι)) = sumLargest x k := by
  simp only [sumLargest, min_assoc, min_self]

/-- The sum of the zero largest entries is zero. -/
@[simp]
theorem sumLargest_zero (x : ι → ℝ) : sumLargest x 0 = 0 := by
  obtain ⟨s, hs, h⟩ := exists_card_eq_and_sum_eq_sumLargest x (Nat.zero_le (Fintype.card ι))
  rw [← h, Finset.card_eq_zero.mp hs, Finset.sum_empty]

/-- Beyond the number of entries, `sumLargest` is the total sum.
Port of `NLAlib.sumLargest_eq_sum_of_card_le`. -/
theorem sumLargest_of_card_le (x : ι → ℝ) {k : ℕ} (hk : Fintype.card ι ≤ k) :
    sumLargest x k = ∑ i, x i := by
  obtain ⟨s, hs, h⟩ := exists_card_eq_min_and_sum_eq_sumLargest x k
  rw [min_eq_right hk] at hs
  rw [← h, (Finset.card_eq_iff_eq_univ s).mp hs]

/-- Any sum over an index set is at most the sum of that many largest entries.
Port of `NLAlib.sum_le_sumLargest`. -/
theorem sum_le_sumLargest (x : ι → ℝ) (s : Finset ι) : ∑ i ∈ s, x i ≤ sumLargest x s.card := by
  exact sum_le_sumLargest_of_card_eq x (min_eq_left s.card_le_univ).symm

private theorem sumLargest_comp_equiv_le (x : ι → ℝ) (e : κ ≃ ι) (k : ℕ) :
    sumLargest (x ∘ e) k ≤ sumLargest x k := by
  refine sumLargest_le fun s hs => ?_
  have h : ∑ i ∈ s, (x ∘ e) i = ∑ j ∈ s.map e.toEmbedding, x j := by
    rw [Finset.sum_map]
    rfl
  rw [h]
  refine sum_le_sumLargest_of_card_eq x ?_
  rw [Finset.card_map, hs, Fintype.card_congr e]

/-- `sumLargest` is invariant under relabelling. Port of `NLAlib.sumLargest_comp_perm`. -/
@[simp]
theorem sumLargest_comp_equiv (x : ι → ℝ) (e : κ ≃ ι) (k : ℕ) :
    sumLargest (x ∘ e) k = sumLargest x k := by
  refine le_antisymm (sumLargest_comp_equiv_le x e k) ?_
  have h := sumLargest_comp_equiv_le (x ∘ e) e.symm k
  rwa [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h

/-- `sumLargest` is subadditive. Port of `NLAlib.sumLargest_add_le`. -/
theorem sumLargest_add_le (x y : ι → ℝ) (k : ℕ) :
    sumLargest (x + y) k ≤ sumLargest x k + sumLargest y k := by
  refine sumLargest_le fun s hs => ?_
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  exact add_le_add (sum_le_sumLargest_of_card_eq x hs) (sum_le_sumLargest_of_card_eq y hs)

/-- `sumLargest` is monotone in the vector. -/
theorem sumLargest_mono {x y : ι → ℝ} (h : x ≤ y) (k : ℕ) : sumLargest x k ≤ sumLargest y k := by
  refine sumLargest_le fun _ hs => ?_
  exact (Finset.sum_le_sum fun i _ => h i).trans (sum_le_sumLargest_of_card_eq y hs)

/-- `sumLargest` is homogeneous for nonnegative scalars. -/
theorem sumLargest_smul {c : ℝ} (hc : 0 ≤ c) (x : ι → ℝ) (k : ℕ) :
    sumLargest (c • x) k = c * sumLargest x k := by
  have hsum (s : Finset ι) : ∑ i ∈ s, (c • x) i = c * ∑ i ∈ s, x i := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine le_antisymm (sumLargest_le fun s hs => ?_) ?_
  · rw [hsum]
    exact mul_le_mul_of_nonneg_left (sum_le_sumLargest_of_card_eq x hs) hc
  · obtain ⟨s, hs, h⟩ := exists_card_eq_min_and_sum_eq_sumLargest x k
    rw [← h, ← hsum]
    exact sum_le_sumLargest_of_card_eq (c • x) hs

/-- The sum of the `k` largest absolute values of the entries is a convex function of a real
vector. It is also invariant under permutations (`sumLargest_comp_equiv`), so with
`Majorized.le_of_convexOn_of_comp_perm` a majorization gives inequalities between sums of largest
absolute values. -/
theorem convexOn_sumLargest_abs (k : ℕ) :
    ConvexOn ℝ Set.univ fun z : ι → ℝ => sumLargest (fun i => |z i|) k := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  have h : (fun i => |(a • x + b • y) i|) ≤ (a • fun i => |x i|) + b • fun i => |y i| := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
      _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  calc sumLargest (fun i => |(a • x + b • y) i|) k
      ≤ sumLargest ((a • fun i => |x i|) + b • fun i => |y i|) k := sumLargest_mono h k
    _ ≤ sumLargest (a • fun i => |x i|) k + sumLargest (b • fun i => |y i|) k :=
        sumLargest_add_le _ _ k
    _ = a • sumLargest (fun i => |x i|) k + b • sumLargest (fun i => |y i|) k := by
        rw [sumLargest_smul ha, sumLargest_smul hb, smul_eq_mul, smul_eq_mul]

/-- **Recognising the largest entries.** If an index set `t` with `min k (card ι)` elements
carries entries that are all at least every entry outside it, the sum of the `k` largest entries
is the sum over `t`. -/
theorem sumLargest_eq_sum_of_forall_le {x : ι → ℝ} {t : Finset ι} {k : ℕ}
    (ht : t.card = min k (Fintype.card ι)) (h : ∀ i ∈ t, ∀ j ∉ t, x j ≤ x i) :
    sumLargest x k = ∑ i ∈ t, x i := by
  classical
  refine le_antisymm (sumLargest_le fun s hs => ?_) (sum_le_sumLargest_of_card_eq x ht)
  have hcard : (s \ t).card = (t \ s).card := Finset.card_sdiff_comm (hs.trans ht.symm)
  have hle : ∑ i ∈ s \ t, x i ≤ ∑ i ∈ t \ s, x i := by
    obtain hts | hts := (t \ s).eq_empty_or_nonempty
    · rw [hts, Finset.card_empty, Finset.card_eq_zero] at hcard
      rw [hts, hcard]
    · have h1 : ∑ i ∈ s \ t, x i ≤ (s \ t).card • (t \ s).inf' hts x :=
        Finset.sum_le_card_nsmul _ _ _ fun j hj => (Finset.le_inf' _ _) fun i hi =>
          h i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2
      have h2 : (t \ s).card • (t \ s).inf' hts x ≤ ∑ i ∈ t \ s, x i :=
        Finset.card_nsmul_le_sum _ _ _ fun i hi => Finset.inf'_le _ hi
      exact h1.trans (hcard ▸ h2)
  have hsub := Finset.sum_sdiff_sub_sum_sdiff (s₁ := s) (s₂ := t) (f := x)
  linarith

/-- For a non-increasing family indexed by `Fin N`, the sum of the `k` largest entries is the sum
of the first `k`. Port of `NLAlib.sumLargest_eq_prefix_of_antitone`. -/
theorem sumLargest_eq_sum_of_antitone {N : ℕ} {a : Fin N → ℝ} (ha : Antitone a) (k : ℕ) :
    sumLargest a k = ∑ i : Fin N, if (i : ℕ) < k then a i else 0 := by
  rw [← Finset.sum_filter]
  refine sumLargest_eq_sum_of_forall_le ?_ fun i hi j hj => ha ?_
  · rw [Fin.card_filter_val_lt, Fintype.card_fin, min_comm]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi hj
    exact Fin.le_def.mpr (hi.le.trans hj)

/-- **Partial sums of a sorted sequence.** If `f : ℕ → ℝ` is non-increasing below `N`, the sum of
the `k` largest of its first `N` values is the partial sum up to `min k N`. This is the bridge
between `sumLargest` and the ℕ-indexed eigenvalues and singular values. -/
theorem sumLargest_fin_eq_sum_range {f : ℕ → ℝ} {N : ℕ} (hf : AntitoneOn f (Set.Iio N))
    (k : ℕ) : sumLargest (fun i : Fin N => f i) k = ∑ i ∈ Finset.range (min k N), f i := by
  have ha : Antitone fun i : Fin N => f i := fun i j hij =>
    hf (Set.mem_Iio.mpr i.isLt) (Set.mem_Iio.mpr j.isLt) (Fin.le_def.mp hij)
  rw [sumLargest_eq_sum_of_antitone ha,
    Fin.sum_univ_eq_sum_range (fun i => if i < k then f i else 0) N, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff, and_comm]

/-- A sum of values of a non-increasing sequence over an index set `s` is at most the sum of its
first `s.card` values. This is `sum_le_sumLargest` for a sorted sequence indexed by `ℕ`, with no
bound on the indices. -/
theorem sum_le_sum_range_card_of_antitone {f : ℕ → ℝ} (hf : Antitone f) (s : Finset ℕ) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ Finset.range s.card, f i := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have h := Finset.card_le_card (fun i hi => Finset.mem_range.mpr (ha i hi) :
        s ⊆ Finset.range a)
      rwa [Finset.card_range] at h
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, Finset.sum_range_succ, add_comm]
    exact add_le_add ih (hf hcard)

/-! ### Majorization -/

/-- `x` is **weakly majorized** by `y`: for every `k`, the sum of the `k` largest entries of `x`
is at most that of `y`. [HornJohnson2013, Definition 4.3.41].
Port of `NLAlib.WeaklyMajorized`. -/
def WeaklyMajorized (x y : ι → ℝ) : Prop :=
  ∀ k, sumLargest x k ≤ sumLargest y k

/-- `x` is **majorized** by `y`: weak majorization together with equal total sums.
[HornJohnson2013, Definition 4.3.41]. Port of `NLAlib.Majorized`. -/
structure Majorized (x y : ι → ℝ) : Prop where
  /-- The sums of the `k` largest entries are ordered. -/
  weaklyMajorized : WeaklyMajorized x y
  /-- The total sums agree. -/
  sum_eq : ∑ i, x i = ∑ i, y i

/-- Weak majorization tested on arbitrary index sets: every partial sum of `x` over an index set
is at most the sum of that many largest entries of `y`.
Port of `NLAlib.weaklyMajorized_iff_sum_le`. -/
theorem weaklyMajorized_iff_forall_sum_le {x y : ι → ℝ} :
    WeaklyMajorized x y ↔ ∀ s : Finset ι, ∑ i ∈ s, x i ≤ sumLargest y s.card := by
  refine ⟨fun h s => (sum_le_sumLargest x s).trans (h s.card), fun h k => ?_⟩
  refine sumLargest_le fun s hs => ?_
  have hs' := h s
  rwa [hs, sumLargest_min_card] at hs'

/-- Weak majorization is reflexive. -/
@[refl]
theorem WeaklyMajorized.refl (x : ι → ℝ) : WeaklyMajorized x x := by
  intro k
  exact le_rfl

/-- Weak majorization is transitive. -/
theorem WeaklyMajorized.trans {x y z : ι → ℝ} (hxy : WeaklyMajorized x y)
    (hyz : WeaklyMajorized y z) : WeaklyMajorized x z := by
  intro k
  exact (hxy k).trans (hyz k)

/-- Majorization is reflexive. -/
@[refl]
theorem Majorized.refl (x : ι → ℝ) : Majorized x x := by
  exact ⟨WeaklyMajorized.refl x, rfl⟩

/-- Majorization is transitive. -/
theorem Majorized.trans {x y z : ι → ℝ} (hxy : Majorized x y) (hyz : Majorized y z) :
    Majorized x z := by
  exact ⟨hxy.weaklyMajorized.trans hyz.weaklyMajorized, hxy.sum_eq.trans hyz.sum_eq⟩

/-- An entrywise smaller vector is weakly majorized. -/
theorem weaklyMajorized_of_le {x y : ι → ℝ} (h : x ≤ y) : WeaklyMajorized x y := by
  intro k
  exact sumLargest_mono h k

/-- Every permutation of a vector is majorized by the vector.
Port of `NLAlib.majorized_comp_perm`. -/
theorem majorized_comp_equiv (x : ι → ℝ) (e : ι ≃ ι) : Majorized (x ∘ e) x := by
  exact ⟨fun k => (sumLargest_comp_equiv x e k).le, Equiv.sum_comp e x⟩

/-- Majorization is invariant under permuting the smaller vector. -/
theorem Majorized.comp_equiv_left {x y : ι → ℝ} (h : Majorized x y) (e : ι ≃ ι) :
    Majorized (x ∘ e) y := by
  exact (majorized_comp_equiv x e).trans h

/-- Majorization is invariant under permuting the larger vector. -/
theorem Majorized.comp_equiv_right {x y : ι → ℝ} (h : Majorized x y) (e : ι ≃ ι) :
    Majorized x (y ∘ e) := by
  exact ⟨fun k => (h.weaklyMajorized k).trans (sumLargest_comp_equiv y e k).ge,
    h.sum_eq.trans (Equiv.sum_comp e y).symm⟩

/-- Weak majorization is invariant under permuting the smaller vector. -/
theorem WeaklyMajorized.comp_equiv_left {x y : ι → ℝ} (h : WeaklyMajorized x y) (e : ι ≃ ι) :
    WeaklyMajorized (x ∘ e) y := by
  intro k
  exact (sumLargest_comp_equiv x e k).le.trans (h k)

/-- Weak majorization is invariant under permuting the larger vector. -/
theorem WeaklyMajorized.comp_equiv_right {x y : ι → ℝ} (h : WeaklyMajorized x y) (e : ι ≃ ι) :
    WeaklyMajorized x (y ∘ e) := by
  intro k
  exact (h k).trans (sumLargest_comp_equiv y e k).ge

/-- For a majorized pair, every partial sum of `x` is at least the sum of the smallest entries
of `y` of that count: the lower half of majorization.
Port of `NLAlib.Majorized.sum_sub_sumLargest_le_sum`. -/
theorem Majorized.sum_sub_sumLargest_le_sum {x y : ι → ℝ} (h : Majorized x y) (s : Finset ι)
    {d : ℕ} (hd : s.card + d = Fintype.card ι) :
    ∑ i, y i - sumLargest y d ≤ ∑ i ∈ s, x i := by
  classical
  have hcard : sᶜ.card = d := by
    rw [Finset.card_compl]
    omega
  have hcompl : ∑ i ∈ sᶜ, x i ≤ sumLargest y d :=
    hcard ▸ (sum_le_sumLargest x sᶜ).trans (h.weaklyMajorized sᶜ.card)
  have hsum : ∑ i ∈ s, x i + ∑ i ∈ sᶜ, x i = ∑ i, y i :=
    (Finset.sum_add_sum_compl s x).trans h.sum_eq
  linarith

/-- **Majorization of sorted sequences is the family of partial-sum inequalities.** For
`f g : ℕ → ℝ` non-increasing below `N`, weak majorization of their first `N` values is
`∑ i < k, f i ≤ ∑ i < k, g i` for all `k ≤ N`. -/
theorem weaklyMajorized_fin_iff_sum_range_le {f g : ℕ → ℝ} {N : ℕ}
    (hf : AntitoneOn f (Set.Iio N)) (hg : AntitoneOn g (Set.Iio N)) :
    WeaklyMajorized (fun i : Fin N => f i) (fun i : Fin N => g i) ↔
      ∀ k ≤ N, ∑ i ∈ Finset.range k, f i ≤ ∑ i ∈ Finset.range k, g i := by
  refine ⟨fun h k hk => ?_, fun h k => ?_⟩
  · have hk' := h k
    rwa [sumLargest_fin_eq_sum_range hf, sumLargest_fin_eq_sum_range hg, min_eq_left hk] at hk'
  · rw [sumLargest_fin_eq_sum_range hf, sumLargest_fin_eq_sum_range hg]
    exact h _ (min_le_right k N)

/-- **Weak majorization by a sorted sequence, tested on index sets.** If `f` is non-increasing
below `N` and every sum of entries of `x` over an index set `S` is at most the sum of the first
`S.card` values of `f`, then `x` is weakly majorized by the first `N` values of `f`. The vector
`x` need not be sorted. -/
theorem weaklyMajorized_fin_of_forall_sum_le {N : ℕ} {x : Fin N → ℝ} {f : ℕ → ℝ}
    (hf : AntitoneOn f (Set.Iio N))
    (h : ∀ S : Finset (Fin N), ∑ i ∈ S, x i ≤ ∑ i ∈ Finset.range S.card, f i) :
    WeaklyMajorized x (fun i : Fin N => f i) := by
  intro k
  rw [sumLargest_fin_eq_sum_range hf]
  refine sumLargest_le fun s hs => ?_
  rw [Fintype.card_fin] at hs
  exact hs ▸ h s

/-! ### Relabelling and sorting -/

/-- Majorization is invariant under relabelling both vectors by the same equivalence of index
types. For a permutation of one of the two vectors see `Majorized.comp_equiv_left` and
`Majorized.comp_equiv_right`. -/
theorem majorized_comp_equiv_iff {x y : ι → ℝ} (e : κ ≃ ι) :
    Majorized (x ∘ e) (y ∘ e) ↔ Majorized x y := by
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

/-- **Sorting.** Every real vector on a finite index type is non-increasing after relabelling
its indices by `Fin (card ι)`. With `sumLargest_comp_equiv` and `majorized_comp_equiv_iff` this
reduces a statement about `sumLargest` or majorization to sorted vectors. -/
theorem exists_equiv_antitone_comp (a : ι → ℝ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, Antitone (a ∘ e) := by
  classical
  refine ⟨(Tuple.sort fun j => -a ((Fintype.equivFin ι).symm j)).trans (Fintype.equivFin ι).symm,
    fun i j hij => ?_⟩
  have h := Tuple.monotone_sort (fun j => -a ((Fintype.equivFin ι).symm j)) hij
  simpa only [Function.comp_apply, neg_le_neg_iff, Equiv.trans_apply] using h

/-- For a non-increasing family indexed by `Fin N`, the sum of the `i + 1` largest entries is the
sum of the `i` largest plus the entry `i`. -/
theorem sumLargest_succ_of_antitone {N : ℕ} {y : Fin N → ℝ} (hy : Antitone y) (i : Fin N) :
    sumLargest y (i + 1) = sumLargest y i + y i := by
  have h (k : Fin N) : (if (k : ℕ) < i + 1 then y k else 0) =
      (if (k : ℕ) < i then y k else 0) + if k = i then y k else 0 := by
    obtain hlt | heq | hgt := lt_trichotomy (k : ℕ) i
    · rw [if_pos (Nat.lt_succ_of_lt hlt), if_pos hlt, if_neg (Fin.ne_of_val_ne hlt.ne), add_zero]
    · rw [if_pos (heq ▸ Nat.lt_succ_self _), if_neg (heq ▸ lt_irrefl _), if_pos (Fin.ext heq),
        zero_add]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (Fin.ne_of_val_ne hgt.ne'), add_zero]
  rw [sumLargest_eq_sum_of_antitone hy, sumLargest_eq_sum_of_antitone hy]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end NLAlib
