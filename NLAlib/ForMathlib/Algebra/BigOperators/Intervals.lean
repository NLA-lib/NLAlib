/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Sums of disjoint interval lengths and their costs

Upstream candidates for `Mathlib.Algebra.BigOperators.Intervals`. Disjoint finite intervals
inside one ambient interval use at most its length. A monotone superadditive cost therefore
bounds the sum of the costs of their lengths by the cost of the ambient length. Empty intervals
are allowed, so a layout may reserve an indexed slot without placing an object there.

## Main results

* `Finset.sum_le_of_pairwiseDisjoint_Ico`: the sum of the lengths is bounded by the ambient size.
* `Finset.sum_apply_le_of_pairwiseDisjoint_Ico`: the corresponding bound for superadditive costs.
-/

@[expose] public section

namespace Finset

/-- Pairwise disjoint intervals inside `[0, n)` use at most `n` positions in total. -/
theorem sum_le_of_pairwiseDisjoint_Ico {ι : Type*} (s : Finset ι)
    {off len : ι → ℕ} {n : ℕ}
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => Ico (off i) (off i + len i))
    (hbound : ∀ i ∈ s, off i + len i ≤ n) : ∑ i ∈ s, len i ≤ n := by
  classical
  have hsub : s.biUnion (fun i => Ico (off i) (off i + len i)) ⊆ range n := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
    exact mem_range.mpr ((mem_Ico.mp hx).2.trans_le (hbound i hi))
  have hcard := card_le_card hsub
  rw [card_biUnion hdisj] at hcard
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left, card_range] using hcard

/-- The sum of a superadditive cost on disjoint interval lengths is bounded by the cost of
an ambient size containing every interval. The cost is monotone and superadditive on
natural numbers. -/
theorem sum_apply_le_of_pairwiseDisjoint_Ico {ι : Type*} (s : Finset ι)
    {off len : ι → ℕ} {n : ℕ} {T : ℕ → ℕ} (hT : Monotone T)
    (hadd : ∀ a b, T a + T b ≤ T (a + b))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => Ico (off i) (off i + len i))
    (hbound : ∀ i ∈ s, off i + len i ≤ n) : ∑ i ∈ s, T (len i) ≤ T n := by
  have hsum : ∑ i ∈ s, T (len i) ≤ T (∑ i ∈ s, len i) := by
    simpa only [toAdd_prod, toAdd_ofAdd] using
      (s.sum_apply_le_apply_prod (f := fun i => Multiplicative.ofAdd (len i))
        (fun x : Multiplicative ℕ => T x.toAdd) (Nat.zero_le _)
        (fun a b => hadd a.toAdd b.toAdd))
  exact hsum.trans (hT (s.sum_le_of_pairwiseDisjoint_Ico hdisj hbound))

end Finset
