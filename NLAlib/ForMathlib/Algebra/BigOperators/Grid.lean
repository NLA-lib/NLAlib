/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Abel

/-!
# Boundary sums on square grids

Internal edges cancel in the sum of oriented cell boundaries. Upstream candidate for Mathlib.

The boundary identity telescopes two finite sums using `Finset.sum_range_succ` and
`Finset.sum_range_succ'`. The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `Finset.sum_grid_boundary_eq`.
-/
@[expose] public section

section

namespace Finset

/-- In an additive commutative group, let $f(i+1)=g(i)$ at the interior nodes of
a chain of length $n>0$. Then $\sum_{i=0}^{n-1}(f(i)-g(i))=f(0)-g(n-1)$. -/
theorem sum_range_sub_of_adjacent {G : Type*} [AddCommGroup G]
    (f g : ℕ → G) {n : ℕ} (hn : 0 < n)
    (h : ∀ i, i + 1 < n → f (i + 1) = g i) :
    ∑ i ∈ range n, (f i - g i) = f 0 - g (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [sum_sub_distrib, sum_range_succ' f, sum_range_succ g]
  have hs : (∑ i ∈ range k, f (i + 1)) = ∑ i ∈ range k, g i := by
    apply sum_congr rfl
    intro i hi
    exact h i (Nat.succ_lt_succ (mem_range.mp hi))
  rw [hs]
  simp only [Nat.succ_sub_one]
  abel

/-- On an $n\times n$ grid with $n>0$, assign an element of an additive commutative
group to each oriented edge. If adjacent cells agree on their shared edge and the bottom
plus right edge equals the top plus left edge in each cell, the same identity holds for
the four side sums around the outside of the grid. -/
theorem sum_grid_boundary_eq {G : Type*} [AddCommGroup G]
    (bottom top left right : ℕ → ℕ → G) {n : ℕ} (hn : 0 < n)
    (hc : ∀ i < n, ∀ j < n, bottom i j + right i j = top i j + left i j)
    (hh : ∀ i < n, ∀ j, j + 1 < n → bottom i (j + 1) = top i j)
    (hv : ∀ i, i + 1 < n → ∀ j < n, left (i + 1) j = right i j) :
    (∑ j ∈ range n, right (n - 1) j) - (∑ j ∈ range n, left 0 j) =
      (∑ i ∈ range n, top i (n - 1)) - (∑ i ∈ range n, bottom i 0) := by
  have hzero : (∑ i ∈ range n, ∑ j ∈ range n,
      ((bottom i j - top i j) + (right i j - left i j))) = 0 := by
    apply sum_eq_zero
    intro i hi
    apply sum_eq_zero
    intro j hj
    have h := hc i (mem_range.mp hi) j (mem_range.mp hj)
    calc
      _ = (bottom i j + right i j) - (top i j + left i j) := by abel
      _ = 0 := sub_eq_zero.mpr h
  simp_rw [sum_add_distrib] at hzero
  have hhorizontal : (∑ i ∈ range n, ∑ j ∈ range n, (bottom i j - top i j)) =
      ∑ i ∈ range n, (bottom i 0 - top i (n - 1)) := by
    apply sum_congr rfl
    intro i hi
    exact sum_range_sub_of_adjacent _ _ hn (hh i (mem_range.mp hi))
  have hvertical : (∑ i ∈ range n, ∑ j ∈ range n, (right i j - left i j)) =
      ∑ j ∈ range n, (right (n - 1) j - left 0 j) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    have h := sum_range_sub_of_adjacent (fun i => left i j) (fun i => right i j)
      hn (fun i hi => hv i hi j (mem_range.mp hj))
    have hneg := congrArg Neg.neg h
    simpa only [← sum_neg_distrib, neg_sub] using hneg
  rw [hhorizontal, hvertical] at hzero
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  have h := eq_neg_of_add_eq_zero_right hzero
  simpa only [← sum_neg_distrib, neg_sub] using h

end Finset

end
