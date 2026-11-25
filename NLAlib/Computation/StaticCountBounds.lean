/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.ClosedCountBudget
public import NLAlib.Computation.StaticCost

/-!
# Pointwise bounds for static instruction counts

Sequences add count coordinates, branches take maxima and an index binder takes the
supremum of its bounded family. These elementary bounds turn compositional count estimates
into domination by the program-independent cubic allowance.

## Main results

* `NLAlib.Computation.sequence_count_le`: a uniform loop body bound times its length.
* `NLAlib.Computation.supRange_count_le`: a uniform bound for a bounded index choice.
* `NLAlib.Computation.count_le_closedCountBudget`: coordinatewise cubic domination.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι : Type}

/-- A single standard instruction contributes at most one to any coordinate. -/
theorem single_count_le (a o : OpKind P ι) : (Finsupp.single a 1 : OpCount P ι) o ≤ 1 := by
  classical
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

/-- Counts of a sequential composition add coordinatewise. -/
@[simp] theorem seq_count (a b : StaticCost P ι) (o : OpKind P ι) :
    (a.seq b).count o = a.count o + b.count o := rfl

/-- A scalar branch takes the larger coordinate count. -/
@[simp] theorem branch_count (a b : StaticCost P ι) (o : OpKind P ι) :
    (a.branch b).count o = max (a.count o) (b.count o) := by
  simp only [StaticCost.branch, Finsupp.sup_apply]

/-- Scoped allocation adds no scalar instruction. -/
@[simp] theorem alloc_count [DecidableEq P] (p : P) (len : ℕ) (width : P → ℕ)
    (a : StaticCost P ι) (o : OpKind P ι) :
    (StaticCost.alloc p len width a).count o = a.count o := rfl

/-- A loop whose every body count is bounded has its length times that count as budget. -/
theorem sequence_count_le {α : Type} (xs : List α) (cost : α → StaticCost P ι)
    (o : OpKind P ι) (bound : ℕ) (h : ∀ x ∈ xs, (cost x).count o ≤ bound) :
    (StaticCost.sequence xs cost).count o ≤ xs.length * bound := by
  induction xs with
  | nil => simp [StaticCost.sequence, StaticCost.zero]
  | cons x xs ih =>
    simp only [StaticCost.sequence, seq_count, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))).trans_eq (Nat.add_comm _ _)

/-- An unknown bounded index chooses one body, without multiplying its count by the range. -/
theorem supRange_count_le (m : ℕ) (cost : ℕ → StaticCost P ι)
    (o : OpKind P ι) (bound : ℕ) (h : ∀ k, k < m → (cost k).count o ≤ bound) :
    (StaticCost.supRange m cost).count o ≤ bound := by
  have hfold (xs : List ℕ) (hx : ∀ k ∈ xs, (cost k).count o ≤ bound) :
      (xs.foldr (fun k a => (cost k).branch a) StaticCost.zero).count o ≤ bound := by
    induction xs with
    | nil => exact Nat.zero_le _
    | cons x xs ih =>
      change max ((cost x).count o) _ ≤ bound
      exact max_le (hx x List.mem_cons_self) (ih (fun y hy => hx y (List.mem_cons_of_mem x hy)))
  exact hfold (List.range m) (fun k hk => h k (List.mem_range.mp hk))

/-- A uniform scalar instruction bound proves domination by the explicit closed budget. -/
theorem count_le_closedCountBudget (N : ℕ) (c : OpCount Unit Empty)
    (h : ∀ o, c o ≤ 1024 * (N + 1) ^ 3) : c ≤ closedCountBudget N := by
  intro o
  rw [closedCountBudget_apply]
  exact h o

end NLAlib.Computation
