/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.CountBoundTactic
public import NLAlib.Matrix.Computation.DenseFactorizationResources
public import Mathlib.Tactic.Linarith

/-!
# Closed cubic instruction budgets for dense factorizations

Every coordinate of the actual static count for each of the seven stored factorization trees
is bounded by the independent cubic allowance. All offsets are zero. The precision-tag type
is `Unit`, the oracle-name type is `Empty`, and instruction charges are one at their own kind.
These comparisons are resource-analysis lemmas; the registered stored-entry targets also
supply numerical success, output guarantees and caller-plus-workspace memory bounds.

## Main results

* `NLAlib.Computation.luFactorResources_count_le`: unpivoted LU.
* `NLAlib.Computation.pluqFactorResources_count_le`: complete-pivoted LU.
* `NLAlib.Computation.choleskyResources_count_le`: positive-definite Cholesky.
-/

@[expose] public section

namespace NLAlib.Computation

/-- Every operation-kind count of the actual symbolic LU tree fits the independent cubic budget. -/
theorem luFactorResources_count_le (N : ℕ) :
    (luFactorResources (ι := Empty) (fun k => Finsupp.single k 1) (fun _ => 0)
      () N 0 0 0).count ≤ closedCountBudget N := by
  apply count_le_closedCountBudget
  intro o
  count_bound N
  nlinarith


/-- The actual partial-pivoted static count is dominated by the independent cubic budget. -/
theorem pluFactorResources_count_le (N : ℕ) :
    (pluFactorResources (fun k => Finsupp.single k 1) (fun _ => 0) () N 0 0 0 0).count ≤
      closedCountBudget N := by
  apply count_le_closedCountBudget
  intro kind
  count_bound N
  nlinarith

/-- The actual complete-pivoted static count is dominated by the independent cubic budget. -/
theorem pluqFactorResources_count_le (N : ℕ) :
    (pluqFactorResources (fun k => Finsupp.single k 1) (fun _ => 0) () N 0 0 0 0 0).count ≤
      closedCountBudget N := by
  apply count_le_closedCountBudget
  intro kind
  count_bound N
  nlinarith

-- The nested scaled scan needs additional elaboration work for its count majorant.
set_option maxHeartbeats 800000 in
-- This theorem-local allowance affects proof construction, not the algorithmic budget.
/-- The actual fixed-scale static count is dominated by the independent cubic budget. -/
theorem scaledPluFactorResources_count_le (N : ℕ) :
    (scaledPluFactorResources (fun k => Finsupp.single k 1) (fun _ => 0) () N 0 0 0 0).count ≤
      closedCountBudget N := by
  apply count_le_closedCountBudget
  intro kind
  count_bound N
  nlinarith


/-- Every actual positive-definite Cholesky count coordinate obeys the closed cubic budget. -/
theorem choleskyResources_count_le (N : ℕ) :
    (choleskyResources (ι := Empty) (fun k => Finsupp.single k 1) (fun _ => 0) () N 0 0).count ≤
      closedCountBudget N := by
  apply count_le_closedCountBudget
  intro kind
  count_bound N
  nlinarith

/-- Every actual guarded PSD Cholesky count coordinate obeys the closed cubic budget. -/
theorem semidefiniteCholeskyResources_count_le (N : ℕ) :
    (semidefiniteCholeskyResources (ι := Empty) (fun k => Finsupp.single k 1)
      (fun _ => 0) () N 0 0).count ≤ closedCountBudget N := by
  apply count_le_closedCountBudget
  intro kind
  count_bound N
  nlinarith

/-- Every actual scalar-pivot LDL count coordinate obeys the closed cubic budget. -/
theorem ldlFactorResources_count_le (N : ℕ) :
    (ldlFactorResources (ι := Empty) (fun k => Finsupp.single k 1) (fun _ => 0) () N 0 0 0).count ≤
      closedCountBudget N := by
  apply count_le_closedCountBudget
  intro kind
  count_bound N
  nlinarith

end NLAlib.Computation
