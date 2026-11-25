/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Program-independent cubic instruction budgets

With one precision tag and no oracle or kernel names, the operation kinds form an explicit
23-element set. The closed budget assigns $1024(N+1)^3$ to every coordinate. Its definition
mentions neither a program nor a resource analysis.

## Main definitions

* `NLAlib.Computation.unitOperationKinds`: every operation kind at the sole unit tag.
* `NLAlib.Computation.closedCountBudget`: the independent cubic coordinate allowance.

## Main results

* `NLAlib.Computation.closedCountBudget_apply`: the explicit value at every operation kind.
-/

@[expose] public section

open scoped BigOperators

namespace NLAlib.Computation

/-- The 23 operation kinds possible with one tag and no oracle or kernel names. -/
noncomputable def unitOperationKinds : Finset (OpKind Unit Empty) := by
  classical
  exact {.bin () .add, .bin () .sub, .bin () .mul, .bin () .div,
    .bin () .shl, .bin () .shr, .bin () .band, .bin () .bor, .bin () .bxor,
    .un () .neg, .un () .conj, .un () .re, .un () .sqrt, .un () .bnot,
    .lit (), .cmp (), .copy (), .toNat (), .convert () (), .rom (),
    .draw () .gaussian, .draw () .rademacher, .draw () .uniform}

/-- Every operation kind is explicitly listed; oracle-bearing cases are impossible. -/
theorem mem_unitOperationKinds (o : OpKind Unit Empty) : o ∈ unitOperationKinds := by
  classical
  cases o with
  | bin p b => cases p; cases b <;> simp [unitOperationKinds]
  | un p u => cases p; cases u <;> simp [unitOperationKinds]
  | lit p | cmp p | copy p | toNat p | rom p => cases p; simp [unitOperationKinds]
  | convert p q => cases p; cases q; simp [unitOperationKinds]
  | draw p d => cases p; cases d <;> simp [unitOperationKinds]
  | load p o | matvec p o => exact Empty.elim o
  | kcall p o dims => exact Empty.elim o

/-- Each possible instruction kind is allowed at most 1024 times the cube of N+1.
This is a closed size-only formula, with no program or static-cost reference. -/
noncomputable def closedCountBudget (N : ℕ) : OpCount Unit Empty :=
  ∑ o ∈ unitOperationKinds, Finsupp.single o (1024 * (N + 1) ^ 3)

/-- Every possible instruction-kind coordinate has the explicit cubic allowance. -/
@[simp] theorem closedCountBudget_apply (N : ℕ) (o : OpKind Unit Empty) :
    closedCountBudget N o = 1024 * (N + 1) ^ 3 := by
  classical
  simp [closedCountBudget, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', mem_unitOperationKinds]

end NLAlib.Computation
