/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.StraightCount
public import NLAlib.Ops.Certification

/-!
# Worked instances: shared lemmas

The modules `NLAlib/Ops/Examples/WorkedInstances/` fix, for a few routines of the library, the
exact outcome of one small run under the execution rules (`NLAlib.Ops.Reference.Execution`): the
words written, the number of calls of each operation, the total number of instructions and the
peak scratch. The purpose is to test the definitions of the core (indexing, strides, loop
bounds, charges, scratch) against values obtained outside the library.

**Provenance of the numbers.** `scripts/worked_instances.py` computes, with exact rational
arithmetic and from the textbook formula of each operation, the outputs and the numbers of
arithmetic operations; `scripts/test_worked_instances.py` checks that the literals of that
script occur in these modules. The totals that include structural instructions (index
arithmetic, operand resolution, rounds, frames, allocations) have no source outside the
library: they are regression values, and each module says which they are.

**Method.** A tree with no test makes the same instructions on every run, so its count and
scratch are those of the tree (`NLAlib.Ops.Reference.Execution.eq_static_of_straight`); the
output comes from the certificate of the routine, or from evaluating the run. This module
holds the lemmas about weights that the instances share.

## Main results

* `NLAlib.Ops.Examples.WorkedInstances.lift_one_stmtCost_tally`,
  `NLAlib.Ops.Examples.WorkedInstances.lift_one_one`: the weight of structural instructions and
  of one instruction.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.WorkedInstances

variable {Op Tst : Type}

/-- With every weight one, a list of structural instructions weighs its length. -/
theorem lift_one_stmtCost_tally (ks : List Bookkeeping) (idx : List ℕ) :
    Count.lift (A := ℕ) (fun _ _ => 1)
      (stmtCost (tally (Op := Op) (Tst := Tst) ks) idx) = ks.length := by
  have h := lift_stmtCost_tally (Op := Op) (Tst := Tst) (fun _ _ => 1) (fun _ _ => 1) ks idx
  have e : (Sum.elim (Sum.elim (fun (_ : Op) (_ : List ℕ) => 1) fun (_ : Bookkeeping) _ => 1)
      fun (_ : Tst) (_ : List ℕ) => 1) = fun _ _ => (1 : ℕ) := by
    funext x
    rcases x with (_ | _) | _ <;> rfl
  rwa [e] at h

/-- With every weight one, one instruction weighs one. -/
theorem lift_one_one (k : Op) (d : List ℕ) :
    Count.lift (Tst := Tst) (A := ℕ) (fun _ _ => 1) (Count.one k d) = 1 := by
  simp [Count.one, Count.lift_single]

end NLAlib.Ops.Examples.WorkedInstances
