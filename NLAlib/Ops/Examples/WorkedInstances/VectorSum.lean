/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.VectorSum
public import NLAlib.Ops.Examples.WorkedInstances.Basic

/-!
# Worked instance: the entrywise sum of two vectors

The certified program `NLAlib.Ops.Examples.VectorSum.vaddProgram`, a loop over the cells of
three blocks, run with exact real arithmetic on $x = (1, 2, 3)$ and $y = (10, 20, 30)$.

Expected, from `scripts/worked_instances.py` (`VectorSum`): the output `[11, 22, 33]` and `3`
additions. The total of `44` instructions and the formula $14 n + 2$ are regression values.

## Main results

* `NLAlib.Ops.Examples.WorkedInstances.VectorSum.calls`,
  `NLAlib.Ops.Examples.WorkedInstances.VectorSum.work`,
  `NLAlib.Ops.Examples.WorkedInstances.VectorSum.peak`: the calls, the instructions and the
  scratch of the tree at every length.
* `NLAlib.Ops.Examples.WorkedInstances.VectorSum.instance_run`: the run on the instance.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.WorkedInstances.VectorSum

open NLAlib.Ops.Examples.VectorSum

/-- The tree of the entrywise sum has no test. -/
theorem program_straight : vaddProgram.body.Straight :=
  Stmt.straight_of_isStraight rfl

/-- The tree contains one addition for each entry and no other operation. -/
theorem calls (d : Fin 1 → ℕ) :
    Count.original (staticCost vaddProgram d) = d 0 • Count.one ScalarOp.add [] := by
  rw [staticCost, original_stmtCost_instrument]
  simp [vaddProgram, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, vadd,
    Program.environment, List.ofFn_succ, List.range_succ, stmtCost, useCost, IExp.evalList,
    IExp.eval, Finset.sum_const]
  rfl

/-- The tree contains exactly $14 n + 2$ instructions, each of weight one. -/
theorem work (M : Machine ℝ) (d : Fin 1 → ℕ) :
    (vaddModel M).resources.work (staticCost vaddProgram d) = 14 * d 0 + 2 := by
  rw [staticCost]
  simp [vaddProgram, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, vadd,
    Program.environment, List.ofFn_succ, List.range_succ, stmtCost, useCost, IExp.evalList,
    IExp.eval, Stmt.instrument, indexBookkeeping, operandBookkeeping, IExp.bookkeeping,
    ResourceModel.work, RoundedScalarBlas.model, Functional.model, Functional.modelWithAdm,
    RoundedScalarBlas.resources, Functional.cellResources, lift_one_stmtCost_tally, lift_one_one]
  ring

/-- The tree allocates nothing, and its additions need no workspace. -/
theorem peak (M : Machine ℝ) (d : Fin 1 → ℕ) :
    staticPeak (vaddModel M).resources vaddProgram d = 0 := by
  rw [staticPeak, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  simp [vaddProgram, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, vadd,
    Program.environment, List.ofFn_succ, List.range_succ, stmtPeak_tally, Stmt.instrument,
    indexBookkeeping, operandBookkeeping, stmtPeak, instrumentWorkspace, IExp.evalList,
    IExp.eval, RoundedScalarBlas.model, Functional.model, Functional.modelWithAdm,
    RoundedScalarBlas.resources, Functional.cellResources]

/-- The length of the instance. -/
abbrev sizes : Fin 1 → ℕ := fun _ => 3

/-- The instance. With exact real arithmetic, from the buffers holding $(1, 2, 3)$,
$(10, 20, 30)$ and three blank cells, the execution rules derive one outcome of the entrywise
sum: the third buffer holds `[11, 22, 33]`, the run makes `3` additions and no other operation,
`44` instructions in all, and uses no scratch. -/
theorem instance_run (I : Interp ScalarOp CmpTst ℝ)
    (hI : (vaddModel exactMachine).contracts sizes
      (vaddDomain.input sizes (![1, 2, 3], ![10, 20, 30]) trivial) I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution vaddProgram I (vaddModel exactMachine).resources
        vaddDomain.formats τ sizes (vaddDomain.memory sizes (![1, 2, 3], ![10, 20, 30])) st ∧
      st.mem.store.readBlock 2 0 3 = some [11, 22, 33] ∧
      Count.original st.cost = 3 • Count.one ScalarOp.add [] ∧
      (vaddModel exactMachine).resources.work st.cost = 44 ∧ st.peak = 0 := by
  obtain ⟨st, hr, -, -, hout⟩ :=
    vadd_checked exactMachine sizes ![1, 2, 3] ![10, 20, 30] I hI τ
  obtain ⟨hc, hp⟩ := hr.eq_static_of_straight program_straight
  refine ⟨st, hr, ?_, ?_, ?_, ?_⟩
  · have h : st.mem.store.readBlock 2 0 3 = some (List.ofFn fun i : Fin 3 =>
        exactMachine.add ((![1, 2, 3] : Fin 3 → ℝ) i) ((![10, 20, 30] : Fin 3 → ℝ) i)) := hout
    rw [h]
    simp [List.ofFn_succ, exactMachine]
    norm_num
  · rw [hc, calls]
  · rw [hc, work]
    rfl
  · rw [hp, peak]

end NLAlib.Ops.Examples.WorkedInstances.VectorSum
