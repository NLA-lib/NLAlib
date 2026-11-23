/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.WorkedInstances.Basic
public import NLAlib.Ops.Examples.Strided
public import NLAlib.Ops.Profiles.Standard

/-!
# Worked instance: scaling a vector with an increment

The routine `NLAlib.Ops.Examples.Strided.scalStrided`, which scales in place the cells of a
vector laid out one every `inc` cells, run on exact integer words: the factor `5` and the
vector $(1, 2, 3)$ in cells `0`, `2` and `4` of a buffer of five. It exercises the address
arithmetic of an operand with an increment: the cells between the entries must be left alone.

The run is evaluated, not derived from the judgment of the routine: the whole final memory is
computed by the evaluator and transferred to the execution rules
(`NLAlib.Ops.Reference.execution_iff_exec`).

Expected, from `scripts/worked_instances.py` (`Strided`): the buffer
`[5, 100, 10, 200, 15]` and `3` multiplications. The total of `59` instructions and the formula
$16 n + 11$ are regression values.

## Main results

* `NLAlib.Ops.Examples.WorkedInstances.Strided.calls`,
  `NLAlib.Ops.Examples.WorkedInstances.Strided.work`,
  `NLAlib.Ops.Examples.WorkedInstances.Strided.peak`: the calls, the instructions and the scratch
  of the tree at every length and increment.
* `NLAlib.Ops.Examples.WorkedInstances.Strided.instance_run`: the run on the instance.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.WorkedInstances.Strided

open NLAlib.Ops.Examples.Strided

/-- Exact integer arithmetic. The square root is the identity: the routine does not use it. -/
def machine : Machine ℤ where
  lit q := q.num
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  div a b := a / b
  neg a := -a
  sqrt a := a

/-- The scalar operations of the integer machine. -/
def interp : Interp ScalarOp Empty ℤ := Interp.ofFns machine.fn

/-- Unit weights and no workspace for the scalar operations. -/
def resources : ResourceModel ScalarOp Empty where
  formats := [.cell]
  operation o := Standard.signature (.scalar o)
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace _ _ := 0
  queryWorkspace q := nomatch q
  operationWork _ _ := 1
  operationSpan _ _ := 1
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- The strided scaling on two buffers: the factor and the vector. -/
def program : Program ScalarOp Empty 2 2 :=
  (scalStrided (Op := ScalarOp) (Tst := Empty)).close 2 2

/-- The factor `5`, and the vector $(1, 2, 3)$ in every second cell of a buffer of five. -/
def initial : Mem ℤ := ⟨[[some 5], [some 1, some 100, some 2, some 200, some 3]], 0⟩

/-- The tree of the strided scaling has no test. -/
theorem program_straight : program.body.Straight :=
  Stmt.straight_of_isStraight rfl

/-- The tree contains one multiplication for each entry and no other operation. -/
theorem calls (d : Fin 2 → ℕ) :
    Count.original (staticCost program d) = d 0 • Count.one ScalarOp.mul [] := by
  rw [staticCost, original_stmtCost_instrument]
  simp [program, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, scalStrided,
    Program.environment, List.ofFn_succ, List.range_succ, stmtCost, useCost, IExp.evalList,
    IExp.eval, Finset.sum_const, Routine.closeDims, Routine.closeOps]
  rfl

/-- Every structural instruction weighs one. -/
theorem coreWork_eq : resources.coreWork = fun _ _ => 1 := rfl

/-- Every scalar operation weighs one. -/
theorem operationWork_eq (o : ScalarOp) (d : List ℕ) : resources.operationWork o d = 1 := rfl

/-- The tree contains exactly $16 n + 11$ instructions, each of weight one, whatever the
increment. -/
theorem work (d : Fin 2 → ℕ) : resources.work (staticCost program d) = 16 * d 0 + 11 := by
  rw [staticCost]
  simp [program, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, scalStrided,
    Program.environment, List.ofFn_succ, List.range_succ, stmtCost, useCost, IExp.evalList,
    IExp.eval, Stmt.instrument, indexBookkeeping, operandBookkeeping, IExp.bookkeeping,
    ResourceModel.work, coreWork_eq, operationWork_eq, Routine.closeDims, Routine.closeOps,
    lift_stmtCost_tally, Finset.sum_const]
  ring

/-- The tree allocates nothing, and its multiplications need no workspace. -/
theorem peak (d : Fin 2 → ℕ) : staticPeak resources program d = 0 := by
  rw [staticPeak, resources.queryReserve_of_zero (fun q => nomatch q), Nat.add_zero]
  simp [program, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, scalStrided,
    Program.environment, List.ofFn_succ, List.range_succ, stmtPeak_tally, Stmt.instrument,
    indexBookkeeping, operandBookkeeping, stmtPeak, instrumentWorkspace, IExp.evalList,
    IExp.eval, resources, Routine.closeDims, Routine.closeOps]

/-- The instance. At length `3` and increment `2`, from the factor `5` and the buffer
`[1, 100, 2, 200, 3]`, the execution rules derive one outcome of the strided scaling: the
buffer holds `[5, 100, 10, 200, 15]`, so cells `1` and `3` are untouched; the run makes `3`
multiplications and no other operation, `59` instructions in all, and uses no scratch. -/
theorem instance_run : ∃ st,
    Reference.Execution program interp resources (fun _ => .cell) (fun _ _ => 0) ![3, 2]
        initial st ∧
      st.mem = ⟨[[some 5], [some 5, some 100, some 10, some 200, some 15]], 0⟩ ∧
      Count.original st.cost = 3 • Count.one ScalarOp.mul [] ∧
      resources.work st.cost = 59 ∧ st.peak = 0 := by
  have h : ∃ st, exec program interp resources (fun _ => .cell) (fun _ _ => 0) ![3, 2]
      initial = some st ∧
      st.mem = ⟨[[some 5], [some 5, some 100, some 10, some 200, some 15]], 0⟩ :=
    ⟨_, rfl, rfl⟩
  obtain ⟨st, he, hm⟩ := h
  obtain ⟨hc, hp⟩ := exec_eq_static_of_straight program_straight he
  refine ⟨st, (Reference.execution_iff_exec _ _ _ _ _ _ _ _).mpr he, hm, ?_, ?_, ?_⟩
  · rw [hc, calls]
    rfl
  · rw [hc, work]
    rfl
  · rw [hp, peak]

end NLAlib.Ops.Examples.WorkedInstances.Strided
