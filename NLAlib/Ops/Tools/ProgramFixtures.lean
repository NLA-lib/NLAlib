/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Tools.Run

/-!
# Computable canonical accounting regressions

Kernel-checked computations cover mandatory bookkeeping, all three weight classes, allocation
widths, query workspace, format rejection, and failed raw reports. Unequal weights make omitted
classes visible. The supplied work/span configuration is a mathematical model, not a timing claim.

## Main results

The examples check all count classes, byte-sized allocation, query reservations, format and
arity rejection, and failed raw diagnostics.
-/

@[expose] public section

namespace NLAlib.Ops.Tools.ProgramFixtures

open NLAlib.Ops NLAlib.Ops.Tools

/-- Explicit, unequal weights for original operations, queries and core bookkeeping. -/
def resources : ResourceModel Unit Qry where
  formats := [.cell, .fp64]
  operation _ := ⟨[], [.cell]⟩
  testInputs q := q.elim (fun c => c.lens.map fun _ => .cell) (fun _ => [])
  indexInputs _ := [.cell]
  workspace _ _ := 5
  queryWorkspace _ _ := 7
  operationWork _ _ := 11
  operationSpan _ _ := 3
  queryWork _ _ := 13
  querySpan _ _ := 5
  coreWork _ _ := 2
  coreSpan _ _ := 1
  operation_span_le _ _ := by omega
  query_span_le _ _ := by omega
  core_span_le _ _ := by omega

/-- One operation after a true query, with a mandatory sequence and skip. -/
def queryProgram : Program Unit Qry 0 1 :=
  ⟨.seq (.ite (.inl .isZero) [] [⟨0, .const 0⟩]
    (.call () [] [] [⟨0, .const 0⟩]) .abort) .skip⟩

/-- A three-word, eight-byte-format scratch allocation. -/
def allocation : Program Unit Qry 0 1 := ⟨.allocAs .fp64 (.const 3) .skip⟩

/-- A supplied zero cell for the standard query and constant-operation factories. -/
def memory : Mem ℚ := ⟨[[some 0]], 0⟩

/-- The canonical full log has the original operation, query, and mandatory control counts. -/
example : (execProgramC queryProgram
    (withQueries fun _ : Unit => BlockFn.const (0 : ℚ))
    resources (fun _ => .cell) (fun _ _ => 0) Fin.elim0
    memory).map (fun st => st.log) =
    some [(.inl (.inr .skip), []), (.inl (.inl ()), []),
      (.inl (.inr .operand), []), (.inl (.inr .indexConst), []),
      (.inr (.inl .isZero), []), (.inl (.inr .branch), []),
      (.inl (.inr .operand), []), (.inl (.inr .indexConst), []),
      (.inl (.inr .sequence), [])] := by rfl

/-- Work includes 11 operation units, 13 query units, and 14 bookkeeping units. -/
example : (profileProgram queryProgram
    (withQueries fun _ : Unit => BlockFn.const (0 : ℚ)) resources (fun _ => .cell) (fun _ _ => 0)
    Fin.elim0 memory).work = some 38 := by rfl

/-- Sequential span adds 3 operation, 5 query, and 7 bookkeeping units. -/
example : (profileProgram queryProgram
    (withQueries fun _ : Unit => BlockFn.const (0 : ℚ)) resources (fun _ => .cell) (fun _ _ => 0)
    Fin.elim0 memory).span = some 15 := by rfl

/-- Query reservation is added to primitive scratch, exactly as in canonical exec. -/
example : (execProgramC queryProgram
    (withQueries fun _ : Unit => BlockFn.const (0 : ℚ))
    resources (fun _ => .cell) (fun _ _ => 0) Fin.elim0
    memory).map (fun st => st.peak) = some 12 := by rfl

/-- Allocation keys retain both width and element count, and physical payload charges use width. -/
example : (execProgramC allocation
    (withQueries fun _ : Unit => BlockFn.const (0 : ℚ))
    resources (fun _ => .cell) (fun _ _ => 0) Fin.elim0
    memory).map (fun st => (st.log, st.peak)) =
    some ([ (.inl (.inr .release), [8, 3]), (.inl (.inr .skip), []),
      (.inl (.inr .allocate), [8, 3]), (.inl (.inr .indexConst), []) ], 24) := by rfl

/-- Removing an allowed format rejects the same numeric scratch program. -/
example : execProgramC allocation
    (withQueries fun _ : Unit => BlockFn.const (0 : ℚ)) { resources with formats := [.cell] }
    (fun _ => .cell) (fun _ _ => 0) Fin.elim0 memory = none := by rfl

/-- The initial buffer count is checked before execution. -/
example : execProgramC queryProgram
    (withQueries fun _ : Unit => BlockFn.const (0 : ℚ))
    resources (fun _ => .cell) (fun _ _ => 0) Fin.elim0
    ⟨[], 0⟩ = none := by rfl

/-- Failed raw evaluation cannot report that its static bounds were satisfied. -/
example : (profile
    (withQueries fun _ : Unit => BlockFn.const (0 : ℚ)) (fun _ _ => 0) (fun _ _ => 0)
    .abort ⟨[], []⟩ memory).within =
    false := by rfl

/-- Full-weight interpretation is insensitive to log order, with every class retained. -/
example : logWeight
    (Sum.elim (Sum.elim resources.operationWork resources.coreWork) resources.queryWork)
    [(.inl (.inl ()), []), (.inr (.inl .isZero), []), (.inl (.inr .skip), [])] = 26 := by rfl

end NLAlib.Ops.Tools.ProgramFixtures
