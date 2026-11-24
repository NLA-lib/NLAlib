/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.WorkedInstances.Basic
public import NLAlib.Ops.Examples.Control

/-!
# Worked instance: a loop with early exit, ended by its test and by its cap

The tree `NLAlib.Ops.Examples.countdown` moves a counter from one cell to another, one unit in
each round, for at most five rounds, testing before each round whether the counter is zero. It
is run on natural-number words from the counters `2` (the test ends the loop) and `7` (the cap
ends it). The two runs fix what a loop with early exit is charged, and in particular the
convention at the exit (`docs/design/Ops-ReferenceReview.md`): leaving the loop is charged the
address of the operand of the test once, whether or not a test is made there.

The runs are evaluated: the final memory and the whole count are computed by the evaluator
and transferred to the execution rules (`NLAlib.Ops.Reference.execution_iff_exec`). The count
is stated as the list of instructions in the order of execution.

Expected, from `scripts/worked_instances.py` (`EarlyExit`):

* from `2`: the cells `(0, 2)`, `2` decrements, `2` increments and `3` tests;
* from `7`: the cells `(2, 5)`, `5` decrements, `5` increments and `5` tests.

The operand resolutions (`11` and `26`) follow the convention above: one for each test made,
four in each round, and one more at the cap, where no test is made. They and the totals of
`37` and `81` instructions are regression values.

## Main definitions

* `NLAlib.Ops.Examples.WorkedInstances.EarlyExit.stopTrace`,
  `NLAlib.Ops.Examples.WorkedInstances.EarlyExit.capTrace`: the instructions of the two runs.
* `NLAlib.Ops.Examples.WorkedInstances.EarlyExit.tallies`: decrements, increments, tests,
  operand resolutions and total of a count.

## Main results

* `NLAlib.Ops.Examples.WorkedInstances.EarlyExit.stop_run`,
  `NLAlib.Ops.Examples.WorkedInstances.EarlyExit.cap_run`: the two runs.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.WorkedInstances.EarlyExit

open NLAlib.Ops.Examples

/-- Unit weights and no workspace for the counter operations and queries. -/
def resources : ResourceModel COp CTst where
  formats := [.cell]
  operation _ := ⟨[.cell], [.cell]⟩
  testInputs _ := [.cell]
  indexInputs _ := [.cell]
  workspace _ _ := 0
  queryWorkspace _ _ := 0
  operationWork _ _ := 1
  operationSpan _ _ := 1
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- The countdown loop as a program on one buffer of two cells. -/
def program : Program COp CTst 0 1 := ⟨countdown⟩

/-- The type of counts of the countdown program. -/
abbrev C : Type := Count (COp ⊕ Bookkeeping) CTst

/-- One structural instruction. -/
noncomputable abbrev core (k : Bookkeeping) : C := Count.one (.inr k) []

/-- One test of the loop. -/
noncomputable abbrev test : C := Count.test .nz []

/-- Entering the loop: its fuel is a constant. -/
noncomputable def entry : List C := [core .indexConst, core .loop]

/-- Resolving one operand at a constant offset. -/
noncomputable def address : List C := [core .indexConst, core .operand]

/-- One round, in the order of execution: a true test, the address of its operand, the round,
and the body (a sequence of a decrement and an increment, each with its two operands). -/
noncomputable def round : List C :=
  [test] ++ address ++ [core .round, core .sequence] ++
    address ++ address ++ [Count.one (.inl .dec) []] ++
    address ++ address ++ [Count.one (.inl .inc) []]

/-- Leaving the loop: the address of the operand of the test, once, the exit and the
continuation `skip`. -/
noncomputable def leave : List C := address ++ [core .exit, core .skip]

/-- The instructions when two rounds are followed by a false test. -/
noncomputable def stopTrace : List C := entry ++ round ++ round ++ [test] ++ leave

/-- The instructions when the cap of five rounds is reached: there is no sixth test. -/
noncomputable def capTrace : List C :=
  entry ++ round ++ round ++ round ++ round ++ round ++ leave

/-- The tree allocates nothing and its operations need no workspace. -/
theorem staticPeak_program (d : Fin 0 → ℕ) : staticPeak resources program d = 0 := by
  rw [staticPeak_eq, resources.queryReserve_of_zero (fun _ _ => rfl), Nat.add_zero]
  simp [program, countdown, stmtPeak, resources, IExp.eval, IExp.evalList]

/-- Every successful run of the program uses no scratch. -/
theorem peak_eq_zero {d : Fin 0 → ℕ} {m : Mem ℕ} {st : St (COp ⊕ Bookkeeping) CTst ℕ}
    (h : exec program ctlInterp resources (fun _ => .cell) (fun _ _ => 0) d m = some st) :
    st.peak = 0 :=
  Nat.le_zero.mp ((exec_static h).2.trans_eq (staticPeak_program d))

/-- The evaluator on the counter `2`: the loop stops at a false test. -/
theorem exec_stop : ∃ st,
    exec program ctlInterp resources (fun _ => .cell) (fun _ _ => 0) (fun _ => 0)
      (twoCells 2 0) = some st ∧ st.mem = twoCells 0 2 ∧
      st.cost = stopTrace.foldl (· + ·) 0 ∧ st.peak = 0 := by
  have h : ∃ st, exec program ctlInterp resources (fun _ => .cell) (fun _ _ => 0) (fun _ => 0)
      (twoCells 2 0) = some st ∧ st.mem = twoCells 0 2 ∧
      st.cost = stopTrace.foldl (· + ·) 0 :=
    ⟨_, rfl, rfl, by
      simp only [St.tick, St.init, St.reserveQueries, stopTrace, entry, round, leave,
        address, List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]⟩
  obtain ⟨st, he, hm, hc⟩ := h
  exact ⟨st, he, hm, hc, peak_eq_zero he⟩

/-- The evaluator on the counter `7`: the loop stops at its cap of five rounds. -/
theorem exec_cap : ∃ st,
    exec program ctlInterp resources (fun _ => .cell) (fun _ _ => 0) (fun _ => 0)
      (twoCells 7 0) = some st ∧ st.mem = twoCells 2 5 ∧
      st.cost = capTrace.foldl (· + ·) 0 ∧ st.peak = 0 := by
  have h : ∃ st, exec program ctlInterp resources (fun _ => .cell) (fun _ _ => 0) (fun _ => 0)
      (twoCells 7 0) = some st ∧ st.mem = twoCells 2 5 ∧
      st.cost = capTrace.foldl (· + ·) 0 :=
    ⟨_, rfl, rfl, by
      simp only [St.tick, St.init, St.reserveQueries, capTrace, entry, round, leave,
        address, List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]⟩
  obtain ⟨st, he, hm, hc⟩ := h
  exact ⟨st, he, hm, hc, peak_eq_zero he⟩

/-- Five tallies of a count: the decrements, the increments, the tests, the operand
resolutions and the total number of instructions. -/
noncomputable def tallies : C →+ ℕ × ℕ × ℕ × ℕ × ℕ :=
  (Finsupp.applyAddHom (.inl (.inl .dec), [])).prod <|
    (Finsupp.applyAddHom (.inl (.inl .inc), [])).prod <|
      (Finsupp.applyAddHom (.inr .nz, [])).prod <|
        (Finsupp.applyAddHom (.inl (.inr .operand), [])).prod
          (Count.lift (A := ℕ) fun _ _ => 1)

/-- The tallies of a list of instructions are the sum of the tallies of its instructions. -/
theorem tallies_foldl (l : List C) : tallies (l.foldl (· + ·) 0) = (l.map tallies).sum := by
  rw [← List.sum_eq_foldl, map_list_sum]

/-- Entering the loop: two structural instructions. -/
theorem tallies_entry : (entry.map tallies).sum = (0, 0, 0, 0, 2) := by
  simp [entry, tallies, Count.one, Count.lift_single]

/-- One test. -/
theorem tallies_test : tallies test = (0, 0, 1, 0, 1) := by
  simp [tallies, Count.test, Count.lift_single]

/-- One round: one decrement, one increment, one test, five operand resolutions, fifteen
instructions. -/
theorem tallies_round : (round.map tallies).sum = (1, 1, 1, 5, 15) := by
  simp [round, address, tallies, Count.one, Count.test, Count.lift_single]

/-- Leaving the loop: one operand resolution, four instructions. -/
theorem tallies_leave : (leave.map tallies).sum = (0, 0, 0, 1, 4) := by
  simp [leave, address, tallies, Count.one, Count.lift_single]

/-- The tallies of the run ended by its test. -/
theorem tallies_stopTrace : tallies (stopTrace.foldl (· + ·) 0) = (2, 2, 3, 11, 37) := by
  rw [tallies_foldl]
  simp [stopTrace, tallies_entry, tallies_round, tallies_leave, tallies_test]

/-- The tallies of the run ended by its cap. -/
theorem tallies_capTrace : tallies (capTrace.foldl (· + ·) 0) = (5, 5, 5, 26, 81) := by
  rw [tallies_foldl]
  simp [capTrace, tallies_entry, tallies_round, tallies_leave]

/-- The run ended by its test. From the counter `2`, the execution rules derive one
outcome of the countdown: the cells hold `(0, 2)`; the instructions are those of
`NLAlib.Ops.Examples.WorkedInstances.EarlyExit.stopTrace`, in that order: `2` decrements, `2`
increments, `3` tests, `11` operand resolutions and `37` instructions in all; no scratch is
used. The operand resolutions are one for each of the three tests and four in each round. -/
theorem stop_run : ∃ st,
    Reference.Execution program ctlInterp resources (fun _ => .cell) (fun _ _ => 0)
        (fun _ => 0) (twoCells 2 0) st ∧
      st.mem = twoCells 0 2 ∧ st.cost = stopTrace.foldl (· + ·) 0 ∧
      tallies st.cost = (2, 2, 3, 11, 37) ∧ st.peak = 0 := by
  obtain ⟨st, he, hm, hc, hp⟩ := exec_stop
  exact ⟨st, (Reference.execution_iff_exec _ _ _ _ _ _ _ _).mpr he, hm, hc,
    hc ▸ tallies_stopTrace, hp⟩

/-- The run ended by its cap. From the counter `7`, the execution rules derive one outcome
of the countdown: the cells hold `(2, 5)`; the instructions are those of
`NLAlib.Ops.Examples.WorkedInstances.EarlyExit.capTrace`, in that order: `5` decrements, `5`
increments, `5` tests, `26` operand resolutions and `81` instructions in all; no scratch is
used. Only five tests are made, and the operand of the test is resolved six times: the sixth
is the charge of the exit. -/
theorem cap_run : ∃ st,
    Reference.Execution program ctlInterp resources (fun _ => .cell) (fun _ _ => 0)
        (fun _ => 0) (twoCells 7 0) st ∧
      st.mem = twoCells 2 5 ∧ st.cost = capTrace.foldl (· + ·) 0 ∧
      tallies st.cost = (5, 5, 5, 26, 81) ∧ st.peak = 0 := by
  obtain ⟨st, he, hm, hc, hp⟩ := exec_cap
  exact ⟨st, (Reference.execution_iff_exec _ _ _ _ _ _ _ _).mpr he, hm, hc,
    hc ▸ tallies_capTrace, hp⟩

end NLAlib.Ops.Examples.WorkedInstances.EarlyExit
