/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Reference.Equivalence

/-!
# Boundary examples for declarative execution

A zero-fuel loop must not query its interpreter or run its aborting body. Increasing its
fuel to one makes it fail because the query fails. Both conclusions are derived from the
reference rules; the general equivalence theorem transfers them to canonical execution.

The payload example nests allocations of unequal word widths, reserves primitive workspace,
then queries after releasing the inner buffer. Its expected count, work, span and scratch
are written explicitly, including the conservative query reservation and initial payload.

## Main results

* `NLAlib.Ops.Reference.Examples.zero_fuel_executes`: zero fuel succeeds with four charges.
* `NLAlib.Ops.Reference.Examples.one_fuel_fails`: a required failing query prevents success.
* `NLAlib.Ops.Reference.Examples.Payload.resource_readback`: explicit resource accounting.
-/

@[expose] public section

namespace NLAlib.Ops.Reference.Examples

/-- No primitive operations, and every query fails. -/
def refusing : Interp Empty Unit Bool where
  call o := nomatch o
  test _ _ _ _ := none
  index _ _ _ := none

/-- Unit structural/query work, no primitive operations or workspace. -/
def resources : ResourceModel Empty Unit where
  formats := [.cell]
  operation o := nomatch o
  testInputs _ := []
  indexInputs _ := []
  workspace o := nomatch o
  queryWorkspace _ _ := 0
  operationWork o := nomatch o
  operationSpan o := nomatch o
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le o := nomatch o
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- An early-exit loop with an aborting body and a skipped continuation. -/
def loopProgram (fuel : ℕ) : Program Empty Unit 0 0 :=
  ⟨.whileFuel (.const fuel) () [] [] .abort .skip⟩

/-- Fuel evaluation, loop entry, final exit and the skipped continuation; no query or body. -/
noncomputable def zeroOutcome : State Empty Unit Bool :=
  { mem := ⟨[], 0⟩,
    cost := core .indexConst + core .loop + core .exit + core .skip,
    cur := 0, peak := 0 }

/-- The reference rules derive the empty-fuel outcome, despite the interpreter and body failing. -/
theorem zero_fuel_execution : Execution (loopProgram 0) refusing resources
    (fun _ => .cell) (fun _ _ => false) (fun _ => 0) ⟨[], 0⟩ zeroOutcome := by
  refine ⟨rfl, rfl, zeroOutcome, ?_, ?_⟩
  · have h := Derives.whileFuel (I := refusing) (R := resources) (τ := fun _ _ => false)
      (ρ := Program.environment (b := 0) (fun _ : Fin 0 => 0))
      (a := St.init ⟨[], 0⟩) (fuel := .const 0) (q := ()) (ds := []) (ins := [])
      (body := .abort) (next := .skip) rfl
      (While.cap () [] [] .abort _ 0 _)
      (Derives.skip _ _)
    simpa only [loopProgram, zeroOutcome, charge, index, dimensions, operands,
      List.map_nil, List.sum_nil, zero_add, add_zero, St.init, add_assoc] using h
  · rw [resources.queryReserve_of_zero (fun _ _ => rfl), Nat.add_zero]

/-- Zero fuel canonically succeeds with precisely the reference outcome. -/
theorem zero_fuel_executes : exec (loopProgram 0) refusing resources (fun _ => .cell)
    (fun _ _ => false) (fun _ => 0) ⟨[], 0⟩ = some zeroOutcome :=
  (execution_iff_exec refusing resources (fun _ _ => false) (loopProgram 0)
    (fun _ => .cell) (fun _ => 0) ⟨[], 0⟩ zeroOutcome).mp zero_fuel_execution

/-- The reference rules cannot derive a loop that must perform a failing query. -/
theorem not_one_fuel_execution : ¬ ∃ out, Execution (loopProgram 1) refusing resources
    (fun _ => .cell) (fun _ _ => false) (fun _ => 0) ⟨[], 0⟩ out := by
  rintro ⟨out, _, _, raw, h, _⟩
  change Derives refusing resources _ (.whileFuel (.const 1) () [] [] .abort .skip) _ _ raw at h
  cases h with
  | whileFuel hn hw hk =>
    have he := Option.some.inj hn
    subst he
    cases hw with
    | stop hd hx hq => cases hq
    | step hd hx hq hb ht => cases hq

/-- One fuel unit canonically fails, rather than acquiring a vacuous success guarantee. -/
theorem one_fuel_fails : exec (loopProgram 1) refusing resources (fun _ => .cell)
    (fun _ _ => false) (fun _ => 0) ⟨[], 0⟩ = none :=
  (exec_eq_none_iff refusing resources (fun _ _ => false) (loopProgram 1)
    (fun _ => .cell) (fun _ => 0) ⟨[], 0⟩).mpr not_one_fuel_execution

namespace Payload

/-- A primitive preserves memory, the Boolean query is false, and index queries return zero. -/
def identity : Interp Unit Unit Bool where
  call _ _ _ _ _ m := some m
  test _ _ _ _ := some false
  index _ _ _ := some 0

/-- Distinct declared weights and workspace: primitive work/span 11/3, query 2/1,
structural instructions 1/1; primitive workspace 7 and query reservation 5 modeled bytes. -/
def resources : ResourceModel Unit Unit where
  formats := [.fp16, .fp32, .fp64]
  operation _ := ⟨[], []⟩
  testInputs _ := []
  indexInputs _ := []
  workspace _ _ := 7
  queryWorkspace _ _ := 5
  operationWork _ _ := 11
  operationSpan _ _ := 3
  queryWork _ _ := 2
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := by omega
  query_span_le _ _ := by omega
  core_span_le _ _ := le_rfl

/-- Two supplied words in a four-byte format account for eight initial modeled bytes. -/
def initial : Mem Bool := ⟨[[some true, some false]], 0⟩

/-- Allocate 6 outer bytes and 16 inner bytes, call the primitive, release the inner buffer,
then execute the false query and its skipped branch before releasing the outer buffer. -/
def program : Program Unit Unit 0 1 :=
  ⟨.allocAs .fp16 (.const 3)
    (.seq (.allocAs .fp64 (.const 2) (.call () [] [] [])) (.ite () [] [] .abort .skip))⟩

/-- The expected chronological count: two length evaluations, two allocations, two releases,
sequence entry, one primitive, one branch, one query and the skipped branch. -/
noncomputable def count : Count (Unit ⊕ Bookkeeping) Unit :=
  core .indexConst + core .allocate [2, 3] + core .sequence +
    core .indexConst + core .allocate [8, 2] + Count.one (.inl ()) [] +
    core .release [8, 2] + core .branch + Count.test () [] + core .skip + core .release [2, 3]

/-- At the primitive, the live buffers use 22 bytes and its workspace uses 7. -/
noncomputable def rawOutcome : State Unit Unit Bool :=
  ⟨initial, count, 0, 29⟩

/-- Canonical scratch adds the five-byte query reservation to the allocation/primitive peak. -/
noncomputable def outcome : State Unit Unit Bool :=
  ⟨initial, count, 0, 34⟩

/-- The source inference rules derive the explicit allocation/primitive peak and count. -/
theorem derives_program : Derives identity resources (fun _ _ => false) program.body
    (Program.environment (b := 1) (fun _ : Fin 0 => 0)) (St.init initial) rawOutcome := by
  let ρ := Program.environment (b := 1) (fun _ : Fin 0 => 0)
  let a₀ : State Unit Unit Bool := St.init initial
  let a₁ := allocated .fp16 3 (charge (index (.const 3)) a₀)
  let a₂ := charge (core .sequence) a₁
  let a₃ := allocated .fp64 2 (charge (index (.const 2)) a₂)
  let a₄ := called resources () [] a₃.mem a₃
  let a₅ := released .fp64 2 a₂.cur a₄
  let a₆ := charge (core .branch + Count.test () []) a₅
  let a₇ := charge (core .skip) a₆
  have hcall : Derives identity resources (fun _ _ => false) (.call () [] [] [])
      ((ρ.pushBuf a₀.mem.store.length).pushBuf a₂.mem.store.length) a₃ a₄ := by
    have h := Derives.call (I := identity) (R := resources) (τ := fun _ _ => false)
      (ρ := (ρ.pushBuf a₀.mem.store.length).pushBuf a₂.mem.store.length)
      (a := a₃) (o := ()) (ds := []) (ins := []) (outs := [])
      rfl rfl rfl (by simp [Mem.Live]) rfl rfl
    simpa [dimensions, operands, charge, a₄] using h
  have hinner : Derives identity resources (fun _ _ => false)
      (.allocAs .fp64 (.const 2) (.call () [] [] [])) (ρ.pushBuf a₀.mem.store.length)
      a₂ a₅ := .allocAs rfl hcall
  have hquery : Derives identity resources (fun _ _ => false)
      (.ite () [] [] .abort .skip) (ρ.pushBuf a₀.mem.store.length) a₅ a₇ := by
    have h := Derives.ite (I := identity) (R := resources) (τ := fun _ _ => false)
      (ρ := ρ.pushBuf a₀.mem.store.length)
      (a := a₅) (q := ()) (ds := []) (ins := []) (s := .abort) (t := .skip)
      (v := false) rfl rfl rfl (Derives.skip _ _)
    simpa [dimensions, operands, a₆, a₇] using h
  have h := Derives.allocAs (I := identity) (R := resources) (τ := fun _ _ => false)
    (ρ := ρ) (a := a₀) (fmt := .fp16) (len := .const 3) rfl (.seq hinner hquery)
  simpa [program, rawOutcome, count, ρ, a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇,
    allocated, released, called, charge, index, resources, initial, St.init,
    StorageFormat.fp16, StorageFormat.fp64, StorageFormat.bytes, Store.push, Store.pop,
    add_assoc] using h

/-- Exactly one executed query contributes five bytes to the final reservation. -/
theorem query_reserve : resources.queryReserve count = 5 := by
  classical
  simp [ResourceModel.queryReserve, count, core, Count.one, Count.test,
    Finsupp.support_add_eq_union, resources]

/-- Two distinct executed query keys reserve their maximum workspace, not their sum. -/
theorem query_reserve_two_keys :
    resources.queryReserve (Count.test () [] + Count.test () [1]) = 5 := by
  classical
  simp [ResourceModel.queryReserve, Count.test, Finsupp.support_add_eq_union, resources]

/-- Source execution with format validation and the final conservative query reservation. -/
theorem execution_program : Execution program identity resources (fun _ => .fp32)
    (fun _ _ => false) (fun _ => 0) initial outcome := by
  refine ⟨rfl, rfl, rawOutcome, derives_program, ?_⟩
  rw [show rawOutcome.cost = count from rfl, query_reserve]
  rfl

/-- The entire canonical outcome is the explicitly stated source outcome. -/
theorem executes_program : exec program identity resources (fun _ => .fp32)
    (fun _ _ => false) (fun _ => 0) initial = some outcome :=
  (execution_iff_exec identity resources (fun _ _ => false) program
    (fun _ => .fp32) (fun _ => 0) initial outcome).mp execution_program

/-- The expected count has eleven instructions: nine structural, one primitive and one query. -/
theorem size_count : Count.lift (A := ℕ) (fun _ _ => 1) count = 11 := by
  simp [count, core, Count.one, Count.test, Count.lift]

/-- Nine structural charges, one work-11 primitive and one work-2 query total 22 work units. -/
theorem work_count : resources.work count = 22 := by
  simp [ResourceModel.work, count, core, Count.one, Count.test, Count.lift, resources]

/-- The sequential modeled span is 9 + 3 + 1 = 13 in the same units as work. -/
theorem span_count : resources.span count = 13 := by
  simp [ResourceModel.span, count, core, Count.one, Count.test, Count.lift, resources]

/-- The same execution restores memory and all allocations, has 34 bytes of reserved scratch,
42 bytes including the supplied payload, and the independently stated work/span 22/13. -/
theorem resource_readback : ∃ st,
    exec program identity resources (fun _ => .fp32) (fun _ _ => false) (fun _ => 0)
      initial = some st ∧ st.mem = initial ∧ st.cur = 0 ∧ st.peak = 34 ∧
      StorageFormat.fp32.bytes * (initial.store.len 0) + st.peak = 42 ∧
      Count.lift (A := ℕ) (fun _ _ => 1) st.cost = 11 ∧
      resources.work st.cost = 22 ∧ resources.span st.cost = 13 := by
  exact ⟨outcome, executes_program, rfl, rfl, rfl, rfl, size_count, work_count, span_count⟩

end Payload

end NLAlib.Ops.Reference.Examples
