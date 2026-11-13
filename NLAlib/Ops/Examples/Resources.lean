/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Cert
public import Mathlib.Tactic.Module

/-!
# Format-aware memory and execution configurations

Mixed allocation uses three binary32 vectors and one binary64 vector, with peak payload 20n.
The full certificate includes counts, work, span, scratch bytes and resident bytes. Further
examples reject format reinterpretation through direct calls or aliased frames, distinguish
binary16 from bfloat16, account for query workspace, and compare primitive configurations.

## Main results

* `NLAlib.Ops.Examples.Resources.mixedAlgorithm`: uniform mixed-format allocation certificate.
* `NLAlib.Ops.Examples.Resources.configurations`: identical work with different modeled span
  and workspace, without a scheduler or automatic parallel speedup claim.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Resources

/-- Initialization performs one unit of work per element; other structural steps cost one. -/
def allocationWork : Bookkeeping → List ℕ → ℕ
  | .allocate, d => (d[1]?).getD 0
  | _, _ => 1

/-- A sequential allocation configuration with explicitly permitted fixed-width formats. -/
def memoryResources : ResourceModel Empty Empty where
  formats := [.fp16, .bf16, .fp32, .fp64]
  operation o := nomatch o
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace o := nomatch o
  queryWorkspace q := nomatch q
  operationWork o := nomatch o
  operationSpan o := nomatch o
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork := allocationWork
  coreSpan := allocationWork
  operation_span_le o := nomatch o
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- A shared query reservation is unnecessary for an empty query signature. -/
@[simp] theorem queryReserve_memoryResources (c : Count (Empty ⊕ Bookkeeping) Empty) :
    memoryResources.queryReserve c = 0 :=
  memoryResources.queryReserve_of_zero (fun q => nomatch q) c

/-- No buffers are supplied; the single runtime size is the vector length. -/
def mixedProblem : Problem Unit 1 0 where
  formats := Fin.elim0
  valid _ := True
  Data _ := Unit
  admissible _ _ _ := True
  admitted := ⟨fun _ => 0, trivial⟩
  supply _ _ := ⟨(), Fin.elim0, trivial⟩

/-- There are no opaque operations in the allocation example. -/
def emptyInterp : Interp Empty Empty Unit where
  call o := nomatch o
  test q := nomatch q
  index q := nomatch q

/-- The empty primitive model is jointly realized; storage is handled by syntax alone. -/
def mixedModel : AccessModel Empty Empty mixedProblem where
  word := ()
  operation _ _ o := nomatch o
  query _ _ q := nomatch q
  resources := memoryResources
  realize _ _ _ := ⟨emptyInterp, (fun o => nomatch o), (fun q => nomatch q)⟩

/-- Three binary32 vectors and one binary64 vector are simultaneously live. -/
def mixedProgram : Program Empty Empty 1 0 :=
  ⟨.allocAs .fp32 (.var 0) (.allocAs .fp32 (.var 0)
    (.allocAs .fp32 (.var 0) (.allocAs .fp64 (.var 0) .skip)))⟩

/-- Independent full instruction budget: four bounds, four allocations/releases and one skip. -/
noncomputable def mixedCount (n : ℕ) : Count (Empty ⊕ Bookkeeping) Empty :=
  4 • Count.one (.inr .indexVar) [] +
    3 • Count.one (.inr .allocate) [4, n] + Count.one (.inr .allocate) [8, n] +
    3 • Count.one (.inr .release) [4, n] + Count.one (.inr .release) [8, n] +
    Count.one (.inr .skip) []

/-- Independent work/span and payload byte bounds; no initial buffers are omitted. -/
noncomputable def mixedSpecification : Specification Empty Empty mixedProblem where
  budget d := mixedCount (d 0)
  scratch d := 20 * d 0
  work d := 4 * d 0 + 9
  span d := 4 * d 0 + 9
  memory d := 20 * d 0
  good _ _ _ _ m := m.store = [] ∧ m.pos = 0

/-- The fixed mixed tree satisfies every declared format before runtime values are supplied. -/
theorem wellTyped_mixedProgram :
    mixedProgram.wellTyped memoryResources mixedProblem.formats = true := by decide

/-- The full counted budget is a closed expression, not a budget defined by the program. -/
theorem staticCost_mixedProgram (d : Fin 1 → ℕ) :
    staticCost mixedProgram d = mixedCount (d 0) := by
  classical
  simp [staticCost, mixedProgram, Stmt.instrument, tally, IExp.bookkeeping, stmtCost,
    useCost, IExp.eval, Program.environment, StorageFormat.bytes, StorageFormat.fp32,
    StorageFormat.fp64, mixedCount]
  module

/-- Simultaneous mixed payload is 3*4n+8n, with no opaque primitive workspace. -/
theorem staticPeak_mixedProgram (d : Fin 1 → ℕ) :
    staticPeak memoryResources mixedProgram d = 20 * d 0 := by
  rw [staticPeak_eq, queryReserve_memoryResources, Nat.add_zero]
  simp [mixedProgram, stmtPeak, IExp.eval, Program.environment,
    StorageFormat.bytes, StorageFormat.fp32, StorageFormat.fp64]
  omega

/-- Four vectors require four initialization passes, plus fixed structural work. -/
theorem work_mixedCount (n : ℕ) : memoryResources.work (mixedCount n) = 4 * n + 9 := by
  simp [ResourceModel.work, mixedCount, Count.one, Count.lift, memoryResources, allocationWork]
  omega

/-- Sequential initialization has span equal to work in this configuration. -/
theorem span_mixedCount (n : ℕ) : memoryResources.span (mixedCount n) = 4 * n + 9 :=
  work_mixedCount n

/-- The allocations succeed, clean up their payload buffers and retain the tape position. -/
theorem wp_mixedProgram (I : Interp Empty Empty Unit) (τ : Tape Unit) (d : Fin 1 → ℕ)
    (x : mixedProblem.Input d) :
    Wp .total I τ mixedProgram.body (Program.environment (b := 0) d)
      (fun m => m.store = [] ∧ m.pos = 0) (mixedProblem.initial d x) := by
  simp [Wp, Mode.Holds, mixedProgram, eval, IExp.eval, Env.pushBuf, Program.environment,
    Problem.initial, Store.push, Store.pop]

/-- A complete mixed-memory certificate for every natural vector length. -/
noncomputable def mixedAlgorithm : Algorithm mixedModel mixedSpecification :=
  Algorithm.ofWp mixedProgram wellTyped_mixedProgram
    (fun d _ x I _ τ => (wp_mixedProgram I τ d x).mono fun _ h _ _ => h)
    (fun d _ => le_of_eq (staticCost_mixedProgram d))
    (fun d _ => le_of_eq (staticPeak_mixedProgram d))
    (fun d _ => le_of_eq (work_mixedCount (d 0)))
    (fun d _ => le_of_eq (span_mixedCount (d 0)))
    (fun d _ x => by simp [Problem.initialBytes, mixedSpecification])

/-- A widening operation declares distinct input and output storage representations. -/
def conversionResources : ResourceModel Unit Unit where
  formats := [.fp16, .bf16, .fp32, .fp64]
  operation _ := ⟨[.fp16], [.fp32]⟩
  testInputs _ := [.fp32]
  indexInputs _ := [.fp32]
  workspace _ _ := 0
  queryWorkspace _ _ := 7
  operationWork _ d := (d[0]?).getD 0
  operationSpan _ d := (d[0]?).getD 0
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- Explicit widening uses separate backing buffers of the declared formats. -/
def conversionProgram : Program Unit Unit 1 0 :=
  ⟨.allocAs .fp16 (.var 0) (.allocAs .fp32 (.var 0)
    (.call () [.var 0] [⟨0, .const 0⟩] [⟨1, .const 0⟩]))⟩

example : conversionProgram.wellTyped conversionResources Fin.elim0 = true := by decide

/-- A frame preserves alias identity; it cannot turn one fp16 buffer into an fp32 output. -/
def badAliasProgram : Program Unit Unit 1 0 :=
  ⟨.allocAs .fp16 (.var 0) (.frame [] [⟨0, .const 0⟩, ⟨0, .const 0⟩]
    (.call () [] [⟨0, .const 0⟩] [⟨1, .const 0⟩]))⟩

example : badAliasProgram.wellTyped conversionResources Fin.elim0 = false := by decide

/-- A mismatched format is rejected by execution, even under an interpreter willing to run it. -/
example (I : Interp Unit Unit Unit) (τ : Tape Unit) (d : Fin 1 → ℕ) (m : Mem Unit) :
    exec badAliasProgram I conversionResources Fin.elim0 τ d m = none := by
  have h : badAliasProgram.wellTyped conversionResources Fin.elim0 = false := by decide
  simp [exec, h]

/-- Equal byte widths do not identify different representations. -/
example : StorageFormat.fp16.bytes = StorageFormat.bf16.bytes ∧
    StorageFormat.fp16 ≠ StorageFormat.bf16 := by decide

/-- Query reservation includes declared workspace; no executed query is silently memory-free. -/
example : conversionResources.queryReserve (Count.test () []) = 7 := by
  classical
  simp [ResourceModel.queryReserve, Count.test, conversionResources]

/-- An unused query contributes no workspace reservation. -/
example : conversionResources.queryReserve 0 = 0 := by
  simp [ResourceModel.queryReserve]

/-- Same-width bfloat16 cannot be substituted for a binary16 input. -/
example : (⟨.allocAs .bf16 (.const 1) (.allocAs .fp32 (.const 1)
    (.call () [] [⟨0, .const 0⟩] [⟨1, .const 0⟩]))⟩ : Program Unit Unit 0 0).wellTyped
      conversionResources Fin.elim0 = false := by decide

/-- A forged smaller representation with the same identifier is still an undeclared format. -/
example : (⟨.allocAs ⟨StorageFormat.fp32.name, 0⟩ (.const 10) .skip⟩ :
    Program Empty Empty 0 0).wellTyped memoryResources Fin.elim0 = false := by decide

/-- A query workspace is reused across calls, rather than summed as if all calls overlapped. -/
example : conversionResources.queryReserve (2 • Count.test () []) = 7 := by
  classical
  simp [ResourceModel.queryReserve, Count.test, conversionResources]

/-- A fixed binary64 allocation has capacity three, but occupies 24 modeled payload bytes. -/
def allocation24 : Program Empty Empty 1 0 := ⟨.allocAs .fp64 (.const 3) .skip⟩

/-- This is actual canonical accounting, not just a static upper bound. -/
theorem exec_allocation24 (d : Fin 1 → ℕ) :
    ∃ st, exec allocation24 emptyInterp memoryResources mixedProblem.formats
      (fun _ _ => ()) d ⟨[], 0⟩ = some st ∧
        st.peak = 24 ∧ st.cur = 0 ∧ st.mem = ⟨[], 0⟩ := by
  let c : Count (Empty ⊕ Bookkeeping) Empty :=
    Count.one (.inr .indexConst) [] + Count.one (.inr .allocate) [8, 3] +
      Count.one (.inr .skip) [] + Count.one (.inr .release) [8, 3]
  have ht : allocation24.wellTyped memoryResources mixedProblem.formats = true := by decide
  have hr : evalCounted emptyInterp.instrument (instrumentWorkspace memoryResources.workspace)
      (fun _ _ => ()) allocation24.body.instrument (Program.environment (b := 0) d)
      (St.init ⟨[], 0⟩) = some ⟨⟨[], 0⟩, c, 0, 24⟩ := by
    simp [allocation24, Stmt.instrument, tally, IExp.bookkeeping, IExp.eval,
      IExp.evalList, Operand.evalList, evalCounted, Interp.callS_instrument_inr,
      instrumentWorkspace, memoryResources, St.init, StorageFormat.bytes,
      StorageFormat.fp64, Store.push, Store.pop, c]
  refine ⟨⟨⟨[], 0⟩, c, 0, 24⟩, ?_, rfl, rfl, rfl⟩
  simpa only [St.reserveQueries, queryReserve_memoryResources, Nat.add_zero]
    using exec_of_evalCounted ht rfl hr

/-- A certificate cannot understate that allocation as 23 bytes, regardless of its postcondition. -/
example (S : Specification Empty Empty mixedProblem) (h : S.scratch (fun _ => 0) < 24) :
    ¬ allocation24.Certifies mixedModel S := by
  intro hc
  let x : mixedProblem.Input (fun _ => 0) := ⟨⟨(), Fin.elim0⟩, trivial⟩
  have hi : mixedModel.contracts (fun _ => 0) x emptyInterp :=
    ⟨(fun o => nomatch o), (fun q => nomatch q)⟩
  obtain ⟨st, he, hp, -⟩ := hc (fun _ => 0) trivial x emptyInterp hi (fun _ _ => ())
  obtain ⟨actual, ha, hpeak, -, -⟩ := exec_allocation24 (fun _ => 0)
  change exec allocation24 emptyInterp memoryResources mixedProblem.formats
    (fun _ _ => ()) (fun _ => 0) ⟨[], 0⟩ = some st at he
  rw [ha] at he
  have hs := Option.some.inj he
  rw [← hs, hpeak] at hp
  omega

/-- A test implementation with no word effects; its modeled temporary workspace is still charged. -/
def queryInterp : Interp Unit Unit Unit where
  call _ _ _ _ _ _ := none
  test _ _ _ _ := some false
  index _ _ _ := some 0

/-- Read a declared binary32 buffer through a Boolean query. -/
def queryProgram : Program Unit Unit 0 1 :=
  ⟨.ite () [] [⟨0, .const 0⟩] .skip .skip⟩

/-- Canonical query execution reserves seven bytes even though raw queries do not change Mem. -/
example : ∃ st, exec queryProgram queryInterp conversionResources (fun _ => .fp32)
    (fun _ _ => ()) Fin.elim0 ⟨[[some ()]], 0⟩ = some st ∧ st.peak = 7 := by
  let c : Count (Unit ⊕ Bookkeeping) Unit :=
    Count.one (.inr .indexConst) [] + Count.one (.inr .operand) [] +
      Count.one (.inr .branch) [] + Count.test () [] + Count.one (.inr .skip) []
  have ht : queryProgram.wellTyped conversionResources (fun _ => .fp32) = true := by decide
  have hr : evalCounted queryInterp.instrument (instrumentWorkspace conversionResources.workspace)
      (fun _ _ => ()) queryProgram.body.instrument (Program.environment (b := 1) Fin.elim0)
      (St.init ⟨[[some ()]], 0⟩) = some ⟨⟨[[some ()]], 0⟩, c, 0, 0⟩ := by
    simp [queryProgram, Stmt.instrument, tally, operandBookkeeping, indexBookkeeping,
      IExp.bookkeeping, evalCounted, IExp.evalList, Operand.evalList, Operand.eval,
      IExp.eval, Interp.callS, Mem.Live, Interp.instrument, queryInterp,
      Program.environment, St.init, St.tick, instrumentWorkspace, conversionResources, c]
  have hq : conversionResources.queryReserve c = 7 := by
    classical
    simp [ResourceModel.queryReserve, c, Count.one, Count.test, conversionResources,
      Finsupp.support_add_eq]
  refine ⟨⟨⟨[[some ()]], 0⟩, c, 0, 7⟩, ?_, rfl⟩
  simpa only [St.reserveQueries, hq, Nat.zero_add] using exec_of_evalCounted ht rfl hr

/-- All supplied capacity counts, including uninitialized output slots. -/
def capacityProblem : Problem Unit 0 2 where
  formats i := if i.val = 0 then .fp16 else .fp64
  valid _ := True
  Data _ := Unit
  admissible _ _ bufs := bufs = (fun _ => [none, none, none])
  admitted := ⟨Fin.elim0, trivial⟩
  supply _ _ := ⟨(), (fun _ => [none, none, none]), rfl⟩

example : capacityProblem.initialBytes Fin.elim0
    ⟨⟨(), (fun _ => [none, none, none])⟩, rfl⟩ = 30 := rfl

/-- Primitive-only models illustrate alternative internal parallel configurations. -/
def configuration (span workspace : ℕ) (hspan : span ≤ 100) : ResourceModel Unit Empty where
  formats := []
  operation _ := ⟨[], []⟩
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace _ _ := workspace
  queryWorkspace q := nomatch q
  operationWork _ _ := 100
  operationSpan _ _ := span
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := hspan
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- A fixed primitive invocation: its implementation configuration is supplied by the model. -/
def primitiveProgram : Program Unit Empty 0 0 := ⟨.call () [] [] []⟩

/-- A willing interpreter, sufficient for this operational resource demonstration. -/
def identityInterp : Interp Unit Empty Unit where
  call _ _ _ _ _ m := some m
  test q := nomatch q
  index q := nomatch q

/-- Actual resource execution of a fixed call under one specified configuration. -/
theorem exec_configuration (sp ws : ℕ) (h : sp ≤ 100) :
    exec primitiveProgram identityInterp (configuration sp ws h) Fin.elim0
      (fun _ _ => ()) Fin.elim0 ⟨[], 0⟩ =
      some ⟨⟨[], 0⟩, Count.one (.inl ()) [], 0, ws⟩ := by
  have ht : primitiveProgram.wellTyped (configuration sp ws h) Fin.elim0 = true := by
    simp [primitiveProgram, Program.wellTyped, Stmt.wellTyped, Operand.formatList, configuration]
  have hr : evalCounted identityInterp.instrument
      (instrumentWorkspace (configuration sp ws h).workspace) (fun _ _ => ())
      primitiveProgram.body.instrument (Program.environment (b := 0) Fin.elim0)
      (St.init ⟨[], 0⟩) = some ⟨⟨[], 0⟩, Count.one (.inl ()) [], 0, ws⟩ := by
    simp [primitiveProgram, Stmt.instrument, tally, indexBookkeeping, operandBookkeeping,
      evalCounted, IExp.evalList, Operand.evalList, Interp.callS, Interp.instrument,
      identityInterp, Mem.Live, St.init, instrumentWorkspace, configuration]
  have hq : (configuration sp ws h).queryReserve (Count.one (.inl ()) []) = 0 :=
    ResourceModel.queryReserve_of_zero _ (fun q => nomatch q) _
  simpa only [St.reserveQueries, hq, Nat.add_zero] using exec_of_evalCounted ht rfl hr

/-- Work100 in both models, with different declared internal span/workspace configurations.
There is no work/P scheduling inference or inter-call overlap. -/
theorem configurations :
    ∃ serial parallel,
      exec primitiveProgram identityInterp (configuration 100 0 le_rfl) Fin.elim0
        (fun _ _ => ()) Fin.elim0 ⟨[], 0⟩ = some serial ∧
      exec primitiveProgram identityInterp (configuration 10 64 (by decide)) Fin.elim0
        (fun _ _ => ()) Fin.elim0 ⟨[], 0⟩ = some parallel ∧
      (configuration 100 0 le_rfl).work serial.cost = 100 ∧
      (configuration 10 64 (by decide)).work parallel.cost = 100 ∧
      (configuration 100 0 le_rfl).span serial.cost = 100 ∧
      (configuration 10 64 (by decide)).span parallel.cost = 10 ∧
      serial.peak = 0 ∧ parallel.peak = 64 := by
  let c : Count (Unit ⊕ Bookkeeping) Empty := Count.one (.inl ()) []
  refine ⟨⟨⟨[], 0⟩, c, 0, 0⟩, ⟨⟨[], 0⟩, c, 0, 64⟩,
    exec_configuration 100 0 le_rfl, exec_configuration 10 64 (by decide),
    ?_, ?_, ?_, ?_, rfl, rfl⟩
  all_goals simp [ResourceModel.work, ResourceModel.span, Count.lift, Count.one, c, configuration]

end NLAlib.Ops.Examples.Resources
