/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Compare

/-!
# Closed models generated from local primitive functions

An exhaustive assignment of block functions generates every operation contract and a
jointly realizing interpretation. Comparisons read only their declared scalar operands.
The model contains no whole-program predicate. Primitive functions and their resource
weights remain explicit specification choices; this constructor proves their consistency.

## Main results

* `NLAlib.Ops.Functional.interp` interprets the declared local block functions.
* `NLAlib.Ops.Functional.model` supplies a jointly realized closed operation model.
* `NLAlib.Ops.Functional.isFn` recovers any declared functional primitive contract.
* `NLAlib.Ops.Functional.isCmp` recovers the exact operand comparison contracts.
-/

@[expose] public section

namespace NLAlib.Ops.Functional

variable {K Op : Type}

/-- Every Boolean comparison reads exactly its scalar input blocks. This model permits
no index query; dimension-literal operations remain ordinary declared primitives. -/
noncomputable def query (dec : K → ℝ) (c : CmpTst) : QueryContract K where
  test _ a m result := ∀ xs, m.readBlocks a c.lens = some xs → result = some (c.fn dec xs)
  index _ _ result := result = none

/-- The operation meanings are local functions of declared input blocks and sample windows.
Comparisons read their declared operands, and index queries are unavailable. -/
noncomputable def interp (dec : K → ℝ) (functions : Op → BlockFn K) :
    Interp Op CmpTst K where
  call := (Interp.ofFns (Tst := CmpTst) functions).call
  test c _ a m := (m.readBlocks a c.lens).map (c.fn dec)
  index _ _ _ := none

/-- The local operation and comparison contracts hold jointly for the generated interpreter. -/
theorem interp_contracts (dec : K → ℝ) (functions : Op → BlockFn K) :
    (∀ o, (interp dec functions).IsFn .total o (functions o) AnyOperands) ∧
      IsCmp dec (interp dec functions) := by
  refine ⟨?_, ?_⟩
  · intro o
    exact Interp.ofFns_isFn (Tst := CmpTst) functions .total o AnyOperands
  · intro c d a m xs h
    change (m.readBlocks a c.lens).map (c.fn dec) = _
    rw [h]
    rfl

/-- A sequential scalar-cell resource configuration with explicit primitive work and
workspace. Comparisons read their declared scalar operands; query and structural costs
are one unit. Work and span coincide for this sequential configuration. -/
def cellResources (signature : Op → OperandSignature)
    (work workspace : Op → List ℕ → ℕ) : ResourceModel Op CmpTst where
  formats := [.cell]
  operation := signature
  testInputs c := c.lens.map (fun _ => .cell)
  indexInputs _ := []
  workspace := workspace
  queryWorkspace _ _ := 0
  operationWork := work
  operationSpan := work
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- Generate the entire closed contract set from an exhaustive local-function assignment.
The assignment may describe a declared oracle at the supplied semantic input. Stored-data
models instead supply primitives that actually read their explicit data operands. All
contracts use the same declared functions and have one joint realization at every input. -/
noncomputable def modelWithAdm [Inhabited K] {r b : ℕ} (P : Problem K r b)
    (dec : K → ℝ) (functions : (d : Fin r → ℕ) → P.Input d → Op → BlockFn K)
    (admissible : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop)
    (resources : ResourceModel Op CmpTst) : AccessModel Op CmpTst P where
  word := default
  operation d x o := ((functions d x) o).rel.spec (admissible o)
  query _ _ := query dec
  resources := resources
  realize d _ x := by
    refine ⟨interp dec (functions d x), ?_, ?_⟩
    · intro o
      exact Interp.ofFns_isFn (Tst := CmpTst) (functions d x) .total o (admissible o)
    · intro c
      exact ⟨(interp_contracts dec (functions d x)).2 c, fun _ _ => rfl⟩

/-- The unrestricted-operand specialization of the generated functional model. A profile
that requires spatial separation instead declares that admission in `modelWithAdm`. -/
noncomputable def model [Inhabited K] {r b : ℕ} (P : Problem K r b)
    (dec : K → ℝ) (functions : (d : Fin r → ℕ) → P.Input d → Op → BlockFn K)
    (resources : ResourceModel Op CmpTst) : AccessModel Op CmpTst P :=
  modelWithAdm P dec functions (fun _ => AnyOperands) resources

/-- Recover an exact primitive contract with its declared operand admission. -/
theorem isFnWithAdm [Inhabited K] {r b : ℕ} {P : Problem K r b} {dec : K → ℝ}
    {functions : (d : Fin r → ℕ) → P.Input d → Op → BlockFn K}
    {admissible : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {resources : ResourceModel Op CmpTst} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Op CmpTst K}
    (h : (modelWithAdm P dec functions admissible resources).contracts d x I) (o : Op) :
    I.IsFn .total o (functions d x o) (admissible o) := h.1 o

/-- Operand admission leaves the exact local comparison contracts unchanged. -/
theorem isCmpWithAdm [Inhabited K] {r b : ℕ} {P : Problem K r b} {dec : K → ℝ}
    {functions : (d : Fin r → ℕ) → P.Input d → Op → BlockFn K}
    {admissible : Op → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {resources : ResourceModel Op CmpTst} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Op CmpTst K}
    (h : (modelWithAdm P dec functions admissible resources).contracts d x I) :
    IsCmp dec I := fun c => (h.2 c).1

/-- A model interpreter meets each generated primitive's exact local functional contract. -/
theorem isFn [Inhabited K] {r b : ℕ} {P : Problem K r b} {dec : K → ℝ}
    {functions : (d : Fin r → ℕ) → P.Input d → Op → BlockFn K}
    {resources : ResourceModel Op CmpTst} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Op CmpTst K} (h : (model P dec functions resources).contracts d x I) (o : Op) :
    I.IsFn .total o (functions d x o) AnyOperands := h.1 o

/-- The generated comparison contracts compare exactly the declared decoded operands. -/
theorem isCmp [Inhabited K] {r b : ℕ} {P : Problem K r b} {dec : K → ℝ}
    {functions : (d : Fin r → ℕ) → P.Input d → Op → BlockFn K}
    {resources : ResourceModel Op CmpTst} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Op CmpTst K} (h : (model P dec functions resources).contracts d x I) :
    IsCmp dec I := fun c => (h.2 c).1

end NLAlib.Ops.Functional
