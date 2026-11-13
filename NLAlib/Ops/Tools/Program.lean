/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Tools.Exec
public import Mathlib.Data.Finsupp.Order

/-!
# Computable canonical program execution

The executable twin below checks formats and initial buffer arity, instruments the fixed tree,
and reserves query workspace exactly as canonical `exec` does. Its full log includes original
operations, queries, and bookkeeping; work and span use all three explicit weight families.
These diagnostics are not a proof of `Runs` or an `Algorithm` certificate. Modeled span adds
across sequential calls and makes no elapsed-time or physical-speedup claim.

## Main results

* `NLAlib.Ops.Tools.map_toSt_execProgramC`: computable and canonical execution agree.
* `NLAlib.Ops.Tools.profileProgram_work` and `NLAlib.Ops.Tools.profileProgram_span`: full weights.
* `NLAlib.Ops.Tools.profileProgram_memory`: the declared problem supplies resident bytes.
-/

@[expose] public section

namespace NLAlib.Ops.Tools

open NLAlib.Ops

variable {Op Tst K : Type}

/-- Sum explicit weights over every log entry, including repeated keys. -/
def logWeight (f : Op ⊕ Tst → List ℕ → ℕ) (l : List (Key Op Tst)) : ℕ :=
  (l.map fun k => f k.1 k.2).sum

/-- Computable weights agree with the core's full count homomorphism. -/
theorem logWeight_eq (f : Op ⊕ Tst → List ℕ → ℕ) (l : List (Key Op Tst)) :
    logWeight f l = Count.lift f (logCount l) := by
  induction l with
  | nil => simp [logWeight]
  | cons k l ih =>
    change f k.1 k.2 + logWeight f l = _
    rw [logCount_cons, map_add, Count.lift_single, one_smul, ih]
    exact add_comm _ _

/-- The maximum declared workspace of all executed queries. -/
def logQueryReserve (R : ResourceModel Op Tst)
    (l : List (Key (Op ⊕ Bookkeeping) Tst)) : ℕ :=
  (l.map fun k => k.1.elim (fun _ => 0) (fun q => R.queryWorkspace q k.2)).foldr max 0

/-- The log reservation agrees with the canonical support-based query reservation. -/
theorem logQueryReserve_eq (R : ResourceModel Op Tst)
    (l : List (Key (Op ⊕ Bookkeeping) Tst)) :
    logQueryReserve R l = R.queryReserve (logCount l) := by
  classical
  induction l with
  | nil => simp [logQueryReserve, ResourceModel.queryReserve]
  | cons k l ih =>
    change max _ (logQueryReserve R l) = _
    rw [ih]
    simp [logCount_cons, ResourceModel.queryReserve,
      Finsupp.support_add_eq_union]

/-- Reserve shared query scratch without changing the full log. -/
def CSt.reserveQueries (st : CSt (Op ⊕ Bookkeeping) Tst K) (R : ResourceModel Op Tst) :
    CSt (Op ⊕ Bookkeeping) Tst K :=
  { st with peak := st.peak + logQueryReserve R st.log }

/-- Computable and canonical query reservations give the same state. -/
theorem CSt.toSt_reserveQueries (st : CSt (Op ⊕ Bookkeeping) Tst K)
    (R : ResourceModel Op Tst) :
    (st.reserveQueries R).toSt = st.toSt.reserveQueries R := by
  simp [CSt.reserveQueries, CSt.toSt, St.reserveQueries, logQueryReserve_eq]

/-- Canonical execution, computably: mandatory format checks and full instrumentation. -/
def execProgramC {r b : ℕ} (p : Program Op Tst r b) (I : Interp Op Tst K)
    (R : ResourceModel Op Tst) (formats : Fin b → StorageFormat) (τ : Tape K)
    (d : Fin r → ℕ) (m : Mem K) : Option (CSt (Op ⊕ Bookkeeping) Tst K) :=
  if p.wellTyped R formats = true ∧ m.store.length = b then
    (execC I.instrument (instrumentWorkspace R.workspace) τ p.body.instrument
      (Program.environment (b := b) d) (CSt.init m)).map (fun st => st.reserveQueries R)
  else none

/-- The computable wrapper is the canonical counted execution, without count projection. -/
theorem map_toSt_execProgramC {r b : ℕ} (p : Program Op Tst r b) (I : Interp Op Tst K)
    (R : ResourceModel Op Tst) (formats : Fin b → StorageFormat) (τ : Tape K)
    (d : Fin r → ℕ) (m : Mem K) :
    (execProgramC p I R formats τ d m).map CSt.toSt = exec p I R formats τ d m := by
  simp only [execProgramC, exec]
  split_ifs
  · rw [Option.map_map, ← map_toSt_execC_init, Option.map_map]
    congr 1
    funext st
    exact st.toSt_reserveQueries R
  · rfl

/-- A canonical diagnostic result with full counts and explicitly weighted resources. -/
structure ProgramReport (Op Tst K : Type) where
  /-- Full canonical outcome; `none` includes format rejection or runtime failure. -/
  result : Option (CSt (Op ⊕ Bookkeeping) Tst K)
  /-- Total modeled work of all executed instructions. -/
  work : Option ℕ
  /-- Sum of primitive spans over sequential execution, including queries and bookkeeping. -/
  span : Option ℕ
  /-- Initially resident payload bytes plus canonical scratch bytes. -/
  memory : Option ℕ

/-- Execute and report canonical resources. No original-operation-only projection is used. -/
def profileProgram {r b : ℕ} (p : Program Op Tst r b) (I : Interp Op Tst K)
    (R : ResourceModel Op Tst) (formats : Fin b → StorageFormat) (τ : Tape K)
    (d : Fin r → ℕ) (m : Mem K) : ProgramReport Op Tst K :=
  let result := execProgramC p I R formats τ d m
  let initialBytes := (List.ofFn fun i : Fin b =>
    (formats i).bytes * (m.store[i.val]?.getD []).length).sum
  { result
    work := result.map fun st => logWeight
      (Sum.elim (Sum.elim R.operationWork R.coreWork) R.queryWork) st.log
    span := result.map fun st => logWeight
      (Sum.elim (Sum.elim R.operationSpan R.coreSpan) R.querySpan) st.log
    memory := result.map fun st => initialBytes + st.peak }

/-- Reported work is the canonical full-count work. -/
theorem profileProgram_work {r b : ℕ} (p : Program Op Tst r b) (I : Interp Op Tst K)
    (R : ResourceModel Op Tst) (formats : Fin b → StorageFormat) (τ : Tape K)
    (d : Fin r → ℕ) (m : Mem K) :
    (profileProgram p I R formats τ d m).work =
      (exec p I R formats τ d m).map (fun st => R.work st.cost) := by
  rw [← map_toSt_execProgramC]
  simp [profileProgram, Option.map_map, Function.comp_def, CSt.toSt,
    ResourceModel.work, logWeight_eq]

/-- Reported span is the canonical full-count modeled span. -/
theorem profileProgram_span {r b : ℕ} (p : Program Op Tst r b) (I : Interp Op Tst K)
    (R : ResourceModel Op Tst) (formats : Fin b → StorageFormat) (τ : Tape K)
    (d : Fin r → ℕ) (m : Mem K) :
    (profileProgram p I R formats τ d m).span =
      (exec p I R formats τ d m).map (fun st => R.span st.cost) := by
  rw [← map_toSt_execProgramC]
  simp [profileProgram, Option.map_map, Function.comp_def, CSt.toSt,
    ResourceModel.span, logWeight_eq]

/-- Resident payload bytes use exactly the declared problem's initially supplied buffers. -/
theorem profileProgram_memory {r b : ℕ} {P : Problem K r b} (p : Program Op Tst r b)
    (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (d : Fin r → ℕ) (x : P.Input d) :
    (profileProgram p I R P.formats τ d (P.initial d x)).memory =
      (exec p I R P.formats τ d (P.initial d x)).map
        (fun st => P.initialBytes d x + st.peak) := by
  rw [← map_toSt_execProgramC]
  simp [profileProgram, Option.map_map, Function.comp_def, CSt.toSt,
    Problem.initialBytes, Problem.initial]

end NLAlib.Ops.Tools
