/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.BufferProblem
public import NLAlib.Krylov.CG.HSPCG.Spec
public import NLAlib.Ops.ContextProblem
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Catalog.StoredOperator
public import Mathlib.Data.Fin.VecNotation

/-!
# Raw system and preconditioner matrices for PCG

Two explicitly supplied dense matrix buffers precede the raw right-hand side and four
uninitialized state capacities. Positive definiteness and the fixed-horizon grade condition
refer to these actual raw words. A joint mathematical input witness proves nonemptiness;
it supplies no execution, preprocessing or desired output.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Stored.problem`: the seven-buffer raw problem.
* `NLAlib.Krylov.CG.HSPCG.Stored.initialBytes_problem`: complete supplied payload.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Stored

open Ops
open scoped Matrix

/-- Each state vector has supplied length n; slot zero is replaced by initialized RHS words. -/
def outputs (d : Fin 2 → ℕ) : Fin 5 → ℕ := ![0, d 0, d 0, d 0, d 0]

/-- The mathematical PCG assumptions are checked on the decoded supplied matrix/RHS data. -/
def accepts (d : Fin 2 → ℕ) (systemRaw preconditionerRaw rhs : List ℝ) : Prop :=
  let A := StoredOperator.denseMatrix (d 0) (d 0) systemRaw
  let B := StoredOperator.denseMatrix (d 0) (d 0) preconditionerRaw
  A.PosDef ∧ B.PosDef ∧ d 1 ≤ krylovGrade (B * A) (B *ᵥ decv id (d 0) rhs)

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ rawA rawP rhs : List ℝ,
    rawA.length = d 0 * d 0 ∧ rawP.length = d 0 * d 0 ∧ rhs.length = d 0 ∧
      accepts d rawA rawP rhs)

include supply in
/-- A joint raw mathematical witness gives a valid original RHS input and both context blocks. -/
theorem context_supply (d : Fin 2 → ℕ) (hd : domain d) :
    ∃ context : Fin 2 → List ℝ, ∃ x : (CG.RawProblem.problem outputs domain admitted).Input d,
      (∀ i, (context i).length = d 0 * d 0) ∧ accepts d (context 0) (context 1) x.val.1 := by
  obtain ⟨rawA, rawP, rhs, ha, hp, hrhs, h⟩ := supply d hd
  refine ⟨![rawA, rawP], ⟨⟨rhs, fun i => if i = 0 then rhs.map some
    else List.replicate (outputs d i) none⟩, rfl, hrhs⟩, ?_, h⟩
  intro i
  fin_cases i
  · exact ha
  · exact hp

/-- Raw system/preconditioner prefixes and the original uninitialized state capacities. -/
def problem : Problem ℝ 2 7 :=
  (CG.RawProblem.problem outputs domain admitted).withContext 2 (fun d _ => d 0 * d 0)
    (fun d c rhs => accepts d (c 0) (c 1) rhs) (context_supply domain admitted supply)

variable {domain admitted supply}

/-- The system matrix is decoded from the first actual raw context block. -/
def matrix {d : Fin 2 → ℕ} (x : (problem domain admitted supply).Input d) :=
  StoredOperator.denseMatrix (d 0) (d 0) (x.val.1.1 0)

/-- The inverse-preconditioner matrix is decoded from the second actual raw block. -/
def preconditioner {d : Fin 2 → ℕ} (x : (problem domain admitted supply).Input d) :=
  StoredOperator.denseMatrix (d 0) (d 0) (x.val.1.1 1)

/-- Raw system matrix words are readable at buffer zero. -/
theorem initial_matrix (d : Fin 2 → ℕ) (x : (problem domain admitted supply).Input d) :
    ((problem domain admitted supply).initial d x).store.readBlock 0 0 (d 0 * d 0) =
      some (x.val.1.1 0) :=
  Problem.withContext.initial_readBlock_context d x 0

/-- Raw inverse-preconditioner words are readable at buffer one. -/
theorem initial_preconditioner (d : Fin 2 → ℕ)
    (x : (problem domain admitted supply).Input d) :
    ((problem domain admitted supply).initial d x).store.readBlock 1 0 (d 0 * d 0) =
      some (x.val.1.1 1) :=
  Problem.withContext.initial_readBlock_context d x 1

/-- The original raw RHS is readable at shifted buffer two without conversion. -/
theorem initial_rhs (d : Fin 2 → ℕ) (x : (problem domain admitted supply).Input d) :
    ((problem domain admitted supply).initial d x).store.readBlock 2 0 (d 0) =
      some x.val.1.2 := by
  have hlen := CG.RawProblem.length_input d (Problem.withContext.originalInput x)
  have hr := Problem.withContext.initial_readBlock_original d x (0 : Fin 5)
    (show (Problem.withContext.originalInput x).val.2 0 = x.val.1.2.map some by
      rw [CG.RawProblem.input_buffers]; simp [Problem.withContext.originalInput])
  change x.val.1.2.length = d 0 at hlen
  change ((problem domain admitted supply).initial d x).store.readBlock
    2 0 x.val.1.2.length = some x.val.1.2 at hr
  rw [hlen] at hr
  exact hr

/-- Every shifted RHS/state buffer retains its declared initial capacity. -/
theorem initial_len (d : Fin 2 → ℕ) (x : (problem domain admitted supply).Input d)
    (i : Fin 5) :
    ((problem domain admitted supply).initial d x).store.len (2 + i.val) =
      if i = 0 then d 0 else outputs d i :=
  (Problem.withContext.initial_len_original d x i).trans
    (CG.RawProblem.initial_len d (Problem.withContext.originalInput x) i)

/-- Positive definiteness and the grade condition come from actual input admissibility. -/
theorem accepts_input {d : Fin 2 → ℕ} (x : (problem domain admitted supply).Input d) :
    (matrix x).PosDef ∧ (preconditioner x).PosDef ∧
      d 1 ≤ krylovGrade (preconditioner x * matrix x)
        (preconditioner x *ᵥ decv id (d 0) x.val.1.2) := x.property.2.2.2

/-- Both supplied matrices and every supplied vector capacity count toward resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = 2 * d 0 * d 0 + 5 * d 0 := by
  have h := Problem.withContext.initialBytes_eq
    (P := CG.RawProblem.problem outputs domain admitted) (count := 2)
    (lengths := fun d _ => d 0 * d 0)
    (extra := fun d c rhs => accepts d (c 0) (c 1) rhs)
    (supply := context_supply domain admitted supply) d x
  rw [CG.RawProblem.initialBytes_eq] at h
  change (problem domain admitted supply).initialBytes d x = _ at h
  refine h.trans ?_
  simp [outputs, List.ofFn_succ]
  ring

end NLAlib.Krylov.CG.HSPCG.Stored
