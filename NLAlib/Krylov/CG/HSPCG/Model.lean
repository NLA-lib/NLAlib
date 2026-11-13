/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Linked
public import NLAlib.Ops.Profiles.Standard

/-!
# A realized closed exact PCG operation model

System and inverse-preconditioner applications have distinct operation names and resource
charges. Exact scalar and BLAS contracts are realized jointly with both operators. The closed
query signature is empty, so neither operator can be acquired through a query escape hatch.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Model.exactModel`: the jointly realized operation model.
* `NLAlib.Krylov.CG.HSPCG.Model.laws`: exactly the declared local contracts.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Model

open Ops

/-- The actual storage arities of scalar, BLAS and both distinct operator calls. -/
def signature : Signature → OperandSignature
  | .scalar a => Standard.signature (.scalar a)
  | .blas a => Standard.signature (.blas a)
  | .operator | .preconditioner => Standard.signature .matvec

/-- Both operator profiles and workspace charges are explicit, alongside scalar/BLAS work.
Span is sequential; every structural instruction retains its own charge. -/
noncomputable def resources (cost : Standard.Costing)
    (aw ap sw sp : List ℕ → ℕ) : ResourceModel Signature Empty where
  formats := [.cell]
  operation := signature
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace o d := match o with
    | .operator => sw d
    | .preconditioner => sp d
    | _ => Blas.ws (Op := Signature) 0 o d
  queryWorkspace q := nomatch q
  operationWork o d := match o with
    | .scalar _ => 1
    | .blas a => cost.blasWork a d
    | .operator => aw d
    | .preconditioner => ap d
  operationSpan o d := match o with
    | .scalar _ => 1
    | .blas a => cost.blasWork a d
    | .operator => aw d
    | .preconditioner => ap d
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- Exact local vector contracts, selected uniformly by the BLAS operation name. -/
def blasContract (a : Blas1Op) : Contract ℝ := match a with
  | .sum => (sumExactRel id).spec (OutApart (fun _ => True))
  | .dot => (dotExactRel id).spec (OutApart (fun _ => True))
  | .axpy => (axpyExactRel id).spec (InPlace (fun _ => True))
  | .nrm2 => (nrm2ExactRel id).spec (OutApart (fun _ => True))
  | .scal => (scalExactRel id).spec (InPlace (fun _ => True))
  | .copy => copyRel.spec (OutApart (fun _ => True))

/-- Jointly realized exact scalar, BLAS, system and preconditioner contracts. No whole solver
property is part of the operation model. The matrix functions specify the mathematical
operators at the supplied problem instance. -/
noncomputable def exactModel {r b : ℕ} (P : Problem ℝ r b) (n : (Fin r → ℕ) → ℕ)
    (A B : (d : Fin r → ℕ) → P.Input d → Matrix (Fin (n d)) (Fin (n d)) ℝ)
    (R : ResourceModel Signature Empty) : AccessModel Signature Empty P where
  word := 0
  operation d x o := match o with
    | .scalar a => (exactMachine.fn a).rel.spec AnyOperands
    | .blas a => blasContract a
    | .operator => (matvecRel id (A d x)).spec (MatvecOperands (n d) (n d))
    | .preconditioner => (matvecRel id (B d x)).spec (MatvecOperands (n d) (n d))
  query _ _ q := nomatch q
  resources := R
  realize d _ x := by
    obtain ⟨I, _, hS, hB, hA, hP⟩ := exists_exactContracts (Op := Signature)
      (Tst := Empty) (A d x) (B d x)
    refine ⟨I, ?_, fun q => nomatch q⟩
    intro o
    cases o with
    | scalar a => exact hS a
    | operator => exact hA
    | preconditioner => exact hP
    | blas a => cases a with
      | sum => exact hB.sum
      | dot => exact hB.dot
      | axpy => exact hB.axpy
      | nrm2 => exact hB.nrm2
      | scal => exact hB.scal
      | copy => exact hB.copy

/-- Exactly the declared local numerical contracts follow from model satisfaction. -/
theorem laws {r b : ℕ} {P : Problem ℝ r b} {n : (Fin r → ℕ) → ℕ}
    {A B : (d : Fin r → ℕ) → P.Input d → Matrix (Fin (n d)) (Fin (n d)) ℝ}
    {R : ResourceModel Signature Empty} {d : Fin r → ℕ} {x : P.Input d}
    {I : Interp Signature Empty ℝ} (h : (exactModel P n A B R).contracts d x I) :
    IsScalar exactMachine I ∧ IsExactBlas1 id (fun _ => True) I ∧
      IsExactMatvec id (A d x) I ∧ IsExactPreconditioner id (B d x) I := by
  exact ⟨fun a => h.1 (.scalar a),
    ⟨h.1 (.blas .sum), h.1 (.blas .dot), h.1 (.blas .axpy),
      h.1 (.blas .nrm2), h.1 (.blas .scal), h.1 (.blas .copy)⟩,
    h.1 .operator, h.1 .preconditioner⟩

end NLAlib.Krylov.CG.HSPCG.Model
