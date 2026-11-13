/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Alg
public import NLAlib.Ops.Profiles.ContextLinear

/-!
# Two explicit stored operators for preconditioned CG

The system and applied inverse preconditioner select their respective raw data capabilities.
Both use the same checked scalar dense leaf and protected-context logic. The source
interpretation is a proof device; no source guard or reference matrix operation runs in the
target implementation.

## Main results

* `NLAlib.Krylov.CG.HSPCG.StoredContext.table` forwards both declared matrices.
* `NLAlib.Krylov.CG.HSPCG.StoredContext.guarded_laws` supplies exact PCG primitive laws.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.StoredContext

open Ops

/-- Local scalar/vector contracts and the two distinct mathematical operator contracts. -/
noncomputable def relation {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Signature → BlockRel ℝ
  | .scalar o => ((RCLikeBlas.machine : Machine ℝ).fn o).rel
  | .blas o => ContextLinear.blasRelation o
  | .operator => matvecRel id A
  | .preconditioner => matvecRel id B

/-- Exact in-place or separate-buffer admissions of the original PCG interface. -/
def admissible (n : ℕ) :
    Signature → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | .scalar _ => AnyOperands
  | .blas .axpy | .blas .scal => InPlace (fun _ => True)
  | .blas _ => OutApart (fun _ => True)
  | .operator | .preconditioner => MatvecOperands n n

/-- Fixed choices of the system and preconditioner context slots. -/
def table (count systemIndex preconditionerIndex : ℕ) :
    ContextTable Signature RCLikeBlas.Operation CmpTst
  | .scalar o => .inr (.inl o)
  | .blas o => .inr (.inr o)
  | .operator => .inl (ContextDense.impl count systemIndex)
  | .preconditioner => .inl (ContextDense.impl count preconditionerIndex)

/-- The primitive source contract family is exactly the existing PCG interface. -/
theorem laws {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Signature CmpTst ℝ}
    (h : ∀ o, I.Meets .total o ((relation A B o).spec (admissible n o))) :
    IsScalar RCLikeBlas.machine I ∧ IsExactBlas1 id (fun _ => True) I ∧
      IsExactMatvec id A I ∧ IsExactPreconditioner id B I :=
  ⟨fun o => h (.scalar o),
    ⟨h (.blas .sum), h (.blas .dot), h (.blas .axpy), h (.blas .nrm2),
      h (.blas .scal), h (.blas .copy)⟩, h .operator, h .preconditioner⟩

/-- Reference functions jointly realizing the source local laws, only for the proof guard. -/
noncomputable def fallbackFunctions {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    Signature → BlockFn ℝ
  | .scalar o => RCLikeBlas.machine.fn o
  | .blas o => RCLikeBlas.functions o
  | .operator => exactMatvecFn A
  | .preconditioner => exactMatvecFn B

/-- The reference interpretation is independent of any algorithm or execution claim. -/
noncomputable def fallback {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    Interp Signature CmpTst ℝ := Functional.interp id (fallbackFunctions A B)

/-- Every reference operation satisfies its local relation on the declared operands. -/
theorem fallback_meets {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (o : Signature) :
    (fallback A B).Meets .total o ((relation A B o).spec (admissible n o)) := by
  have hS : IsScalar RCLikeBlas.machine (fallback A B) := fun a =>
    Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A B) .total (.scalar a) AnyOperands
  have hB : RCLikeBlas.IsExact (fallback A B) := fun b =>
    Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A B) .total (.blas b)
      (RCLikeBlas.admissible b)
  cases o with
  | scalar a => exact hS a
  | blas b =>
    cases b <;> first
      | exact hB.toExactBlas1.sum
      | exact hB.toExactBlas1.dot
      | exact hB.toExactBlas1.axpy
      | exact hB.toExactBlas1.nrm2
      | exact hB.toExactBlas1.scal
      | exact hB.toExactBlas1.copy
  | operator =>
    exact (Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A B) .total .operator
      AnyOperands).meets_matvec
  | preconditioner =>
    exact (Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A B) .total .preconditioner
      AnyOperands).meets_matvec

/-- Proof-side delegation protects both raw input matrices at their declared capabilities. -/
noncomputable def guarded (I : Interp RCLikeBlas.Operation CmpTst ℝ)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    (cutoff : ℕ) (reference : Store ℝ) (n : ℕ) (systemRaw preconditionerRaw : List ℝ) :
    Interp Signature CmpTst ℝ :=
  (I.linkContext (table context.length systemIndex preconditionerIndex) context).guardContext
    (fun o => (relation (StoredOperator.denseMatrix n n systemRaw)
      (StoredOperator.denseMatrix n n preconditionerRaw) o).spec (admissible n o))
    (Mem.ContextSnapshot cutoff reference) cutoff
    (fallback (StoredOperator.denseMatrix n n systemRaw)
      (StoredOperator.denseMatrix n n preconditionerRaw))

/-- The two-operator bridge derives every source local law from the actual protected raw
reads and target scalar/vector contracts. It assumes no successful PCG execution. -/
theorem guarded_meets {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (systemRaw preconditionerRaw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hA : reference.readBlock context[systemIndex].1 context[systemIndex].2 (n * n) =
      some systemRaw)
    (hP : reference.readBlock context[preconditionerIndex].1 context[preconditionerIndex].2
      (n * n) = some preconditionerRaw) :
    ∀ o, (guarded I context systemIndex preconditionerIndex cutoff reference n
      systemRaw preconditionerRaw).Meets .total o
      ((relation (StoredOperator.denseMatrix n n systemRaw)
        (StoredOperator.denseMatrix n n preconditionerRaw) o).spec (admissible n o)) := by
  intro o
  apply Interp.meets_guardContext _ _ _ _ _ _ (fallback_meets _ _ o)
  intro d ins outs τ mem hs ho hp
  cases o with
  | scalar a =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    exact hS a d ins outs τ mem hp
  | blas b =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    cases b <;> first
      | exact hB.toExactBlas1.sum d ins outs τ mem hp
      | exact hB.toExactBlas1.dot d ins outs τ mem hp
      | exact hB.toExactBlas1.axpy d ins outs τ mem hp
      | exact hB.toExactBlas1.nrm2 d ins outs τ mem hp
      | exact hB.toExactBlas1.scal d ins outs τ mem hp
      | exact hB.toExactBlas1.copy d ins outs τ mem hp
  | operator =>
    have hi := hc context[systemIndex] (List.getElem_mem ..)
    have hd := (hs.2.readBlock hi context[systemIndex].2 (n * n)).trans hA
    exact ContextDense.callS_source hS context systemIndex rfl systemRaw
      (hs.live hc) hi hd ho hp
  | preconditioner =>
    have hi := hc context[preconditionerIndex] (List.getElem_mem ..)
    have hd := (hs.2.readBlock hi context[preconditionerIndex].2 (n * n)).trans hP
    exact ContextDense.callS_source hS context preconditionerIndex rfl preconditionerRaw
      (hs.live hc) hi hd ho hp

/-- Exact PCG interfaces for both decoded raw matrices, obtained through the shared
primitive bridge before applying the original numerical word theorem. -/
theorem guarded_laws {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (systemRaw preconditionerRaw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hA : reference.readBlock context[systemIndex].1 context[systemIndex].2 (n * n) =
      some systemRaw)
    (hP : reference.readBlock context[preconditionerIndex].1 context[preconditionerIndex].2
      (n * n) = some preconditionerRaw) :
    let J := guarded I context systemIndex preconditionerIndex cutoff reference n
      systemRaw preconditionerRaw
    IsScalar RCLikeBlas.machine J ∧ IsExactBlas1 id (fun _ => True) J ∧
      IsExactMatvec id (StoredOperator.denseMatrix n n systemRaw) J ∧
        IsExactPreconditioner id (StoredOperator.denseMatrix n n preconditionerRaw) J :=
  laws (guarded_meets hS hB context systemIndex preconditionerIndex reference
    systemRaw preconditionerRaw hc hA hP)

end NLAlib.Krylov.CG.HSPCG.StoredContext
