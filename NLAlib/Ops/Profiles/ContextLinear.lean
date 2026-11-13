/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ContextDense
public import NLAlib.Ops.Profiles.Standard
public import NLAlib.Ops.Logic.ContextSnapshot
public import NLAlib.Ops.Logic.RCLikeBlasReal
public import NLAlib.Ops.Catalog.Functional

/-!
# Exact linear contracts with explicit matrix context

A fixed context table preserves scalar and BLAS names and replaces the operator by a
scalar dense leaf. The proof-side guarded source interpretation satisfies the ordinary
exact linear contracts using only local target laws and a protected raw matrix snapshot.

## Main results

* `NLAlib.Ops.ContextLinear.relation` and `admissible` declare source local contracts.
* `NLAlib.Ops.ContextLinear.table` selects the declared stored matrix operand.
-/

@[expose] public section

namespace NLAlib.Ops.ContextLinear

/-- Exact real BLAS relations, indexed exhaustively by the existing vector operation names. -/
def blasRelation : Blas1Op → BlockRel ℝ
  | .sum => sumExactRel id
  | .dot => dotExactRel id
  | .axpy => axpyExactRel id
  | .nrm2 => nrm2ExactRel id
  | .scal => scalExactRel id
  | .copy => copyRel

/-- Scalar and vector local relations, together with the mathematical operator relation. -/
noncomputable def relation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Standard.Operation → BlockRel ℝ
  | .scalar o => ((RCLikeBlas.machine : Machine ℝ).fn o).rel
  | .blas o => blasRelation o
  | .matvec => matvecRel id A

/-- The original linear contracts use separate output buffers or prescribed exact in-place
updates. These admissions imply preservation of the protected matrix prefix. -/
def admissible (n : ℕ) :
    Standard.Operation → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | .scalar _ => AnyOperands
  | .blas .axpy | .blas .scal => InPlace (fun _ => True)
  | .blas _ => OutApart (fun _ => True)
  | .matvec => MatvecOperands n n

/-- Preserve scalar and BLAS calls and expose a selected data operand to scalar matvec. -/
def table (count index : ℕ) :
    ContextTable Standard.Operation RCLikeBlas.Operation CmpTst
  | .scalar o => .inr (.inl o)
  | .blas o => .inr (.inr o)
  | .matvec => .inl (ContextDense.impl count index)

/-- Primitive exact laws are precisely the exhaustive family of source contracts. -/
theorem meets_relation {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Standard.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : IsExactBlas1 id (fun _ => True) I)
    (hA : IsExactMatvec id A I) (o : Standard.Operation) :
    I.Meets .total o ((relation A o).spec (admissible n o)) := by
  cases o with
  | scalar o => exact hS o
  | matvec => exact hA
  | blas o => cases o with
    | sum => exact hB.sum
    | dot => exact hB.dot
    | axpy => exact hB.axpy
    | nrm2 => exact hB.nrm2
    | scal => exact hB.scal
    | copy => exact hB.copy

/-- Recover the ordinary numerical interfaces from the exhaustive source contracts. -/
theorem laws {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Standard.Operation CmpTst ℝ}
    (h : ∀ o, I.Meets .total o ((relation A o).spec (admissible n o))) :
    IsScalar RCLikeBlas.machine I ∧ IsExactBlas1 id (fun _ => True) I ∧
      IsExactMatvec id A I :=
  ⟨fun o => h (.scalar o),
    ⟨h (.blas .sum), h (.blas .dot), h (.blas .axpy), h (.blas .nrm2),
      h (.blas .scal), h (.blas .copy)⟩, h .matvec⟩

/-- Select the individual exact vector contracts from the standard numerical interface. -/
theorem meets_blas {Op Tst : Type} [Has Blas1Op Op] {I : Interp Op Tst ℝ}
    (hB : IsExactBlas1 id (fun _ => True) I) (o : Blas1Op) :
    I.Meets .total (Has.inj o) ((blasRelation o).spec (match o with
      | .axpy | .scal => InPlace (fun _ => True)
      | _ => OutApart (fun _ => True))) := by
  cases o with
  | sum => exact hB.sum
  | dot => exact hB.dot
  | axpy => exact hB.axpy
  | nrm2 => exact hB.nrm2
  | scal => exact hB.scal
  | copy => exact hB.copy

/-- The actual context-linked matvec meets its source local post on a protected raw
snapshot. All matrix arithmetic is performed by the declared scalar leaf. -/
theorem matvec_active {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (context : List (ℕ × ℕ))
    (index : Fin context.length) {n cutoff : ℕ} {reference : Store ℝ} (raw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape ℝ} {mem : Mem ℝ}
    (hs : mem.ContextSnapshot cutoff reference) (ho : ∀ z ∈ outs, cutoff ≤ z.1)
    (hp : (((relation (StoredOperator.denseMatrix n n raw) .matvec).spec
      (admissible n .matvec)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext (table context.length index) context).callS
      .matvec d ins outs τ mem)
      ((((relation (StoredOperator.denseMatrix n n raw) .matvec).spec
        (admissible n .matvec)).on .total d ins outs τ mem).post mem) := by
  have hi := hc context[index] (List.getElem_mem ..)
  have hd := (hs.2.readBlock hi context[index].2 (n * n)).trans hData
  exact ContextDense.callS_source hS context index rfl raw (hs.live hc) hi hd ho hp

/-- Protected raw data and ordinary local primitive laws give globally valid source
contracts for the proof-side guard. The fallback is used only outside the protected regime. -/
theorem meets_guarded {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : IsExactBlas1 id (fun _ => True) I)
    (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (raw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw)
    (fallback : Interp Standard.Operation CmpTst ℝ)
    (hFallback : ∀ o, fallback.Meets .total o
      ((relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o))) :
    ∀ o, ((I.linkContext (table context.length index) context).guardContext
      (fun o => (relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o))
      (Mem.ContextSnapshot cutoff reference) cutoff fallback).Meets .total o
      ((relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o)) := by
  intro o
  apply Interp.meets_guardContext _ _ _ _ _ _ (hFallback o)
  intro d ins outs τ mem hs ho hp
  cases o with
  | scalar o =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    exact hS o d ins outs τ mem hp
  | blas o =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    cases o with
    | sum => exact hB.sum d ins outs τ mem hp
    | dot => exact hB.dot d ins outs τ mem hp
    | axpy => exact hB.axpy d ins outs τ mem hp
    | nrm2 => exact hB.nrm2 d ins outs τ mem hp
    | scal => exact hB.scal d ins outs τ mem hp
    | copy => exact hB.copy d ins outs τ mem hp
  | matvec => exact matvec_active hS context index raw hc hData hs ho hp

/-- Local reference functions used only to realize the proof-side source laws outside
the protected context regime. The executed target contains the scalar dense leaf instead. -/
noncomputable def fallbackFunctions {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Standard.Operation → BlockFn ℝ
  | .scalar o => RCLikeBlas.machine.fn o
  | .blas o => RCLikeBlas.functions o
  | .matvec => exactMatvecFn A

/-- A jointly valid reference interpretation for the proof-side guard. -/
noncomputable def fallback {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Interp Standard.Operation CmpTst ℝ :=
  Functional.interp id (fallbackFunctions A)

/-- The explicit reference realizes every source primitive contract jointly. -/
theorem fallback_meets {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (o : Standard.Operation) :
    (fallback A).Meets .total o ((relation A o).spec (admissible n o)) := by
  apply meets_relation (I := fallback A) ?_ ?_ ?_ o
  · intro a
    exact Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A) .total (.scalar a) AnyOperands
  · apply RCLikeBlas.IsExact.toExactBlas1
    intro b
    exact Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A) .total (.blas b)
      (RCLikeBlas.admissible b)
  · exact (Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A) .total .matvec
      AnyOperands).meets_matvec

/-- The guarded source interpreter, a proof device determined by the actual context and
the raw matrix snapshot. All target instructions remain the explicitly linked program. -/
noncomputable def guarded (I : Interp RCLikeBlas.Operation CmpTst ℝ)
    (context : List (ℕ × ℕ)) (index : Fin context.length) (cutoff : ℕ)
    (reference : Store ℝ) (n : ℕ) (raw : List ℝ) : Interp Standard.Operation CmpTst ℝ :=
  (I.linkContext (table context.length index) context).guardContext
    (fun o => (relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o))
    (Mem.ContextSnapshot cutoff reference) cutoff
    (fallback (StoredOperator.denseMatrix n n raw))

/-- Ordinary exact scalar/vector laws and protected raw data give every guarded source
contract. No source execution assumption is required to establish these local laws. -/
theorem guarded_meets {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I)
    (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (raw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw) :
    ∀ o, (guarded I context index cutoff reference n raw).Meets .total o
      ((relation (StoredOperator.denseMatrix n n raw) o).spec (admissible n o)) :=
  meets_guarded hS hB.toExactBlas1 context index reference raw hc hData _ (fallback_meets _)

/-- Exact numerical interfaces for reusing the source algorithm word theorem. The matrix
is the decoder of the actual raw words; comparisons remain those of the target interpreter. -/
theorem guarded_laws {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : RCLikeBlas.IsExact I) (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (raw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw) :
    let J := guarded I context index cutoff reference n raw
    IsScalar RCLikeBlas.machine J ∧ IsExactBlas1 id (fun _ => True) J ∧
      IsExactMatvec id (StoredOperator.denseMatrix n n raw) J ∧ IsCmp id J := by
  obtain ⟨hs, hb, ha⟩ := laws (guarded_meets hS hB context index reference raw hc hData)
  exact ⟨hs, hb, ha, hCmp⟩

end NLAlib.Ops.ContextLinear
