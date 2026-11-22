/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ContextDense
public import NLAlib.Ops.Profiles.Standard
public import NLAlib.Ops.Contract
public import NLAlib.Ops.ContextRun
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.RCLikeBlasReal
public import NLAlib.Ops.Catalog.Functional

/-!
# Exact linear contracts with explicit matrix context

A fixed context table preserves scalar and BLAS names and replaces the operator by a
scalar dense leaf. The proof-side guarded source interpretation satisfies the ordinary
exact linear contracts using only local target laws and an isolated raw matrix snapshot.

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
updates. These admissions imply preservation of the isolated matrix prefix. -/
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
theorem satisfies_relation {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Standard.Operation CmpTst ℝ}
    (hS : IsScalar RCLikeBlas.machine I) (hB : IsExactBlas1 id (fun _ => True) I)
    (hA : IsExactMatvec id A I) (o : Standard.Operation) :
    I.Satisfies .total o ((relation A o).spec (admissible n o)) := by
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
    (h : ∀ o, I.Satisfies .total o ((relation A o).spec (admissible n o))) :
    IsScalar RCLikeBlas.machine I ∧ IsExactBlas1 id (fun _ => True) I ∧
      IsExactMatvec id A I :=
  ⟨fun o => h (.scalar o),
    ⟨h (.blas .sum), h (.blas .dot), h (.blas .axpy), h (.blas .nrm2),
      h (.blas .scal), h (.blas .copy)⟩, h .matvec⟩

/-- Select the individual exact vector contracts from the standard numerical interface. -/
theorem satisfies_blas {Op Tst : Type} [Has Blas1Op Op] {I : Interp Op Tst ℝ}
    (hB : IsExactBlas1 id (fun _ => True) I) (o : Blas1Op) :
    I.Satisfies .total (Has.inj o) ((blasRelation o).spec (match o with
      | .axpy | .scal => InPlace (fun _ => True)
      | _ => OutApart (fun _ => True))) := by
  cases o with
  | sum => exact hB.sum
  | dot => exact hB.dot
  | axpy => exact hB.axpy
  | nrm2 => exact hB.nrm2
  | scal => exact hB.scal
  | copy => exact hB.copy

/-- Local reference functions used only to realize the proof-side source laws outside
the isolated context regime. The executed target contains the scalar dense leaf instead. -/
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
theorem fallback_satisfies {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (o : Standard.Operation) :
    (fallback A).Satisfies .total o ((relation A o).spec (admissible n o)) := by
  apply satisfies_relation (I := fallback A) ?_ ?_ ?_ o
  · intro a
    exact Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A) .total (.scalar a) AnyOperands
  · apply RCLikeBlas.IsExact.toExactBlas1
    intro b
    exact Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A) .total (.blas b)
      (RCLikeBlas.admissible b)
  · exact (Interp.ofFns_isFn (Tst := CmpTst) (fallbackFunctions A) .total .matvec
      AnyOperands).satisfies_matvec

end NLAlib.Ops.ContextLinear
