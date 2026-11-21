/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Routine
public import NLAlib.Matrix.Factorizations.MGS.Resources
public import NLAlib.Ops.Certification
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Profiles.Standard

/-!
# Canonical certification of rank-revealing MGS

One raw column-major matrix buffer is overwritten by its mathematical Gram–Schmidt
matrix. Rank deficiency and zero dimensions are admitted. Exact field, Hermitian BLAS
and real-part comparison contracts have a joint realization independent of the program.
The same execution satisfies the full instrumented count, work, span and memory budgets.

## Main results

* `NLAlib.MGS.Certification.algorithm`: the total canonical in-place certificate.
-/

@[expose] public section

namespace NLAlib.MGS.Certification

open Ops

variable {𝕜 : Type} [RCLike 𝕜]

/-- Zero supplies the default needed to read packed scalar entries. -/
local instance instInhabited : Inhabited 𝕜 := ⟨0⟩

/-- The admitted inputs of the factorization: every matrix, at every size, stored column by
column in the one operand, which is updated in place. -/
def inputs : (factorRoutine (Op := RCLikeBlas.Operation) (Tst := CmpTst)).Domain 𝕜 2 1 where
  valid _ := True
  In d := Matrix (Fin (d 0)) (Fin (d 1)) 𝕜
  accepts _ _ := True
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar 𝕜) (d 0) (d 1)) id]
  fits := by domain_fits
  faithful d x y h := (Codec.matrix (EntryCodec.scalar 𝕜) (d 0) (d 1)).encode_injective (by
    have h0 := h 0
    simpa only [Slot.input, Matrix.cons_val_zero, Option.some.injEq, id] using h0)
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨0, trivial⟩

/-- The supplied buffer holds the matrix, and nothing else is supplied. Every matrix is
admitted (`NLAlib.Ops.Routine.Domain.covers`). -/
abbrev problem : Problem 𝕜 2 1 := (inputs (𝕜 := 𝕜)).problem

/-- The supplied matrix occupies exactly its declared column-major payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem (𝕜 := 𝕜)).Input d) :
    problem.initialBytes d x = d 1 * d 0 := by
  refine ((inputs (𝕜 := 𝕜)).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.matrix, List.ofFn_succ]

/-- Scalar/BLAS calls share their standard signatures; all bookkeeping is charged. -/
noncomputable def resources (cost : Standard.Costing) :
    ResourceModel RCLikeBlas.Operation CmpTst where
  formats := [.cell]
  operation o := Standard.signature (Sum.elim Standard.Operation.scalar
    Standard.Operation.blas o)
  testInputs q := q.lens.map (fun _ => .cell)
  indexInputs _ := []
  workspace _ _ := 0
  queryWorkspace _ := 0
  operationWork o d := Sum.elim (fun _ => 1) (fun b => cost.blasWork b d) o
  operationSpan o d := Sum.elim (fun _ => 1) (fun b => cost.blasWork b d) o
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- Exact functional catalog contracts and real-part comparisons, jointly realized. -/
noncomputable def model (cost : Standard.Costing) :
    AccessModel RCLikeBlas.Operation CmpTst (problem (𝕜 := 𝕜)) where
  word := 0
  operation _ _ o := (RCLikeBlas.operationFunctions o).rel.spec (match o with
    | .inl _ => AnyOperands
    | .inr b => RCLikeBlas.admissible b)
  query _ _ := Standard.comparisonContract RCLike.re
  resources := resources cost
  realize _ _ _ := by
    refine ⟨RCLikeBlas.interp, ?_, ?_⟩
    · intro o
      cases o with
      | inl a => exact RCLikeBlas.interp_contracts.1 a
      | inr a => exact RCLikeBlas.interp_contracts.2.1 a
    · intro q
      exact ⟨fun _ _ _ _ h => RCLikeBlas.interp_contracts.2.2 q _ _ _ _ h, by
        intro a m
        rfl⟩

/-- Satisfying the declared contracts gives exactly the local laws used by MGS. -/
theorem laws {cost : Standard.Costing} {d : Fin 2 → ℕ}
    {x : (problem (𝕜 := 𝕜)).Input d} {I : Interp RCLikeBlas.Operation CmpTst 𝕜}
    (h : (model cost).contracts d x I) :
    IsScalar RCLikeBlas.machine I ∧ RCLikeBlas.IsExact I ∧ IsCmp RCLike.re I := by
  exact ⟨fun o => h.1 (.inl o), fun o => h.1 (.inr o), fun q _ _ _ _ hr =>
    (h.2 q).1 _ _ _ _ hr⟩

/-- The fixed instrumented tree determines its complete size-only instruction budget. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (RCLikeBlas.Operation ⊕ Bookkeeping) CmpTst := staticCost MGS.factorProgram d

/-- Two scoped scalar cells are the complete extra payload for this exact catalog model. -/
theorem staticPeak_factorProgram (cost : Standard.Costing) (d : Fin 2 → ℕ) :
    staticPeak (resources cost) MGS.factorProgram d = 2 := by
  rw [staticPeak_eq, (resources cost).queryReserve_of_zero (fun _ _ => rfl), Nat.add_zero]
  change stmtPeak (fun (_ : RCLikeBlas.Operation) _ => 0)
    (.frame [.var 0, .var 1] [⟨0, .var 2⟩, ⟨0, .var 2⟩] factor)
    (Program.environment (b := 1) d).idx = 2
  simp only [stmtPeak, Program.environment, List.ofFn_succ, List.ofFn_zero,
    List.cons_append, List.nil_append, IExp.evalList, IExp.eval,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  exact factor_peak_zero _

/-- Full resources and packed mathematical output refer to the same canonical execution. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem (𝕜 := 𝕜)) where
  budget := staticBudget
  scratch d := staticPeak (resources cost) MGS.factorProgram d
  work d := (resources cost).work (staticBudget d)
  span d := (resources cost).span (staticBudget d)
  memory d := d 1 * d 0 + staticPeak (resources cost) MGS.factorProgram d
  good d x _ _ m := m.pos = 0 ∧ m.store.readBlock 0 0 (d 1 * d 0) =
    some ((EntryCodec.scalar 𝕜).packFinMatrix (gramSchmidtQ x.val.1))

/-- Every raw matrix, at every rank and dimension, has a total canonical MGS execution.
The actual program performs all sweeps, comparisons, normalizations and scoped cleanup. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (model (𝕜 := 𝕜) cost) (specification cost) := by
  refine (inputs (𝕜 := 𝕜)).algorithm (fun _ _ => factorSpec 𝕜) ?_ (fun _ _ _ _ _ => trivial)
    ?_ (hmemory := ?_)
  · intro d _ x I hI
    obtain ⟨hS, hB, hC⟩ := laws hI
    exact factorRoutine_meets hS hB hC
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (qs)
    have hqs' : qs = (EntryCodec.scalar 𝕜).packFinMatrix (gramSchmidtQ x.val.1) := by
      have h : qs = (EntryCodec.scalar 𝕜).packFinMatrix (gramSchmidtQ
          ((EntryCodec.scalar 𝕜).matrix (d 0) (d 1)
            ((EntryCodec.scalar 𝕜).packFinMatrix x.val.1))) := hrel
      exact h.trans (congrArg (fun A => (EntryCodec.scalar 𝕜).packFinMatrix (gramSchmidtQ A))
        (EntryCodec.matrix_packFinMatrix (EntryCodec.scalar 𝕜) x.val.1))
    exact ⟨hpos, hqs.trans (congrArg some hqs')⟩
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.MGS.Certification
