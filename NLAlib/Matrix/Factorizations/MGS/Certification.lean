/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Factor
public import NLAlib.Matrix.Factorizations.MGS.Resources
public import NLAlib.Ops.Certification
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

/-- The supplied buffer represents the mathematical matrix directly; no initializer is run. -/
def problem : Problem 𝕜 2 1 where
  formats _ := .cell
  valid _ := True
  Data d := Matrix (Fin (d 0)) (Fin (d 1)) 𝕜
  admissible _ A buffers := buffers 0 = ((EntryCodec.scalar 𝕜).packFinMatrix A).map some
  admitted := ⟨fun _ => 0, trivial⟩
  supply d _ := ⟨0, fun _ => ((EntryCodec.scalar 𝕜).packFinMatrix
    (0 : Matrix (Fin (d 0)) (Fin (d 1)) 𝕜)).map some, rfl⟩

/-- The supplied matrix occupies exactly its declared column-major payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem (𝕜 := 𝕜)).Input d) :
    problem.initialBytes d x = d 1 * d 0 := by
  change 1 * (x.val.2 0).length + 0 = _
  rw [one_mul, Nat.add_zero, x.property, List.length_map]
  exact (EntryCodec.length_packFinMatrix (EntryCodec.scalar 𝕜) x.val.1).trans
    (by simp)

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
    Count (RCLikeBlas.Operation ⊕ Bookkeeping) CmpTst := staticCost MGS.program d

/-- Two scoped scalar cells are the complete extra payload for this exact catalog model. -/
theorem staticPeak_program (cost : Standard.Costing) (d : Fin 2 → ℕ) :
    staticPeak (resources cost) MGS.program d = 2 := by
  rw [staticPeak_eq, (resources cost).queryReserve_of_zero (fun _ _ => rfl), Nat.add_zero]
  change stmtPeak (fun (_ : RCLikeBlas.Operation) _ => 0)
    (.frame [.var 0, .var 1] [⟨0, .const 0⟩] factor.body)
    (Program.environment (b := 1) d).idx = 2
  simp only [stmtPeak, Program.environment, List.ofFn_succ, List.ofFn_zero,
    List.cons_append, List.nil_append, IExp.evalList, IExp.eval,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  exact factor_peak_zero _

/-- Full resources and packed mathematical output refer to the same canonical execution. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem (𝕜 := 𝕜)) where
  budget := staticBudget
  scratch d := staticPeak (resources cost) MGS.program d
  work d := (resources cost).work (staticBudget d)
  span d := (resources cost).span (staticBudget d)
  memory d := d 1 * d 0 + staticPeak (resources cost) MGS.program d
  good d x _ _ m := m.pos = 0 ∧ m.store.readBlock 0 0 (d 1 * d 0) =
    some ((EntryCodec.scalar 𝕜).packFinMatrix (gramSchmidtQ x.val.1))

/-- Every raw matrix, at every rank and dimension, has a total canonical MGS execution.
The actual program performs all sweeps, comparisons, normalizations and scoped cleanup. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (model (𝕜 := 𝕜) cost) (specification cost) := by
  refine Algorithm.ofWp MGS.program (by rfl) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI τ
    obtain ⟨hS, hB, hC⟩ := laws hI
    let μ := (problem (𝕜 := 𝕜)).initial d x
    have hRead := Problem.initial_readBlock d x (0 : Fin 1) x.property
    have hLen := Problem.initial_len (P := problem (𝕜 := 𝕜)) d x (0 : Fin 1)
    have hLength : ((EntryCodec.scalar 𝕜).packFinMatrix x.val.1).length = d 1 * d 0 := by
      exact (EntryCodec.length_packFinMatrix (EntryCodec.scalar 𝕜) x.val.1).trans
        (by simp)
    rw [hLength] at hRead
    have hCap : μ.store.len 0 = d 1 * d 0 := by
      change _ = _ at hLen
      rw [x.property, List.length_map, hLength] at hLen
      exact hLen
    have hRun := writes_factor (m := μ) (τ := τ) hS hB hC x.val.1
      (y := (0, 0)) (by simp [μ, Mem.Live, Problem.initial]) hRead
      (by simpa only [Nat.zero_add] using hCap.ge)
    change Wp .total I τ (.frame _ _ _) _ _ μ
    apply wp_frame rfl rfl (by simp [μ, Mem.Live, Problem.initial])
    exact hRun.wp fun m _ h c _ => h
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.MGS.Certification
