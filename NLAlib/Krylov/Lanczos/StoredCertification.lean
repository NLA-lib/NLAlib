/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.RoutineProblem
public import NLAlib.Krylov.Lanczos.StoredRoutine
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense Lanczos certification

The supplied raw matrix is an explicit read-only buffer. Its applications execute scalar
loops in the fixed program, and the remaining vector calls use a jointly realized exact
BLAS model. Mathematical output and complete instruction/work/span/memory limits concern
the same total execution, including empty inputs and early breakdown.

## Main results

* `NLAlib.Krylov.Lanczos.Stored.Certification.algorithm`: the ordinary stored canonical certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Stored.Certification

open Ops

/-- The admitted inputs of Lanczos on a stored matrix: at the sizes of `domain`, every matrix,
stored column by column, with every right-hand side; the basis and the coefficients are
blank. -/
noncomputable def inputs (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) :
    solveRoutine.Domain ℝ 2 4 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)
  accepts _ _ := True
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) Prod.fst,
    .stored (Codec.vector (d 0)) Prod.snd, .blank ((d 1 + 1) * d 0), .blank (2 * d 1 + 2)]
  fits := by domain_fits
  faithful d x y h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1)
  admitted := admitted
  inhabited _ _ := ⟨(0, fun _ => 0), trivial⟩

/-- The stored matrix, the right-hand side, and blank basis and coefficients. -/
noncomputable abbrev problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) :
    Problem ℝ 2 4 := (inputs domain admitted).problem

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- All supplied matrix, right-hand side, basis and coefficient capacity is resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem domain admitted).Input d) :
    (problem domain admitted).initialBytes d x =
      d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2)) := by
  refine ((inputs domain admitted).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, Codec.matrix, List.ofFn_succ]
  ring

/-- The target model has scalar/vector names only; the matrix lives in the declared input. -/
noncomputable def model (cost : Standard.Costing) :
    AccessModel RCLikeBlas.Operation CmpTst (problem domain admitted) :=
  ExactBlas.model _ cost

/-- Complete canonical instrumentation bounds are recomputed on the actual stored tree. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (RCLikeBlas.Operation ⊕ Bookkeeping) CmpTst := staticCost program d

/-- Exact recurrence output and conservative full static resources for the same execution.
Supplied output capacity and raw matrix data count toward resident memory. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted) where
  budget := staticBudget
  scratch d := staticPeak (ExactBlas.resources cost) program d
  work d := (ExactBlas.resources cost).work (staticBudget d)
  span d := (ExactBlas.resources cost).span (staticBudget d)
  memory d := d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2)) +
    staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ m.store.length = 4 ∧ ∃ vs cs,
    m.store.readBlock 2 0 ((d 1 + 1) * d 0) = some vs ∧
    m.store.readBlock 3 0 (2 * d 1 + 2) = some cs ∧
    Output id x.val.1.1 x.val.1.2 (d 1) vs cs

/-- Every admitted raw dense matrix and right-hand side have a total canonical execution.
No operator oracle, preprocessing, successful-run premise or output callback is required. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (model (domain := domain) (admitted := admitted) cost) (specification cost) := by
  refine (inputs domain admitted).algorithm (fun d _ => solveSpec (d 0)) ?_ ?_ ?_
    (hmemory := ?_)
  · intro d _ x I hI
    obtain ⟨hS, hB, hCmp⟩ := ExactBlas.laws hI
    exact solveRoutine_meets hS hB hCmp
  · intro d _ x hx τ
    exact ⟨rfl, rfl⟩
  · intro d _ x τ m' hfr hpos ys hys hrel c _
    have hlen4 : ((problem domain admitted).initial d x).store.length = 4 := by
      simp [Problem.initial]
    read_outputs hys as (vs, cs)
    have hA := StoredOperator.denseMatrix_packFinMatrix x.val.1.1
    have hb := decv_ofFn (n := d 0) x.val.1.2
    refine ⟨hpos, hfr.length_eq.trans hlen4, vs, cs, hvs, hcs, ?_⟩
    rw [← hA, ← hb]
    exact hrel
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.Lanczos.Stored.Certification
