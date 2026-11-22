/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.StoredRoutine
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense HSCG.Carried

The supplied matrix and RHS are raw input. Zero initialization is executed, and every matrix
application runs scalar dense loops. Positive definiteness is mathematical admission; any RHS
and cap are allowed. All counts, work, span and memory refer to the actual transformed tree.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Stored.Certification.algorithm`: the total stored dense
  certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Stored.Certification

open Ops

/-- The admitted systems: a positive-definite matrix with any right-hand side. -/
def accepts (d : Fin 2 → ℕ)
    (x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)) : Prop :=
  x.1.PosDef

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d →
    ∃ x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ), accepts d x)

/-- The admitted inputs: at the sizes of `domain`, every positive-definite matrix, stored
column by column, with every right-hand side; the iterate, the residual, the direction and the
scalar cache are blank. -/
noncomputable def inputs : zeroStartRoutine.Domain ℝ 2 6 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)
  accepts := accepts
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) Prod.fst,
    .stored (Codec.vector (d 0)) Prod.snd, .blank (d 0), .blank (d 0), .blank (d 0), .blank 1]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1)
  admitted := admitted
  inhabited := supply

/-- The stored matrix, the right-hand side and the blank state of the solver. -/
noncomputable abbrev problem : Problem ℝ 2 6 := (inputs domain admitted supply).problem

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 6 := zeroStartRoutine.close 2 6

/-- Resident memory counts the matrix words, RHS and all supplied output capacity. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = d 0 * d 0 + (4 * d 0 + 1) := by
  refine ((inputs domain admitted supply).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, Codec.matrix, List.ofFn_succ]
  ring

/-- Canonical resources and the exact converged-or-capped physical CG state. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak (ExactBlas.resources cost) program
  work d := (ExactBlas.resources cost).work (staticCost program d)
  span d := (ExactBlas.resources cost).span (staticCost program d)
  memory d := d 0 * d 0 + (4 * d 0 + 1) + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (2, 0) (3, 0) (4, 0) (5, 0)
    (cgState x.val.1.1 x.val.1.2 0 (min (d 1) (krylovGrade x.val.1.1 x.val.1.2))) m

/-- A jointly realized scalar/vector model certifies every admitted raw SPD matrix and RHS.
There is no successful-run, oracle matrix or numerical-output callback in the assumptions. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (ExactBlas.model (problem domain admitted supply) cost)
      (specification domain admitted supply cost) := by
  refine (inputs domain admitted supply).algorithm (fun d _ => zeroStartSpec (d 0))
    ?_ ?_ ?_ (hmemory := ?_)
  · intro d _ x I hI
    obtain ⟨hS, hB, hC⟩ := ExactBlas.laws hI
    exact zeroStartRoutine_meets hS hB hC
  · intro d _ x hx τ
    refine ⟨rfl, ?_⟩
    change (StoredOperator.denseMatrix (d 0) (d 0)
        ((EntryCodec.scalar ℝ).packFinMatrix x.1)).PosDef
    rw [StoredOperator.denseMatrix_packFinMatrix]
    exact hx
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, ps, vs)
    have hA := StoredOperator.denseMatrix_packFinMatrix x.val.1.1
    have hb := decv_ofFn (n := d 0) x.val.1.2
    rcases vs with _ | ⟨rr, _ | ⟨_, _⟩⟩
    · exact False.elim hrel
    · refine ⟨hpos, xs', rs, ps, rr, hys, ?_⟩
      rw [← hA, ← hb]
      exact hrel
    · exact False.elim hrel
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Routine.Domain.Checked`). The matrix is stored: its products are executed and
counted. -/
theorem algorithm_checked (cost : Standard.Costing) :
    (inputs domain admitted supply).Checked (algorithm domain admitted supply cost) :=
  (inputs domain admitted supply).checked_all _

end NLAlib.Krylov.CG.HSCG.Carried.Stored.Certification
