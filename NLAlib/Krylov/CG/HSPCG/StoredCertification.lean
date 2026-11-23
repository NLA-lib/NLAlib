/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.StoredRoutine
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense PCG

The system matrix, the inverse preconditioner and the right-hand side are the inputs. Zero
initialization is executed, and every matrix application runs scalar dense loops. Positive
definiteness and the preconditioned grade bound are the admission of the inputs. All counts,
work, span and memory refer to the actual transformed tree.

## Main definitions

* `NLAlib.Krylov.CG.HSPCG.Stored.Certification.inputs`: the admitted inputs.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Stored.Certification.algorithm`: the total stored dense certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Stored.Certification

open Ops
open scoped Matrix

/-- The inputs of the solver: the system matrix, the inverse preconditioner and the right-hand
side. -/
abbrev Inputs (d : Fin 2 → ℕ) : Type :=
  Matrix (Fin (d 0)) (Fin (d 0)) ℝ × Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)

/-- The admitted systems: both matrices are positive definite and the horizon is at most the
preconditioned Krylov grade of the right-hand side. -/
def accepts (d : Fin 2 → ℕ) (x : Inputs d) : Prop :=
  x.1.PosDef ∧ x.2.1.PosDef ∧ d 1 ≤ krylovGrade (x.2.1 * x.1) (x.2.1 *ᵥ x.2.2)

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ x : Inputs d, accepts d x)

/-- The admitted inputs: at the sizes of `domain`, the two matrices stored column by column and
the right-hand side, satisfying `accepts`; the four state vectors are blank. -/
noncomputable def inputs : zeroStartRoutine.Domain ℝ 2 7 where
  valid := domain
  In := Inputs
  accepts := accepts
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) Prod.fst,
    .stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) fun x => x.2.1,
    .stored (Codec.vector (d 0)) fun x => x.2.2,
    .blank (d 0), .blank (d 0), .blank (d 0), .blank (d 0)]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, Option.some.injEq] at h0 h1 h2
    exact Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h0)
      (Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h1)
        ((Codec.vector (d 0)).encode_injective h2))
  admitted := admitted
  inhabited := supply

/-- The two stored matrices, the right-hand side and four blank state vectors. -/
noncomputable abbrev problem : Problem ℝ 2 7 := (inputs domain admitted supply).problem

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 7 := zeroStartRoutine.close 2 7

/-- Both supplied matrices and every supplied vector capacity count toward resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = 2 * d 0 * d 0 + 5 * d 0 := by
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
  memory d := 2 * d 0 * d 0 + 5 * d 0 + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (3, 0) (4, 0) (5, 0) (6, 0)
    (pcgState x.val.1.1 x.val.1.2.1 x.val.1.2.2 0 (d 1)) m

/-- A jointly realized scalar/vector model certifies every admitted positive-definite system,
preconditioner and right-hand side. There is no successful-run, oracle matrix or
numerical-output callback in the assumptions. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (ExactBlas.model (problem domain admitted supply) cost)
      (specification domain admitted supply cost) := by
  refine (inputs domain admitted supply).algorithm (fun d _ => zeroStartSpec (d 0))
    ?_ ?_ ?_ (hmemory := ?_)
  · intro d _ x I hI
    obtain ⟨hS, hB, _⟩ := ExactBlas.laws hI
    exact zeroStartRoutine_meets hS hB
  · intro d _ x hx τ
    refine ⟨rfl, ?_⟩
    have hA := StoredOperator.denseMatrix_packFinMatrix x.1
    have hP := StoredOperator.denseMatrix_packFinMatrix x.2.1
    have hb := decv_ofFn (n := d 0) x.2.2
    obtain ⟨h1, h2, h3⟩ := hx
    refine ⟨?_, ?_, ?_⟩
    · exact hA.symm ▸ h1
    · exact hP.symm ▸ h2
    · change d 1 ≤ krylovGrade
        (StoredOperator.denseMatrix (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.2.1) *
          StoredOperator.denseMatrix (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.1))
        (StoredOperator.denseMatrix (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.2.1) *ᵥ
          decv id (d 0) (List.ofFn x.2.2))
      rw [hA, hP, hb]
      exact h3
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, zs, ps)
    have hA := StoredOperator.denseMatrix_packFinMatrix x.val.1.1
    have hP := StoredOperator.denseMatrix_packFinMatrix x.val.1.2.1
    have hb := decv_ofFn (n := d 0) x.val.1.2.2
    refine ⟨hpos, xs', rs, zs, ps, hys, ?_⟩
    rw [← hA, ← hP, ← hb]
    exact hrel
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Inputs.Checked`). The matrix is stored: its products are executed and
counted. -/
theorem algorithm_checked (cost : Standard.Costing) :
    (inputs domain admitted supply).Checked (algorithm domain admitted supply cost) :=
  (inputs domain admitted supply).checked_all _

end NLAlib.Krylov.CG.HSPCG.Stored.Certification
