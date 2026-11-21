/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.StoredRoutine
public import NLAlib.Krylov.CG.StoredProblem
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense Reorth

The supplied matrix and RHS are raw input. Zero initialization is executed, and every matrix
application runs scalar dense loops. Positive definiteness is mathematical admission; any RHS
and cap are allowed. All counts, work, span and memory refer to the actual transformed tree.

## Main results

* `NLAlib.Krylov.CG.Reorth.Stored.Certification.algorithm`: the total stored dense certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth.Stored.Certification

open Ops

/-- Positive definiteness concerns the actual raw matrix; RHS words are unrestricted. -/
def accepts (d : Fin 2 → ℕ) (raw : List ℝ) (_ : List ℝ) : Prop :=
  (StoredOperator.denseMatrix (d 0) (d 0) raw).PosDef

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
    raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts d raw rhs)

/-- A declared dense matrix prefix, raw RHS and supplied uninitialized state capacities. -/
abbrev problem : Problem ℝ 2 5 :=
  StoredProblem.problem (fun d => ![0, d 0, d 0, d 0]) domain admitted accepts supply

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 5 := zeroStartRoutine.close 2 5

/-- Resident memory counts the matrix words, RHS and all supplied output capacity. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = d 0 * d 0 + (4 * d 0) := by
  have h := Problem.withContext.initialBytes_eq d x
  refine h.trans ?_
  rw [RawProblem.initialBytes_eq]
  simp [List.ofFn_succ]
  omega

/-- Canonical resources and the exact converged-or-capped physical CG state. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak (ExactBlas.resources cost) program
  work d := (ExactBlas.resources cost).work (staticCost program d)
  span d := (ExactBlas.resources cost).span (staticCost program d)
  memory d := d 0 * d 0 + (4 * d 0) + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ HSCG.StoresState id (d 0) (2, 0) (3, 0) (4, 0)
    (cgState (StoredProblem.matrix x) (decv id (d 0) x.val.1.2) 0
      (min (d 1) (krylovGrade (StoredProblem.matrix x) (decv id (d 0) x.val.1.2)))) m

/-- A jointly realized scalar/vector model certifies every admitted raw SPD matrix and RHS.
There is no successful-run, oracle matrix or numerical-output callback in the assumptions. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (ExactBlas.model (problem domain admitted supply) cost)
      (specification domain admitted supply cost) := by
  refine Routine.algorithm (r := 2) (b := 5) (P := problem domain admitted supply) zeroStartRoutine
    (fun d _ => zeroStartSpec (d 0)) (fun _ x => [x.val.1.1 0, x.val.1.2])
    ?_ ?_ ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI
    obtain ⟨hS, hB, hC⟩ := ExactBlas.laws hI
    exact zeroStartRoutine_meets hS hB hC
  · intro d _ x
    let μ := (problem domain admitted supply).initial d x
    have hlen (i : Fin 4) := StoredProblem.initial_len d x i
    refine ⟨Mem.readBlocks_of_cons (StoredProblem.initial_matrix d x)
        (Mem.readBlocks_of_cons (StoredProblem.initial_rhs d x) rfl),
      fun _ => ⟨rfl, Problem.withContext.extra_input x⟩, ?_⟩
    change μ.Room [(2, 0), (3, 0), (4, 0)] [d 0, d 0, d 0]
    simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add]
    exact ⟨by simpa [μ] using (hlen 1).ge, by simpa [μ] using (hlen 2).ge,
      by simpa [μ] using (hlen 3).ge⟩
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, ps)
    exact ⟨hpos, xs', rs, ps, hys, hrel⟩
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.Reorth.Stored.Certification
