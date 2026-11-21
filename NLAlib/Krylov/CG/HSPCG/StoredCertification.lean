/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.StoredRoutine
public import NLAlib.Krylov.CG.HSPCG.StoredProblem
public import NLAlib.Krylov.CG.StoredProblem
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense PCG

The supplied matrix and RHS are raw input. Zero initialization is executed, and every matrix
application runs scalar dense loops. Positive definiteness and the preconditioned grade
bound are explicit input admission. All counts, work, span and memory refer to the actual
transformed tree.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Stored.algorithm`: the total stored dense certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Stored

open Ops

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ rawA rawP rhs : List ℝ,
    rawA.length = d 0 * d 0 ∧ rawP.length = d 0 * d 0 ∧ rhs.length = d 0 ∧
      accepts d rawA rawP rhs)

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 7 := storedRoutine.close 2 7

/-- Canonical resources and the exact converged-or-capped physical CG state. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak (ExactBlas.resources cost) program
  work d := (ExactBlas.resources cost).work (staticCost program d)
  span d := (ExactBlas.resources cost).span (staticCost program d)
  memory d := 2 * d 0 * d 0 + 5 * d 0 + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (3, 0) (4, 0) (5, 0) (6, 0)
    (pcgState (matrix x) (preconditioner x) (decv id (d 0) x.val.1.2) 0 (d 1)) m

/-- A jointly realized scalar/vector model certifies every admitted raw SPD matrix and RHS.
There is no successful-run, oracle matrix or numerical-output callback in the assumptions. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (ExactBlas.model (problem domain admitted supply) cost)
      (specification domain admitted supply cost) := by
  refine Routine.algorithm (r := 2) (b := 7) (P := problem domain admitted supply) storedRoutine
    (fun d _ => storedSpec (d 0)) (fun _ x => [x.val.1.1 0, x.val.1.1 1, x.val.1.2])
     ?_ ?_ ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI
    obtain ⟨hS, hB, _⟩ := ExactBlas.laws hI
    exact storedRoutine_meets hS hB
  · intro d _ x
    let μ := (problem domain admitted supply).initial d x
    have hlen (i : Fin 5) := initial_len d x i
    refine ⟨Mem.readBlocks_of_cons (initial_matrix d x)
        (Mem.readBlocks_of_cons (initial_preconditioner d x)
          (Mem.readBlocks_of_cons (initial_rhs d x) rfl)),
      fun _ => ⟨rfl, accepts_input x⟩, ?_⟩
    change μ.Room [(3, 0), (4, 0), (5, 0), (6, 0)] [d 0, d 0, d 0, d 0]
    simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add]
    exact ⟨by simpa [μ, outputs] using (hlen 1).ge, by simpa [μ, outputs] using (hlen 2).ge,
      by simpa [μ, outputs] using (hlen 3).ge, by simpa [μ, outputs] using (hlen 4).ge⟩
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, zs, ps)
    exact ⟨hpos, xs', rs, zs, ps, hys, hrel⟩
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSPCG.Stored
