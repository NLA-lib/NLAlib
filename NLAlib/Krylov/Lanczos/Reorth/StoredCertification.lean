/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.StoredProblem
public import NLAlib.Krylov.Lanczos.Reorth.StoredRoutine
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored reorthogonalized Lanczos certification

The supplied raw matrix is an explicit read-only buffer. Its applications execute scalar
loops in the fixed program, and the remaining vector calls use a jointly realized exact
BLAS model. Mathematical output and complete instruction/work/span/memory limits concern
the same total execution, including empty inputs and early breakdown.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Stored.Certification.algorithm`: the stored reorthogonalized
  certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Stored.Certification

open Ops

/-- Full reorthogonalization admits supplied symmetric matrices and arbitrary right-hand sides. -/
def problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem ℝ 2 4 :=
  StoredProblem.problem (fun cap => 3 * cap + 2) domain admitted true

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- All supplied matrix, right-hand side, basis and coefficient capacity is resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem domain admitted).Input d) :
    (problem domain admitted).initialBytes d x =
      d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (3 * d 1 + 2)) := by
  exact StoredProblem.initialBytes_eq d x

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
  memory d := d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (3 * d 1 + 2)) +
    staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ m.store.length = 4 ∧ ∃ vs cs,
    m.store.readBlock 2 0 ((d 1 + 1) * d 0) = some vs ∧
    m.store.readBlock 3 0 (3 * d 1 + 2) = some cs ∧
    Lanczos.Reorth.Output id (StoredProblem.matrix x) (decv id (d 0) x.val.1.2) (d 1) vs cs

/-- Every admitted raw dense matrix and right-hand side have a total canonical execution.
No operator oracle, preprocessing, successful-run premise or output callback is required. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (model (domain := domain) (admitted := admitted) cost) (specification cost) := by
  refine Routine.algorithm (r := 2) (b := 4) (P := problem domain admitted) solveRoutine
    (fun d _ => solveSpec (d 0)) (fun _ x => [x.val.1.1 0, x.val.1.2])  ?_ ?_ ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI
    obtain ⟨hS, hB, hCmp⟩ := ExactBlas.laws hI
    exact solveRoutine_meets hS hB hCmp
  · intro d _ x
    exact ⟨Mem.readBlocks_of_cons (StoredProblem.initial_matrix d x)
        (Mem.readBlocks_of_cons (StoredProblem.initial_rhs d x) rfl),
      fun _ => ⟨⟨rfl, StoredProblem.matrix_isHermitian x⟩, rfl⟩, StoredProblem.initial_room d x⟩
  · intro d _ x τ m' hfr hpos ys hys hrel c _
    have hlen4 : ((problem domain admitted).initial d x).store.length = 4 := by
      simp [Problem.initial]
    read_outputs hys as (vs, cs)
    exact ⟨hpos, hfr.length_eq.trans hlen4, vs, cs, hvs, hcs, hrel⟩
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.Lanczos.Reorth.Stored.Certification
