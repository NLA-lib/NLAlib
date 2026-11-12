/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.BufferProblem
public import NLAlib.Krylov.Lanczos.Reorth.RoundedModels

/-!
# Canonical full resource certificate for reorthogonalized Lanczos

One fixed program initializes all packed outputs, executes both classical passes in every
active round and exits safely at zero norm or the cap. Its actual rounded history and all
primitive, query, structural, work, span and payload bounds concern the same execution.

Caller-owned basis and coefficient capacity count toward resident memory. Extra raw-norm
entries and growing classical-pass scratch are explicit; cells are abstract payload units.
No global orthogonality or tau-admissibility assumption is required for total execution.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Certification.algorithm`: canonical rounded certificate.
* `NLAlib.Krylov.Lanczos.Reorth.Certification.original_staticBudget`: primitive projection.
* `NLAlib.Krylov.Lanczos.Reorth.Certification.exactReferenceAlgorithm`: nonvacuous witness.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Certification

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K]

/-- Full reorthogonalization supplies the ordinary coefficients and cap saved raw norms. -/
def problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 3 :=
  PackedProblem.problem (fun cap => 3 * cap + 2) domain admitted

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- One fixed tree, with only its dimension and cap supplied by the canonical environment. -/
def program : Program Standard.Operation CmpTst 2 3 := ⟨solve⟩

/-- The canonical size environment is precisely the public Lanczos buffer interface. -/
theorem environment_eq (d : Fin 2 → ℕ) :
    Program.environment (b := 3) d = Env.frame [d 0, d 1] [(0, 0), (1, 0), (2, 0)] := by
  rfl

/-- The complete instruction budget is computed syntactically before any input is executed.
It includes index expressions, addressing, allocations, control and all primitive/query calls. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (Standard.Operation ⊕ Bookkeeping) CmpTst := staticCost program d

/-- Projecting the full manifest recovers the explicit Lanczos primitive and query budget.
The complete canonical certificate still bounds structural counts before this projection. -/
theorem original_staticBudget (d : Fin 2 → ℕ) :
    Count.original (staticBudget d) = solveCount (Op := Standard.Operation) (Tst := CmpTst)
      (d 0) (d 1) := by
  rw [staticBudget, staticCost, original_stmtCost_instrument]
  change stmtCost solve [d 0, d 1, 0, 0, 0] = _
  exact stmtCost_solve ..

/-- Every declared standard resource configuration accepts the entire fixed program. -/
theorem wellTyped_program (scheme : Standard.Scheme) (cost : Standard.Costing)
    (work scratch : List ℕ → ℕ) :
    program.wellTyped (Standard.resources scheme cost work scratch) (fun _ => .cell) = true := by
  rfl

/-- The independent full manifest bounds scratch plus the core's explicit query reservation. -/
theorem staticPeak_program_le (R : ResourceModel Standard.Operation CmpTst)
    (d : Fin 2 → ℕ) :
    staticPeak R program d ≤
      solvePeak R.workspace (d 0) (d 1) + R.queryReserve (staticBudget d) := by
  rw [staticPeak_eq]
  exact Nat.add_le_add_right (stmtPeak_solve_le R.workspace (d 0) (d 1) 0 0 0) _

/-- Full canonical bounds and the numerical packed-output relation for the same execution.
The full count/work/span use the syntactic size-only manifest; memory separately includes all
supplied resident buffer capacity and the declared scoped/primitive/query scratch. -/
noncomputable def specification
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (em E : (Fin 2 → ℕ) → ℝ) :
    Specification Standard.Operation CmpTst (problem (K := K) domain admitted) where
  budget := staticBudget
  scratch d := solvePeak model.access.workspace (d 0) (d 1) +
    model.resources.queryReserve (staticBudget d)
  work d := model.resources.work (staticBudget d)
  span d := model.resources.span (staticBudget d)
  memory d := d 0 + (d 1 + 1) * d 0 + (3 * d 1 + 2) +
    (solvePeak model.access.workspace (d 0) (d 1) + model.resources.queryReserve (staticBudget d))
  good d x _ _ m := m.pos = 0 ∧ ∃ vs cs,
    m.store.readBlock 1 0 ((d 1 + 1) * d 0) = some vs ∧
    m.store.readBlock 2 0 (3 * d 1 + 2) = some cs ∧
    Rounded.Output model.decode (model.matrix d x) (decv model.decode (d 0) x.val.1)
      (em d) (model.scheme.roundoff model.unit) (E d) (model.scheme.errors model.unit)
      (d 1) vs cs

/-- Declared primitive contracts and explicit Lanczos precision assumptions
certify successful canonical execution for every admitted size and every supplied word input.
Scheme applicability, a common accuracy envelope and the normwise matvec allowance
are mathematical data/model hypotheses. No execution or desired output is assumed. The same
actual execution satisfies all instruction, work, sequential span and payload bounds. -/
noncomputable def algorithm
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (cost : Standard.Costing) (matvecWork matvecScratch : List ℕ → ℕ)
    (hresources : model.resources =
      Standard.resources model.scheme cost matvecWork matvecScratch)
    (em E : (Fin 2 → ℕ) → ℝ)
    (hok : ∀ d, domain d → model.scheme.admits (d 0))
    (haccuracy : ∀ d, domain d → Standard.Accuracy (em d)
      (model.scheme.roundoff model.unit) (E d) (model.scheme.errors model.unit) (d 0))
    (hbudget : ∀ d, domain d → ∀ x, model.scheme.roundoff (model.matvecAllowance d x) ≤
      em d * specNorm (model.matrix d x)) :
    Algorithm model.access (specification model em E) :=
  Algorithm.ofWp program
    (by change program.wellTyped model.resources (fun _ => .cell) = true
        rw [hresources]; exact wellTyped_program ..)
    (fun d hd x I hI τ => by
      have hr := Rounded.runs_solve_of_model model hI (cap := d 1) (hok d hd)
        (hbudget d hd x) (haccuracy d hd) (τ := τ)
        (μ := (problem domain admitted).initial d x)
        (B := (0, 0)) (V := (1, 0)) (C := (2, 0))
        (by omega) (by omega) (by omega) (PackedProblem.initial_live d x)
        (PackedProblem.initial_readBlock d x) (PackedProblem.initial_room d x)
      rw [← environment_eq] at hr
      exact hr.wp.mono fun m hg _ _ => hg)
    (fun _ _ => le_rfl)
    (fun d _ => staticPeak_program_le model.resources d)
    (fun _ _ => le_rfl)
    (fun _ _ => le_rfl)
    (fun d _ x => by
      have hbytes : (problem domain admitted).initialBytes d x =
          d 0 + (d 1 + 1) * d 0 + (3 * d 1 + 2) := PackedProblem.initialBytes_problem d x
      rw [hbytes]
      exact le_rfl)

/-- An explicit exact standard backend for the identity operator. Every dimension, cap and
right-hand side is admitted by the caller's size domain, and all numerical budgets are zero. -/
noncomputable def exactReferenceModel (domain : (Fin 2 → ℕ) → Prop)
    (admitted : ∃ d, domain d) (cost : Standard.Costing)
    (matvecWork matvecScratch : List ℕ → ℕ) :
    Standard.Model (problem (K := ℝ) domain admitted) (fun d => d 0) :=
  Standard.referenceModel _ _ .exact 0 le_rfl cost matvecWork matvecScratch

/-- A concrete canonical certificate exists for every cap and every supplied real input in
the exact identity-operator model. This witnesses the numerical and nonempty-input obligations
without assuming any successful execution or desired output. -/
noncomputable def exactReferenceAlgorithm (domain : (Fin 2 → ℕ) → Prop)
    (admitted : ∃ d, domain d) (cost : Standard.Costing)
    (matvecWork matvecScratch : List ℕ → ℕ) :
    Algorithm (exactReferenceModel domain admitted cost matvecWork matvecScratch).access
      (specification (exactReferenceModel domain admitted cost matvecWork matvecScratch)
        (fun _ => 0) (fun _ => 0)) := by
  refine algorithm (exactReferenceModel domain admitted cost matvecWork matvecScratch)
    cost matvecWork matvecScratch rfl (fun _ => 0) (fun _ => 0) ?_ ?_ ?_
  · intro d hd
    trivial
  · intro d hd
    constructor <;> norm_num [exactReferenceModel, Standard.referenceModel,
      Standard.Model.ofKernels, Standard.Scheme.roundoff, Standard.Scheme.errors,
      Blas.seq.err, Blas.level1Err, Blas.seqSumErr]
  · intro d hd x
    simp [exactReferenceModel, Standard.referenceModel, Standard.Model.ofKernels,
      Standard.Scheme.roundoff]

end NLAlib.Krylov.Lanczos.Reorth.Certification
