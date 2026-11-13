/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedModels
public import NLAlib.Krylov.Lanczos.BufferProblem

/-!
# Canonical resource certification of ordinary Lanczos

The fixed ordinary Lanczos tree has a total certificate for explicitly supplied right-hand-side,
basis and coefficient buffers. A declared standard operation model provides jointly realized
primitive contracts. The certificate accounts for every primitive, query and structural
instruction on the same successful execution that returns the packed numerical output.

The full size-only count is the syntactic static manifest of the fixed instrumented tree.
Its original-operation projection is the existing explicit Lanczos operation budget. Work and
sequential span apply the declared weights to this full manifest. Resident memory includes
all supplied output capacity as well as the input, with scoped and primitive scratch added.
All payload units are abstract cells; backend operator storage requires its own accounting.

## Main results

* `NLAlib.Krylov.Lanczos.Certification.algorithm`: canonical total standard-model certificate.
* `NLAlib.Krylov.Lanczos.Certification.original_staticBudget`: explicit primitive projection.
* `NLAlib.Krylov.Lanczos.Certification.initialBytes_problem`: complete supplied payload.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Certification

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K]

/-- The matrix-free Lanczos problem has an initialized right-hand side and explicitly supplied
uninitialized basis/coefficient slots. The nonempty size-only domain can express reduction
applicability and precision caps without imposing a restriction on the right-hand-side words. -/
def problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 3 :=
  PackedProblem.problem (fun cap => 2 * cap + 2) domain admitted

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- Admissibility identifies the three actual supplied buffers. -/
theorem input_buffers (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    x.val.2 = ![x.val.1.map some, List.replicate ((d 1 + 1) * d 0) none,
      List.replicate (2 * d 1 + 2) none] := PackedProblem.input_buffers d x

/-- Every supplied word list has the declared dimension. -/
theorem length_input (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    x.val.1.length = d 0 := PackedProblem.length_input d x

/-- The input and all output capacity count toward resident modeled payload, regardless of
whether early breakdown leaves some output slots zero. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x =
      d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2) := by
  exact PackedProblem.initialBytes_problem d x

/-- The supplied right-hand-side buffer reads back the declared raw word list. -/
theorem initial_readBlock (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 0 0 (d 0) = some x.val.1 := by
  exact PackedProblem.initial_readBlock d x

/-- All three supplied handles are live in the canonical initial memory. -/
theorem initial_live (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).Live [(0, 0), (1, 0), (2, 0)] := by
  exact PackedProblem.initial_live d x

/-- The public output capacities are supplied before execution; they are not hidden scratch. -/
theorem initial_room (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).Room [(1, 0), (2, 0)]
      [(d 1 + 1) * d 0, 2 * d 1 + 2] := by
  exact PackedProblem.initial_room d x

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
      solvePeak R.workspace (d 0) + R.queryReserve (staticBudget d) := by
  rw [staticPeak_eq]
  exact Nat.add_le_add_right (stmtPeak_solve_le R.workspace (d 0) (d 1) 0 0 0) _

/-- Full canonical bounds and the numerical packed-output relation for the same execution.
The full count/work/span use the syntactic size-only manifest; memory separately includes all
supplied resident buffer capacity and the declared scoped/primitive/query scratch. -/
noncomputable def specification
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (E : (Fin 2 → ℕ) → ℝ) :
    Specification Standard.Operation CmpTst (problem (K := K) domain admitted) where
  budget := staticBudget
  scratch d := solvePeak model.access.workspace (d 0) +
    model.resources.queryReserve (staticBudget d)
  work d := model.resources.work (staticBudget d)
  span d := model.resources.span (staticBudget d)
  memory d := d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2) +
    (solvePeak model.access.workspace (d 0) + model.resources.queryReserve (staticBudget d))
  good d x _ _ m := m.pos = 0 ∧ ∃ vs cs,
    m.store.readBlock 1 0 ((d 1 + 1) * d 0) = some vs ∧
    m.store.readBlock 2 0 (2 * d 1 + 2) = some cs ∧
    Rounded.Output model.decode (model.matrix d x) (decv model.decode (d 0) x.val.1)
      (E d) (d 1) vs cs

/-- Declared primitive contracts and explicit spectral-free Lanczos precision assumptions
certify successful canonical execution for every admitted size and every supplied word input.
Symmetry, scheme applicability, a common accuracy envelope and the normwise matvec allowance
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
      em d * specNorm (model.matrix d x))
    (hAT : ∀ d, domain d → ∀ x, (model.matrix d x)ᵀ = model.matrix d x) :
    Algorithm model.access (specification model E) :=
  Algorithm.ofWp program
    (by change program.wellTyped model.resources (fun _ => .cell) = true
        rw [hresources]; exact wellTyped_program ..)
    (fun d hd x I hI τ => by
      have hr := Rounded.runs_solve_of_model model hI (cap := d 1) (hok d hd)
        (hbudget d hd x) (hAT d hd x) (haccuracy d hd) (τ := τ)
        (μ := (problem (K := K) domain admitted).initial d x)
        (B := (0, 0)) (V := (1, 0)) (C := (2, 0))
        (by omega) (by omega) (by omega) (initial_live d x)
        (initial_readBlock d x) (initial_room d x)
      rw [← environment_eq] at hr
      exact hr.wp.mono fun m hg _ _ => hg)
    (fun _ _ => le_rfl)
    (fun d _ => staticPeak_program_le model.resources d)
    (fun _ _ => le_rfl)
    (fun _ _ => le_rfl)
    (fun d _ x => by
      rw [initialBytes_problem]
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
        (fun _ => 0)) := by
  refine algorithm (exactReferenceModel domain admitted cost matvecWork matvecScratch)
    cost matvecWork matvecScratch rfl (fun _ => 0) (fun _ => 0) ?_ ?_ ?_ ?_
  · intro d hd
    trivial
  · intro d hd
    constructor <;> norm_num [exactReferenceModel, Standard.referenceModel,
      Standard.Model.ofKernels, Standard.Scheme.roundoff, Standard.Scheme.errors,
      Blas.seq.err, Blas.level1Err, Blas.seqSumErr]
  · intro d hd x
    simp [exactReferenceModel, Standard.referenceModel, Standard.Model.ofKernels,
      Standard.Scheme.roundoff]
  · intro d hd x
    simp [exactReferenceModel, Standard.referenceModel, Standard.Model.ofKernels]

end NLAlib.Krylov.Lanczos.Certification
