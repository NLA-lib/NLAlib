/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Certificate

/-!
# Canonical certification after sequential scalar lowering

This certificate checks the actual fixed tree with BLAS calls replaced by their sequential
scalar implementations. Its complete static manifest, work/span and scratch are recomputed
on that lowered syntax. Matvec stays a declared primitive, and its own error and resources
remain explicit. The common supplied-buffer problem and full resident payload are unchanged.

The sequential reduction errors are derived from the model's scalar unit roundoff even when
the enclosing standard model also offers a different BLAS scheme. No abstract BLAS resource
certificate is substituted for the lowered program's complete canonical accounting.

## Main results

* `NLAlib.Krylov.Lanczos.SequentialCertification.algorithm`: actual lowered-tree certificate.
* `NLAlib.Krylov.Lanczos.SequentialCertification.body_program_eq_link`: the precise scalar lowering.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.SequentialCertification

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K]
variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The computable fixed table underlying the proved sequential BLAS profile. -/
def sequentialTable : Table Standard.Operation Standard.Operation CmpTst :=
  Table.comp Blas.level1Table Blas.sumSeqTable

/-- A fixed sequential scalar tree; dimensions and cap are supplied only at runtime. -/
def program : Program Standard.Operation CmpTst 2 3 :=
  Certification.program.link sequentialTable

/-- The canonical program is exactly the tree whose sequential numerical proof is reused. -/
theorem body_program_eq_link : program.body =
    (solve (Op := Standard.Operation) (Tst := CmpTst)).link Blas.seq.table := rfl

/-- Full accounting is recomputed on the actual instrumented lowered tree, before inputs run. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (Standard.Operation ⊕ Bookkeeping) CmpTst := staticCost program d

/-- Structural projection preserves the actual lowered syntax's primitive and query count. -/
theorem original_staticBudget (d : Fin 2 → ℕ) :
    Count.original (staticBudget d) =
      stmtCost ((solve (Op := Standard.Operation) (Tst := CmpTst)).link Blas.seq.table)
        [d 0, d 1, 0, 0, 0] := by
  rw [staticBudget, staticCost, original_stmtCost_instrument, body_program_eq_link]
  rfl

/-- The entire lowered scalar program matches the standard cell-format signatures. -/
theorem wellTyped_program (scheme : Standard.Scheme) (cost : Standard.Costing)
    (work scratch : List ℕ → ℕ) :
    program.wellTyped (Standard.resources scheme cost work scratch) (fun _ => .cell) = true := by
  rfl

/-- Complete lowered instruction/work/span/scratch limits and actual numerical output.
Resident payload includes every supplied output slot; scratch is the static bound of the
actual lowered tree, including its primitive workspace and query reservation. -/
noncomputable def specification
    (model : Standard.Model (Certification.problem (K := K) domain admitted) (fun d => d 0))
    (E : (Fin 2 → ℕ) → ℝ) :
    Specification Standard.Operation CmpTst (Certification.problem (K := K) domain admitted) :=
  { Certification.specification model E with
    budget := staticBudget
    scratch d := staticPeak model.resources program d
    work d := model.resources.work (staticBudget d)
    span d := model.resources.span (staticBudget d)
    memory d := d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2) +
      staticPeak model.resources program d }

/-- The actual sequential scalar lowering succeeds under its scalar-derived reduction errors,
rounded matvec, symmetry and precision assumptions. Every canonical resource bound is checked
on that same lowered program, with no successful-execution premise. -/
noncomputable def algorithm
    (model : Standard.Model (Certification.problem (K := K) domain admitted) (fun d => d 0))
    (cost : Standard.Costing) (matvecWork matvecScratch : List ℕ → ℕ)
    (hresources : model.resources =
      Standard.resources model.scheme cost matvecWork matvecScratch)
    (em E : (Fin 2 → ℕ) → ℝ)
    (haccuracy : ∀ d, domain d → Standard.Accuracy (em d)
      (model.scheme.roundoff model.unit) (E d)
      (Blas.seq.err (model.scheme.roundoff model.unit)) (d 0))
    (hbudget : ∀ d, domain d → ∀ x, model.scheme.roundoff (model.matvecAllowance d x) ≤
      em d * specNorm (model.matrix d x))
    (hAT : ∀ d, domain d → ∀ x, (model.matrix d x)ᵀ = model.matrix d x) :
    Algorithm model.access (specification model E) :=
  Algorithm.ofWp program
    (by change program.wellTyped model.resources (fun _ => .cell) = true
        rw [hresources]; exact wellTyped_program ..)
    (fun d hd x I hI τ => by
      obtain ⟨hS, _, hA, hCmp⟩ := model.laws hI
      have hu := (model.scheme.errors_nonneg model.unit_nonneg (d 0)).1
      obtain ⟨_, hd0, ha0, hc0⟩ := Standard.Scheme.errors_nonneg .sequential hu (d 0)
      have hp := Rounded.Precision.of_budgets (haccuracy d hd).nonneg
        (haccuracy d hd).small hu hd0 ha0 hc0 (haccuracy d hd).matvec
        (haccuracy d hd).scalar (haccuracy d hd).dot (haccuracy d hd).axpy
        (haccuracy d hd).scal
      have hr := Rounded.runs_solve_seq hS model.scalar hu (hA.mono (hbudget d hd x))
        hCmp (hAT d hd x) hp (τ := τ)
        (μ := (Certification.problem (K := K) domain admitted).initial d x)
        (B := (0, 0)) (V := (1, 0)) (C := (2, 0))
        (by omega) (by omega) (by omega) (Certification.initial_live d x)
        (Certification.initial_readBlock d x) (Certification.initial_room d x)
      rw [← Certification.environment_eq] at hr
      have hw := hr.wp
      rw [← body_program_eq_link] at hw
      exact hw.mono fun m hg _ _ => hg)
    (fun _ _ => le_rfl)
    (fun _ _ => le_rfl)
    (fun _ _ => le_rfl)
    (fun _ _ => le_rfl)
    (fun d _ x => by
      rw [Certification.initialBytes_problem]
      exact le_rfl)

/-- The sequentially lowered canonical program has an explicit exact identity-operator
instance for every admitted dimension, cap and supplied real right-hand side. -/
noncomputable def exactReferenceAlgorithm (domain : (Fin 2 → ℕ) → Prop)
    (admitted : ∃ d, domain d) (cost : Standard.Costing)
    (matvecWork matvecScratch : List ℕ → ℕ) :
    Algorithm (Certification.exactReferenceModel domain admitted cost
      matvecWork matvecScratch).access
      (specification (Certification.exactReferenceModel domain admitted cost
        matvecWork matvecScratch) (fun _ => 0)) := by
  refine algorithm (Certification.exactReferenceModel domain admitted cost
    matvecWork matvecScratch) cost matvecWork matvecScratch rfl
    (fun _ => 0) (fun _ => 0) ?_ ?_ ?_
  · intro d hd
    constructor <;> norm_num [Certification.exactReferenceModel, Standard.referenceModel,
      Standard.Model.ofKernels, Standard.Scheme.roundoff, Blas.seq.err, Blas.level1Err,
      Blas.seqSumErr]
  · intro d hd x
    simp [Certification.exactReferenceModel, Standard.referenceModel,
      Standard.Model.ofKernels, Standard.Scheme.roundoff]
  · intro d hd x
    simp [Certification.exactReferenceModel, Standard.referenceModel, Standard.Model.ofKernels]

end NLAlib.Krylov.Lanczos.SequentialCertification
