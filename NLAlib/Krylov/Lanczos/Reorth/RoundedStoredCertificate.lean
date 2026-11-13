/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedStoredWords
public import NLAlib.Krylov.Lanczos.StoredProblem
public import NLAlib.Krylov.Lanczos.StoredProgram
public import NLAlib.Ops.Profiles.RoundedBlas
public import NLAlib.Ops.Profiles.RoundedScalarBlas
public import NLAlib.Matrix.FinitePrecision.StoredDense

/-!
# Canonical rounded stored reorthogonalized Lanczos

The matrix is the actual raw dense input. Every matrix product executes the scalar dense
loop, whose error follows from standard scalar rounding. The output reads the actual stored
basis and coefficients, including zero tails and early breakdown. Full canonical accounting
uses the same fixed tree and includes the raw matrix and supplied output capacity.

## Main results

* `NLAlib.Krylov.Lanczos.Stored.Reorth.Rounded.algorithm`: total rounded stored certification.
* `NLAlib.Krylov.Lanczos.Stored.Reorth.Rounded.scalarAlgorithm`: actual scalar-only certification.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Stored.Reorth.Rounded

open Ops

/-- Supplied symmetric dense matrices and arbitrary right-hand-side words, with ordinary
basis and coefficient capacity. An actual zero matrix witnesses every admitted size. -/
def problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem ℝ 2 4 :=
  StoredProblem.problem (fun cap => 3 * cap + 2) domain admitted true

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The target has scalar machine functions and sequential rounded BLAS contracts. The
matrix is an explicit supplied operand, with no matrix-vector primitive in the model. -/
noncomputable def model (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (cost : Standard.Costing) :
    AccessModel RCLikeBlas.Operation CmpTst (problem domain admitted) :=
  RoundedBlas.model _ M u hM hu cost

/-- Complete canonical instruction counts of the actual context-linked stored tree. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (RCLikeBlas.Operation ⊕ Bookkeeping) CmpTst := staticCost program d

/-- Rounded numerical output and full canonical resources refer to the same execution.
Every supplied matrix, input and output cell contributes to resident modeled payload. -/
noncomputable def specification (cost : Standard.Costing) (u : ℝ)
    (E : (Fin 2 → ℕ) → ℝ) :
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
    Lanczos.Reorth.Rounded.Output id (StoredProblem.matrix x) (decv id (d 0) x.val.1.2)
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d)
      (Blas.seq.err u) (d 1) vs cs

/-- Nonnegative standard scalar rounding and explicit dimension-dependent precision certify
total stored execution for every admitted raw symmetric matrix and arbitrary right-hand side.
The matvec allowance is derived from the executed scalar products; there is no accuracy oracle,
successful-run premise, output callback or nonbreakdown assumption. -/
noncomputable def algorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (cost : Standard.Costing) (E : (Fin 2 → ℕ) → ℝ)
    (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d) (Blas.seq.err u) (d 0)) :
    Algorithm (model (domain := domain) (admitted := admitted) M u hM hu cost)
      (specification cost u E) := by
  refine Algorithm.ofWp program (by rfl) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI τ
    obtain ⟨hS, hB, hCmp⟩ := RoundedBlas.laws hI
    have hw := Lanczos.Reorth.Rounded.stored_solve_wp
      (n := d 0) (cap := d 1) (cutoff := 1) (τ := τ)
      (μ := (problem domain admitted).initial d x) (B := (1, 0)) (V := (2, 0)) (C := (3, 0))
      hS hM hB trivial hCmp (hprec d hd) [(0, 0)] 0 (x.val.1.1 0)
      (mul_nonneg (mul_nonneg (ScalarProducts.roundoff_nonneg hu _) (Real.sqrt_nonneg _))
        (specNorm_nonneg _))
      (hM.norm_mulVec_sub_rowWord_le hu _ _ _) (by simp) (by simp [Problem.initial])
      (StoredProblem.initial_matrix d x) (by simp)
      (by norm_num) (by norm_num) (by norm_num)
      (StoredProblem.initial_live d x) (StoredProblem.initial_rhs d x)
      (StoredProblem.initial_room d x)
    rw [← Stored.environment_eq] at hw
    exact hw.mono fun _ h _ _ => h
  · intro d _ x
    have hbytes : (problem domain admitted).initialBytes d x =
        d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (3 * d 1 + 2)) :=
      StoredProblem.initialBytes_eq d x
    rw [hbytes]
    exact le_rfl

/-- One fixed tree expands every level-one operation to scalar loops. The target signature
contains scalar operation names only: neither BLAS nor matvec primitives are available. -/
def scalarProgram : Program ScalarOp CmpTst 2 4 :=
  program.link RoundedScalarBlas.table

/-- Full instruction and scratch budgets are recomputed after scalar vector lowering.
The mathematical output is exactly the same physical packed output relation. -/
noncomputable def scalarSpecification (M : Machine ℝ) (u : ℝ)
    (E : (Fin 2 → ℕ) → ℝ) :
    Specification ScalarOp CmpTst (problem domain admitted) where
  budget d := staticCost scalarProgram d
  scratch d := staticPeak (RoundedScalarBlas.model (problem domain admitted) M).resources
    scalarProgram d
  work d := (RoundedScalarBlas.model (problem domain admitted) M).resources.work
    (staticCost scalarProgram d)
  span d := (RoundedScalarBlas.model (problem domain admitted) M).resources.span
    (staticCost scalarProgram d)
  memory d := d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (3 * d 1 + 2)) +
    staticPeak (RoundedScalarBlas.model (problem domain admitted) M).resources scalarProgram d
  good d x τ _ mem := (specification .unit u E).good d x τ 0 mem

/-- The actual scalar-only stored tree has the same rounded output and full canonical
resources for every admitted raw input. Both matrix and vector arithmetic execute fixed scalar
implementations; early breakdown, zero input and empty dimensions remain total. -/
noncomputable def scalarAlgorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (E : (Fin 2 → ℕ) → ℝ)
    (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d) (Blas.seq.err u) (d 0)) :
    Algorithm (RoundedScalarBlas.model (problem domain admitted) M)
      (scalarSpecification M u E) := by
  refine (algorithm M u hM hu .unit E hprec).link RoundedScalarBlas.table
    (RoundedScalarBlas.model (problem domain admitted) M) (scalarSpecification M u E)
    (by rfl) ?_ ?_ (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) ?_
  · intro d _ x I hI
    exact RoundedScalarBlas.contracts_link hM hu hI
  · intro d _ x τ c mem _ hg c' _
    exact hg
  · intro d _ x
    have hbytes : (problem domain admitted).initialBytes d x =
        d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (3 * d 1 + 2)) :=
      StoredProblem.initialBytes_eq d x
    rw [hbytes]
    exact le_rfl

end NLAlib.Krylov.Lanczos.Stored.Reorth.Rounded
