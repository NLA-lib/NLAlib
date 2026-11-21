/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.StoredRoutine
public import NLAlib.Krylov.CG.StoredProblem
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Profiles.RoundedBlas
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Canonical rounded stored dense HSCG.Carried

The supplied matrix and RHS are raw input. Zero initialization is executed, and every matrix
application runs scalar dense loops. Symmetry and spectral bounds concern the actual matrix.
The theorem states the scalar precision and cap window needed for totality. All counts, work,
span and memory refer to the actual transformed tree.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification.algorithm`: the total stored dense
  certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification

open Ops
open scoped Matrix

/-- The actual raw matrix is symmetric with spectrum in the supplied positive window. -/
def accepts (lower upper : (Fin 2 → ℕ) → ℝ) (d : Fin 2 → ℕ)
    (raw : List ℝ) (_ : List ℝ) : Prop :=
  let A := StoredOperator.denseMatrix (d 0) (d 0) raw
  Aᵀ = A ∧ spectrum ℝ A ⊆ Set.Icc (lower d) (upper d)

variable (lower upper : (Fin 2 → ℕ) → ℝ)

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
    raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts lower upper d raw rhs)

/-- A declared dense matrix prefix, raw RHS and supplied uninitialized state capacities. -/
abbrev problem : Problem ℝ 2 6 :=
  StoredProblem.problem (fun d => ![0, d 0, d 0, d 0, 1]) domain admitted
    (accepts lower upper) supply

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 6 := zeroStartRoutine.close 2 6

/-- Resident memory counts the matrix words, RHS and all supplied output capacity. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem lower upper domain admitted supply).Input d) :
    (problem lower upper domain admitted supply).initialBytes d x = d 0 * d 0 + (4 * d 0 + 1) := by
  have h := Problem.withContext.initialBytes_eq d x
  refine h.trans ?_
  rw [RawProblem.initialBytes_eq]
  simp [List.ofFn_succ]
  omega

/-- Canonical resources and rounded stability of the actual stored CG state. -/
noncomputable def specification (cost : Standard.Costing) (E : (Fin 2 → ℕ) → ℝ) :
    Specification RCLikeBlas.Operation CmpTst (problem lower upper domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak (ExactBlas.resources cost) program
  work d := (ExactBlas.resources cost).work (staticCost program d)
  span d := (ExactBlas.resources cost).span (staticCost program d)
  memory d := d 0 * d 0 + (4 * d 0 + 1) + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧
    StableOutput id (StoredProblem.matrix x) (decv id (d 0) x.val.1.2)
      (E d) (lower d) (upper d) (d 1) (2, 0) (3, 0) (4, 0) (5, 0) m

/-- A jointly realized scalar/vector model certifies every admitted raw SPD matrix and RHS.
There is no successful-run, oracle matrix or numerical-output callback in the assumptions. -/
noncomputable def algorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (cost : Standard.Costing) (em E : (Fin 2 → ℕ) → ℝ)
    (hMatvec : ∀ d, domain d → ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0) ≤ em d)
    (hAccuracy : ∀ d, domain d → Standard.Accuracy (em d) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lower d)
    (hprec : ∀ d, domain d → 3 * E d * upper d ≤ lower d)
    (hwindow : ∀ d, domain d → (d 1 : ℝ) ^ 2 * Real.sqrt (d 1) * E d *
      (upper d / lower d) ^ 2 ≤ 1 / 10 ^ 5) :
    Algorithm (RoundedBlas.model (problem lower upper domain admitted supply) M u hM hu cost)
      (specification lower upper domain admitted supply cost E) := by
  refine Routine.algorithm (r := 2) (b := 6)
    (P := problem lower upper domain admitted supply) zeroStartRoutine
    (fun d _ => zeroStartSpec (d 0) (E d) (lower d) (upper d))
    (fun _ x => [x.val.1.1 0, x.val.1.2])  ?_ ?_ ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI
    obtain ⟨hS, hB, hC⟩ := RoundedBlas.laws hI
    exact zeroStartRoutine_meets hS hM hu hB hC (hMatvec d hd) (hAccuracy d hd) (ha d hd)
      (hprec d hd)
  · intro d hd x
    let μ := (problem lower upper domain admitted supply).initial d x
    have hlen (i : Fin 5) := StoredProblem.initial_len d x i
    refine ⟨Mem.readBlocks_of_cons (StoredProblem.initial_matrix d x)
        (Mem.readBlocks_of_cons (StoredProblem.initial_rhs d x) rfl),
      fun _ => ⟨rfl, (Problem.withContext.extra_input x).1,
        (Problem.withContext.extra_input x).2, hwindow d hd⟩, ?_⟩
    change μ.Room [(2, 0), (3, 0), (4, 0), (5, 0)] [d 0, d 0, d 0, 1]
    simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add]
    exact ⟨by simpa [μ] using (hlen 1).ge, by simpa [μ] using (hlen 2).ge,
      by simpa [μ] using (hlen 3).ge, by simpa [μ] using (hlen 4).ge⟩
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs, rs, ps, vs)
    exact ⟨hpos, StableOutput.of_values hys hrel⟩
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

/-- The complete fixed tree uses scalar operations only, including every BLAS and matvec call. -/
def scalarProgram : Program ScalarOp CmpTst 2 6 := program.link RoundedScalarBlas.table

/-- Output stability is preserved while all resource bounds are recomputed on the final
scalar-only tree, including vector scratch, structural instructions and resident matrix data. -/
noncomputable def scalarSpecification (E : (Fin 2 → ℕ) → ℝ) :
    Specification ScalarOp CmpTst (problem lower upper domain admitted supply) where
  budget := staticCost scalarProgram
  scratch := staticPeak RoundedScalarBlas.resources scalarProgram
  work d := RoundedScalarBlas.resources.work (staticCost scalarProgram d)
  span d := RoundedScalarBlas.resources.span (staticCost scalarProgram d)
  memory d := d 0 * d 0 + (4 * d 0 + 1) +
    staticPeak RoundedScalarBlas.resources scalarProgram d
  good d x τ _ mem := (specification lower upper domain admitted supply .unit E).good d x τ 0 mem

/-- Standard scalar rounding and the actual raw matrix's spectral window imply total execution,
physical numerical stability and full counted resources for the scalar-only stored solver.
No BLAS, matvec accuracy callback or successful-run assumption is required. -/
noncomputable def scalarAlgorithm (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (em E : (Fin 2 → ℕ) → ℝ)
    (hMatvec : ∀ d, domain d → ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0) ≤ em d)
    (hAccuracy : ∀ d, domain d → Standard.Accuracy (em d) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lower d)
    (hprec : ∀ d, domain d → 3 * E d * upper d ≤ lower d)
    (hwindow : ∀ d, domain d → (d 1 : ℝ) ^ 2 * Real.sqrt (d 1) * E d *
      (upper d / lower d) ^ 2 ≤ 1 / 10 ^ 5) :
    Algorithm (RoundedScalarBlas.model (problem lower upper domain admitted supply) M)
      (scalarSpecification lower upper domain admitted supply E) := by
  refine (algorithm lower upper domain admitted supply M u hM hu .unit em E
    hMatvec hAccuracy ha hprec hwindow).link RoundedScalarBlas.table
    (RoundedScalarBlas.model (problem lower upper domain admitted supply) M)
    (scalarSpecification lower upper domain admitted supply E)
    (by rfl) ?_ ?_ (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) ?_
  · intro d _ x I hI
    exact RoundedScalarBlas.contracts_link hM hu hI
  · intro d _ x τ c mem _ hg c' _
    exact hg
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification
