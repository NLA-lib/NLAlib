/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.StoredRoutine
public import NLAlib.Ops.RoutineProblem
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

/-- The admitted systems: a symmetric matrix with spectrum in the supplied positive window,
with any right-hand side. -/
def accepts (lower upper : (Fin 2 → ℕ) → ℝ) (d : Fin 2 → ℕ)
    (x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)) : Prop :=
  x.1ᵀ = x.1 ∧ spectrum ℝ x.1 ⊆ Set.Icc (lower d) (upper d)

variable (lower upper : (Fin 2 → ℕ) → ℝ)

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d →
    ∃ x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ), accepts lower upper d x)

/-- The admitted inputs: at the sizes of `domain`, every symmetric matrix with spectrum in the
window, stored column by column, with every right-hand side; the iterate, the residual, the
direction and the residual product cell are blank. -/
noncomputable def inputs : zeroStartRoutine.Domain ℝ 2 6 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)
  accepts := accepts lower upper
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
noncomputable abbrev problem : Problem ℝ 2 6 :=
  (inputs lower upper domain admitted supply).problem

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 6 := zeroStartRoutine.close 2 6

/-- Resident memory counts the matrix words, RHS and all supplied output capacity. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem lower upper domain admitted supply).Input d) :
    (problem lower upper domain admitted supply).initialBytes d x = d 0 * d 0 + (4 * d 0 + 1) := by
  refine ((inputs lower upper domain admitted supply).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, Codec.matrix, List.ofFn_succ]
  ring

/-- Canonical resources and rounded stability of the actual stored CG state. -/
noncomputable def specification (cost : Standard.Costing) (E : (Fin 2 → ℕ) → ℝ) :
    Specification RCLikeBlas.Operation CmpTst (problem lower upper domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak (ExactBlas.resources cost) program
  work d := (ExactBlas.resources cost).work (staticCost program d)
  span d := (ExactBlas.resources cost).span (staticCost program d)
  memory d := d 0 * d 0 + (4 * d 0 + 1) + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧
    StableOutput id x.val.1.1 x.val.1.2
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
  refine (inputs lower upper domain admitted supply).algorithm
    (fun d _ => zeroStartSpec (d 0) (E d) (lower d) (upper d)) ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hB, hC⟩ := RoundedBlas.laws hI
    exact zeroStartRoutine_meets hS hM hu hB hC (hMatvec d hd) (hAccuracy d hd) (ha d hd)
      (hprec d hd)
  · intro d hd x hx τ
    have hA := StoredOperator.denseMatrix_packFinMatrix x.1
    refine ⟨rfl, ?_, ?_, hwindow d hd⟩
    · change (StoredOperator.denseMatrix (d 0) (d 0)
          ((EntryCodec.scalar ℝ).packFinMatrix x.1))ᵀ =
        StoredOperator.denseMatrix (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.1)
      rw [hA]
      exact hx.1
    · change spectrum ℝ (StoredOperator.denseMatrix (d 0) (d 0)
          ((EntryCodec.scalar ℝ).packFinMatrix x.1)) ⊆ _
      rw [hA]
      exact hx.2
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs, rs, ps, vs)
    have hA := StoredOperator.denseMatrix_packFinMatrix x.val.1.1
    have hb := decv_ofFn (n := d 0) x.val.1.2
    refine ⟨hpos, ?_⟩
    rw [← hA, ← hb]
    exact StableOutput.of_values hys hrel
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

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Routine.Domain.Checked`). -/
theorem algorithm_checked (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (cost : Standard.Costing) (em E : (Fin 2 → ℕ) → ℝ)
    (hMatvec : ∀ d, domain d → ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0) ≤ em d)
    (hAccuracy : ∀ d, domain d → Standard.Accuracy (em d) u (E d) (Blas.seq.err u) (d 0))
    (ha : ∀ d, domain d → 0 < lower d)
    (hprec : ∀ d, domain d → 3 * E d * upper d ≤ lower d)
    (hwindow : ∀ d, domain d → (d 1 : ℝ) ^ 2 * Real.sqrt (d 1) * E d *
      (upper d / lower d) ^ 2 ≤ 1 / 10 ^ 5) :
    (inputs lower upper domain admitted supply).Checked
      (algorithm lower upper domain admitted supply M u hM hu cost em E hMatvec hAccuracy ha
        hprec hwindow) :=
  (inputs lower upper domain admitted supply).checked_all _

end NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Certification
