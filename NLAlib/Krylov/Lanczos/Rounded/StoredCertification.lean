/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Rounded.StoredRoutine
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Krylov.Lanczos.StoredProgram
public import NLAlib.Ops.Profiles.RoundedBlas
public import NLAlib.Ops.Profiles.RoundedScalarBlas
public import NLAlib.Matrix.FinitePrecision.StoredDense

/-!
# Canonical rounded stored ordinary Lanczos

The matrix is the actual raw dense input. Every matrix product executes the scalar dense
loop, whose error follows from standard scalar rounding. The output reads the actual stored
basis and coefficients, including zero tails and early breakdown. Full canonical accounting
uses the same fixed tree and includes the raw matrix and supplied output capacity.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.Stored.Certification.algorithm`: total rounded stored
  certification.
* `NLAlib.Krylov.Lanczos.Rounded.Stored.Certification.scalarAlgorithm`: actual scalar-only
  certification.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded.Stored.Certification

open Ops
open scoped Matrix

/-- The admitted inputs: at the sizes of `domain`, every symmetric matrix, stored column by
column, with every right-hand side; the basis and the coefficients are blank. -/
noncomputable def inputs (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) :
    Lanczos.Stored.solveRoutine.Domain ℝ 2 4 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)
  accepts _ x := x.1.IsHermitian
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) Prod.fst,
    .stored (Codec.vector (d 0)) Prod.snd, .blank ((d 1 + 1) * d 0), .blank (2 * d 1 + 2)]
  fits := by domain_fits
  faithful d x y h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1)
  admitted := admitted
  inhabited _ _ := ⟨(0, fun _ => 0), Matrix.isHermitian_zero⟩

/-- The stored symmetric matrix, the right-hand side, and blank basis and coefficients. -/
noncomputable abbrev problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) :
    Problem ℝ 2 4 := (inputs domain admitted).problem

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The target has scalar machine functions and sequential rounded BLAS contracts. The
matrix is an explicit supplied operand, with no matrix-vector primitive in the model. -/
noncomputable def model (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (cost : Standard.Costing) :
    AccessModel RCLikeBlas.Operation CmpTst (problem domain admitted) :=
  RoundedBlas.model _ M u hM hu cost

/-- Complete canonical instruction counts of the actual context-linked stored tree. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (RCLikeBlas.Operation ⊕ Bookkeeping) CmpTst := staticCost Lanczos.Stored.program d

/-- Rounded numerical output and full canonical resources refer to the same execution.
Every supplied matrix, input and output cell contributes to resident modeled payload. -/
noncomputable def specification (cost : Standard.Costing)
    (E : (Fin 2 → ℕ) → ℝ) :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted) where
  budget := staticBudget
  scratch d := staticPeak (ExactBlas.resources cost) Lanczos.Stored.program d
  work d := (ExactBlas.resources cost).work (staticBudget d)
  span d := (ExactBlas.resources cost).span (staticBudget d)
  memory d := d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2)) +
    staticPeak (ExactBlas.resources cost) Lanczos.Stored.program d
  good d x _ _ m := m.pos = 0 ∧ m.store.length = 4 ∧ ∃ vs cs,
    m.store.readBlock 2 0 ((d 1 + 1) * d 0) = some vs ∧
    m.store.readBlock 3 0 (2 * d 1 + 2) = some cs ∧
    Lanczos.Rounded.Output id x.val.1.1 x.val.1.2
      (E d) (d 1) vs cs

/-- Nonnegative standard scalar rounding and explicit dimension-dependent precision certify
total stored execution for every admitted raw symmetric matrix and arbitrary right-hand side.
The matvec allowance is derived from the executed scalar products; there is no accuracy oracle,
successful-run premise, output callback or nonbreakdown assumption. -/
noncomputable def algorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (cost : Standard.Costing) (E : (Fin 2 → ℕ) → ℝ)
    (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d) (Blas.seq.err u) (d 0)) :
    Algorithm (model (domain := domain) (admitted := admitted) M u hM hu cost)
      (specification cost E) := by
  refine (inputs domain admitted).algorithm
    (fun d _ => solveSpec (d 0) (E d)) ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hB, hCmp⟩ := RoundedBlas.laws hI
    exact solveRoutine_meets hS hM hB trivial hCmp (hprec d hd)
      (mul_nonneg (ScalarProducts.roundoff_nonneg hu _) (Real.sqrt_nonneg _))
      (fun _ => hM.norm_mulVec_sub_rowWord_le hu _ _ _)
  · intro d _ x hx τ
    refine ⟨⟨rfl, ?_⟩, rfl⟩
    change (StoredOperator.denseMatrix (d 0) (d 0)
        ((EntryCodec.scalar ℝ).packFinMatrix x.1))ᵀ =
      StoredOperator.denseMatrix (d 0) (d 0) ((EntryCodec.scalar ℝ).packFinMatrix x.1)
    rw [StoredOperator.denseMatrix_packFinMatrix]
    have hH : x.1.IsHermitian := hx
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hH
  · intro d _ x τ m' hfr hpos ys hys hrel c _
    have hlen4 : ((problem domain admitted).initial d x).store.length = 4 := by
      simp [Problem.initial]
    read_outputs hys as (vs, cs)
    have hA := StoredOperator.denseMatrix_packFinMatrix x.val.1.1
    have hb := decv_ofFn (n := d 0) x.val.1.2
    refine ⟨hpos, hfr.length_eq.trans hlen4, vs, cs, hvs, hcs, ?_⟩
    rw [← hA, ← hb]
    exact hrel
  · intro d _ x
    have hbytes : (problem domain admitted).initialBytes d x =
        d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2)) := by
      refine ((inputs domain admitted).initialBytes_eq x).trans ?_
      simp [inputs, Slot.len, Codec.vector, Codec.matrix, List.ofFn_succ]
      ring
    rw [hbytes]
    exact le_rfl

/-- One fixed tree expands every level-one operation to scalar loops. The target signature
contains scalar operation names only: neither BLAS nor matvec primitives are available. -/
def scalarProgram : Program ScalarOp CmpTst 2 4 :=
  Lanczos.Stored.program.link RoundedScalarBlas.table

/-- Full instruction and scratch budgets are recomputed after scalar vector lowering.
The mathematical output is exactly the same physical packed output relation. -/
noncomputable def scalarSpecification (M : Machine ℝ)
    (E : (Fin 2 → ℕ) → ℝ) :
    Specification ScalarOp CmpTst (problem domain admitted) where
  budget d := staticCost scalarProgram d
  scratch d := staticPeak (RoundedScalarBlas.model (problem domain admitted) M).resources
    scalarProgram d
  work d := (RoundedScalarBlas.model (problem domain admitted) M).resources.work
    (staticCost scalarProgram d)
  span d := (RoundedScalarBlas.model (problem domain admitted) M).resources.span
    (staticCost scalarProgram d)
  memory d := d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2)) +
    staticPeak (RoundedScalarBlas.model (problem domain admitted) M).resources scalarProgram d
  good d x τ _ mem := (specification .unit E).good d x τ 0 mem

/-- The actual scalar-only stored tree has the same rounded output and full canonical
resources for every admitted raw input. Both matrix and vector arithmetic execute fixed scalar
implementations; early breakdown, zero input and empty dimensions remain total. -/
noncomputable def scalarAlgorithm (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u)
    (E : (Fin 2 → ℕ) → ℝ)
    (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d) (Blas.seq.err u) (d 0)) :
    Algorithm (RoundedScalarBlas.model (problem domain admitted) M)
      (scalarSpecification M E) := by
  refine (algorithm M u hM hu .unit E hprec).link RoundedScalarBlas.table
    (RoundedScalarBlas.model (problem domain admitted) M) (scalarSpecification M E)
    (by rfl) ?_ ?_ (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) ?_
  · intro d _ x I hI
    exact RoundedScalarBlas.contracts_link hM hu hI
  · intro d _ x τ c mem _ hg c' _
    exact hg
  · intro d _ x
    have hbytes : (problem domain admitted).initialBytes d x =
        d 0 * d 0 + (d 0 + (d 1 + 1) * d 0 + (2 * d 1 + 2)) := by
      refine ((inputs domain admitted).initialBytes_eq x).trans ?_
      simp [inputs, Slot.len, Codec.vector, Codec.matrix, List.ofFn_succ]
      ring
    rw [hbytes]
    exact le_rfl

end NLAlib.Krylov.Lanczos.Rounded.Stored.Certification
