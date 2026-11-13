/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.StoredWords
public import NLAlib.Krylov.CG.StoredProblem
public import NLAlib.Krylov.CG.ZeroStart
public import NLAlib.Ops.Profiles.RoundedBlas
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Canonical rounded stored dense HSCG.Carried

The supplied matrix and RHS are raw input. Zero initialization is executed, and every matrix
application runs scalar dense loops. Symmetry and spectral bounds concern the actual matrix.
The theorem states the scalar precision and cap window needed for totality. All counts, work,
span and memory refer to the actual transformed tree.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.algorithm`: the total stored dense certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored

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
def program : Program RCLikeBlas.Operation CmpTst 2 6 :=
  ⟨.seq (.frame [.var 0] [⟨2, .var 4⟩] CG.zeroVector.body)
    (.frame [.var 0, .var 1]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨2, .var 4⟩,
        ⟨3, .var 5⟩, ⟨4, .var 6⟩, ⟨5, .var 7⟩]
      ((solve (Op := Standard.Operation) (Tst := CmpTst)).linkContext 1 2
        (ContextLinear.table 1 0)))⟩

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
  refine Algorithm.ofWp program (by rfl) ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI τ
    obtain ⟨hS, hB, hC⟩ := RoundedBlas.laws hI
    let μ := (problem lower upper domain admitted supply).initial d x
    have hlen (i : Fin 5) := StoredProblem.initial_len d x i
    have hz := CG.writes_zeroVector_readBlock (m := μ) (τ := τ) (n := d 0)
      (x := (2, 0)) hS (by simpa [μ] using (hlen 1).ge)
    change Wp .total I τ (.seq _ _) _ _ μ
    apply wp_seq
    refine (hz.in_frame rfl rfl (by simp [Mem.Live, μ, Problem.initial])).wp ?_
    intro ν hfr hz'
    have hData : ν.store.readBlock 0 0 (d 0 * d 0) = some (x.val.1.1 0) :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint)
        (StoredProblem.initial_matrix d x)
    have hRhs : ν.store.readBlock 1 0 (d 0) = some x.val.1.2 :=
      hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by disjoint)
        (StoredProblem.initial_rhs d x)
    have hx0 : decv id (d 0) (List.replicate (d 0) (M.lit 0)) = 0 := by
      have hzero : M.lit 0 = 0 := hM.zero
      ext i
      simp [decv, vec, i.isLt, hzero]
    have hw := stored_solve_wp (n := d 0) (cap := d 1) (cutoff := 1) (τ := τ)
      (μ := ν) (B := (1, 0)) (X := (2, 0)) (R := (3, 0)) (P := (4, 0)) (V := (5, 0))
      hS hM hu hB hC [(0, 0)] 0 (x.val.1.1 0)
      (by simp) (by simp [hfr.length_eq, μ, Problem.initial]) hData (by simp)
      (hMatvec d hd) (hAccuracy d hd)
      (Problem.withContext.extra_input x).1 (ha d hd)
      (Problem.withContext.extra_input x).2 (hprec d hd) (hwindow d hd)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial]) hRhs hz'.2 hx0 (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add, hfr.len_eq]
        exact ⟨by simpa [μ] using (hlen 1).ge, by simpa [μ] using (hlen 2).ge,
          by simpa [μ] using (hlen 3).ge, by simpa [μ] using (hlen 4).ge⟩)
    apply wp_frame rfl rfl (by simp [Mem.Live, hfr.length_eq, μ, Problem.initial])
    exact hw.mono fun m h _ _ => by
      simpa [specification, StoredProblem.matrix, μ, Problem.initial] using
        And.intro (h.1.trans hz'.1) h.2
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

end NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored
