/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.StoredRoutine
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Catalog.StoredOperator
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense Hestenes–Stiefel CG

The inputs are a matrix, stored column by column, and a right-hand side (`inputs`); the problem
is derived from the routine. Zero initialization is executed, and every matrix
application runs scalar dense loops. Positive definiteness and the grade bound on the
prescribed horizon are mathematical admission. All counts, work, span and memory refer to
the actual transformed tree.

## Main results

* `NLAlib.Krylov.CG.HSCG.Stored.Certification.algorithm`: the total stored dense certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Stored.Certification

open Ops

/-- The admitted systems: a positive-definite matrix and a right-hand side whose Krylov grade
is at least the horizon. -/
def accepts (d : Fin 2 → ℕ)
    (x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)) : Prop :=
  x.1.PosDef ∧ d 1 ≤ krylovGrade x.1 x.2

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d →
    ∃ x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ), accepts d x)

/-- The admitted inputs of conjugate gradient on a stored matrix: at the sizes of `domain`,
every positive-definite matrix, stored column by column, with every right-hand side whose
Krylov grade is at least the horizon; the iterate, the residual and the direction are blank. -/
noncomputable def inputs : zeroStartRoutine.Domain ℝ 2 5 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)
  accepts := accepts
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) Prod.fst,
    .stored (Codec.vector (d 0)) Prod.snd, .blank (d 0), .blank (d 0), .blank (d 0)]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1)
  admitted := admitted
  inhabited := supply

/-- The stored matrix, the right-hand side and three blank state vectors. -/
noncomputable abbrev problem : Problem ℝ 2 5 := (inputs domain admitted supply).problem

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 5 := zeroStartRoutine.close 2 5

/-- Resident memory counts the matrix words, RHS and all supplied output capacity. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = d 0 * d 0 + (4 * d 0) := by
  refine ((inputs domain admitted supply).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, Codec.matrix, List.ofFn_succ]
  omega

/-- Canonical resources and the exact physical CG state at the prescribed horizon. -/
noncomputable def specification (cost : Standard.Costing) :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted supply) where
  budget := staticCost program
  scratch := staticPeak (ExactBlas.resources cost) program
  work d := (ExactBlas.resources cost).work (staticCost program d)
  span d := (ExactBlas.resources cost).span (staticCost program d)
  memory d := d 0 * d 0 + (4 * d 0) + staticPeak (ExactBlas.resources cost) program d
  good d x _ _ m := m.pos = 0 ∧ HSCG.StoresState id (d 0) (2, 0) (3, 0) (4, 0)
    (cgState x.val.1.1 x.val.1.2 0 (d 1)) m

/-- A jointly realized scalar/vector model certifies every admitted raw SPD matrix and RHS.
There is no successful-run, oracle matrix or numerical-output callback in the assumptions. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (ExactBlas.model (problem domain admitted supply) cost)
      (specification domain admitted supply cost) := by
  refine (inputs domain admitted supply).algorithm (fun d _ => zeroStartSpec (d 0))
    ?_ ?_ ?_ (hmemory := ?_)
  · intro d _ x I hI
    obtain ⟨hS, hB, hC⟩ := ExactBlas.laws hI
    exact zeroStartRoutine_meets hS hB hC
  · intro d _ x hx τ
    refine ⟨rfl, ?_⟩
    change (StoredOperator.denseMatrix (d 0) (d 0)
        ((EntryCodec.scalar ℝ).packFinMatrix x.1)).PosDef ∧
      d 1 ≤ krylovGrade (StoredOperator.denseMatrix (d 0) (d 0)
        ((EntryCodec.scalar ℝ).packFinMatrix x.1)) (decv id (d 0) (List.ofFn x.2))
    rw [StoredOperator.denseMatrix_packFinMatrix, decv_ofFn]
    exact hx
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, ps)
    have h : HSCG.decodedState id (d 0) xs' rs ps =
        cgState (StoredOperator.denseMatrix (d 0) (d 0)
          ((EntryCodec.scalar ℝ).packFinMatrix x.val.1.1))
          (decv id (d 0) (List.ofFn x.val.1.2)) 0 (d 1) := hrel
    rw [StoredOperator.denseMatrix_packFinMatrix, decv_ofFn] at h
    exact ⟨hpos, xs', rs, ps, hys, h⟩
  · intro d _ x
    rw [initialBytes_problem]
    exact le_rfl

/-! ### Unit weights: a closed-form count -/

/-- The number of instructions at order `d 0` and horizon `d 1`, at most. -/
def operationCount (d : Fin 2 → ℕ) : ℕ :=
  156 * d 1 + 23 * (d 0 * d 1) + 33 * (d 0 * d 0 * d 1) + 125 + 33 * (d 0 * d 0) + 29 * d 0

/-- The instruction polynomial of the program, evaluated by the kernel. -/
theorem countPoly_program : program.countPoly =
    [(156, [1]), (23, [0, 1]), (33, [0, 0, 1]), (125, []), (33, [0, 0]), (29, [0])] := by
  kernel_rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_program (d : Fin 2 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = operationCount d := by
  rw [countPoly_program]
  poly_eval [operationCount]

/-- Under unit costing every scalar and vector operation counts at most one. -/
theorem operationWork_unit_le (o : RCLikeBlas.Operation) (d : List ℕ) :
    (ExactBlas.resources .unit).operationWork o d ≤ 1 := by
  cases o <;> simp [ExactBlas.resources, Functional.cellResources, Standard.Costing.blasWork]

/-- The specification under unit weights, with the explicit operation count as work and span. -/
noncomputable def countedSpecification :
    Specification RCLikeBlas.Operation CmpTst (problem domain admitted supply) :=
  { specification domain admitted supply .unit with
    work := operationCount
    span := operationCount }

/-- Conjugate gradient on a stored matrix of order `n` at horizon `k` runs within
`33 n² k + 23 n k + 156 k + 33 n² + 29 n + 125` instructions of the model with unit weights,
with the output of `algorithm`. Products with the matrix are executed by the tree and
counted. The program, the model and the hypotheses are those of `algorithm`. -/
noncomputable def countedAlgorithm :
    Algorithm (ExactBlas.model (problem domain admitted supply) .unit)
      (countedSpecification domain admitted supply) :=
  (algorithm domain admitted supply .unit).withCountPoly operationWork_unit_le
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) operationCount
    (fun d _ => (eval_countPoly_program d).le)

/-- What the certificate states, with no reference to routines or contracts. For every order
$n$ and horizon $k$, every positive-definite matrix $\mathbf{A}$ and every right-hand side $b$
whose Krylov grade is at least $k$, every interpretation of exact scalar arithmetic and exact
level-one vector operations, and every tape, the counted run of the fixed program from
$\mathbf{A}$ stored column by column, $b$ and three blank vectors succeeds, executes at most
$33 n^2 k + 23 n k + 156 k + 33 n^2 + 29 n + 125$ instructions (each vector operation counting
one; products with the matrix are executed and counted), keeps its resident memory within the
memory of the specification, and the three vectors then hold the
iterate, residual and direction of conjugate gradient after $k$ steps from the zero iterate.
Every such system is admitted (`NLAlib.Ops.Routine.Domain.covers`). -/
theorem stored_checked (d : Fin 2 → ℕ) (hd : domain d)
    (A : Matrix (Fin (d 0)) (Fin (d 0)) ℝ) (rhs : Fin (d 0) → ℝ) (hA : A.PosDef)
    (hrhs : d 1 ≤ krylovGrade A rhs) (I : Interp RCLikeBlas.Operation CmpTst ℝ)
    (hI : (ExactBlas.model (problem domain admitted supply) .unit).contracts d
      ((inputs domain admitted supply).input d (A, rhs) ⟨hA, hrhs⟩) I)
    (τ : Tape ℝ) :
    ∃ st, exec program I (ExactBlas.model (problem domain admitted supply) .unit).resources
        (inputs domain admitted supply).formats τ d
        ((inputs domain admitted supply).memory d (A, rhs)) = some st ∧
      (ExactBlas.model (problem domain admitted supply) .unit).resources.work st.cost ≤
        operationCount d ∧
      (inputs domain admitted supply).bytes d + st.peak ≤
        (countedSpecification domain admitted supply).memory d ∧
      ∃ x r p : Fin (d 0) → ℝ, st.mem.Holds (Codec.vector (d 0)) 2 x ∧
        st.mem.Holds (Codec.vector (d 0)) 3 r ∧ st.mem.Holds (Codec.vector (d 0)) 4 p ∧
        cgState A rhs 0 (d 1) = ⟨x, r, p⟩ := by
  obtain ⟨st, hr, -, -, hw, -, hm, -, xs, rs, ps, hys, hst⟩ :=
    (inputs domain admitted supply).checked (countedAlgorithm domain admitted supply)
      d hd (A, rhs) ⟨hA, hrhs⟩ I hI τ
  obtain ⟨_, _, _, _, _, _, he, hx, hr', hp, hl⟩ := Mem.readBlocks_three hys
  obtain ⟨rfl, rfl, rfl⟩ : _ = _ ∧ _ = _ ∧ _ = _ := by simpa using he
  obtain ⟨rfl, rfl, rfl⟩ : _ = _ ∧ _ = _ ∧ _ = _ := by simpa using hl
  exact ⟨st, hr, hw, hm, _, _, _, Mem.holds_decode _ hx, Mem.holds_decode _ hr',
    Mem.holds_decode _ hp, hst.symm⟩

end NLAlib.Krylov.CG.HSCG.Stored.Certification
