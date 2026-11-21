/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.StoredRoutine
public import NLAlib.Krylov.CG.StoredProblem
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Profiles.ExactBlas

/-!
# Canonical stored dense Hestenes–Stiefel CG

The supplied matrix and RHS are raw input. Zero initialization is executed, and every matrix
application runs scalar dense loops. Positive definiteness and the grade bound on the
prescribed horizon are mathematical admission. All counts, work, span and memory refer to
the actual transformed tree.

## Main results

* `NLAlib.Krylov.CG.HSCG.Stored.Certification.algorithm`: the total stored dense certificate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Stored.Certification

open Ops

/-- Positive definiteness concerns the actual raw matrix. The horizon is no greater than
the initial Krylov grade. -/
def accepts (d : Fin 2 → ℕ) (raw rhs : List ℝ) : Prop :=
  (StoredOperator.denseMatrix (d 0) (d 0) raw).PosDef ∧
    d 1 ≤ krylovGrade (StoredOperator.denseMatrix (d 0) (d 0) raw) (decv id (d 0) rhs)

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
  (supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
    raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts d raw rhs)

/-- A declared dense matrix prefix, raw RHS and supplied uninitialized state capacities. -/
abbrev problem : Problem ℝ 2 5 :=
  StoredProblem.problem (fun d => ![0, d 0, d 0, d 0]) domain admitted accepts supply

/-- The fixed tree initializes the iterate and forwards the matrix to each scalar matvec. -/
def program : Program RCLikeBlas.Operation CmpTst 2 5 := zeroStartRoutine.close 2 5

/-- Resident memory counts the matrix words, RHS and all supplied output capacity. -/
theorem initialBytes_problem (d : Fin 2 → ℕ) (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = d 0 * d 0 + (4 * d 0) := by
  have h := Problem.withContext.initialBytes_eq d x
  refine h.trans ?_
  rw [RawProblem.initialBytes_eq]
  simp [List.ofFn_succ]
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
    (cgState (StoredProblem.matrix x) (decv id (d 0) x.val.1.2) 0
      (d 1)) m

/-- A jointly realized scalar/vector model certifies every admitted raw SPD matrix and RHS.
There is no successful-run, oracle matrix or numerical-output callback in the assumptions. -/
noncomputable def algorithm (cost : Standard.Costing) :
    Algorithm (ExactBlas.model (problem domain admitted supply) cost)
      (specification domain admitted supply cost) := by
  refine Routine.algorithm (r := 2) (b := 5) (P := problem domain admitted supply) zeroStartRoutine
    (fun d _ => zeroStartSpec (d 0)) (fun _ x => [x.val.1.1 0, x.val.1.2])
    ?_ ?_ ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI
    obtain ⟨hS, hB, hC⟩ := ExactBlas.laws hI
    exact zeroStartRoutine_meets hS hB hC
  · intro d _ x
    let μ := (problem domain admitted supply).initial d x
    have hlen (i : Fin 4) := StoredProblem.initial_len d x i
    refine ⟨Mem.readBlocks_of_cons (StoredProblem.initial_matrix d x)
        (Mem.readBlocks_of_cons (StoredProblem.initial_rhs d x) rfl),
      fun _ => ⟨rfl, Problem.withContext.extra_input x⟩, ?_⟩
    change μ.Room [(2, 0), (3, 0), (4, 0)] [d 0, d 0, d 0]
    simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add]
    exact ⟨by simpa [μ] using (hlen 1).ge, by simpa [μ] using (hlen 2).ge,
      by simpa [μ] using (hlen 3).ge⟩
  · intro d _ x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, ps)
    exact ⟨hpos, xs', rs, ps, hys, hrel⟩
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
$n$ and horizon $k$, every positive-definite matrix stored as $n^2$ words in the first buffer and
right-hand side in the second whose Krylov grade is at least $k$, every interpretation of exact
scalar arithmetic and exact level-one vector operations, and every tape, the counted run of the
fixed program succeeds, executes at most
$33 n^2 k + 23 n k + 156 k + 33 n^2 + 29 n + 125$ instructions (each vector operation counting
one; products with the matrix are executed and counted), and leaves in the last three buffers
the iterate, residual and direction of conjugate gradient after $k$ steps from the zero
iterate. -/
theorem stored_checked (d : Fin 2 → ℕ) (hd : domain d)
    (x : (problem domain admitted supply).Input d) (I : Interp RCLikeBlas.Operation CmpTst ℝ)
    (hI : (ExactBlas.model (problem domain admitted supply) .unit).contracts d x I)
    (τ : Tape ℝ) :
    ∃ st, exec program I (ExactBlas.model (problem domain admitted supply) .unit).resources
        (problem domain admitted supply).formats τ d
        ((problem domain admitted supply).initial d x) = some st ∧
      (ExactBlas.model (problem domain admitted supply) .unit).resources.work st.cost ≤
        operationCount d ∧
      ∃ xs rs ps, st.mem.readBlocks [(2, 0), (3, 0), (4, 0)] [d 0, d 0, d 0] =
          some [xs, rs, ps] ∧
        HSCG.decodedState id (d 0) xs rs ps =
          cgState (StoredOperator.denseMatrix (d 0) (d 0) (x.val.1.1 0))
            (decv id (d 0) x.val.1.2) 0 (d 1) := by
  obtain ⟨st, hr, -, -, hw, -, -, -, xs, rs, ps, hys, hst⟩ :=
    (countedAlgorithm domain admitted supply).correct d hd x I hI τ
  exact ⟨st, hr, hw, xs, rs, ps, hys, hst⟩

end NLAlib.Krylov.CG.HSCG.Stored.Certification
