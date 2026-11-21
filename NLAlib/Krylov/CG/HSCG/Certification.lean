/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Model
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Krylov.CG.HSCG.ZeroStart
public import NLAlib.Ops.OperationCount

/-!
# Canonical exact fixed-horizon conjugate gradient

The admitted inputs (`inputs`) are the right-hand sides whose Krylov grade is at least the
horizon; the problem is derived from the routine (`NLAlib.Ops.Routine.Domain`), so every such
right-hand side is covered. The program initializes its iterate, applies the operator, and
returns the actual CG state with full canonical resource accounting.

With unit weights (every scalar operation, level-one vector operation and product with the
matrix counts one) the work is a closed form computed by the kernel from the tree. That count
is at the level of vector operations and matrix products, not a scalar operation count: the
model has those as primitives. The last theorem states what the certificate means in terms of
the evaluator alone.

## Main results

* `NLAlib.Krylov.CG.HSCG.Certification.algorithm`: total fixed-horizon CG certificate.
* `NLAlib.Krylov.CG.HSCG.Certification.countedAlgorithm`: the same certificate under unit
  weights, with work at most `6 n + 127 k + 92`.
* `NLAlib.Krylov.CG.HSCG.Certification.cg_checked`: what it states, on the evaluator.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Certification

open Ops
open scoped Matrix

variable (A : (d : Fin 2 → ℕ) → Matrix (Fin (d 0)) (Fin (d 0)) ℝ)
  (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)

/-- The admitted right-hand sides: the horizon is at most the Krylov grade. -/
def accepts (d : Fin 2 → ℕ) (rhs : Fin (d 0) → ℝ) : Prop :=
  d 1 ≤ krylovGrade (A d) rhs

variable (supply : ∀ d, domain d → ∃ rhs : Fin (d 0) → ℝ, accepts A d rhs)

/-- The admitted inputs of conjugate gradient: at the sizes of `domain`, every right-hand side
whose Krylov grade is at least the horizon, held by the first operand; the iterate, the residual
and the direction are blank. The matrix `A d` is not stored: it is a parameter of the model. -/
noncomputable def inputs :
    (zeroStartRoutine (Op := HSPCG.Signature) (Tst := Empty)).Domain ℝ 2 4 where
  valid := domain
  In d := Fin (d 0) → ℝ
  accepts := accepts A
  slot d := ![.stored (Codec.vector (d 0)) id, .blank (d 0), .blank (d 0), .blank (d 0)]
  fits := by domain_fits
  faithful d x y _ h := (Codec.vector (d 0)).encode_injective (by
    have h0 := h 0
    simpa only [Slot.input, Matrix.cons_val_zero, Option.some.injEq, id] using h0)
  admitted := admitted
  inhabited := supply

/-- The right-hand side and three blank state vectors: the problem of conjugate gradient. -/
noncomputable abbrev problem : Problem ℝ 2 4 := (inputs A domain admitted supply).problem

/-- One fixed CG tree, including visible zero-iterate initialization. -/
def program : Program HSPCG.Signature Empty 2 4 := zeroStartRoutine.close 2 4

/-- The fixed wrapper uses exactly the declared scalar, BLAS and two operator signatures. -/
theorem wellTyped_program (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    program.wellTyped (HSPCG.Model.resources cost aw ap sw sp) (fun _ => .cell) = true := by
  rfl

/-- Full canonical original, query and structural instruction budget. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) : Count (HSPCG.Signature ⊕ Bookkeeping) Empty :=
  staticCost program d

/-- The original-operation projection retains the explicit zero loop and solver budget.
Structural and addressing charges remain in the full canonical manifest. -/
theorem original_staticBudget (d : Fin 2 → ℕ) :
    Count.original (staticBudget d) =
      (d 0) • Count.one (Has.inj (ScalarOp.lit 0)) [] +
        solveCount (Op := HSPCG.Signature) (Tst := Empty) (d 0) (d 1) := by
  rw [staticBudget, staticCost, original_stmtCost_instrument]
  simp [program, Routine.close, Routine.bindsFit, Routine.flat, Port.flat,
    zeroStartRoutine, zeroStart, solveRoutine, Program.environment, List.ofFn_succ,
    stmtCost, IExp.evalList, IExp.eval, fillRoutine, stmtCost_fillMap, staticCost_solve]

/-- The declared initial vector payload occupies four length-n buffers. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem A domain admitted supply).Input d) :
    (problem A domain admitted supply).initialBytes d x = 4 * d 0 := by
  refine ((inputs A domain admitted supply).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, List.ofFn_succ]
  omega

/-- The same counted run returns the full physical CG state at the prescribed horizon. -/
noncomputable def specification (R : ResourceModel HSPCG.Signature Empty) :
    Specification HSPCG.Signature Empty (problem A domain admitted supply) where
  budget := staticBudget
  scratch := staticPeak R program
  work d := R.work (staticBudget d)
  span d := R.span (staticBudget d)
  memory d := 4 * d 0 + staticPeak R program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (1, 0) (2, 0) (3, 0)
    (cgState (A d) x.val.1 0 (d 1)) m

/-- A positive-definite system matrix give successful canonical
CG for every raw input in its explicitly inhabited grade-bounded horizon domain. No success
or numerical execution witness is an assumption. The unused preconditioner primitive has
no executed charge. -/
noncomputable def algorithm (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ)
    (hA : ∀ d, domain d → (A d).PosDef) :
    Algorithm
      (HSPCG.Model.exactModel (problem A domain admitted supply) (fun d => d 0)
        (fun d _ => A d) (fun _ _ => 1) (HSPCG.Model.resources cost aw ap sw sp))
      (specification A domain admitted supply (HSPCG.Model.resources cost aw ap sw sp)) := by
  refine (inputs A domain admitted supply).algorithm (fun d _ => zeroStartSpec id (A d))
    (ht := wellTyped_program ..) ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hBlas, hOp, -⟩ := HSPCG.Model.laws hI
    exact zeroStartRoutine_meets hS exactModel_exactMachine hBlas hOp (hA d hd)
  · intro d hd x hx τ
    refine ⟨rfl, ?_⟩
    exact le_of_le_of_eq hx (congrArg (krylovGrade (A d)) (decv_ofFn (n := d 0) x).symm)
  · intro d hd x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, ps)
    have h : decodedState id (d 0) xs' rs ps = cgState (A d) x.val.1 0 (d 1) :=
      Eq.trans hrel (congrArg (fun v => cgState (A d) v 0 (d 1)) (decv_ofFn (n := d 0) x.val.1))
    exact ⟨hpos, xs', rs, ps,
      Mem.readBlocks_of_cons hxs' (Mem.readBlocks_of_cons hrs (Mem.readBlocks_of_cons hps rfl)),
      h⟩
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

/-! ### Unit weights: a closed-form count -/

/-- **The oracles of the model.** The matrix `A d` is in no buffer: it is a parameter of the
certificate, reached only through the products with the matrix and with the preconditioner
(which the tree never calls). Scalar arithmetic and the vector operations have one contract at
every size and input, and the contract of a product does not depend on the input of the
problem. The cost of the certificate is counted in calls of the product. -/
noncomputable def oracles (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    (inputs A domain admitted supply).Oracles
      (HSPCG.Model.exactModel (problem A domain admitted supply) (fun d => d 0)
        (fun d _ => A d) (fun _ _ => 1) (HSPCG.Model.resources cost aw ap sw sp)) where
  ops := [.operator, .preconditioner]
  operation o ho d x d' x' := by
    cases o with
    | scalar a => rfl
    | blas a => rfl
    | operator => exact absurd (by simp) ho
    | preconditioner => exact absurd (by simp) ho
  query _ _ _ _ q := nomatch q
  through o _ d X Y _ := by cases o <;> rfl

/-- The weights under which every scalar operation, vector operation and product counts one. -/
noncomputable abbrev unitResources : ResourceModel HSPCG.Signature Empty :=
  HSPCG.Model.resources .unit (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0)

/-- The exact model in which every scalar operation, vector operation and product counts one. -/
noncomputable abbrev unitModel :
    AccessModel HSPCG.Signature Empty (problem A domain admitted supply) :=
  HSPCG.Model.exactModel (problem A domain admitted supply) (fun d => d 0)
    (fun d _ => A d) (fun _ _ => 1) unitResources

/-- The number of instructions at order `d 0` and horizon `d 1`, at most. -/
def operationCount (d : Fin 2 → ℕ) : ℕ := 6 * d 0 + 127 * d 1 + 92

/-- The instruction polynomial of the program, evaluated by the kernel. -/
theorem countPoly_program : program.countPoly = [(6, [0]), (127, [1]), (92, [])] := by
  kernel_rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_program (d : Fin 2 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = operationCount d := by
  rw [countPoly_program]
  poly_eval [operationCount]

/-- Under unit costing every operation of the signature counts at most one. -/
theorem operationWork_unit_le (o : HSPCG.Signature) (d : List ℕ) :
    unitResources.operationWork o d ≤ 1 := by
  cases o <;> simp [HSPCG.Model.resources, Standard.Costing.blasWork]

/-- The specification under unit weights, with the explicit operation count as work and span. -/
noncomputable def countedSpecification :
    Specification HSPCG.Signature Empty (problem A domain admitted supply) :=
  { specification A domain admitted supply unitResources with
    work := operationCount
    span := operationCount }

/-- Conjugate gradient at order `n` and horizon `k` runs within `6 n + 127 k + 92` instructions
of the model with unit weights, with the output of `algorithm`. The program, the model and the
hypotheses are those of `algorithm`. -/
noncomputable def countedAlgorithm (hA : ∀ d, domain d → (A d).PosDef) :
    Algorithm (unitModel A domain admitted supply)
      (countedSpecification A domain admitted supply) :=
  (algorithm A domain admitted supply .unit (fun _ => 1) (fun _ => 1) (fun _ => 0)
    (fun _ => 0) hA).withCountPoly operationWork_unit_le (fun _ _ => le_rfl) (fun q => nomatch q)
    operationCount (fun d _ => (eval_countPoly_program d).le)

/-- What the certificate states, with no reference to routines or contracts. Let
$\mathbf{A}$ be positive definite of order $n$. For every right-hand side $b$ whose Krylov grade
is at least the horizon $k$, every interpretation of exact scalar arithmetic, exact level-one
vector operations and exact products with $\mathbf{A}$, and every tape, the counted run of the
fixed program from $b$ and three blank vectors succeeds, executes at most $6 n + 127 k + 92$
instructions (each vector operation and each product counting one), and leaves in the three
vectors the iterate, residual and direction of conjugate gradient after $k$ steps from the zero
iterate. Every such right-hand side is admitted (`NLAlib.Ops.Routine.Domain.covers`). -/
theorem cg_checked (hA : ∀ d, domain d → (A d).PosDef) (d : Fin 2 → ℕ) (hd : domain d)
    (rhs : Fin (d 0) → ℝ) (hrhs : d 1 ≤ krylovGrade (A d) rhs)
    (I : Interp HSPCG.Signature Empty ℝ)
    (hI : (unitModel A domain admitted supply).contracts d
      ((inputs A domain admitted supply).input d rhs hrhs) I) (τ : Tape ℝ) :
    ∃ st, exec program I (unitModel A domain admitted supply).resources
        (inputs A domain admitted supply).formats τ d
        ((inputs A domain admitted supply).memory d rhs) = some st ∧
      (unitModel A domain admitted supply).resources.work st.cost ≤
        6 * d 0 + 127 * d 1 + 92 ∧
      ∃ xs rs ps, st.mem.readBlocks [(1, 0), (2, 0), (3, 0)] [d 0, d 0, d 0] =
          some [xs, rs, ps] ∧
        decodedState id (d 0) xs rs ps = cgState (A d) rhs 0 (d 1) := by
  obtain ⟨st, hr, -, -, hw, -, -, xs, rs, ps, hys, hst⟩ :=
    (inputs A domain admitted supply).checked (countedAlgorithm A domain admitted supply hA)
      d hd rhs hrhs I hI τ
  exact ⟨st, hr, hw, xs, rs, ps, hys, hst⟩

end NLAlib.Krylov.CG.HSCG.Certification
