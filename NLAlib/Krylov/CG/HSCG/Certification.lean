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

The admitted inputs (`inputs`) are the positive-definite matrices and right-hand sides whose
Krylov grade is at least the horizon; the problem is derived from the routine
(`NLAlib.Ops.Routine.Domain`), so every such system is covered. The matrix is the declared
unstored input, reached only through the product operation. The program initializes its
iterate, applies the operator, and returns the actual CG state with full canonical resource
accounting.

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

variable (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)

/-- The admitted systems: the matrix is positive definite and the horizon is at most the Krylov
grade of the right-hand side. -/
def accepts (d : Fin 2 → ℕ) (x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)) : Prop :=
  x.1.PosDef ∧ d 1 ≤ krylovGrade x.1 x.2

variable (supply : ∀ d, domain d →
  ∃ x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ), accepts d x)

/-- The admitted inputs of conjugate gradient: at the sizes of `domain`, every positive-definite
matrix and right-hand side whose Krylov grade is at least the horizon. The right-hand side is
held by the first operand; the iterate, the residual and the direction are blank. The matrix is
the declared unstored input: it is in no buffer and is reached only through the product
operation (`NLAlib.Krylov.CG.HSCG.Certification.oracles`). -/
noncomputable def inputs :
    (zeroStartRoutine (Op := HSPCG.Signature) (Tst := Empty)).Domain ℝ 2 4 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ)
  accepts := accepts
  slot d := ![.stored (Codec.vector (d 0)) Prod.snd, .blank (d 0), .blank (d 0), .blank (d 0)]
  fits := by domain_fits
  Unstored d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ
  unstored _ x := x.1
  faithful d x y hu h := Prod.ext hu ((Codec.vector (d 0)).encode_injective (by
    have h0 := h 0
    simpa only [Slot.input, Matrix.cons_val_zero, Option.some.injEq] using h0))
  admitted := admitted
  inhabited := supply

/-- The right-hand side and three blank state vectors: the problem of conjugate gradient. -/
noncomputable abbrev problem : Problem ℝ 2 4 := (inputs domain admitted supply).problem

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
    (x : (problem domain admitted supply).Input d) :
    (problem domain admitted supply).initialBytes d x = 4 * d 0 := by
  refine ((inputs domain admitted supply).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.vector, List.ofFn_succ]
  omega

/-- The same counted run returns the full physical CG state at the prescribed horizon. -/
noncomputable def specification (R : ResourceModel HSPCG.Signature Empty) :
    Specification HSPCG.Signature Empty (problem domain admitted supply) where
  budget := staticBudget
  scratch := staticPeak R program
  work d := R.work (staticBudget d)
  span d := R.span (staticBudget d)
  memory d := 4 * d 0 + staticPeak R program d
  good d x _ _ m := m.pos = 0 ∧ StoresState id (d 0) (1, 0) (2, 0) (3, 0)
    (cgState x.val.1.1 x.val.1.2 0 (d 1)) m

/-- Conjugate gradient succeeds on every admitted system: a positive-definite matrix and a
right-hand side whose Krylov grade is at least the horizon. No success or numerical execution
witness is an assumption. The unused preconditioner primitive has no executed charge. -/
noncomputable def algorithm (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    Algorithm
      (HSPCG.Model.exactModel (problem domain admitted supply) (fun d => d 0)
        (fun _ X => X.val.1.1) (fun _ _ => 1) (HSPCG.Model.resources cost aw ap sw sp))
      (specification domain admitted supply (HSPCG.Model.resources cost aw ap sw sp)) := by
  refine (inputs domain admitted supply).algorithm (fun d x => zeroStartSpec id x.1)
    (ht := wellTyped_program ..) ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hBlas, hOp, -⟩ := HSPCG.Model.laws hI
    exact zeroStartRoutine_meets hS exactModel_exactMachine hBlas hOp x.property.1.1
  · intro d hd x hx τ
    refine ⟨rfl, ?_⟩
    exact le_of_le_of_eq hx.2 (congrArg (krylovGrade x.1) (decv_ofFn (n := d 0) x.2).symm)
  · intro d hd x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, ps)
    have h : decodedState id (d 0) xs' rs ps = cgState x.val.1.1 x.val.1.2 0 (d 1) :=
      Eq.trans hrel
        (congrArg (fun v => cgState x.val.1.1 v 0 (d 1)) (decv_ofFn (n := d 0) x.val.1.2))
    exact ⟨hpos, xs', rs, ps,
      Mem.readBlocks_of_cons hxs' (Mem.readBlocks_of_cons hrs (Mem.readBlocks_of_cons hps rfl)),
      h⟩
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

/-! ### Unit weights: a closed-form count -/

/-- The oracles of the model. The matrix is the unstored input: it is in no buffer and is
reached only through the products with the matrix and with the preconditioner (which the tree
never calls). Scalar arithmetic and the vector operations have one contract at every size and
input, and the contract of the product depends on the input only through the matrix. The cost
of the certificate is counted in calls of the product. -/
noncomputable def oracles (cost : Standard.Costing) (aw ap sw sp : List ℕ → ℕ) :
    (inputs domain admitted supply).Oracles
      (HSPCG.Model.exactModel (problem domain admitted supply) (fun d => d 0)
        (fun _ X => X.val.1.1) (fun _ _ => 1) (HSPCG.Model.resources cost aw ap sw sp)) where
  ops := [.operator, .preconditioner]
  operation o ho d x d' x' := by
    cases o with
    | scalar a => rfl
    | blas a => rfl
    | operator => exact absurd (by simp) ho
    | preconditioner => exact absurd (by simp) ho
  query _ _ _ _ q := nomatch q
  through o _ d X Y h := by
    cases o with
    | scalar a => rfl
    | blas a => rfl
    | operator =>
      change (matvecRel id X.val.1.1).spec _ = (matvecRel id Y.val.1.1).spec _
      rw [show X.val.1.1 = Y.val.1.1 from h]
    | preconditioner => rfl

/-- The weights under which every scalar operation, vector operation and product counts one. -/
noncomputable abbrev unitResources : ResourceModel HSPCG.Signature Empty :=
  HSPCG.Model.resources .unit (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0)

/-- The exact model in which every scalar operation, vector operation and product counts one. -/
noncomputable abbrev unitModel :
    AccessModel HSPCG.Signature Empty (problem domain admitted supply) :=
  HSPCG.Model.exactModel (problem domain admitted supply) (fun d => d 0)
    (fun _ X => X.val.1.1) (fun _ _ => 1) unitResources

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
    Specification HSPCG.Signature Empty (problem domain admitted supply) :=
  { specification domain admitted supply unitResources with
    work := operationCount
    span := operationCount }

/-- Conjugate gradient at order `n` and horizon `k` runs within `6 n + 127 k + 92` instructions
of the model with unit weights, with the output of `algorithm`. The program, the model and the
hypotheses are those of `algorithm`. -/
noncomputable def countedAlgorithm :
    Algorithm (unitModel domain admitted supply)
      (countedSpecification domain admitted supply) :=
  (algorithm domain admitted supply .unit (fun _ => 1) (fun _ => 1) (fun _ => 0)
    (fun _ => 0)).withCountPoly operationWork_unit_le (fun _ _ => le_rfl) (fun q => nomatch q)
    operationCount (fun d _ => (eval_countPoly_program d).le)

/-- What the certificate states, with no reference to routines or contracts. For every
positive-definite $\mathbf{A}$ of order $n$ and right-hand side $b$ whose Krylov grade
is at least the horizon $k$, every interpretation of exact scalar arithmetic, exact level-one
vector operations and exact products with $\mathbf{A}$, and every tape, the counted run of the
fixed program from $b$ and three blank vectors succeeds, executes at most $6 n + 127 k + 92$
instructions (each vector operation and each product counting one), keeps its resident memory
within the memory of the specification, and the three vectors then
hold the iterate, residual and direction of conjugate gradient after $k$ steps from the zero
iterate. Every such system is admitted (`NLAlib.Ops.Inputs.covers`). The matrix
is in no buffer: it is reached only through the product operation, and the work is counted in
calls of it (`NLAlib.Krylov.CG.HSCG.Certification.oracles`). -/
theorem cg_checked (d : Fin 2 → ℕ) (hd : domain d)
    (A : Matrix (Fin (d 0)) (Fin (d 0)) ℝ) (rhs : Fin (d 0) → ℝ) (hA : A.PosDef)
    (hrhs : d 1 ≤ krylovGrade A rhs) (I : Interp HSPCG.Signature Empty ℝ)
    (hI : (unitModel domain admitted supply).contracts d
      ((inputs domain admitted supply).input d (A, rhs) ⟨hA, hrhs⟩) I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution program I (unitModel domain admitted supply).resources
        (inputs domain admitted supply).formats τ d
        ((inputs domain admitted supply).memory d (A, rhs)) st ∧
      (unitModel domain admitted supply).resources.work st.cost ≤
        6 * d 0 + 127 * d 1 + 92 ∧
      (inputs domain admitted supply).bytes d + st.peak ≤
        (countedSpecification domain admitted supply).memory d ∧
      ∃ x r p : Fin (d 0) → ℝ, st.mem.Holds (Codec.vector (d 0)) 1 x ∧
        st.mem.Holds (Codec.vector (d 0)) 2 r ∧ st.mem.Holds (Codec.vector (d 0)) 3 p ∧
        cgState A rhs 0 (d 1) = ⟨x, r, p⟩ := by
  obtain ⟨st, hr, -, -, hw, -, hm, -, xs, rs, ps, hys, hst⟩ :=
    (inputs domain admitted supply).checked (countedAlgorithm domain admitted supply)
      d hd (A, rhs) ⟨hA, hrhs⟩ I hI τ
  obtain ⟨_, _, _, _, _, _, he, hx, hr', hp, hl⟩ := Mem.readBlocks_three hys
  obtain ⟨rfl, rfl, rfl⟩ : _ = _ ∧ _ = _ ∧ _ = _ := by simpa using he
  obtain ⟨rfl, rfl, rfl⟩ : _ = _ ∧ _ = _ ∧ _ = _ := by simpa using hl
  exact ⟨st, hr, hw, hm, _, _, _, Mem.holds_decode _ hx, Mem.holds_decode _ hr',
    Mem.holds_decode _ hp, hst.symm⟩

end NLAlib.Krylov.CG.HSCG.Certification
