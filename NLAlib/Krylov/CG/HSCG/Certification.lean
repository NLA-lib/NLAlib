/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Model
public import NLAlib.Krylov.CG.HorizonProblem
public import NLAlib.Krylov.CG.HSCG.ZeroStart
public import NLAlib.Ops.OperationCount

/-!
# Canonical exact fixed-horizon conjugate gradient

Raw RHS admissibility states the existing mathematical grade restriction and has an explicit
inhabitant at each admitted size. The program initializes its iterate, applies the operator, and
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

/-- Admissible raw words satisfy only the fixed-horizon mathematical grade restriction. -/
def accepts (d : Fin 2 → ℕ) (rhs : List ℝ) : Prop :=
  d 1 ≤ krylovGrade (A d) (decv id (d 0) rhs)

variable (supply : ∀ d, domain d → ∃ rhs : List ℝ, rhs.length = d 0 ∧ accepts A d rhs)

/-- RHS plus three uninitialized state vectors, with an explicitly inhabited input domain. -/
noncomputable def problem : Problem ℝ 2 4 :=
  CG.RawProblem.restricted (fun d => ![0, d 0, d 0, d 0]) domain admitted
    (accepts A) supply

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
  change (CG.RawProblem.problem (fun d => ![0, d 0, d 0, d 0]) domain admitted).initialBytes
    d (CG.RawProblem.forgetInput x) = _
  rw [CG.RawProblem.initialBytes_eq]
  simp [List.ofFn_succ]
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
    (cgState (A d) (decv id (d 0) x.val.1) 0 (d 1)) m

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
  refine Routine.algorithm (r := 2) (b := 4) zeroStartRoutine (fun d _ => zeroStartSpec id (A d))
    (fun _ x => [x.val.1]) (ht := wellTyped_program ..) ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    obtain ⟨hS, hBlas, hOp, -⟩ := HSPCG.Model.laws hI
    exact zeroStartRoutine_meets hS exactModel_exactMachine hBlas hOp (hA d hd)
  · intro d hd x
    let μ := (problem A domain admitted supply).initial d x
    let raw := CG.RawProblem.forgetInput x
    have hμ :
        (CG.RawProblem.problem (fun d => ![0, d 0, d 0, d 0]) domain admitted).initial d raw = μ :=
      rfl
    have hlen (i : Fin 4) : μ.store.len i = if i = 0 then d 0 else ![0, d 0, d 0, d 0] i := by
      rw [← hμ]
      exact CG.RawProblem.initial_len d raw i
    refine ⟨Mem.readBlocks_of_cons (CG.RawProblem.initial_readBlock d raw) rfl,
      fun _ => ⟨rfl, x.property.2⟩, ?_⟩
    change μ.Room [(1, 0), (2, 0), (3, 0)] [d 0, d 0, d 0]
    simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add]
    exact ⟨by simpa [μ, raw] using (hlen 1).ge, by simpa [μ, raw] using (hlen 2).ge,
      by simpa [μ, raw] using (hlen 3).ge⟩
  · intro d hd x τ m' _ hpos ys hys hrel c _
    read_outputs hys as (xs', rs, ps)
    exact ⟨hpos, xs', rs, ps,
      Mem.readBlocks_of_cons hxs' (Mem.readBlocks_of_cons hrs (Mem.readBlocks_of_cons hps rfl)),
      hrel⟩
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

/-! ### Unit weights: a closed-form count -/

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
$\mathbf{A}$ be positive definite of order $n$. For every right-hand side $b$ supplied in the
first buffer whose Krylov grade is at least the horizon $k$, every interpretation of exact
scalar arithmetic, exact level-one vector operations and exact products with $\mathbf{A}$, and
every tape, the counted run of the fixed program succeeds, executes at most
$6 n + 127 k + 92$ instructions (each vector operation and each product counting one), and
leaves in the next three buffers the iterate, residual and direction of conjugate gradient after
$k$ steps from the zero iterate. -/
theorem cg_checked (hA : ∀ d, domain d → (A d).PosDef) (d : Fin 2 → ℕ) (hd : domain d)
    (x : (problem A domain admitted supply).Input d) (I : Interp HSPCG.Signature Empty ℝ)
    (hI : (unitModel A domain admitted supply).contracts d x I) (τ : Tape ℝ) :
    ∃ st, exec program I (unitModel A domain admitted supply).resources
        (problem A domain admitted supply).formats τ d
        ((problem A domain admitted supply).initial d x) = some st ∧
      (unitModel A domain admitted supply).resources.work st.cost ≤
        6 * d 0 + 127 * d 1 + 92 ∧
      ∃ xs rs ps, st.mem.readBlocks [(1, 0), (2, 0), (3, 0)] [d 0, d 0, d 0] =
          some [xs, rs, ps] ∧
        decodedState id (d 0) xs rs ps = cgState (A d) (decv id (d 0) x.val.1) 0 (d 1) := by
  obtain ⟨st, hr, -, -, hw, -, -, -, xs, rs, ps, hys, hst⟩ :=
    (countedAlgorithm A domain admitted supply hA).correct d hd x I hI τ
  exact ⟨st, hr, hw, xs, rs, ps, hys, hst⟩

end NLAlib.Krylov.CG.HSCG.Certification
