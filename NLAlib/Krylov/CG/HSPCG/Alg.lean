/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Catalog.Tagged
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Count

/-!
# Preconditioned Hestenes–Stiefel programs

The system and the applied inverse preconditioner are two separately counted linear operators.
Four state blocks store the iterate, residual, preconditioned residual and search direction.
Initialization and each round free their own scratch before returning.

## Main results

* `NLAlib.Krylov.CG.HSPCG.step`, `NLAlib.Krylov.CG.HSPCG.initializeState`, and
  `NLAlib.Krylov.CG.HSPCG.solve` are uniform first-order trees.
* `NLAlib.Krylov.CG.HSPCG.staticCost_step` and `NLAlib.Krylov.CG.HSPCG.staticCost_solve`
  expose the evaluator's operation counts.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops

/-- The tag distinguishing the applied inverse preconditioner from the system operator. -/
inductive Preconditioner

/-- The scalar, vector, system-operator and preconditioner operations of PCG. -/
inductive Signature where
  /-- Scalar arithmetic. -/
  | scalar (op : ScalarOp)
  /-- Level-one vector operations. -/
  | blas (op : Blas1Op)
  /-- The system matrix. -/
  | operator
  /-- The applied inverse preconditioner. -/
  | preconditioner
  deriving DecidableEq

instance : Has ScalarOp Signature where
  inj := .scalar
  proj
    | .scalar o => some o
    | _ => none
  proj_inj _ := rfl
  inj_of_proj o g h := by
    cases o <;> cases h
    all_goals rfl

instance : Has Blas1Op Signature where
  inj := .blas
  proj
    | .blas o => some o
    | _ => none
  proj_inj _ := rfl
  inj_of_proj o g h := by
    cases o <;> cases h
    all_goals rfl

instance : Has OperatorOp Signature where
  inj _ := .operator
  proj
    | .operator => some .matvec
    | _ => none
  proj_inj o := by cases o; rfl
  inj_of_proj o g h := by
    cases o <;> cases h
    all_goals rfl

instance : Has (Tagged Preconditioner OperatorOp) Signature where
  inj _ := .preconditioner
  proj
    | .preconditioner => some ⟨.matvec⟩
    | _ => none
  proj_inj o := by rcases o with ⟨o⟩; cases o; rfl
  inj_of_proj o g h := by
    cases o <;> cases h
    all_goals rfl

instance : Apart Blas1Op ScalarOp Signature := ⟨fun _ => rfl⟩
instance : Apart Blas1Op OperatorOp Signature := ⟨fun _ => rfl⟩
instance : Apart Blas1Op (Tagged Preconditioner OperatorOp) Signature := ⟨fun _ => rfl⟩
instance : Apart ScalarOp OperatorOp Signature := ⟨fun _ => rfl⟩
instance : Apart ScalarOp (Tagged Preconditioner OperatorOp) Signature := ⟨fun _ => rfl⟩
instance : Apart OperatorOp (Tagged Preconditioner OperatorOp) Signature := ⟨fun _ => rfl⟩

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- The applied inverse preconditioner satisfies the existing exact rectangular-operator
contract at its own operation name. -/
def IsExactPreconditioner [Inhabited K] (dec : K → ℝ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (I : Interp Op Tst K) : Prop :=
  I.Meets .total (Tagged.inj Preconditioner OperatorOp.matvec)
    ((matvecRel dec M).spec (MatvecOperands n n))

/-- One exact-PCG round computes the Hestenes–Stiefel recurrence with one application of the
system and one of the inverse preconditioner. [Saad2003, Algorithm 9.1]. -/
def step : Stmt Op Tst := ops% [n] (X, R, Z, P) → (X, R, Z, P) {
  let Q ← alloc n;
  let U ← alloc n;
  let t ← alloc 4;
  call (Has.inj Blas1Op.dot) [n] (R, Z) → (t[0]);
  call (Has.inj OperatorOp.matvec) [n, n] (P) → (Q);
  call (Has.inj Blas1Op.dot) [n] (P, Q) → (t[1]);
  call (Has.inj ScalarOp.div) [] (t[0], t[1]) → (t[2]);
  call (Has.inj Blas1Op.axpy) [n] (t[2], P, X) → (X);
  call (Has.inj ScalarOp.neg) [] (t[2]) → (t[2]);
  call (Has.inj Blas1Op.axpy) [n] (t[2], Q, R) → (R);
  call (Tagged.inj Preconditioner OperatorOp.matvec) [n, n] (R) → (Z);
  call (Has.inj Blas1Op.dot) [n] (R, Z) → (t[3]);
  call (Has.inj ScalarOp.div) [] (t[3], t[0]) → (t[3]);
  call (Has.inj Blas1Op.copy) [n] (Z) → (U);
  call (Has.inj Blas1Op.axpy) [n] (t[3], P, U) → (U);
  call (Has.inj Blas1Op.copy) [n] (U) → (P)
}

/-- A PCG round has one size parameter and four state input and output blocks. -/
def stepImpl : Impl Op Tst := ⟨1, 4, 4, step⟩

/-- Initialization forms the residual, applies the preconditioner, and copies the first
search direction while retaining the initial iterate. -/
def initializeState : Stmt Op Tst := ops% [n] (B, X) → (X, R, Z, P) {
  let Q ← alloc n;
  let t ← alloc 1;
  call (Has.inj Blas1Op.copy) [n] (B) → (R);
  call (Has.inj OperatorOp.matvec) [n, n] (X) → (Q);
  call (Has.inj (ScalarOp.lit (-1))) [] () → (t);
  call (Has.inj Blas1Op.axpy) [n] (t, Q, R) → (R);
  call (Tagged.inj Preconditioner OperatorOp.matvec) [n, n] (R) → (Z);
  call (Has.inj Blas1Op.copy) [n] (Z) → (P)
}

/-- Initialization reads the right-hand side and initial iterate and outputs all four states. -/
def initializeImpl : Impl Op Tst := ⟨1, 2, 4, initializeState⟩

/-- Each round is a framed call of the same state interface and reuses its scratch. -/
def rounds : Stmt Op Tst :=
  .loop (.var 1) (.frame [.var 0]
    [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩,
      ⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩] step)

/-- The loop has two size parameters and four input and output blocks. -/
def roundsImpl : Impl Op Tst := ⟨2, 4, 4, rounds⟩

/-- Initialize the PCG state and execute a prescribed number of active rounds. -/
def solve : Stmt Op Tst :=
  .seq (.frame [.var 0]
    [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩,
      ⟨4, .var 6⟩, ⟨5, .var 7⟩] initializeState)
    (.frame [.var 0, .var 1]
      [⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩, ⟨5, .var 7⟩,
        ⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩, ⟨5, .var 7⟩] rounds)

/-- The full solver reads two blocks and outputs four blocks. -/
def solveImpl : Impl Op Tst := ⟨2, 2, 4, solve⟩

/-- The two distinct operator charges and scalar/vector operations of one PCG round. -/
noncomputable def stepCount (n : ℕ) : Count Op Tst :=
  3 • Count.one (Has.inj Blas1Op.dot) [n] + Count.one (Has.inj OperatorOp.matvec) [n, n] +
    Count.one (Tagged.inj Preconditioner OperatorOp.matvec) [n, n] +
    2 • Count.one (Has.inj ScalarOp.div) [] + 3 • Count.one (Has.inj Blas1Op.axpy) [n] +
    Count.one (Has.inj ScalarOp.neg) [] + 2 • Count.one (Has.inj Blas1Op.copy) [n]

/-- Initialization adds one application of each operator, one axpy, two copies and minus one. -/
noncomputable def initializeCount (n : ℕ) : Count Op Tst :=
  2 • Count.one (Has.inj Blas1Op.copy) [n] + Count.one (Has.inj OperatorOp.matvec) [n, n] +
    Count.one (Tagged.inj Preconditioner OperatorOp.matvec) [n, n] +
    Count.one (Has.inj (ScalarOp.lit (-1))) [] + Count.one (Has.inj Blas1Op.axpy) [n]

/-- The complete fixed-horizon budget, computed by sequential composition. -/
noncomputable def solveCount (n k : ℕ) : Count Op Tst := initializeCount n + k • stepCount n

/-- A round holds two scratch vectors, four scalar cells and a called operation's workspace. -/
def stepPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * n + 4 + max (W (Has.inj OperatorOp.matvec) [n, n])
    (max (W (Tagged.inj Preconditioner OperatorOp.matvec) [n, n])
      (max (W (Has.inj Blas1Op.dot) [n]) (max (W (Has.inj ScalarOp.div) [])
        (max (W (Has.inj Blas1Op.axpy) [n])
          (max (W (Has.inj ScalarOp.neg) []) (W (Has.inj Blas1Op.copy) [n]))))))

/-- Initialization needs one scratch vector, one cell and the largest operation workspace. -/
def initializePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  n + 1 + max (W (Has.inj Blas1Op.copy) [n])
    (max (W (Has.inj OperatorOp.matvec) [n, n])
      (max (W (Tagged.inj Preconditioner OperatorOp.matvec) [n, n])
        (max (W (Has.inj (ScalarOp.lit (-1))) []) (W (Has.inj Blas1Op.axpy) [n]))))

/-- The initializer and every round reuse scratch, so the total workspace is a maximum. -/
def solvePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max (initializePeak W n) (stepPeak W n)

/-- Static evaluation counts all thirteen operations of one PCG round. -/
theorem staticCost_step (n a b c d a' b' c' d' : ℕ) :
    staticCost (step (Op := Op) (Tst := Tst)) [n, a, b, c, d, a', b', c', d'] =
      stepCount n := by
  simp [step, stepCount, staticCost, useCost, IExp.evalList, IExp.eval]
  abel

/-- The round's static workspace is bounded by its scratch plus the largest call workspace. -/
theorem staticPeak_step_le (W : Op → List ℕ → ℕ) (n a b c d a' b' c' d' : ℕ) :
    staticPeak W (step (Op := Op) (Tst := Tst)) [n, a, b, c, d, a', b', c', d'] ≤
      stepPeak W n := by
  simp [step, staticPeak, stepPeak]
  omega

/-- Static evaluation counts the initializer operations. -/
theorem staticCost_initialize (n b x x' r z p : ℕ) :
    staticCost (initializeState (Op := Op) (Tst := Tst)) [n, b, x, x', r, z, p] =
      initializeCount n := by
  simp [initializeState, initializeCount, staticCost, useCost, IExp.evalList, IExp.eval]
  abel

/-- Initialization has its declared static workspace. -/
theorem staticPeak_initialize_le (W : Op → List ℕ → ℕ) (n b x x' r z p : ℕ) :
    staticPeak W (initializeState (Op := Op) (Tst := Tst)) [n, b, x, x', r, z, p] ≤
      initializePeak W n := by
  simp [initializeState, staticPeak, initializePeak]
  omega

/-- The loop's evaluator count is exactly the number of rounds times the round count. -/
theorem staticCost_rounds (n k a b c d a' b' c' d' : ℕ) :
    staticCost (rounds (Op := Op) (Tst := Tst)) [n, k, a, b, c, d, a', b', c', d'] =
      k • stepCount n := by
  simp [rounds, staticCost, IExp.eval, IExp.evalList, staticCost_step]

/-- All rounds share the same scratch bound. -/
theorem staticPeak_rounds_le (W : Op → List ℕ → ℕ) (n k a b c d a' b' c' d' : ℕ) :
    staticPeak W (rounds (Op := Op) (Tst := Tst)) [n, k, a, b, c, d, a', b', c', d'] ≤
      stepPeak W n := by
  simp only [rounds, staticPeak]
  exact Finset.sup_le fun i _ => by
    simpa [IExp.eval, IExp.evalList, Operand.off] using staticPeak_step_le W n a b c d a b c d

/-- The complete evaluator budget composes initialization with the round loop. -/
theorem staticCost_solve (n k b x x' r z p : ℕ) :
    staticCost (solve (Op := Op) (Tst := Tst)) [n, k, b, x, x', r, z, p] = solveCount n k := by
  simp [solve, staticCost, IExp.eval, IExp.evalList, staticCost_initialize,
    staticCost_rounds, solveCount]

/-- The complete evaluator workspace is bounded by the larger block workspace. -/
theorem staticPeak_solve_le (W : Op → List ℕ → ℕ) (n k b x x' r z p : ℕ) :
    staticPeak W (solve (Op := Op) (Tst := Tst)) [n, k, b, x, x', r, z, p] ≤ solvePeak W n := by
  simp only [solve, staticPeak, solvePeak]
  exact max_le_max
    (by simpa [IExp.eval, IExp.evalList] using staticPeak_initialize_le W n b x x' r z p)
    (by simpa [IExp.eval, IExp.evalList] using staticPeak_rounds_le W n k x' r z p x' r z p)

end NLAlib.Krylov.CG.HSPCG
