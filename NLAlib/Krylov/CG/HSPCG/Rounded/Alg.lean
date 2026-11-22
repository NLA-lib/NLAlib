/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Rounded.Initialization
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.RoutineSyntax

/-!
# Capped zero-start rounded PCG programs

The existing four-vector PCG step is reused unchanged. A fifth, scoped scalar stores the
computed residual pairing for the positivity test. Each active round refreshes that scalar;
functional dot semantics identify it with the pairings inside the existing step. The cap
bounds the number of active rounds and does not assert convergence.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.guardedStep` refreshes the residual-pairing cache.
* `NLAlib.Krylov.CG.HSPCG.Rounded.rounds` stops on the computed residual pairing.
* `NLAlib.Krylov.CG.HSPCG.Rounded.solve` initializes and runs capped zero-start PCG;
  `NLAlib.Krylov.CG.HSPCG.Rounded.solveRoutine` is its routine.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- Execute the existing four-vector step, then refresh the actual residual pairing in the
fifth state block. This cache is used only for the next round's stopping test. -/
def guardedStep : Stmt Op Tst := ops% [n] (X, R, Z, P, V) → (X, R, Z, P, V) {
  run (HSPCG.stepRoutine (Op := Op) (Tst := Tst)) [n] (X, R, Z, P);
  call (Has.inj Blas1Op.dot) [n] (R, Z) → (V)
}

/-- The stopping cache adds one dot product to the existing PCG round. -/
noncomputable def guardedStepCount (n : ℕ) : Count Op Tst :=
  HSPCG.stepCount n + Count.one (Has.inj Blas1Op.dot) [n]

/-- The cache is caller storage at the step interface; the final dot reuses the round's
workspace after its scoped scratch has been released. -/
def guardedStepPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max (HSPCG.stepPeak W n) (W (Has.inj Blas1Op.dot) [n])

/-- Static accounting includes the cache refresh. -/
theorem staticCost_guardedStep (n a b c d v a' b' c' d' v' : ℕ) :
    stmtCost (guardedStep (Op := Op) (Tst := Tst))
      [n, a, b, c, d, v, a', b', c', d', v'] = guardedStepCount n := by
  simp [guardedStep, HSPCG.stepRoutine, stmtCost, IExp.evalList, IExp.eval,
    HSPCG.staticCost_step, useCost, guardedStepCount]

/-- Scratch for the wrapped step is independent of the number of rounds. -/
theorem staticPeak_guardedStep_le (W : Op → List ℕ → ℕ)
    (n a b c d v a' b' c' d' v' : ℕ) :
    stmtPeak W (guardedStep (Op := Op) (Tst := Tst))
      [n, a, b, c, d, v, a', b', c', d', v'] ≤ guardedStepPeak W n := by
  simpa [guardedStep, HSPCG.stepRoutine, stmtPeak, IExp.evalList, IExp.eval, guardedStepPeak]
    using max_le_max (HSPCG.staticPeak_step_le W n a b c d a b c d) le_rfl

variable [Has CmpTst Tst]

/-- Perform at most the cap rounds, stopping when the computed residual pairing is no longer
positive. Numerical spectral hypotheses identify this case with a zero residual. -/
def rounds : Stmt Op Tst := ops% [n, cap] (X, R, Z, P, V) → (X, R, Z, P, V) {
  while i < cap, (Has.inj CmpTst.isPos) [] (V) {
    run (guardedStep (Op := Op) (Tst := Tst)) [n] (X, R, Z, P, V, X, R, Z, P, V)
  } then { skip }
}

/-- The cap budgets one positivity query and one wrapped PCG step per permitted round. -/
noncomputable def roundsCount (n cap : ℕ) : Count Op Tst :=
  cap • (Count.test (Has.inj CmpTst.isPos) [] + guardedStepCount n)

/-- The loop's static count includes comparison queries. -/
theorem staticCost_rounds (n cap a b c d v a' b' c' d' v' : ℕ) :
    stmtCost (rounds (Op := Op) (Tst := Tst))
      [n, cap, a, b, c, d, v, a', b', c', d', v'] = roundsCount n cap := by
  simp [rounds, stmtCost, testCost, IExp.evalList, IExp.eval,
    staticCost_guardedStep, roundsCount]

/-- Every iteration reuses the same scratch blocks. -/
theorem staticPeak_rounds_le (W : Op → List ℕ → ℕ)
    (n cap a b c d v a' b' c' d' v' : ℕ) :
    stmtPeak W (rounds (Op := Op) (Tst := Tst))
      [n, cap, a, b, c, d, v, a', b', c', d', v'] ≤ guardedStepPeak W n := by
  simp only [rounds, stmtPeak]
  apply max_le
  · apply Finset.sup_le
    intro i hi
    simpa [IExp.evalList, IExp.eval] using
      staticPeak_guardedStep_le W n a b c d v a b c d v
  · simp

/-- Copy the raw right-hand side into the residual and initialize the preconditioned vectors,
then allocate the scalar stopping cache and execute the capped loop. The supplied iterate is
zero; `zeroStart` establishes that fact from uninitialized capacity. -/
def solve : Stmt Op Tst := ops% [n, cap] (B, X) → (X, R, Z, P) {
  run (initializeRoutine (Op := Op) (Tst := Tst)) [n] (B, X, R, Z, P);
  let C ← alloc 1;
  call (Has.inj Blas1Op.dot) [n] (R, Z) → (C[0]);
  run (rounds (Op := Op) (Tst := Tst)) [n, cap] (X, R, Z, P, C, X, R, Z, P, C)
}

/-- The capped rounded solver from a zero iterate: the right-hand side is read, the iterate is
updated in place, and the residual, the preconditioned residual and the direction are written. -/
def solveRoutine : Routine Op Tst :=
  routine% [n, cap] (b : n, x : n) → (x, r : n, z : n, p : n) := solve

/-- Initialize the iterate through literal-zero writes, then run the solver on it. The fixed
program receives the raw right-hand side and four uninitialized output blocks. -/
def zeroStart : Stmt Op Tst := ops% [n, cap] (B) → (X, R, Z, P) {
  run (fillRoutine (Op := Op) (Tst := Tst) (Has.inj (ScalarOp.lit 0))) [n] (X);
  run (solveRoutine (Op := Op) (Tst := Tst)) [n, cap] (B, X, R, Z, P)
}

/-- The solver budget contains initialization, the initial pairing, and the capped rounds. -/
noncomputable def solveCount (n cap : ℕ) : Count Op Tst :=
  initializeCount n + Count.one (Has.inj Blas1Op.dot) [n] + roundsCount n cap

/-- Literal-zero writes are counted in addition to the complete solver. -/
noncomputable def zeroStartCount (n cap : ℕ) : Count Op Tst :=
  n • Count.one (Has.inj (ScalarOp.lit 0)) [] + solveCount n cap

/-- Solver scratch includes its scoped cache, in addition to reused round workspace. -/
def solvePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max (initializePeak W n)
    (1 + max (W (Has.inj Blas1Op.dot) [n]) (guardedStepPeak W n))

/-- Static evaluation counts initialization, the pairing cache and capped rounds. -/
theorem staticCost_solve (n cap a b c d e f : ℕ) :
    stmtCost (solve (Op := Op) (Tst := Tst)) [n, cap, a, b, c, d, e, f] =
      solveCount n cap := by
  simp [solve, initializeRoutine, stmtCost, IExp.evalList, IExp.eval, useCost,
    staticCost_initialize, staticCost_rounds, solveCount, add_assoc]

/-- The public zero-start budget counts every literal-zero write. -/
theorem staticCost_zeroStart (n cap a b c d e : ℕ) :
    stmtCost (zeroStart (Op := Op) (Tst := Tst)) [n, cap, a, b, c, d, e] =
      zeroStartCount n cap := by
  simp [zeroStart, solveRoutine, stmtCost, IExp.evalList, IExp.eval, fillRoutine,
    stmtCost_fillMap, staticCost_solve, zeroStartCount]

end NLAlib.Krylov.CG.HSPCG.Rounded
