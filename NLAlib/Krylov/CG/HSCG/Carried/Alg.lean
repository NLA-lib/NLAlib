/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Alg
public import NLAlib.Ops.Catalog.Compare

/-!
# Hestenes–Stiefel rounds with a retained residual product

The fourth state block stores the computed residual self-product. A round uses this retained
value in both divisions and replaces it by the new residual self-product. Thus it performs two
dot products per round, including under rounded arithmetic where recomputing a self-product
need not reproduce an earlier computed value. [HestenesStiefel1952, (3:1)].

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.step` is the uniform round program.
* `NLAlib.Krylov.CG.HSCG.Carried.staticCost_step` gives its operation budget.
* `NLAlib.Krylov.CG.HSCG.Carried.staticPeak_step_le` bounds its scratch space.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- A standard CG round on `(X,R,P,rho)`, retaining the new residual self-product. Scratch
consists of one vector and three scalar cells. The product buffer becomes the new direction
after the residual update. -/
def step : Stmt Op Tst := ops% [n] (X, R, P, rho) → (X, R, P, rho) {
  let Q ← alloc n;
  let t ← alloc 3;
  call (Has.inj OperatorOp.matvec) [n, n] (P) → (Q);
  call (Has.inj Blas1Op.dot) [n] (P, Q) → (t[0]);
  call (Has.inj ScalarOp.div) [] (rho, t[0]) → (t[1]);
  call (Has.inj Blas1Op.axpy) [n] (t[1], P, X) → (X);
  call (Has.inj ScalarOp.neg) [] (t[1]) → (t[1]);
  call (Has.inj Blas1Op.axpy) [n] (t[1], Q, R) → (R);
  call (Has.inj Blas1Op.dot) [n] (R, R) → (t[2]);
  call (Has.inj ScalarOp.div) [] (t[2], rho) → (t[0]);
  call (Has.inj Blas1Op.copy) [n] (R) → (Q);
  call (Has.inj Blas1Op.axpy) [n] (t[0], P, Q) → (Q);
  call (Has.inj Blas1Op.copy) [n] (Q) → (P);
  call (Has.inj ScalarOp.copy) [] (t[2]) → (rho)
}

/-- The block interface has one dimension and four state inputs and outputs. -/
def stepImpl : Impl Op Tst := ⟨1, 4, 4, step⟩

/-- Two dot products, two divisions, three axpys and all copies of one standard CG round. -/
noncomputable def stepCount (n : ℕ) : Count Op Tst :=
  2 • Count.one (Has.inj Blas1Op.dot) [n] + Count.one (Has.inj OperatorOp.matvec) [n, n] +
    2 • Count.one (Has.inj ScalarOp.div) [] + 3 • Count.one (Has.inj Blas1Op.axpy) [n] +
    Count.one (Has.inj ScalarOp.neg) [] + 2 • Count.one (Has.inj Blas1Op.copy) [n] +
    Count.one (Has.inj ScalarOp.copy) []

/-- Scratch excludes the four persistent caller state blocks. -/
def stepPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  n + 3 + max (W (Has.inj OperatorOp.matvec) [n, n])
    (max (W (Has.inj Blas1Op.dot) [n]) (max (W (Has.inj ScalarOp.div) [])
      (max (W (Has.inj Blas1Op.axpy) [n]) (max (W (Has.inj ScalarOp.neg) [])
        (max (W (Has.inj Blas1Op.copy) [n]) (W (Has.inj ScalarOp.copy) []))))))

/-- Static evaluation counts the two dot products and the retained scalar copy. -/
theorem staticCost_step (n a b c d a' b' c' d' : ℕ) :
    staticCost (step (Op := Op) (Tst := Tst)) [n, a, b, c, d, a', b', c', d'] =
      stepCount n := by
  simp [step, staticCost, stepCount, useCost, IExp.evalList, IExp.eval]
  module

/-- One vector, three cells and the largest call workspace bound the round's scratch. -/
theorem staticPeak_step_le (W : Op → List ℕ → ℕ) (n a b c d a' b' c' d' : ℕ) :
    staticPeak W (step (Op := Op) (Tst := Tst)) [n, a, b, c, d, a', b', c', d'] ≤
      stepPeak W n := by
  simp [step, staticPeak, stepPeak]
  omega


section Comparisons

variable [Has CmpTst Tst]

/-- Run at most the requested number of rounds, exiting as soon as the retained residual
product is no longer positive. Exact arithmetic stops precisely at a zero residual. -/
def rounds : Stmt Op Tst :=
  .whileFuel (.var 1) (Has.inj CmpTst.isPos) [] [⟨3, .var 5⟩]
    (.frame [.var 0]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩,
        ⟨4, .var 6⟩, ⟨5, .var 7⟩, ⟨6, .var 8⟩, ⟨7, .var 9⟩] step) .skip

/-- The early-exit loop has dimensions `n,cap` and four input/output state blocks. -/
def roundsImpl : Impl Op Tst := ⟨2, 4, 4, rounds⟩

/-- A cap budgets one positivity test and one active round per permitted iteration. -/
noncomputable def roundsCount (n cap : ℕ) : Count Op Tst :=
  cap • (Count.test (Has.inj CmpTst.isPos) [] + stepCount n)

/-- Static loop accounting includes comparison queries as well as operation calls. -/
theorem staticCost_rounds (n cap a b c d a' b' c' d' : ℕ) :
    staticCost (rounds (Op := Op) (Tst := Tst)) [n, cap, a, b, c, d, a', b', c', d'] =
      roundsCount n cap := by
  simp [rounds, staticCost, testCost, IExp.evalList, IExp.eval, staticCost_step, roundsCount]

/-- Early exit and the cap share the same reusable round workspace. -/
theorem staticPeak_rounds_le (W : Op → List ℕ → ℕ) (n cap a b c d a' b' c' d' : ℕ) :
    staticPeak W (rounds (Op := Op) (Tst := Tst))
      [n, cap, a, b, c, d, a', b', c', d'] ≤ stepPeak W n := by
  simp only [rounds, staticPeak]
  apply max_le
  · apply Finset.sup_le
    intro i hi
    simpa [IExp.evalList, IExp.eval] using staticPeak_step_le W n a b c d a' b' c' d'
  · simp


end Comparisons

/-- Initialize the ordinary CG state, then compute its retained residual self-product. -/
def initializeState : Stmt Op Tst :=
  .seq (.frame [.var 0]
    [⟨0, .var 1⟩, ⟨1, .var 2⟩, ⟨2, .var 3⟩, ⟨3, .var 4⟩, ⟨4, .var 5⟩]
    HSCG.initializeState)
    (.seq (.call (Has.inj Blas1Op.dot) [.var 0]
      [⟨3, .var 4⟩, ⟨3, .var 4⟩] [⟨5, .var 6⟩]) .skip)

/-- Initialization takes the right-hand side and iterate, and produces four state blocks. -/
def initializeImpl : Impl Op Tst := ⟨1, 2, 4, initializeState⟩

/-- Initialization includes one self-product beyond the three-vector initialization. -/
noncomputable def initializeCount (n : ℕ) : Count Op Tst :=
  HSCG.initializeCount n + Count.one (Has.inj Blas1Op.dot) [n]

/-- Initializer and self-product scratch are used sequentially. -/
def initializePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max (HSCG.initializePeak W n) (W (Has.inj Blas1Op.dot) [n])

/-- Static accounting includes the retained initial residual product. -/
theorem staticCost_initialize (n a b c d e f : ℕ) :
    staticCost (initializeState (Op := Op) (Tst := Tst)) [n, a, b, c, d, e, f] =
      initializeCount n := by
  simp [initializeState, staticCost, IExp.evalList, IExp.eval,
    HSCG.staticCost_initialize, useCost, initializeCount]

/-- The retained scalar is caller storage, so initialization adds no allocation for it. -/
theorem staticPeak_initialize_le (W : Op → List ℕ → ℕ) (n a b c d e f : ℕ) :
    staticPeak W (initializeState (Op := Op) (Tst := Tst)) [n, a, b, c, d, e, f] ≤
      initializePeak W n := by
  simpa [initializeState, staticPeak, IExp.evalList, IExp.eval, initializePeak] using
    max_le_max (HSCG.staticPeak_initialize_le W n a b c d e) le_rfl

variable [Has CmpTst Tst]

/-- Complete CG initialization followed by an early-exit loop with an arbitrary cap. -/
def solve : Stmt Op Tst :=
  .seq (.frame [.var 0]
    [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩,
      ⟨4, .var 6⟩, ⟨5, .var 7⟩] initializeState)
    (.frame [.var 0, .var 1]
      [⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩, ⟨5, .var 7⟩,
        ⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩, ⟨5, .var 7⟩] rounds)

/-- The solver has dimensions `n,cap`, two inputs and four state outputs. -/
def solveImpl : Impl Op Tst := ⟨2, 2, 4, solve⟩

/-- The static budget includes initialization and at most `cap` tested rounds. -/
noncomputable def solveCount (n cap : ℕ) : Count Op Tst :=
  initializeCount n + roundsCount n cap

/-- Initialization and the early-exit loop reuse their scratch. -/
def solvePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max (initializePeak W n) (stepPeak W n)

/-- The complete program budget follows by evaluating its two framed components. -/
theorem staticCost_solve (n cap a b c d e f : ℕ) :
    staticCost (solve (Op := Op) (Tst := Tst)) [n, cap, a, b, c, d, e, f] =
      solveCount n cap := by
  simp [solve, staticCost, IExp.evalList, IExp.eval, staticCost_initialize,
    staticCost_rounds, solveCount]

/-- The complete solver's peak is bounded independently of its cap. -/
theorem staticPeak_solve_le (W : Op → List ℕ → ℕ) (n cap a b c d e f : ℕ) :
    staticPeak W (solve (Op := Op) (Tst := Tst)) [n, cap, a, b, c, d, e, f] ≤
      solvePeak W n := by
  simpa [solve, staticPeak, IExp.evalList, IExp.eval, solvePeak] using
    max_le_max (staticPeak_initialize_le W n a b c d e f)
      (staticPeak_rounds_le W n cap c d e f c d e f)

end NLAlib.Krylov.CG.HSCG.Carried
