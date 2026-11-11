/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import NLAlib.Krylov.CG.Reorth.Round
public import NLAlib.Ops.Catalog.Compare

/-!
# A capped CG solver with full residual reorthogonalization

The solver keeps the initialized residual history in scoped storage. Before each active round
it saves the current residual, sweeps the new residual against that history, and refreshes the
norm used by the next positivity test. A zero residual exits before any further division.

## Main results

* `NLAlib.Krylov.CG.Reorth.solve` is the complete uniform program.
* `NLAlib.Krylov.CG.Reorth.solveCount` counts every allowed round and every history projection.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
variable [Has CmpTst Tst]

/-- Save residual column `i`, execute the full sweep round, and refresh the guard norm.
The surrounding solver supplies the history and guard buffers at indices 5 and 6. -/
def advance : Stmt Op Tst :=
  .seq (.call (Has.inj Blas1Op.copy) [.var 0] [⟨3, .var 5⟩]
    [⟨5, .var 7 * .var 0⟩])
    (.seq (.frame [.var 0, .var 7 + .const 1]
      [⟨1, .var 3⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩, ⟨5, .const 0⟩,
        ⟨1, .var 3⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩] round)
      (.call (Has.inj Blas1Op.dot) [.var 0] [⟨3, .var 5⟩, ⟨3, .var 5⟩] [⟨6, .const 0⟩]))

/-- Stop at a zero residual self-product or at the cap; the cap itself performs no test. -/
def rounds : Stmt Op Tst :=
  .whileFuel (.var 1) (Has.inj CmpTst.isPos) [] [⟨6, .const 0⟩] advance .skip

/-- Initialize the state, then run capped full-reorthogonalized CG with scoped history. -/
def solve : Stmt Op Tst :=
  .alloc (.var 1 * .var 0) (.alloc (.const 1)
    (.seq (.frame [.var 0]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨1, .var 3⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩]
      HSCG.initializeState)
      (.seq (.call (Has.inj Blas1Op.dot) [.var 0]
        [⟨3, .var 5⟩, ⟨3, .var 5⟩] [⟨6, .const 0⟩]) rounds)))

/-- Inputs are the right-hand side and initial iterate; outputs are the three CG state blocks. -/
def solveImpl : Impl Op Tst := ⟨2, 2, 3, solve⟩

/-- The cost of one basis projection, independent of the round index. -/
noncomputable def projectionCount (n : ℕ) : Count Op Tst :=
  2 • Count.one (Has.inj Blas1Op.dot) [n] + Count.one (Has.inj ScalarOp.div) [] +
    Count.one (Has.inj ScalarOp.neg) [] + Count.one (Has.inj Blas1Op.axpy) [n]

/-- The initialization calls, one guard-norm refresh per round, and a triangular number of
history projections. This is an upper budget when the program exits before the cap. -/
noncomputable def solveCount (n cap : ℕ) : Count Op Tst :=
  HSCG.initializeCount n + Count.one (Has.inj Blas1Op.dot) [n] +
    cap • (Count.test (Has.inj CmpTst.isPos) [] + HSCG.stepCount n +
      Count.one (Has.inj Blas1Op.copy) [n] + Count.one (Has.inj Blas1Op.dot) [n]) +
    (cap * (cap + 1) / 2) • projectionCount n

/-- The history and guard cell, together with the largest initialization or round workspace. -/
def solvePeak (W : Op → List ℕ → ℕ) (n cap : ℕ) : ℕ :=
  cap * n + 1 + max (HSCG.initializePeak W n)
    (max (roundPeak W n)
      (max (W (Has.inj Blas1Op.copy) [n]) (W (Has.inj Blas1Op.dot) [n])))

/-- The evaluator includes all guards, saved residuals, and full-sweep calls in the budget. -/
theorem staticCost_solve (n cap b x x' r p : ℕ) :
    stmtCost (solve (Op := Op) (Tst := Tst)) [n, cap, b, x, x', r, p] = solveCount n cap := by
  have htri : ∑ i ∈ Finset.range cap, (i + 1) = cap * (cap + 1) / 2 := by
    have h := Finset.sum_range_id (cap + 1)
    rw [Finset.sum_range_succ'] at h
    simpa [Nat.mul_comm] using h
  have hsup : (Finset.range (cap + 1)).sup (fun _ => (0 : Count Op Tst)) = 0 := by
    exact le_antisymm (Finset.sup_le fun _ _ => le_rfl) zero_le
  simp [solve, rounds, advance, stmtCost, useCost, testCost, staticCost_round,
    HSCG.staticCost_initialize, roundCount, sweepCount, solveCount, projectionCount,
    Finset.sum_add_distrib, Finset.sum_nsmul_assoc, htri, hsup]
  module

/-- Scoped history grows with the cap; temporary round storage is reused at every iteration. -/
theorem staticPeak_solve_le (W : Op → List ℕ → ℕ) (n cap b x x' r p : ℕ) :
    stmtPeak W (solve (Op := Op) (Tst := Tst)) [n, cap, b, x, x', r, p] ≤
      solvePeak W n cap := by
  have hin := HSCG.staticPeak_initialize_le (Op := Op) (Tst := Tst) W n b x x r p
  have hbody : (Finset.range cap).sup (fun i => max (W (Has.inj Blas1Op.copy) [n])
      (max (stmtPeak W round [n, i + 1, x, r, p, 0, x, r, p])
        (W (Has.inj Blas1Op.dot) [n]))) ≤
      max (roundPeak W n) (max (W (Has.inj Blas1Op.copy) [n]) (W (Has.inj Blas1Op.dot) [n])) :=
    Finset.sup_le fun i _ => by
      have h := staticPeak_round_le (Op := Op) (Tst := Tst) W n (i + 1) x r p 0 x r p
      omega
  simp [solve, rounds, advance, stmtPeak, solvePeak]
  omega

end NLAlib.Krylov.CG.Reorth
