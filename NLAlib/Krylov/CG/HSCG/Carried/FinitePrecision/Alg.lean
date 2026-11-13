/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Initialization
public import NLAlib.Krylov.CG.HSCG.Carried.Linked

/-!
# A zero-start rounded CG solver over shared operations

The new initializer preserves the exact decoded right-hand side. The existing carried-product
round loop then advances or stops early. Both components are uniform first-order programs.
The caller provides a decoded zero iterate buffer; no matrix data enters the program tree.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.solve` composes the full program.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.staticCost_solve` exposes its abstract operation budget.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.push_solveCount_seq` exposes scalar and comparison costs.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has CmpTst Tst]

/-- Retain the zero iterate, initialize residual/direction/cache, and perform capped rounded
CG with the retained residual self-product. [HestenesStiefel1952, (3:1)]. -/
def solve : Stmt Op Tst :=
  .seq (.frame [.var 0]
    [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .var 5⟩,
      ⟨4, .var 6⟩, ⟨5, .var 7⟩] initializeState)
    (.frame [.var 0, .var 1]
      [⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩, ⟨5, .var 7⟩,
        ⟨2, .var 4⟩, ⟨3, .var 5⟩, ⟨4, .var 6⟩, ⟨5, .var 7⟩] Carried.rounds)

/-- The solver has dimension and cap parameters, two input blocks and four output blocks. -/
def solveImpl : Impl Op Tst := ⟨2, 2, 4, solve⟩

/-- The abstract operation budget includes initialization and at most one tested round per cap. -/
noncomputable def solveCount (n cap : ℕ) : Count Op Tst :=
  initializeCount n + Carried.roundsCount n cap

/-- Initialization and rounds reuse their operation workspace. -/
def solvePeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max (initializePeak W n) (Carried.stepPeak W n)

/-- Evaluating the uniform solver gives its stated abstract operation budget. -/
theorem staticCost_solve (n cap a b c d e f : ℕ) :
    stmtCost (solve (Op := Op) (Tst := Tst)) [n, cap, a, b, c, d, e, f] =
      solveCount n cap := by
  simp [solve, stmtCost, IExp.evalList, IExp.eval, staticCost_initialize,
    Carried.staticCost_rounds, solveCount]

/-- The static solver workspace is independent of the cap. -/
theorem staticPeak_solve_le (W : Op → List ℕ → ℕ) (n cap a b c d e f : ℕ) :
    stmtPeak W (solve (Op := Op) (Tst := Tst)) [n, cap, a, b, c, d, e, f] ≤
      solvePeak W n := by
  simpa [solve, stmtPeak, IExp.evalList, IExp.eval, solvePeak] using
    max_le_max (staticPeak_initialize_le W n a b c d e f)
      (Carried.staticPeak_rounds_le W n cap c d e f c d e f)

/-- The sequential initializer performs two vector copies and one residual self-dot. -/
noncomputable def seqInitializeCount (n : ℕ) : Count Op Tst :=
  n • Count.one (Has.inj ScalarOp.mul) [] + (n - 1) • Count.one (Has.inj ScalarOp.add) [] +
    (2 * n + (1 - (1 - n))) • Count.one (Has.inj ScalarOp.copy) [] +
    Count.one (Has.inj (ScalarOp.lit 0)) []

/-- The scalar budget includes all initialization, comparison and carried-round operations. -/
noncomputable def seqSolveCount (n cap : ℕ) : Count Op Tst :=
  seqInitializeCount n + cap • (Count.test (Has.inj CmpTst.isPos) [] + Carried.seqStepCount n)

variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

omit [Has OperatorOp Op] [Has CmpTst Tst] [Apart Blas1Op OperatorOp Op] in
/-- Pushing initialization through sequential BLAS gives the closed scalar count. -/
theorem push_initializeCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (initializeCount n) =
      seqInitializeCount n := by
  count_eval [initializeCount, seqInitializeCount]

/-- Profile transfer computes the complete solver's scalar and comparison budget. -/
theorem push_solveCount_seq (n cap : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (solveCount n cap) =
      seqSolveCount n cap := by
  simp only [solveCount, Carried.roundsCount, map_add, map_nsmul, Count.push_test,
    push_initializeCount_seq, Carried.push_stepCount_seq, seqSolveCount]

/-- Sequential BLAS needs at most the reused vector scratch and four cells. -/
theorem solvePeak_seq_le (n : ℕ) : solvePeak (Blas.ws (Op := Op) 0) n ≤ 2 * n + 4 := by
  apply max_le _ (Carried.stepPeak_seq_le n)
  simp [initializePeak, Blas.ws]
  omega

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
