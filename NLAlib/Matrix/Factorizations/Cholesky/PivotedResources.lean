/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.PivotedRoutine
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.Static

/-!
# Closed resources of scalar diagonal-pivoted PSD Cholesky

The fixed program performs actual diagonal scans and bounded stored-index reads, symmetric
word exchanges, zero-safe materialization and full saved-pivot updates. Structural instruction
charges are included in its size-only cubic. Caller source, factor and log capacities are
charged separately from the copied residual and scalar/vector scratch. All orders are covered.

## Main results

* `NLAlib.Cholesky.PivotedCertification.countPoly_program`: the actual tree's polynomial.
* `NLAlib.Cholesky.PivotedCertification.staticPeak_program_le`: scoped storage bound.
-/

@[expose] public section

namespace NLAlib.Cholesky.PivotedCertification

open Ops

/-- The fixed actual program, before the dimension, input and interpreter are supplied. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 1 3 :=
  (pivotedRightLooking (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 1 3

/-- Closed total instruction work and sequential span of the fixed scalar program. -/
def work (d : Fin 1 → ℕ) : ℕ := 22 * d 0 ^ 3 + 283 * d 0 ^ 2 + 504 * d 0 + 60

/-- Additional residual, saved vectors and four scalar cells, excluding caller slots. -/
def scratch (d : Fin 1 → ℕ) : ℕ := d 0 * d 0 + 2 * d 0 + 4

/-- The kernel computes the literal polynomial from the actual guarded instruction tree. -/
theorem countPoly_program :
    program.countPoly = [(504, [0]), (22, [0, 0, 0]), (283, [0, 0]), (60, [])] := by
  kernel_rfl

/-- The actual instruction polynomial evaluates to the declared closed cubic at every order. -/
theorem eval_countPoly_program (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

private theorem stmtPeak_diagonalChoice_le (n k : ℕ) :
    stmtPeak ScalarIndex.resources.workspace
      (diagonalChoice (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
      [n, k, 0, 0] ≤ n - k + 3 := by
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  simp [diagonalChoice, copyDiagonal, copyStridedRoutine, LU.argmaxAbs, absolute,
    stmtPeak, ScalarIndex.resources, Stmt.alloc, IExp.eval, IExp.evalList, h0]

private theorem stmtPeak_symmetricPivot_le (n k r : ℕ) :
    stmtPeak ScalarIndex.resources.workspace
      (symmetricPivot (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
      [n, k, r, 0, 0, 0, 0] ≤ 1 := by
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  simp [symmetricPivot, LU.swapRows, LU.swapColumns, Examples.Strided.swapMatrixRows,
    Examples.Strided.swapRows, stmtPeak, ScalarIndex.resources, Stmt.ifPos, Stmt.alloc,
    IExp.eval, IExp.evalList, h0]

private theorem stmtPeak_rightStepTotal_le (n k : ℕ) :
    stmtPeak ScalarIndex.resources.workspace
      (rightStepTotal (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries))
      [n, k, 0, 0] ≤ 2 * n + 3 := by
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  have h2 : (Finset.range n).sup (fun _ : ℕ => 1 + (1 + 0)) ≤ 2 :=
    Finset.sup_le (fun _ _ => by omega)
  have h : max 1 (n + (n + (1 + (Finset.range n).sup (fun _ : ℕ => 1 + (1 + 0))))) ≤
      2 * n + 3 := by omega
  simpa [rightStepTotal, rightStep, rightColumn, LU.schurStep, LU.pivotSaved, LU.rankOne,
    LU.schurColumn, copyLoopRoutine, copyLoop, scalLoopRoutine, scalLoop, axpyLoopRoutine,
    axpyLoop, fillRoutine, fillMap, copyStridedRoutine, stmtPeak, ScalarIndex.resources,
    Stmt.alloc, IExp.eval, IExp.evalList, h0, Nat.add_assoc] using h

/-- Every actual control branch and scoped temporary fits the declared extra cell allowance.
The proof uses the fixed tree and bounded index queries, with no execution or matrix premise. -/
theorem staticPeak_program_le (d : Fin 1 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  change stmtPeak ScalarIndex.resources.workspace
    (pivotedRightLooking (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
    [n, 0, 0, 0] ≤ n * n + 2 * n + 4
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  let choice : Stmt ScalarIndex.Operation ScalarIndex.Queries := diagonalChoice.body
  let exchange : Stmt ScalarIndex.Operation ScalarIndex.Queries := symmetricPivot.body
  let columnStep : Stmt ScalarIndex.Operation ScalarIndex.Queries := rightStepTotal
  suffices h : ∀ b < 1 - (1 - n), n * n + (Finset.range n).sup (fun i => 1 +
      max (stmtPeak (fun _ _ => 0) choice [n, i, 0, 0])
        ((Finset.range (n - 1 + 1)).sup fun v =>
          max (stmtPeak (fun _ _ => 0) exchange [n, i, v, 0, 0, 0, 0])
            (stmtPeak (fun _ _ => 0) columnStep [n, i, 0, 0]))) ≤ n * n + 2 * n + 4 by
    simpa [pivotedRightLooking, pivotedWithScratch, pivotedLoop, pivotedStep, pivotedAdvance,
      initializeLower, copyLoopRoutine, copyLoop, fillRoutine, fillMap, stmtPeak,
      ScalarIndex.resources, Stmt.ifPos, Stmt.alloc, IExp.eval, IExp.evalList,
      choice, exchange, columnStep, h0] using h
  intro _ _
  have hstep : (Finset.range n).sup (fun i => 1 +
      max (stmtPeak (fun _ _ => 0) choice [n, i, 0, 0])
        ((Finset.range (n - 1 + 1)).sup fun v =>
          max (stmtPeak (fun _ _ => 0) exchange [n, i, v, 0, 0, 0, 0])
            (stmtPeak (fun _ _ => 0) columnStep [n, i, 0, 0]))) ≤ 2 * n + 4 := by
    apply Finset.sup_le
    intro i _
    have hd : stmtPeak (fun _ _ => 0) choice [n, i, 0, 0] ≤ n - i + 3 :=
      stmtPeak_diagonalChoice_le n i
    have hi : n - i ≤ n := Nat.sub_le n i
    have hinner : (Finset.range (n - 1 + 1)).sup (fun v =>
        max (stmtPeak (fun _ _ => 0) exchange [n, i, v, 0, 0, 0, 0])
          (stmtPeak (fun _ _ => 0) columnStep [n, i, 0, 0])) ≤ 2 * n + 3 := by
      apply Finset.sup_le
      intro v _
      have hs : stmtPeak (fun _ _ => 0) exchange [n, i, v, 0, 0, 0, 0] ≤ 1 :=
        stmtPeak_symmetricPivot_le n i v
      have ht : stmtPeak (fun _ _ => 0) columnStep [n, i, 0, 0] ≤ 2 * n + 3 :=
        stmtPeak_rightStepTotal_le n i
      omega
    omega
  omega

end NLAlib.Cholesky.PivotedCertification
