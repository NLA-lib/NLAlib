/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedAlg
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.Static

/-!
# Shared scoped storage of pivoted LU

Concrete pivot policies supply their selector's actual peak. The common engine adds a copied
residual, two selected-index words, exchanges and the saved-row/column Schur step. These
bounds inspect the actual tree and are independent of numerical execution and matrix data.

## Main results

* `NLAlib.LU.stmtPeak_pivotedStep_le`: one step adds the larger selector or Schur peak.
* `NLAlib.LU.stmtPeak_factorPivoted_le`: the complete common engine's scoped cell bound.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

/-- A common pivot step uses the larger of its actual selector peak and the saved-vector
Schur peak. The two log-cell offsets do not affect allocated storage. -/
theorem stmtPeak_pivotedStep_le (choose : Stmt ScalarIndex.Operation ScalarIndex.Queries)
    (n k h q : ℕ) :
    stmtPeak ScalarIndex.resources.workspace (pivotedStep choose).body
      [n, k, 0, 0, 0, 0, 0, 0, h, q, 0] ≤
      max (stmtPeak ScalarIndex.resources.workspace choose [n, k, 0, 0]) (2 * n + 3) := by
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  have h2 : (Finset.range n).sup (fun _ : ℕ => 2) ≤ 2 :=
    Finset.sup_le (fun _ _ => le_rfl)
  suffices hh : max (stmtPeak (fun _ _ => 0) choose [n, k, 0, 0])
      ((Finset.range (n - 1 + 1)).sup fun r =>
        (Finset.range (n - 1 + 1)).sup fun c =>
          max ((Finset.range (1 - (1 - (r - k)))).sup fun _ => 1)
            (max ((Finset.range (1 - (1 - (c - k)))).sup fun _ => 1)
              (n + (n + (1 + (Finset.range n).sup fun _ => 2))))) ≤
      max (stmtPeak (fun _ _ => 0) choose [n, k, 0, 0]) (2 * n + 3) by
    simpa [pivotedStep, choiceRoutine, pivotSwaps, swapRows, swapColumns,
      Examples.Strided.swapMatrixRows, Examples.Strided.swapRows, step, materializeColumn,
      materializeUpper, normalizeColumn, schurStepTotal, schurStep, pivotSaved, rankOne,
      schurColumn, copyLoopRoutine, copyLoop, scalLoopRoutine, scalLoop, axpyLoopRoutine,
      axpyLoop, fillRoutine, fillMap, copyStridedRoutine, stmtPeak, ScalarIndex.resources,
      Stmt.ifPos, Stmt.alloc, IExp.eval, IExp.evalList, h0] using hh
  apply max_le_max_left
  apply Finset.sup_le
  intro r _
  apply Finset.sup_le
  intro c _
  refine max_le ?_ (max_le ?_ ?_)
  · exact Finset.sup_le (fun _ _ => by omega)
  · exact Finset.sup_le (fun _ _ => by omega)
  · omega

/-- A selector fitting `bound` cells gives the actual common engine a copied residual,
two selected-index cells and at most `bound` further cells. The scalar Schur step must also
fit that allowance. Both history-storage flags and dimension zero are covered. -/
theorem stmtPeak_factorPivoted_le_of_selector
    (choose : Stmt ScalarIndex.Operation ScalarIndex.Queries) (fixedColumns : Bool)
    (n bound : ℕ)
    (hchoose : ∀ k < n,
      stmtPeak ScalarIndex.resources.workspace choose [n, k, 0, 0] ≤ bound)
    (hstep : 2 * n + 3 ≤ bound) :
    stmtPeak ScalarIndex.resources.workspace (factorPivoted choose fixedColumns).body
      [n, 0, 0, 0, 0, 0] ≤ n * n + 2 + bound := by
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  have hh (columns : ℕ) :
      n * n + (2 + (Finset.range n).sup (fun k =>
        stmtPeak ScalarIndex.resources.workspace (pivotedStep choose).body
          [n, k, 0, 0, 0, 0, 0, 0, k, columns * k, 0])) ≤ n * n + 2 + bound := by
    have hloop : (Finset.range n).sup (fun k =>
        stmtPeak ScalarIndex.resources.workspace (pivotedStep choose).body
          [n, k, 0, 0, 0, 0, 0, 0, k, columns * k, 0]) ≤ bound := by
      apply Finset.sup_le
      intro k hk
      exact (stmtPeak_pivotedStep_le choose n k k (columns * k)).trans
        (max_le (hchoose k (Finset.mem_range.mp hk)) hstep)
    omega
  have hhguard := fun (b : ℕ) (_ : b < 1 - (1 - n)) =>
    hh (if fixedColumns then 0 else 1)
  cases fixedColumns <;>
    simpa [factorPivoted, factorPivotedCore, pivotedLoop, initializeFactors,
      copyLoopRoutine, copyLoop, fillRoutine, fillMap, stmtPeak, ScalarIndex.resources,
      Stmt.ifPos, Stmt.alloc, IExp.eval, IExp.evalList, h0] using hhguard

/-- A selector fitting `2n+5` cells gives the actual common engine its complete-pivot
allowance. Concrete row policies can use the sharper parametric result with a smaller bound. -/
theorem stmtPeak_factorPivoted_le
    (choose : Stmt ScalarIndex.Operation ScalarIndex.Queries) (fixedColumns : Bool) (n : ℕ)
    (hchoose : ∀ k < n,
      stmtPeak ScalarIndex.resources.workspace choose [n, k, 0, 0] ≤ 2 * n + 5) :
    stmtPeak ScalarIndex.resources.workspace (factorPivoted choose fixedColumns).body
      [n, 0, 0, 0, 0, 0] ≤ n * n + 2 * n + 7 := by
  exact (stmtPeak_factorPivoted_le_of_selector choose fixedColumns n (2 * n + 5)
    hchoose (by omega)).trans (by omega)

end NLAlib.LU
