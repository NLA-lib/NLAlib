/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RowPivoted
public import NLAlib.Matrix.Factorizations.LU.PivotedResources

/-!
# Scratch storage for actual row-policy LU

The row-only wrapper scopes one column-index word around the common policy engine. It never
allocates an unreported length-order history. A selector-specific bound therefore gives a
sharp storage bound for both partial and fixed-column threshold policies.

## Main results

* `NLAlib.LU.stmtPeak_factorRowPivoted_le`: additional cells of the actual row wrapper.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

/-- The actual row wrapper needs one scoped column word in addition to the common pivoted
engine. The hypotheses bound the actual selector and saved-vector Schur step independently. -/
theorem stmtPeak_factorRowPivoted_le
    (choose : Stmt ScalarIndex.Operation ScalarIndex.Queries) (n B : ℕ)
    (hchoose : ∀ k < n, stmtPeak ScalarIndex.resources.workspace choose [n, k, 0, 0] ≤ B)
    (hstep : 2 * n + 3 ≤ B) :
    stmtPeak ScalarIndex.resources.workspace
      (factorRowPivoted choose).body [n, 0, 0, 0, 0] ≤ n * n + 3 + B := by
  have hengine := stmtPeak_factorPivoted_le_of_selector choose true n B hchoose hstep
  have hh : 1 + stmtPeak ScalarIndex.resources.workspace
      (factorPivoted choose true).body [n, 0, 0, 0, 0, 0] ≤ n * n + 3 + B := by omega
  simpa [factorRowPivoted, stmtPeak, ScalarIndex.resources, Stmt.ifPos, IExp.eval,
    IExp.evalList] using (fun (b : ℕ) (_ : b < 1 - (1 - n)) => hh)

end NLAlib.LU
