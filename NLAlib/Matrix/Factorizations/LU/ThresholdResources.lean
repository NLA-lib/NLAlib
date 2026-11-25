/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Threshold
public import NLAlib.Matrix.Factorizations.LU.PartialResources
public import NLAlib.Matrix.Factorizations.LU.RowPivotedResources
public import NLAlib.Ops.OperationCount

/-!
# Closed resources of threshold-pivot LU

The fixed scalar program includes every active-column first-maximum scan,
stored-index query, row exchange, factor materialization and full Schur
update. Structural charges are included in its closed cubic. The source, factors and the
reported log are caller storage; the residual and scoped candidates are additional cells.
The full instruction budget is $22n^3+323n^2+725n+112$. Additional storage is at most
$n^2+2n+7$ abstract cells. Including the three caller matrices and row log gives
$4n^2+3n+7$ resident cells; no hardware byte-width or elapsed-time claim is made.

## Main results

* `NLAlib.LU.ThresholdCertification.countPoly_program`: actual literal instruction polynomial.
* `NLAlib.LU.ThresholdCertification.staticPeak_program_le`: scoped extra cells at every order.
-/

@[expose] public section

namespace NLAlib.LU.ThresholdCertification

open Ops

/-- The fixed threshold-pivot tree, before dimensions, source, interpreter and tape. -/
def program (threshold : ℚ) : Program ScalarIndex.Operation ScalarIndex.Queries 1 4 :=
  (factorThreshold (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries) threshold).close 1 4

/-- Closed total instruction work and sequential span, including all structural charges. -/
def work (d : Fin 1 → ℕ) : ℕ := 22 * d 0 ^ 3 + 323 * d 0 ^ 2 + 725 * d 0 + 112

/-- Extra residual, selected pair, saved Schur vectors and scoped selector candidates. -/
def scratch (d : Fin 1 → ℕ) : ℕ := d 0 * d 0 + 2 * d 0 + 7

/-- The literal polynomial is computed by the kernel from the actual guarded scalar tree. -/
theorem countPoly_program (threshold : ℚ) :
    (program threshold).countPoly = [(22, [0, 0, 0]), (323, [0, 0]), (725, [0]), (112, [])] := by
  kernel_rfl

/-- The actual instruction polynomial has the stated closed cubic value at every order. -/
theorem eval_countPoly_program (threshold : ℚ) (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) (program threshold).countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

private theorem stmtPeak_thresholdChoice_le (threshold : ℚ) (n k : ℕ) :
    stmtPeak ScalarIndex.resources.workspace
      (thresholdChoice (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries) threshold).body
      [n, k, 0, 0] ≤ 5 := by
  have hpartial := PartialCertification.stmtPeak_partialChoice_le n k
  have hthree (t : ℕ) : (Finset.range t).sup (fun _ : ℕ => 3) ≤ 3 :=
    Finset.sup_le fun _ _ => le_rfl
  have hh : 2 + max (stmtPeak ScalarIndex.resources.workspace
      (partialChoice (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
      [n, k, 0, 0]) ((Finset.range (n - 1 + 1)).sup (fun _ : ℕ => 3)) ≤ 5 := by
    have hm := max_le hpartial (hthree (n - 1 + 1))
    omega
  simpa [thresholdChoice, thresholdCandidate, absolute, stmtPeak, ScalarIndex.resources,
    Stmt.alloc, IExp.eval, IExp.evalList] using hh

/-- The actual scoped peak fits the residual and `2n+7` further cells. The proof uses the
fixed tree and bounded query branches; it has no matrix, execution or positive-order premise. -/
theorem staticPeak_program_le (threshold : ℚ) (d : Fin 1 → ℕ) :
    staticPeak ScalarIndex.resources (program threshold) d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  change stmtPeak ScalarIndex.resources.workspace
    (factorThreshold (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries) threshold).body
    [n, 0, 0, 0, 0] ≤ n * n + 2 * n + 7
  have hrow := stmtPeak_factorRowPivoted_le
    (thresholdChoice (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries) threshold).body
    n (2 * n + 3) (fun k hk => (stmtPeak_thresholdChoice_le threshold n k).trans (by omega))
    le_rfl
  simpa only [factorThreshold] using hrow.trans (by omega)

end NLAlib.LU.ThresholdCertification
