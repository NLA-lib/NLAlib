/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Partial
public import NLAlib.Matrix.Factorizations.LU.RowPivotedResources
public import NLAlib.Ops.OperationCount

/-!
# Closed resources of partial-pivot LU

The fixed scalar program includes every active-column first-maximum scan,
stored-index query, row exchange, factor materialization and full Schur
update. Structural charges are included in its closed cubic. The source, factors and the
reported log are caller storage; the residual and scoped candidates are additional cells.
The full instruction budget is $22n^3+323n^2+598n+112$. Additional storage is at most
$n^2+2n+7$ abstract cells. Including the three caller matrices and row log gives
$4n^2+3n+7$ resident cells; no hardware byte-width or elapsed-time claim is made.

## Main results

* `NLAlib.LU.PartialCertification.countPoly_program`: actual literal instruction polynomial.
* `NLAlib.LU.PartialCertification.staticPeak_program_le`: scoped extra cells at every order.
-/

@[expose] public section

namespace NLAlib.LU.PartialCertification

open Ops

/-- The fixed partial-pivot tree, before dimensions, source, interpreter and tape. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 1 4 :=
  (factorPartial (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 1 4

/-- Closed total instruction work and sequential span, including all structural charges. -/
def work (d : Fin 1 → ℕ) : ℕ := 22 * d 0 ^ 3 + 323 * d 0 ^ 2 + 598 * d 0 + 112

/-- Extra residual, selected pair, saved Schur vectors and scoped selector candidates. -/
def scratch (d : Fin 1 → ℕ) : ℕ := d 0 * d 0 + 2 * d 0 + 7

/-- The literal polynomial is computed by the kernel from the actual guarded scalar tree. -/
theorem countPoly_program :
    program.countPoly = [(22, [0, 0, 0]), (323, [0, 0]), (598, [0]), (112, [])] := by
  kernel_rfl

/-- The actual instruction polynomial has the stated closed cubic value at every order. -/
theorem eval_countPoly_program (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

/-- The actual contiguous active-column selector uses three scratch cells, independently
of the order and pivot position; no packed line buffer is allocated. -/
theorem stmtPeak_partialChoice_le (n k : ℕ) :
    stmtPeak ScalarIndex.resources.workspace
      (partialChoice (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
      [n, k, 0, 0] ≤ 3 := by
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  simp [partialChoice, argmaxAbs, absolute, stmtPeak, ScalarIndex.resources,
    Stmt.alloc, IExp.eval, IExp.evalList, h0]

/-- The actual scoped peak fits the residual and `2n+7` further cells. The proof uses the
fixed tree and bounded query branches; it has no matrix, execution or positive-order premise. -/
theorem staticPeak_program_le (d : Fin 1 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  change stmtPeak ScalarIndex.resources.workspace
    (factorPartial (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
    [n, 0, 0, 0, 0] ≤ n * n + 2 * n + 7
  have hrow := stmtPeak_factorRowPivoted_le
    (partialChoice (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
    n (2 * n + 3) (fun k _ => (stmtPeak_partialChoice_le n k).trans (by omega)) le_rfl
  simpa only [factorPartial] using hrow.trans (by omega)

end NLAlib.LU.PartialCertification
