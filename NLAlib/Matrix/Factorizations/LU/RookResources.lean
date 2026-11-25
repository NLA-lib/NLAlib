/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Rook
public import NLAlib.Matrix.Factorizations.LU.PivotedResources
public import NLAlib.Ops.OperationCount

/-!
# Closed resources of rook-pivot LU

The fixed scalar program includes every alternating active-column/row gather and first-maximum scan,
stored-index query, finite strict-improvement loop, independent row/column exchange,
factor materialization and full Schur
update. Structural charges are included in its closed cubic. The source, factors and both
reported logs are caller storage; the residual and scoped candidates are additional cells.

## Main results

* `NLAlib.LU.RookCertification.countPoly_program`: actual literal instruction polynomial.
* `NLAlib.LU.RookCertification.staticPeak_program_le`: scoped extra cells at every order.
-/

@[expose] public section

namespace NLAlib.LU.RookCertification

open Ops

/-- The fixed rook-pivot tree, before dimensions, source, interpreter and tape. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 1 5 :=
  (factorRook (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 1 5

/-- Closed total instruction work and sequential span, including all structural charges. -/
def work (d : Fin 1 → ℕ) : ℕ := 142 * d 0 ^ 3 + 727 * d 0 ^ 2 + 876 * d 0 + 109

/-- Extra residual, selected pair, saved Schur vectors and scoped selector candidates. -/
def scratch (d : Fin 1 → ℕ) : ℕ := d 0 * d 0 + 2 * d 0 + 7

/-- The literal polynomial is computed by the kernel from the actual guarded scalar tree. -/
theorem countPoly_program :
    program.countPoly = [(109, []), (876, [0]), (727, [0, 0]), (142, [0, 0, 0])] := by
  kernel_rfl

/-- The actual instruction polynomial has the stated closed cubic value at every order. -/
theorem eval_countPoly_program (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

private theorem stmtPeak_rookChoice_le (n k : ℕ) :
    stmtPeak ScalarIndex.resources.workspace
      (rookChoice (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
      [n, k, 0, 0] ≤ n - k + 6 := by
  have h0 (m : ℕ) : (Finset.range m).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  suffices hh : 1 + (1 + (1 + (n - k + 3))) ≤ n - k + 6 by
    simpa [rookChoice, rookInitialize, rookSearch, rookAdvance, completeColumn, rookRow,
      lineChoice, argmaxAbs, absolute, copyStridedRoutine, stmtPeak, ScalarIndex.resources,
      Stmt.alloc, IExp.eval, IExp.evalList, h0] using hh
  omega

/-- The actual scoped peak fits the residual and `2n+7` further cells. The proof uses the
fixed tree and bounded query branches; it has no matrix, execution or positive-order premise. -/
theorem staticPeak_program_le (d : Fin 1 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  change stmtPeak ScalarIndex.resources.workspace
    (factorRook (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
    [n, 0, 0, 0, 0, 0] ≤ n * n + 2 * n + 7
  have hengine := stmtPeak_factorPivoted_le
    (rookChoice (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body false n
    (fun k hk => by have := stmtPeak_rookChoice_le n k; omega)
  simpa [factorRook, stmtPeak, ScalarIndex.resources, Stmt.ifPos, IExp.eval,
    IExp.evalList] using (fun (b : ℕ) (_ : b < 1 - (1 - n)) => hengine)

end NLAlib.LU.RookCertification
