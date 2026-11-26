/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.Blocked
public import NLAlib.Matrix.Factorizations.LU.BlockedResources
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.Static

/-!
# Closed resources of actual blocked scalar Cholesky

The literal instruction polynomial counts the actual clipped-panel tree, including the
scalar packing, multiplication, subtraction, and structural instructions. Its arguments are
order, positive block size, and the supplied ceiling block count. Symbolic clipping yields a
conservative polynomial in these three dimensions; oversized blocks need not give a tight
bound. These abstract counts assert no native BLAS throughput or elapsed-time guarantee.

## Main results

* `NLAlib.Cholesky.BlockedCertification.countPoly_program`: actual-tree polynomial equality.
* `NLAlib.Cholesky.BlockedCertification.eval_countPoly_program`: closed dimension-only work.
-/

@[expose] public section

namespace NLAlib.Cholesky.BlockedCertification

open Ops

/-- The fixed blocked scalar Cholesky tree before dimensions, matrix words, interpreter and tape. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 3 2 :=
  (factorBlocked (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 3 2

/-- Closed full instruction work and sequential span in order, block size and block count. -/
def work (d : Fin 3 → ℕ) : ℕ :=
  44 * d 0 + 395 * d 1 * d 2 + 180 * d 0 * d 1 ^ 2 * d 2 +
    180 * d 0 * d 1 ^ 2 * d 2 ^ 2 + 49 * d 1 ^ 2 * d 2 +
    49 * d 1 ^ 2 * d 2 ^ 2 + 83 * d 0 ^ 2 * d 2 + 22 * d 0 * d 2 +
    33 * d 0 ^ 2 * d 1 * d 2 + 187 * d 0 * d 1 * d 2 + 215 * d 2 +
    44 * d 0 ^ 2 + 118

/-- The kernel computes this polynomial from the actual scalar panels, matrix updates and
root scaling. -/
theorem countPoly_program : program.countPoly =
    [(44, [0]), (44, [0, 0]), (395, [1, 2]), (180, [0, 1, 1, 2]), (180, [0, 1, 1, 2, 2]),
      (49, [1, 1, 2]), (49, [1, 1, 2, 2]), (83, [0, 0, 2]), (22, [0, 2]),
      (33, [0, 0, 1, 2]), (187, [0, 1, 2]), (215, [2]), (118, [])] := by
  kernel_rfl

/-- Evaluation of the actual instruction polynomial is the displayed closed expression. -/
theorem eval_countPoly_program (d : Fin 3 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

/-- Additional scoped cells: the upper factor, the blocked LU workspaces and one root
scaling temporary. Caller source and output matrices are counted separately. -/
def scratch (d : Fin 3 → ℕ) : ℕ := 6 * d 0 * d 0 + 2 * d 0 + 3

/-- The actual scoped upper factor, blocked LU and column scaling have this closed scratch
bound for every dimension tuple, without numerical data or a successful-run hypothesis. -/
theorem staticPeak_program_le (d : Fin 3 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  let b := d 1
  let q := d 2
  have hLU := LU.BlockedCertification.stmtPeak_factorBlocked_le n b q 0 0 0
  have hscale : stmtPeak ScalarIndex.resources.workspace
      (scaleLuColumns (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
      [n, 0, 0, 0] ≤ 1 := by
    simp [scaleLuColumns, scaleLuColumn, fillRoutine, fillMap, stmtPeak,
      ScalarIndex.resources, Stmt.alloc, IExp.eval, IExp.evalList]
  have hmax := max_le hLU (hscale.trans (by omega : 1 ≤ 5 * n * n + 2 * n + 3))
  have hpoint : n * n + max (stmtPeak ScalarIndex.resources.workspace
      (LU.factorBlocked (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
      [n, b, q, 0, 0, 0])
      (stmtPeak ScalarIndex.resources.workspace
        (scaleLuColumns (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
        [n, 0, 0, 0]) ≤ 6 * n * n + 2 * n + 3 := by nlinarith
  change stmtPeak ScalarIndex.resources.workspace
    (factorBlocked (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
    [n, b, q, 0, 0] ≤ 6 * n * n + 2 * n + 3
  simpa [factorBlocked, Stmt.ifPos, blockedWithScratch, stmtPeak, IExp.eval, IExp.evalList]
    using (fun (guard : ℕ) (_ : guard < 1 - (1 - n)) => hpoint)

end NLAlib.Cholesky.BlockedCertification
