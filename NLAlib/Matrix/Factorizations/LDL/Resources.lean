/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LDL.Routine
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.Static

/-!
# Closed resources of stored scalar LDL

The fixed LDL tree has instruction polynomial $22n^3+141n^2+255n+93$, including scalar
calls, queries, addressing and structural instructions. It uses at most $2n^2+2n+3$ additional
abstract cells: a temporary upper factor, residual, saved pivot column and row, and three
scalar temporaries.
The caller's source and blank output buffers are additional resident storage. All bounds
include order zero and assert neither hardware BLAS costs nor elapsed time.

## Main results

* `NLAlib.LDL.Certification.countPoly_program`: the actual fixed tree's literal polynomial.
* `NLAlib.LDL.Certification.eval_countPoly_program`: its closed size-only work expression.
* `NLAlib.LDL.Certification.staticPeak_program_le`: the closed additional scratch allowance.
-/

@[expose] public section

namespace NLAlib.LDL.Certification

open Ops

/-- The fixed scalar LDL program, before its order, matrix, interpreter and tape are supplied. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 1 3 :=
  (factor (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 1 3

/-- Full instruction work and sequential span, including all structural charges. -/
def work (d : Fin 1 → ℕ) : ℕ :=
  22 * d 0 ^ 3 + 141 * d 0 ^ 2 + 255 * d 0 + 93

/-- Additional scoped storage, counted in the model's abstract unit-width cells. -/
def scratch (d : Fin 1 → ℕ) : ℕ := 2 * (d 0 * d 0) + 2 * d 0 + 3

/-- The polynomial is computed by the kernel from the actual instrumented LDL tree. -/
theorem countPoly_program :
    program.countPoly = [(141, [0, 0]), (22, [0, 0, 0]), (255, [0]), (93, [])] := by
  kernel_rfl

/-- The literal instruction polynomial has the stated closed cubic value at every order. -/
theorem eval_countPoly_program (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

/-- The actual fixed tree's additional scratch is bounded by the temporary upper factor,
residual, two saved vectors
and three scalar cells. No successful execution, input matrix or positive-order premise occurs. -/
theorem staticPeak_program_le (d : Fin 1 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  change stmtPeak ScalarIndex.resources.workspace
    (factor (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body [n, 0, 0, 0] ≤ _
  have h0 : (Finset.range n).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  have h2 : (Finset.range n).sup (fun _ : ℕ => 1 + (1 + 0)) ≤ 2 :=
    Finset.sup_le (fun _ _ => by omega)
  have h3 : (Finset.range n).sup (fun _ : ℕ =>
      n + (n + (1 + (Finset.range n).sup (fun _ : ℕ => 1 + (1 + 0))))) ≤ 2 * n + 3 :=
    Finset.sup_le (fun _ _ => by omega)
  change _ ≤ 2 * (n * n) + 2 * n + 3
  simpa [factor, copyDiagonal, LU.factor, LU.initializeFactors, LU.step,
    LU.materializeColumn, LU.materializeUpper, LU.normalizeColumn, LU.schurStepTotal,
    LU.schurStep, LU.pivotSaved, LU.rankOne, LU.schurColumn, copyLoopRoutine, copyLoop,
    scalLoopRoutine, scalLoop, axpyLoopRoutine, axpyLoop, fillRoutine, fillMap,
    copyStridedRoutine, stmtPeak, ScalarIndex.resources, Stmt.alloc, IExp.eval, IExp.evalList,
    Stmt.ifPos, h0, two_mul, Nat.add_assoc] using
    (Finset.sup_le (s := Finset.range (1 - (1 - n)))
      (fun _ _ => Nat.add_le_add_left (Nat.add_le_add_left h3 (n * n)) (n * n)))

end NLAlib.LDL.Certification
