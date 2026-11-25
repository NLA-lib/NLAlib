/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightLooking
public import NLAlib.Matrix.Factorizations.Cholesky.Semidefinite
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.Static

/-!
# Closed resources of scalar right-looking Cholesky

The positive-definite and zero-safe semidefinite routines are fixed scalar programs.
Their complete instruction counts include addressing, queries, frames and arithmetic.
The additional scratch allowance is the copied square residual, two saved Schur vectors
and three scalar cells. Caller source and factor capacities are charged separately.
All bounds include order zero and are statements about the abstract sequential model.

## Main results

* `NLAlib.Cholesky.Certification.countPoly_program`: the positive-definite instruction count.
* `NLAlib.Cholesky.SemidefiniteCertification.countPoly_program`: the guarded instruction count.
* The two `staticPeak_program_le` theorems bound the actual programs' scoped storage.
-/

@[expose] public section

namespace NLAlib.Cholesky.Certification

open Ops

/-- The fixed scalar program before any order, input matrix or interpretation is supplied. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 1 2 :=
  (rightLooking (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 1 2

/-- Closed work and sequential span, including all scalar and structural instructions. -/
def work (d : Fin 1 → ℕ) : ℕ := 22 * d 0 ^ 3 + 115 * d 0 ^ 2 + 167 * d 0 + 56

/-- Additional scoped residual, two saved vectors and three scalar cells. -/
def scratch (d : Fin 1 → ℕ) : ℕ := d 0 * d 0 + 2 * d 0 + 3

/-- The kernel computes this literal polynomial from the actual instrumented routine tree. -/
theorem countPoly_program :
    program.countPoly = [(22, [0, 0, 0]), (115, [0, 0]), (167, [0]), (56, [])] := by
  kernel_rfl

/-- Evaluation of the actual instruction polynomial is the stated size-only cubic. -/
theorem eval_countPoly_program (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

/-- Every order satisfies the closed additional scratch bound, independently of the input,
interpreter and whether any execution has been supplied. -/
theorem staticPeak_program_le (d : Fin 1 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  change stmtPeak ScalarIndex.resources.workspace
    (rightLooking (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body [n, 0, 0] ≤ _
  have h0 : (Finset.range n).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  have h2 : (Finset.range n).sup (fun _ : ℕ => 1 + (1 + 0)) ≤ 2 :=
    Finset.sup_le (fun _ _ => by omega)
  have h4 : (Finset.range n).sup (fun _ : ℕ =>
      max 1 (n + (n + (1 + (Finset.range n).sup (fun _ : ℕ => 1 + (1 + 0)))))) ≤
      2 * n + 3 := Finset.sup_le (fun _ _ => by omega)
  change _ ≤ n * n + 2 * n + 3
  simpa [rightLooking, rightWithScratch, rightLoop, rightStep, initializeLower,
    rightColumn, LU.schurStep,
    LU.pivotSaved, LU.rankOne, LU.schurColumn, copyLoopRoutine, copyLoop,
    scalLoopRoutine, scalLoop, axpyLoopRoutine, axpyLoop, fillRoutine, fillMap,
    copyStridedRoutine, stmtPeak, ScalarIndex.resources, Stmt.alloc, IExp.eval, IExp.evalList,
    Stmt.ifPos, h0, Nat.add_assoc] using
    (Finset.sup_le (s := Finset.range (1 - (1 - n)))
      (fun _ _ => Nat.add_le_add_left h4 (n * n)))

end NLAlib.Cholesky.Certification

namespace NLAlib.Cholesky.SemidefiniteCertification

open Ops

/-- The fixed scalar program before any order, input matrix or interpretation is supplied. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 1 2 :=
  (semidefiniteRightLooking (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 1 2

/-- Closed work and sequential span, including all scalar and structural instructions. -/
def work (d : Fin 1 → ℕ) : ℕ := 22 * d 0 ^ 3 + 121 * d 0 ^ 2 + 198 * d 0 + 56

/-- Additional scoped residual, two saved vectors and three scalar cells. -/
def scratch (d : Fin 1 → ℕ) : ℕ := d 0 * d 0 + 2 * d 0 + 3

/-- The kernel computes this literal polynomial from the actual instrumented routine tree. -/
theorem countPoly_program :
    program.countPoly = [(198, [0]), (121, [0, 0]), (22, [0, 0, 0]), (56, [])] := by
  kernel_rfl

/-- Evaluation of the actual instruction polynomial is the stated size-only cubic. -/
theorem eval_countPoly_program (d : Fin 1 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

/-- Every order satisfies the closed additional scratch bound, independently of the input,
interpreter and whether any execution has been supplied. -/
theorem staticPeak_program_le (d : Fin 1 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  let n := d 0
  change stmtPeak ScalarIndex.resources.workspace
    (semidefiniteRightLooking
      (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body [n, 0, 0] ≤ _
  have h0 : (Finset.range n).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  have h2 : (Finset.range n).sup (fun _ : ℕ => 1 + (1 + 0)) ≤ 2 :=
    Finset.sup_le (fun _ _ => by omega)
  have h4 : (Finset.range n).sup (fun _ : ℕ =>
      max 1 (n + (n + (1 + (Finset.range n).sup (fun _ : ℕ => 1 + (1 + 0)))))) ≤
      2 * n + 3 := Finset.sup_le (fun _ _ => by omega)
  change _ ≤ n * n + 2 * n + 3
  simpa [semidefiniteRightLooking, semidefiniteRightWithScratch, rightLoopTotal, rightStepTotal,
    rightStep, initializeLower,
    rightColumn, LU.schurStep,
    LU.pivotSaved, LU.rankOne, LU.schurColumn, copyLoopRoutine, copyLoop,
    scalLoopRoutine, scalLoop, axpyLoopRoutine, axpyLoop, fillRoutine, fillMap,
    copyStridedRoutine, stmtPeak, ScalarIndex.resources, Stmt.alloc, IExp.eval, IExp.evalList,
    Stmt.ifPos, h0, Nat.add_assoc] using
    (Finset.sup_le (s := Finset.range (1 - (1 - n)))
      (fun _ _ => Nat.add_le_add_left h4 (n * n)))

end NLAlib.Cholesky.SemidefiniteCertification

