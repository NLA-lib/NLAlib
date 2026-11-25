/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedRoutine
public import NLAlib.Ops.Profiles.ScalarIndex
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.Static

/-!
# Closed resources of actual blocked scalar LU

The literal instruction polynomial counts the actual clipped-panel tree, including the
scalar packing, multiplication, subtraction, and structural instructions. Its arguments are
order, positive block size, and the supplied ceiling block count. Symbolic clipping yields a
conservative polynomial in these three dimensions; oversized blocks need not give a tight
bound. These abstract counts assert no native BLAS throughput or elapsed-time guarantee.

## Main results

* `NLAlib.LU.BlockedCertification.countPoly_program`: actual-tree polynomial equality.
* `NLAlib.LU.BlockedCertification.eval_countPoly_program`: closed dimension-only work.
-/

@[expose] public section

namespace NLAlib.LU.BlockedCertification

open Ops

/-- The fixed blocked scalar LU tree before dimensions, matrix words, interpreter and tape. -/
def program : Program ScalarIndex.Operation ScalarIndex.Queries 3 3 :=
  (factorBlocked (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).close 3 3

/-- Closed full instruction work and sequential span in order, block size and block count. -/
def work (d : Fin 3 → ℕ) : ℕ :=
  395 * d 1 * d 2 + 180 * d 0 * d 1 ^ 2 * d 2 +
    180 * d 0 * d 1 ^ 2 * d 2 ^ 2 + 49 * d 1 ^ 2 * d 2 +
    49 * d 1 ^ 2 * d 2 ^ 2 + 83 * d 0 ^ 2 * d 2 + 22 * d 0 * d 2 +
    33 * d 0 ^ 2 * d 1 * d 2 + 187 * d 0 * d 1 * d 2 + 215 * d 2 +
    22 * d 0 ^ 2 + 75

/-- The kernel computes this polynomial from the actual scalar panels and matrix updates. -/
theorem countPoly_program : program.countPoly =
    [(395, [1, 2]), (180, [0, 1, 1, 2]), (180, [0, 1, 1, 2, 2]),
      (49, [1, 1, 2]), (49, [1, 1, 2, 2]), (83, [0, 0, 2]), (22, [0, 2]),
      (33, [0, 0, 1, 2]), (187, [0, 1, 2]), (215, [2]), (22, [0, 0]), (75, [])] := by
  kernel_rfl

/-- Evaluation of the actual instruction polynomial is the displayed closed expression. -/
theorem eval_countPoly_program (d : Fin 3 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = work d := by
  rw [countPoly_program]
  poly_eval [work]

/-- Additional scoped cells. The allowance covers the residual, the saved pivot vectors,
rank-one workspace and the packed scalar GEMM temporaries; caller buffers are additional. -/
def scratch (d : Fin 3 → ℕ) : ℕ := 5 * d 0 * d 0 + 2 * d 0 + 3

/-- Scratch of the actual blocked routine is independent of the caller's three offsets.
The clipped panel and product extents are bounded by the matrix order even without valid
block controls. This form also supports scoped factorization consumers. -/
theorem stmtPeak_factorBlocked_le (n b q ao lo uo : ℕ) :
    stmtPeak ScalarIndex.resources.workspace
      (factorBlocked (Op := ScalarIndex.Operation) (Tst := ScalarIndex.Queries)).body
      [n, b, q, ao, lo, uo] ≤ 5 * n * n + 2 * n + 3 := by
  have hz (t : ℕ) : (Finset.range t).sup (fun _ : ℕ => 0) = 0 :=
    Finset.sup_eq_zero.mpr (fun _ _ => rfl)
  have htwo (t : ℕ) : (Finset.range t).sup (fun _ : ℕ => 2) ≤ 2 :=
    Finset.sup_le (fun _ _ => le_rfl)
  simp only [factorBlocked, Stmt.ifPos, blockedWithScratch, blockedLoop, blockedStep, panel,
   panelIteration,
   panelSchurStep, preparePanelPivot, panelRectangles, rankOneStridedWithScratch,
   initializeFactors, materializeColumn, materializeUpper, normalizeColumn,
   pivotSaved, rankOne, schurColumn, ScalarMatrix.update, ScalarMatrix.updateWithScratch,
   ScalarMatrix.multiply, ScalarMatrix.columns, ScalarMatrix.column, ScalarProducts.sumRoutine,
   ScalarProducts.sum, ScalarProducts.step,
   copyMatrixRoutine, subtractMatrixRoutine, copyLoopRoutine, copyLoop,
   scalLoopRoutine, scalLoop, axpyLoopRoutine, axpyLoop, fillRoutine, fillMap,
   copyStridedRoutine, stmtPeak, ScalarIndex.resources, Stmt.alloc, IExp.eval, IExp.evalList]
  simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero,
    Option.map_some, Option.bind_some, Option.getD_some, StorageFormat.bytes_cell,
    List.cons_append, List.nil_append, one_mul, Nat.one_lt_ofNat, List.getElem_cons_succ,
    Nat.reduceLT, List.map_cons, List.map_nil, IExp.evalList_cons, IExp.evalList_nil,
    Nat.lt_add_one, Order.lt_two_iff, zero_le, max_self, IExp.eval_mul, IExp.eval_add,
    Finset.sup_le_iff, Finset.mem_range, sup_of_le_left, mul_one, sup_of_le_right,
    le_sup_iff, or_self, hz, Nat.add_zero]
  intro guard hguard
  calc
   _ ≤ n*n + (4*n*n+2*n+3) := Nat.add_le_add_left (Finset.sup_le fun i hi => ?_) _
   _ ≤ _ := by nlinarith
  apply max_le
  · refine Finset.sup_le fun j hj => ?_
    have ha := htwo (b*i+(b-(b-(n-b*i)))-(b*i+j))
    have hb := htwo (n-(b*i+(b-(b-(n-b*i)))))
    have hm := max_le ha hb
    nlinarith
  · have hw : b-(b-(n-b*i)) ≤ n := by omega
    have ht : n-(b*i+(b-(b-(n-b*i)))) ≤ n := Nat.sub_le _ _
    have hh := Nat.mul_le_mul ht hw
    have hh2 := Nat.mul_le_mul hw ht
    have hh3 := Nat.mul_le_mul ht ht
    nlinarith
 

/-- The actual fixed tree has this additional scratch bound for every dimension tuple.
No successful execution or numerical hypothesis occurs in the bound. -/
theorem staticPeak_program_le (d : Fin 3 → ℕ) :
    staticPeak ScalarIndex.resources program d ≤ scratch d := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  exact stmtPeak_factorBlocked_le (d 0) (d 1) (d 2) 0 0 0

end NLAlib.LU.BlockedCertification
