/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.NodeMatrixShapes

/-!
# Matrix-call shapes in the downward traversal

The stored-size query's declared bound suffices for every conservative static branch.
No assertion about the contents of size metadata is needed for this syntactic result.

## Main results

* `NLAlib.SpectralBisection.downwardPass_matrixShapes`: root-bounded downward matrix calls.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private theorem downLarge_shape (n L cap d lo k : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (downLargeImpl (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))).body
      ([n, L, cap, d, lo, k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨callsSatisfy_testCost _ _ _ _, ?_⟩
  refine (Count.callsSatisfy_sup _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine callsSatisfy_stmtCost_frame (d := [n, L, cap, d, lo, k])
    (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => node_matrixShapes n L cap d lo k os hk

private theorem downNode_shape (n L cap d lo k : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (downNodeImpl (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))).body
      ([n, L, cap, d, lo, k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_sum _ _ (MatrixShape n)).mpr ?_
  intro i hi
  refine callsSatisfy_stmtCost_frame (d := [n, L, cap, d, lo, k])
    (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => downLarge_shape n L cap d lo k os hk

private theorem downNodes_shape (n L cap d : ℕ) (offs : List ℕ) (hlen : offs.length = 13) :
    (stmtCost (downNodesImpl (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))).body
      ([n, L, cap, d] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_sum _ _ (MatrixShape n)).mpr ?_
  intro lo hlo
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨Count.callsSatisfy_test _ _ _, ?_⟩
  refine (Count.callsSatisfy_finset_sup _ _ (MatrixShape n)).mpr ?_
  intro k hk
  have hkn : k ≤ n := by
    have hb := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    simp [IExp.eval, hlen] at hb
    omega
  refine (Count.callsSatisfy_sum _ _ (MatrixShape n)).mpr ?_
  intro i hi
  refine callsSatisfy_stmtCost_frame (d := [n, L, cap, d, lo, k])
    (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os => downNode_shape n L cap d lo k os hkn

private theorem downLevelImpl_shape (n L cap d : ℕ) (offs : List ℕ) :
    (stmtCost (downLevelImpl (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))).body
      ([n, L, cap, d] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine callsSatisfy_stmtCost_frame_of_length (d := [n, L, cap, d])
    (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os hos => downNodes_shape n L cap d os hos

private theorem downLevel_shape (n L cap d : ℕ) (offs : List ℕ) :
    (stmtCost (downLevel (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)))
      ([n, L, cap, d] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine callsSatisfy_stmtCost_frame (d := [n, L, cap, d]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => downLevelImpl_shape n L cap d os

/-- Every downward matrix operation has a legal shape bounded by the root dimension.
The result covers every depth and bounded size-query choice in the static manifest. -/
theorem downwardPass_matrixShapes (n L cap : ℕ) (offs : List ℕ)
    (hlen : offs.length = 12) :
    (stmtCost (downwardPass (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))).body
      ([n, L, cap] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_sum _ _ (MatrixShape n)).mpr ?_
  intro d hd
  refine callsSatisfy_stmtCost_frame (d := [n, L, cap, d]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os => downLevel_shape n L cap d os

end NLAlib.SpectralBisection
