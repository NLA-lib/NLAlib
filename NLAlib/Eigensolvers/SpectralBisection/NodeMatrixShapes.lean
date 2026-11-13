/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.MatrixShapes

/-!
# Matrix-call shapes through the bisection node

Bounded split queries restrict both child dimensions. Shape-independent scalar fragments
are discharged by the generic operation checker on the actual source tree.

## Main results

* `NLAlib.SpectralBisection.node_matrixShapes`: all node matrix dimensions fit the root.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private theorem projectors_shape (n k cap : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (nodeProjectors (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([k, cap] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · refine callsSatisfy_stmtCost_frame (d := [k, cap]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => sign_matrixShapes n k cap os hk
  · exact matrixShapes_of_allOps n _ (by rfl) _

private theorem split_shape (n d lo k r : ℕ) (offs : List ℕ) (hk : k ≤ n) (hr : r ≤ k) :
    (stmtCost (split (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, d, lo, k, r] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · refine callsSatisfy_stmtCost_frame (d := [n, k, r, lo, 0]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => deflate_matrixShapes n k r lo 0 os hk
  · refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
    · refine callsSatisfy_stmtCost_frame (d := [n, k, k - r, lo, 1])
        (P := MatrixShape n) ?_ ?_
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => deflate_matrixShapes n k (k - r) lo 1 os hk
    · refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
      · refine callsSatisfy_stmtCost_frame (d := [k, r]) (P := MatrixShape n) ?_ ?_
        · simp [IExp.evalList, IExp.eval]
        · exact fun os => compress_matrixShapes n k r os hk (hr.trans hk)
      · refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
        · refine callsSatisfy_stmtCost_frame (d := [k, k - r]) (P := MatrixShape n) ?_ ?_
          · simp [IExp.evalList, IExp.eval]
          · exact fun os => compress_matrixShapes n k (k - r) os hk ((Nat.sub_le ..).trans hk)
        · exact matrixShapes_of_allOps n _ (by rfl) _

private theorem prepare_shape (n L cap d lo k : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (nodePrepare (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, L, cap, d, lo, k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine callsSatisfy_stmtCost_frame (d := [k, cap]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => projectors_shape n k cap os hk

private theorem branch_shape (n d lo k r : ℕ) (offs : List ℕ) (hk : k ≤ n) (hr : r ≤ k) :
    (stmtCost (nodeBranch (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, d, lo, k, r] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_sum _ _ (MatrixShape n)).mpr ?_
  intro i hi
  refine callsSatisfy_stmtCost_frame (d := [n, d, lo, k, r]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => split_shape n d lo k r os hk hr

private theorem nodeBody_shape (n L cap d lo k : ℕ) (offs : List ℕ)
    (hlen : offs.length = 17) (hk : k ≤ n) :
    (stmtCost (nodeBody (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, L, cap, d, lo, k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · refine callsSatisfy_stmtCost_frame (d := [n, L, cap, d, lo, k])
      (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => prepare_shape n L cap d lo k os hk
  · refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
      ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
    refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
      ⟨Count.callsSatisfy_test _ _ _, ?_⟩
    refine (Count.callsSatisfy_finset_sup _ _ (MatrixShape n)).mpr ?_
    intro r hr
    have hrk : r ≤ k := by
      simpa [IExp.eval] using Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    refine callsSatisfy_stmtCost_frame (d := [n, d, lo, k, r]) (P := MatrixShape n) ?_ ?_
    · simp [IExp.evalList, IExp.eval, hlen]
    · exact fun os => branch_shape n d lo k r os hk hrk

/-- All static matrix-call shapes in a node are root bounded, including all permitted
split-query results. Node scratch allocation changes neither logical matrix dimension. -/
theorem node_matrixShapes (n L cap d lo k : ℕ) (offs : List ℕ) (hk : k ≤ n) :
    (stmtCost (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, L, cap, d, lo, k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine callsSatisfy_stmtCost_frame_of_length (d := [n, L, cap, d, lo, k])
    (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os hos => nodeBody_shape n L cap d lo k os hos hk

end NLAlib.SpectralBisection
