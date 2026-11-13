/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.MatrixShapes

/-!
# Matrix-call shapes in reverse reconstruction

Both child products retain their actual rectangular dimensions. The declared size and split
query bounds constrain all static branches, independently of the stored metadata values.

## Main results

* `NLAlib.SpectralBisection.upwardPass_matrixShapes`: root-bounded reconstruction calls.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private theorem upSplit_shape (n k r : ℕ) (offs : List ℕ) (hk : k ≤ n) (hr : r ≤ k) :
    (stmtCost (upSplitResultImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([k, r] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr ⟨?_, ?_⟩
  · change (Count.one (DenseOp.matrix .mul) [k, r, r] :
      Count DenseOp (CmpTst ⊕ IdxTst)).CallsSatisfy (MatrixShape n)
    exact (Count.callsSatisfy_one _ _ _).mpr ⟨k, r, r, rfl, hk, hr.trans hk, hr.trans hk⟩
  · refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
      ⟨?_, matrixShapes_of_allOps n _ (by rfl) _⟩
    change (Count.one (DenseOp.matrix .mul) [k, k - r, k - r] :
      Count DenseOp (CmpTst ⊕ IdxTst)).CallsSatisfy (MatrixShape n)
    exact (Count.callsSatisfy_one _ _ _).mpr
      ⟨k, k - r, k - r, rfl, hk, (Nat.sub_le ..).trans hk, (Nat.sub_le ..).trans hk⟩

private theorem upNode_shape (n d lo k : ℕ) (offs : List ℕ)
    (hlen : offs.length = 6) (hk : k ≤ n) :
    (stmtCost (upNodeImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([n, d, lo, k] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨Count.callsSatisfy_test _ _ _, ?_⟩
  refine (Count.callsSatisfy_finset_sup _ _ (MatrixShape n)).mpr ?_
  intro kind hkind
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_sum _ _ (MatrixShape n)).mpr ?_
  intro i hi
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨Count.callsSatisfy_test _ _ _, ?_⟩
  refine (Count.callsSatisfy_finset_sup _ _ (MatrixShape n)).mpr ?_
  intro r hr
  have hrk : r ≤ k := by
    simpa [IExp.eval] using Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  refine callsSatisfy_stmtCost_frame (d := [k, r]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os => upSplit_shape n k r os hk hrk

private theorem upNodes_shape (n d : ℕ) (offs : List ℕ) (hlen : offs.length = 7) :
    (stmtCost (upNodesImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([n, d] ++ offs)).CallsSatisfy (MatrixShape n) := by
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
  refine callsSatisfy_stmtCost_frame_of_length (d := [n, d, lo, k])
    (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os hos => upNode_shape n d lo k os hos hkn

private theorem upLevel_shape (n d : ℕ) (offs : List ℕ) :
    (stmtCost (upLevel (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, d] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine (Count.callsSatisfy_add _ _ (MatrixShape n)).mpr
    ⟨matrixShapes_of_allOps n _ (by rfl) _, ?_⟩
  refine callsSatisfy_stmtCost_frame_of_length (d := [n, d]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval]
  · exact fun os hos => upNodes_shape n d os hos

/-- Reverse reconstruction has root-bounded matrix shapes for every bounded metadata query.
Loop depth and shared-arena offsets do not enter the matrix-workspace envelope. -/
theorem upwardPass_matrixShapes (n L : ℕ) (offs : List ℕ) (hlen : offs.length = 8) :
    (stmtCost (upwardPass (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([n, L] ++ offs)).CallsSatisfy (MatrixShape n) := by
  refine (Count.callsSatisfy_sum _ _ (MatrixShape n)).mpr ?_
  intro r hr
  refine callsSatisfy_stmtCost_frame (d := [n, L - r]) (P := MatrixShape n) ?_ ?_
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os => upLevel_shape n (L - r) os

end NLAlib.SpectralBisection
