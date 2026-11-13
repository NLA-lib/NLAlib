/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Eigensolvers.SpectralBisection.NodeWork

/-!
# Weighted matrix work of active-slot dispatch

Scalar threshold computation and both terminal leaf paths have zero matrix-kernel weight.
The explicit guards execute their bodies at most once.

## Main results

* `NLAlib.SpectralBisection.downNode_matrixWork_le`: local kernel bound for slot iteration.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable (T : ℕ → ℕ)

local notation "mw" => Dense.matrixWeight (MatrixOp.dimensionWeight T)
local notation "qz" => (fun (_ : CmpTst ⊕ IdxTst) (_ : List ℕ) => 0)

/-- The large-node branch either terminates without matrix kernels or executes one node. -/
theorem downLarge_matrixWork_le (n L cap d lo k : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz
      (downLargeImpl (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))).body
      ([n, L, cap, d, lo, k] ++ offs) ≤ (2 * cap + 9) * T k := by
  calc
    _ ≤ 0 + (0 + max 0 ((2 * cap + 9) * T k)) := by
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply Nat.add_le_add
      · simp [IExp.evalList]
      · apply max_le_max
        · exact le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _)
        · apply stmtWeightedCost_frame_le (d := [n, L, cap, d, lo, k])
          · simp [IExp.evalList, IExp.eval]
          · exact fun os => node_matrixWork_le T n L cap d lo k os
    _ = _ := by simp

/-- Active-slot dispatch preserves the local node's kernel bound. Both leaf paths are
matrix free, and the zero-or-one-trip guard does not multiply this bound by the node size. -/
theorem downNode_matrixWork_le (n L cap d lo k : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz
      (downNodeImpl (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))).body
      ([n, L, cap, d, lo, k] ++ offs) ≤ (2 * cap + 9) * T k := by
  calc
    _ ≤ 0 + (2 * cap + 9) * T k := by
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply stmtWeightedCost_ifZero_le
      intro i
      apply stmtWeightedCost_frame_le (d := [n, L, cap, d, lo, k])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => downLarge_matrixWork_le T n L cap d lo k os
    _ = _ := Nat.zero_add _

end NLAlib.SpectralBisection
