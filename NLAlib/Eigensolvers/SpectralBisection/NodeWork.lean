/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Node
public import NLAlib.Eigensolvers.SpectralBisection.SignWork

/-!
# Weighted matrix work of one bisection node

Weights are applied before maximizing bounded query answers. Every called matrix kernel
has largest dimension exactly the local node size, including rectangular compression.

## Main results

* `NLAlib.SpectralBisection.node_matrixWork_le`: capped sign plus eight split kernels.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable (T : ℕ → ℕ)

local notation "mw" => Dense.matrixWeight (MatrixOp.dimensionWeight T)
local notation "qz" => (fun (_ : CmpTst ⊕ IdxTst) (_ : List ℕ) => 0)

private theorem deflate_work (n k r lo side : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (deflate (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([n, k, r, lo, side] ++ offs) ≤ 2 * T k := by
  calc
    _ ≤ 0 + (T k + (T k + 0)) := Nat.add_le_add
      (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      (Nat.add_le_add ?_ (Nat.add_le_add ?_
        (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))))
    _ = _ := by omega
  · change T (max k (max k (max k 0))) ≤ T k
    simp
  · change T (max k (max k 0)) ≤ T k
    simp

private theorem compress_work (k r : ℕ) (offs : List ℕ) (hr : r ≤ k) :
    stmtWeightedCost mw qz (compress (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([k, r] ++ offs) ≤ 2 * T k := by
  calc
    _ ≤ 0 + (T k + (T k + 0)) := Nat.add_le_add
      (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      (Nat.add_le_add ?_ (Nat.add_le_add ?_
        (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))))
    _ = _ := by omega
  · change T (max r (max k (max k 0))) ≤ T k
    simp [max_eq_right hr]
  · change T (max r (max k (max r 0))) ≤ T k
    simp [max_eq_left hr, max_eq_right hr]

private theorem projectors_work (k cap : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (nodeProjectors (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      ([k, cap] ++ offs) ≤ (2 * cap + 1) * T k := by
  calc
    _ ≤ (2 * cap + 1) * T k + 0 := Nat.add_le_add ?_
      (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
    _ = _ := Nat.add_zero _
  apply stmtWeightedCost_frame_le (d := [k, cap])
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => sign_matrixWork_le T k cap os

private theorem split_work (n d lo k r : ℕ) (offs : List ℕ) (hr : r ≤ k) :
    stmtWeightedCost mw qz (split (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, d, lo, k, r] ++ offs) ≤ 8 * T k := by
  calc
    _ ≤ 2 * T k + (2 * T k + (2 * T k + (2 * T k + 0))) :=
      Nat.add_le_add ?_ (Nat.add_le_add ?_ (Nat.add_le_add ?_ (Nat.add_le_add ?_
        (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _)))))
    _ = _ := by omega
  · apply stmtWeightedCost_frame_le (d := [n, k, r, lo, 0])
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => deflate_work T n k r lo 0 os
  · apply stmtWeightedCost_frame_le (d := [n, k, k - r, lo, 1])
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => deflate_work T n k (k - r) lo 1 os
  · apply stmtWeightedCost_frame_le (d := [k, r])
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => compress_work T k r os hr
  · apply stmtWeightedCost_frame_le (d := [k, k - r])
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => compress_work T k (k - r) os (Nat.sub_le ..)

private theorem prepare_work (n L cap d lo k : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (nodePrepare (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, L, cap, d, lo, k] ++ offs) ≤ (2 * cap + 1) * T k := by
  calc
    _ ≤ 0 + (0 + (0 + (2 * cap + 1) * T k)) := by
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply stmtWeightedCost_frame_le (d := [k, cap])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => projectors_work T k cap os
    _ = _ := by omega

private theorem branch_work (n d lo k r : ℕ) (offs : List ℕ) (hr : r ≤ k) :
    stmtWeightedCost mw qz (nodeBranch (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, d, lo, k, r] ++ offs) ≤ 8 * T k := by
  calc
    _ ≤ 0 + (0 + 8 * T k) := by
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply stmtWeightedCost_ifZero_le
      intro i
      apply stmtWeightedCost_frame_le (d := [n, d, lo, k, r])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => split_work T n d lo k r os hr
    _ = _ := by omega

private theorem nodeBody_work (n L cap d lo k : ℕ) (offs : List ℕ)
    (hlen : offs.length = 17) :
    stmtWeightedCost mw qz (nodeBody (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, L, cap, d, lo, k] ++ offs) ≤ (2 * cap + 9) * T k := by
  calc
    _ ≤ (2 * cap + 1) * T k + (0 + 8 * T k) := by
      apply Nat.add_le_add
      · apply stmtWeightedCost_frame_le (d := [n, L, cap, d, lo, k])
        · simp [IExp.evalList, IExp.eval]
        · exact fun os => prepare_work T n L cap d lo k os
      · apply Nat.add_le_add
          (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
        change 0 + _ ≤ _
        rw [Nat.zero_add]
        apply Finset.sup_le
        intro r hr
        have hrk : r ≤ k := by
          simpa [IExp.eval] using Nat.le_of_lt_succ (Finset.mem_range.mp hr)
        apply stmtWeightedCost_frame_le (d := [n, d, lo, k, r])
        · simp [IExp.evalList, IExp.eval, hlen]
        · exact fun os => branch_work T n d lo k r os hrk
    _ = _ := by ring

/-- A nonleaf node's capped sign iteration contributes at most 2cap+1 matrix products;
a split contributes eight further multiplication/QR calls. All have maximum dimension k.
The bound does not require monotonicity or superadditivity of the supplied weight function. -/
theorem node_matrixWork_le (n L cap d lo k : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (node (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      ([n, L, cap, d, lo, k] ++ offs) ≤ (2 * cap + 9) * T k := by
  apply stmtWeightedCost_frame_le_of_length (d := [n, L, cap, d, lo, k])
  · simp [IExp.evalList, IExp.eval]
  · exact fun os hos => nodeBody_work T n L cap d lo k os hos

end NLAlib.SpectralBisection
