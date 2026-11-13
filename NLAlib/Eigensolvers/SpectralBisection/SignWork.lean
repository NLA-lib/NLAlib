/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Alg
public import NLAlib.Ops.Profiles.DenseWeight
public import Mathlib.Tactic.Ring

/-!
# Weighted matrix work of the capped sign iteration

The scalar estimator weights each actual matrix call before combining alternative branches.
Scalar operations and queries retain their separate canonical counts.

## Main results

* `NLAlib.SpectralBisection.sign_matrixWork_le`: at most two products per capped round.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable (T : ℕ → ℕ)

local notation "mw" => Dense.matrixWeight (MatrixOp.dimensionWeight T)
local notation "qz" => (fun (_ : CmpTst ⊕ IdxTst) (_ : List ℕ) => 0)

private theorem test_work (k : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (Sign.test (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k] ++ offs) ≤ T k := by
  calc
    _ ≤ T k + 0 := Nat.add_le_add ?_
      (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
    _ = _ := Nat.add_zero _
  change T (max k (max k (max k 0))) ≤ T k
  simp

private theorem step_work (k : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (Sign.step (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k] ++ offs) ≤ T k := by
  calc
    _ ≤ 0 + (0 + (T k + 0)) := Nat.add_le_add
      (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      (Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
        (Nat.add_le_add ?_ (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))))
    _ = _ := by omega
  change T (max k (max k (max k 0))) ≤ T k
  simp

private theorem round_work (k : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (Sign.round (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k] ++ offs) ≤ 2 * T k := by
  calc
    _ ≤ T k + T k := by
      apply Nat.add_le_add
      · apply stmtWeightedCost_frame_le (d := [k])
        · simp [IExp.evalList, IExp.eval]
        · exact fun os => step_work T k os
      · apply stmtWeightedCost_frame_le (d := [k])
        · simp [IExp.evalList, IExp.eval]
        · exact fun os => test_work T k os
    _ = _ := by omega

private theorem loop_work (k cap : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (Sign.loop (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k, cap] ++ offs) ≤ cap * (2 * T k) := by
  calc
    _ ≤ (∑ i ∈ Finset.range cap, 2 * T k) + 0 := by
      apply Nat.add_le_add
      · apply Finset.sum_le_sum
        intro i hi
        simp only [IExp.evalList_nil, Option.map_some, Option.getD_some, Nat.zero_add]
        apply stmtWeightedCost_frame_le (d := [k])
        · simp [IExp.evalList, IExp.eval]
        · exact fun os => round_work T k os
      · simp [stmtWeightedCost]
    _ = _ := by simp

private theorem start_work (k cap : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (Sign.start (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k, cap] ++ offs) ≤ (2 * cap + 1) * T k := by
  calc
    _ ≤ T k + cap * (2 * T k) := by
      apply Nat.add_le_add
      · apply stmtWeightedCost_frame_le (d := [k])
        · simp [IExp.evalList, IExp.eval]
        · exact fun os => test_work T k os
      · apply stmtWeightedCost_frame_le (d := [k, cap])
        · simp [IExp.evalList, IExp.eval]
        · exact fun os => loop_work T k cap os
    _ = _ := by ring

private theorem initialized_work (k cap : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (Sign.initialized (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k, cap] ++ offs) ≤ (2 * cap + 1) * T k := by
  calc
    _ ≤ 0 + (0 + (0 + (2 * cap + 1) * T k)) := by
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply Nat.add_le_add (le_of_eq (stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl) _))
      apply stmtWeightedCost_frame_le (d := [k, cap])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => start_work T k cap os
    _ = _ := by omega

/-- The capped sign implementation uses at most one initial matrix product and two products
per possible loop round. Scalar work and queries are separate; no monotonicity of T is needed. -/
theorem sign_matrixWork_le (k cap : ℕ) (offs : List ℕ) :
    stmtWeightedCost mw qz (Sign.program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
      (Has.inj MatrixOp.mul)).body ([k, cap] ++ offs) ≤ (2 * cap + 1) * T k := by
  apply stmtWeightedCost_frame_le (d := [k, cap])
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => initialized_work T k cap os

end NLAlib.SpectralBisection
