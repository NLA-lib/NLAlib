/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Eigensolvers.SpectralBisection.NodeWorkspace

/-!
# Workspace shared by the level traversals

Every slot reuses the same node scratch. Bounded size queries give dimensions at most the
root size even when inspecting the conservative static workspace function. These estimates
exclude primitive workspace and count stored cells in the actual statement trees.

## Main results

* `NLAlib.SpectralBisection.stmtPeak_downNodes_zero_le`: slot loops share node scratch.
* `NLAlib.SpectralBisection.stmtPeak_downLevel_zero_le`: five level scratch cells plus nodes.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has MatrixOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- A large slot either writes a leaf without allocation or executes the actual node. -/
theorem stmtPeak_downLarge_zero_le (n L cap d lo k : ℕ) (offs : List ℕ)
    (hn : 2 ≤ n) (hk : k ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (downLargeImpl (node (Op := Op) (Tst := Tst))).body
      ([n, L, cap, d, lo, k] ++ offs) ≤ 18 * (n * n) + 9 := by
  apply max_le
  · rw [stmtPeak_zero_of_allocationFree (by rfl)]
    exact Nat.zero_le _
  · apply max_le
    · rw [stmtPeak_zero_of_allocationFree (by rfl)]
      exact Nat.zero_le _
    · apply stmtPeak_frame_le (d := [n, L, cap, d, lo, k])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => stmtPeak_node_zero_le n L cap d lo k os hn hk

/-- The one-dimensional leaf branch allocates nothing; every other active slot shares the
root-size node scratch reservation. Guarded trip counts do not accumulate stored scratch. -/
theorem stmtPeak_downNode_zero_le (n L cap d lo k : ℕ) (offs : List ℕ)
    (hn : 2 ≤ n) (hk : k ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (downNodeImpl (node (Op := Op) (Tst := Tst))).body
      ([n, L, cap, d, lo, k] ++ offs) ≤ 18 * (n * n) + 9 := by
  apply max_le
  · rw [stmtPeak_zero_of_allocationFree (by rfl)]
    exact Nat.zero_le _
  · apply Finset.sup_le
    intro i hi
    apply stmtPeak_frame_le (d := [n, L, cap, d, lo, k])
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => stmtPeak_downLarge_zero_le n L cap d lo k os hn hk

/-- The actual size query is bounded by the unused root slots. Every possible returned
size therefore fits the same peak reservation, independently of the number of occupied slots. -/
theorem stmtPeak_downNodes_zero_le (n L cap d : ℕ) (offs : List ℕ)
    (hlen : offs.length = 13) (hn : 2 ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (downNodesImpl (node (Op := Op) (Tst := Tst))).body
      ([n, L, cap, d] ++ offs) ≤ 18 * (n * n) + 9 := by
  apply Finset.sup_le
  intro lo hlo
  apply Finset.sup_le
  intro k hk
  have hkn : k ≤ n := by
    have hb := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    simp [IExp.eval, hlen] at hb
    omega
  apply Finset.sup_le
  intro i hi
  apply stmtPeak_frame_le (d := [n, L, cap, d, lo, k])
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os => stmtPeak_downNode_zero_le n L cap d lo k os hn hkn

variable [Has SampleOp Op]

/-- Sampling and parameter computation allocate no stored buffers. The prepared slot loop
uses the same node reservation for every position in the level. -/
theorem stmtPeak_downLevelImpl_zero_le (n L cap d : ℕ) (offs : List ℕ)
    (hn : 2 ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (downLevelImpl (node (Op := Op) (Tst := Tst))).body
      ([n, L, cap, d] ++ offs) ≤ 18 * (n * n) + 9 := by
  apply max_le
  · rw [stmtPeak_zero_of_allocationFree (by rfl)]
    exact Nat.zero_le _
  · apply stmtPeak_frame_le_of_length (d := [n, L, cap, d])
    · simp [IExp.evalList, IExp.eval]
    · exact fun os hos => stmtPeak_downNodes_zero_le n L cap d os hos hn

/-- A complete downward level adds five caller-owned scalar scratch cells to the reusable
node reservation. The result is independent of the sign iteration cap and level number. -/
theorem stmtPeak_downLevel_zero_le (n L cap d : ℕ) (offs : List ℕ) (hn : 2 ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (downLevel (node (Op := Op) (Tst := Tst)))
      ([n, L, cap, d] ++ offs) ≤ 18 * (n * n) + 14 := by
  simp only [downLevel, stmtPeak_alloc]
  have hb : stmtPeak (fun (_ : Op) _ => 0)
      (.frame [.var 0, .var 1, .var 2, .var 3]
        [⟨0, .var 4⟩, ⟨1, .var 5⟩, ⟨2, .var 6⟩, ⟨3, .var 7⟩,
          ⟨4, .var 8⟩, ⟨5, .var 9⟩, ⟨6, .var 10⟩, ⟨7, .var 11⟩,
          ⟨8, .var 12⟩, ⟨9, .var 13⟩, ⟨10, .var 14⟩, ⟨11, .var 15⟩,
          ⟨12, .const 0⟩] (downLevelImpl (node (Op := Op) (Tst := Tst))).body)
      ([n, L, cap, d] ++ offs) ≤ 18 * (n * n) + 9 := by
    apply stmtPeak_frame_le (d := [n, L, cap, d])
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => stmtPeak_downLevelImpl_zero_le n L cap d os hn
  simp [IExp.eval] at hb ⊢
  omega

end NLAlib.SpectralBisection
