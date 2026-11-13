/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Workspace

/-!
# Composing the node's stored workspace

These bounds follow the real nested frames and allocations, with primitive workspace zero.
The projectors retain their matrix-sign scratch only while sign runs; the later deflation
and compression buffers therefore share that peak reservation.

## Main results

* `NLAlib.SpectralBisection.stmtPeak_nodeProjectors_zero_le`: matrix-sign scratch.
* `NLAlib.SpectralBisection.stmtPeak_split_zero_le`: deflation and compression scratch.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has MatrixOp Op]

/-- Projector construction uses only the sign program's two square pair matrices and
five scalar cells beyond its caller-owned matrix buffers. -/
theorem stmtPeak_nodeProjectors_zero_le [Has CmpTst Tst]
    (k cap : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (nodeProjectors (Tst := Tst)).body
      ([k, cap] ++ offs) ≤ 4 * (k * k) + 5 := by
  apply max_le
  · apply stmtPeak_frame_le (d := [k, cap])
    · simp [IExp.evalList, IExp.eval]
    · intro os
      exact le_of_eq (stmtPeak_sign_zero _ k cap os)
  · rw [stmtPeak_zero_of_allocationFree (by rfl)]
    exact Nat.zero_le _

/-- The two deflations and two compressions execute sequentially. For any bounded split,
their extra stored scratch is at most four square pair matrices, including empty children. -/
theorem stmtPeak_split_zero_le (n d lo k kp : ℕ) (offs : List ℕ) (hp : kp ≤ k) :
    stmtPeak (fun (_ : Op) _ => 0) (split (Tst := Tst))
      ([n, d, lo, k, kp] ++ offs) ≤ 8 * (k * k) := by
  apply max_le
  · apply stmtPeak_frame_le (d := [n, k, kp, lo, 0])
    · simp [IExp.evalList, IExp.eval]
    · intro os
      exact le_of_eq (stmtPeak_deflate_zero n k kp lo 0 os)
  · apply max_le
    · apply stmtPeak_frame_le (d := [n, k, k - kp, lo, 1])
      · simp [IExp.evalList, IExp.eval]
      · intro os
        exact le_of_eq (stmtPeak_deflate_zero n k (k - kp) lo 1 os)
    · apply max_le
      · apply stmtPeak_frame_le (d := [k, kp])
        · simp [IExp.evalList, IExp.eval]
        · exact fun os => stmtPeak_compress_zero_le k kp os hp
      · apply max_le
        · apply stmtPeak_frame_le (d := [k, k - kp])
          · simp [IExp.evalList, IExp.eval]
          · exact fun os => stmtPeak_compress_zero_le k (k - kp) os (Nat.sub_le ..)
        · rw [stmtPeak_zero_of_allocationFree (by rfl)]
          exact Nat.zero_le _

/-- The shift and scalar-parameter stages allocate nothing; preparation's only nested
stored scratch is the sign iteration used to form the projectors. -/
theorem stmtPeak_nodePrepare_zero_le [Has CmpTst Tst]
    (n L cap d lo k : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (nodePrepare (Tst := Tst))
      ([n, L, cap, d, lo, k] ++ offs) ≤ 4 * (k * k) + 5 := by
  apply max_le
  · rw [stmtPeak_zero_of_allocationFree (by rfl)]
    exact Nat.zero_le _
  · apply max_le
    · rw [stmtPeak_zero_of_allocationFree (by rfl)]
      exact Nat.zero_le _
    · apply max_le
      · rw [stmtPeak_zero_of_allocationFree (by rfl)]
        exact Nat.zero_le _
      · apply stmtPeak_frame_le (d := [k, cap])
        · simp [IExp.evalList, IExp.eval]
        · exact stmtPeak_nodeProjectors_zero_le k cap

/-- One-child branches allocate nothing and a two-child branch uses the shared sequential
deflation/compression reservation. The guarded trip counts do not multiply the peak. -/
theorem stmtPeak_nodeBranch_zero_le (n d lo k kp : ℕ) (offs : List ℕ)
    (hp : kp ≤ k) :
    stmtPeak (fun (_ : Op) _ => 0) (nodeBranch (Tst := Tst))
      ([n, d, lo, k, kp] ++ offs) ≤ 8 * (k * k) := by
  apply max_le
  · rw [stmtPeak_zero_of_allocationFree (by rfl)]
    exact Nat.zero_le _
  · apply max_le
    · rw [stmtPeak_zero_of_allocationFree (by rfl)]
      exact Nat.zero_le _
    · apply Finset.sup_le
      intro i hi
      apply stmtPeak_frame_le (d := [n, d, lo, k, kp])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => stmtPeak_split_zero_le n d lo k kp os hp

/-- The caller-owned node stages share their nested sign and split scratch reservation.
The offset length is the actual seventeen-operand frame shape, locating its bounded query. -/
theorem stmtPeak_nodeBody_zero_le [Has CmpTst Tst] [Has IdxTst Tst]
    (n L cap d lo k : ℕ) (offs : List ℕ) (hlen : offs.length = 17) :
    stmtPeak (fun (_ : Op) _ => 0) (nodeBody (Tst := Tst))
      ([n, L, cap, d, lo, k] ++ offs) ≤ max (4 * (k * k) + 5) (8 * (k * k)) := by
  apply max_le
  · apply stmtPeak_frame_le (d := [n, L, cap, d, lo, k])
    · simp [IExp.evalList, IExp.eval]
    · intro os
      exact (stmtPeak_nodePrepare_zero_le n L cap d lo k os).trans (Nat.le_max_left ..)
  · apply max_le
    · rw [stmtPeak_zero_of_allocationFree (by rfl)]
      exact Nat.zero_le _
    · apply Finset.sup_le
      intro kp hkp
      have hp : kp ≤ k := by
        simpa [IExp.eval] using Nat.le_of_lt_succ (Finset.mem_range.mp hkp)
      apply stmtPeak_frame_le (d := [n, d, lo, k, kp])
      · simp [IExp.evalList, IExp.eval, hlen]
      · intro os
        exact (stmtPeak_nodeBranch_zero_le n d lo k kp os hp).trans (Nat.le_max_right ..)

/-- With a root dimension at least two, every bounded node needs at most eighteen root
square words and nine scalar cells. This includes its seven live allocations and all
nested sign, deflation and compression buffers, but excludes primitive workspace. -/
theorem stmtPeak_node_zero_le [Has CmpTst Tst] [Has IdxTst Tst]
    (n L cap d lo k : ℕ) (offs : List ℕ) (hn : 2 ≤ n) (hk : k ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (node (Tst := Tst))
      ([n, L, cap, d, lo, k] ++ offs) ≤ 18 * (n * n) + 9 := by
  simp only [node, stmtPeak_alloc]
  have hkk := Nat.mul_le_mul hk hk
  have hmax : max (4 * (k * k) + 5) (8 * (k * k)) ≤ 8 * (n * n) := by
    apply max_le <;> nlinarith
  suffices hb : stmtPeak (fun (_ : Op) _ => 0)
      (.frame [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5]
        [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨2, .var 8⟩, ⟨3, .var 9⟩,
          ⟨4, .var 10⟩, ⟨5, .var 11⟩, ⟨6, .var 12⟩, ⟨7, .var 13⟩,
          ⟨8, .var 14⟩, ⟨9, .var 15⟩, ⟨10, .const 0⟩, ⟨11, .const 0⟩,
          ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨14, .const 0⟩, ⟨15, .const 0⟩,
          ⟨16, .const 0⟩] (nodeBody (Op := Op) (Tst := Tst)))
      ([n, L, cap, d, lo, k] ++ offs) ≤ 8 * (n * n) by
    simp [IExp.eval] at hb ⊢
    nlinarith
  apply stmtPeak_frame_le_of_length (d := [n, L, cap, d, lo, k])
  · simp [IExp.evalList, IExp.eval]
  · intro os hos
    exact (stmtPeak_nodeBody_zero_le n L cap d lo k os hos).trans hmax

end NLAlib.SpectralBisection
