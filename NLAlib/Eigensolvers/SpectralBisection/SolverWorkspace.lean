/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.LevelWorkspace

/-!
# Independent stored-workspace bound for the complete solver

The estimates count the real eleven-arena reservation and the largest nested node scratch.
They do not define the requested bound using the static manifest or static peak. Primitive
workspace is zero here; arbitrary matrix-kernel workspace requires an additional envelope.

## Main results

* `NLAlib.SpectralBisection.stmtPeak_downwardPass_zero_le`: one shared level reservation.
* `NLAlib.SpectralBisection.stmtPeak_solve_zero_le`: complete independent storage polynomial.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has MatrixOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

omit [Has IndexOp Op] [Has CmpTst Tst] in
/-- Reconstruction needs exactly its two scalar shift cells, independently of slot kinds,
sizes or depth. Matrix products' own primitive workspace is excluded. -/
theorem stmtPeak_upLevel_zero (n d : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (upLevel (Tst := Tst)) ([n, d] ++ offs) = 2 := by
  simp only [upLevel, stmtPeak_alloc]
  rw [stmtPeak_zero_of_allocationFree (by rfl)]
  rfl

omit [Has IndexOp Op] [Has CmpTst Tst] in
/-- Reverse reconstruction shares the same two scalar cells between all levels. -/
theorem stmtPeak_upwardPass_zero_le (n L : ℕ) (offs : List ℕ) (hlen : offs.length = 8) :
    stmtPeak (fun (_ : Op) _ => 0) (upwardPass (Tst := Tst)).body
      ([n, L] ++ offs) ≤ 2 := by
  apply Finset.sup_le
  intro r hr
  apply stmtPeak_frame_le (d := [n, L - r])
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os => le_of_eq (stmtPeak_upLevel_zero n (L - r) os)

omit [Has IndexOp Op] [Has CmpTst Tst] in
/-- Bottom identities, zero values and the final copies add no stored scratch beyond the
two scalar cells reused by reverse reconstruction. -/
theorem stmtPeak_reconstructResult_zero_le (n L : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (reconstructResult (Tst := Tst)).body
      ([n, L] ++ offs) ≤ 2 := by
  apply max_le
  · rw [stmtPeak_zero_of_allocationFree (by rfl)]
    exact Nat.zero_le _
  · apply max_le
    · apply stmtPeak_frame_le_of_length (d := [n, L])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os hos => stmtPeak_upwardPass_zero_le n L os hos
    · rw [stmtPeak_zero_of_allocationFree (by rfl)]
      exact Nat.zero_le _

variable [Has SampleOp Op]

/-- Every downward level reuses the same five scalar cells and node buffers. The level
loop does not multiply the stored workspace by the recursion depth. -/
theorem stmtPeak_downwardPass_zero_le (n L cap : ℕ) (offs : List ℕ)
    (hlen : offs.length = 12) (hn : 2 ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (downwardPass (node (Op := Op) (Tst := Tst))).body
      ([n, L, cap] ++ offs) ≤ 18 * (n * n) + 14 := by
  apply Finset.sup_le
  intro d hd
  apply stmtPeak_frame_le (d := [n, L, cap, d])
  · simp [IExp.evalList, IExp.eval, hlen]
  · exact fun os => stmtPeak_downLevel_zero_le n L cap d os hn

/-- Initialization, both passes and output copies execute sequentially. Their maximum
scratch is the downward node reservation, excluding the already allocated eleven arenas. -/
theorem stmtPeak_solveBody_zero_le (n L cap : ℕ) (offs : List ℕ) (hn : 2 ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (solveBody (node (Op := Op) (Tst := Tst)))
      ([n, L, cap] ++ offs) ≤ 18 * (n * n) + 14 := by
  apply max_le
  · rw [stmtPeak_zero_of_allocationFree (by rfl)]
    exact Nat.zero_le _
  · apply max_le
    · apply stmtPeak_frame_le_of_length (d := [n, L, cap])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os hos => stmtPeak_downwardPass_zero_le n L cap os hos hn
    · apply stmtPeak_frame_le (d := [n, L])
      · simp [IExp.evalList, IExp.eval]
      · exact fun os => (stmtPeak_reconstructResult_zero_le n L os).trans (by omega)

/-- For root size at least two, the complete solver's stored scratch is bounded by an
explicit polynomial, independently of its iteration cap and operation-count manifest.
This includes all eleven arenas and nested node/sign/deflation/compression buffers.
Primitive operations are assigned zero additional workspace in this statement. -/
theorem stmtPeak_solve_zero_le (n L cap : ℕ) (offs : List ℕ) (hn : 2 ≤ n) :
    stmtPeak (fun (_ : Op) _ => 0) (solve (node (Op := Op) (Tst := Tst)))
      ([n, L, cap] ++ offs) ≤
      6 * (n * n) * L + 32 * (n * n) + 4 * n * L + 7 * n + 2 * L + 24 := by
  simp only [solve, stmtPeak_alloc]
  have hb : stmtPeak (fun (_ : Op) _ => 0)
      (.frame [.var 0, .var 1, .var 2]
        [⟨0, .var 3⟩, ⟨1, .var 4⟩, ⟨2, .var 5⟩, ⟨3, .var 6⟩,
          ⟨4, .const 0⟩, ⟨5, .const 0⟩, ⟨6, .const 0⟩, ⟨7, .const 0⟩,
          ⟨8, .const 0⟩, ⟨9, .const 0⟩, ⟨10, .const 0⟩, ⟨11, .const 0⟩,
          ⟨12, .const 0⟩, ⟨13, .const 0⟩, ⟨14, .const 0⟩]
        (solveBody (node (Op := Op) (Tst := Tst))))
      ([n, L, cap] ++ offs) ≤ 18 * (n * n) + 14 := by
    apply stmtPeak_frame_le (d := [n, L, cap])
    · simp [IExp.evalList, IExp.eval]
    · exact fun os => stmtPeak_solveBody_zero_le n L cap os hn
  simp [IExp.eval] at hb ⊢
  nlinarith

end NLAlib.SpectralBisection
