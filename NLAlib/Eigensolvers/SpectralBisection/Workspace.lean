/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ArenaLayout
public import NLAlib.Eigensolvers.SpectralBisection.Node
public import NLAlib.Ops.AllocationFree
public import Mathlib.Tactic.Ring

/-!
# Stored workspace of the spectral bisection kernels

These are allocation bounds for the actual statement trees, independently of their
syntactic operation counts. Primitive matrix workspace is deliberately excluded by setting
the primitive workspace function to zero. It must be added separately for a concrete model.
The eleven persistent arena capacities are counted exactly, including empty reserved slots.

## Main results

* `NLAlib.SpectralBisection.sum_arenaLengths`: exact persistent storage.
* `NLAlib.SpectralBisection.stmtPeak_deflate_zero`: actual deflation allocations.
* `NLAlib.SpectralBisection.stmtPeak_compress_zero`: actual compression allocations.
* `NLAlib.SpectralBisection.stmtPeak_sign_zero`: actual matrix-sign allocations.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has MatrixOp Op]

/-- The complete eleven-arena reservation, in scalar cells, including all unused slots. -/
theorem sum_arenaLengths (n L : ℕ) :
    (arenaLengths n L).sum =
      6 * (n * n) * L + 14 * (n * n) + 4 * n * L + 7 * n + 2 * L + 10 := by
  simp only [arenaLengths, List.sum_cons, List.sum_nil]
  ring

/-- Deflation holds four square pair matrices simultaneously. Scalar scaling, multiplication,
QR and the final copy allocate no additional stored cells inside this statement tree. -/
theorem stmtPeak_deflate_zero (n k r lo side : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (deflate (Tst := Tst)).body
      ([n, k, r, lo, side] ++ offs) = 8 * (k * k) := by
  simp only [deflate, stmtPeak_alloc]
  rw [stmtPeak_zero_of_allocationFree (by rfl)]
  simp [IExp.eval]
  ring

/-- Compression holds two rectangular and two square pair matrices simultaneously. This
counts the actual allocation syntax and excludes primitive multiplication workspace. -/
theorem stmtPeak_compress_zero (k r : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (compress (Tst := Tst)).body
      ([k, r] ++ offs) = 4 * (k * r) + 4 * (r * r) := by
  simp only [compress, stmtPeak_alloc]
  rw [stmtPeak_zero_of_allocationFree (by rfl)]
  simp [IExp.eval]
  ring

/-- A compression to at most the input dimension needs no more stored scratch than the
four square matrices reserved by deflation. This includes zero-size children. -/
theorem stmtPeak_compress_zero_le (k r : ℕ) (offs : List ℕ) (hr : r ≤ k) :
    stmtPeak (fun (_ : Op) _ => 0) (compress (Tst := Tst)).body
      ([k, r] ++ offs) ≤ 8 * (k * k) := by
  rw [stmtPeak_compress_zero]
  have hkr := Nat.mul_le_mul_left k hr
  have hrr := Nat.mul_le_mul hr hr
  nlinarith

omit [Has MatrixOp Op] in
/-- Matrix sign reserves two square pair matrices and five scalar cells. Neither the
stopping loop nor its cap changes this allocation peak. Primitive workspace is excluded. -/
theorem stmtPeak_sign_zero [Has IndexOp Op] [Has CmpTst Tst]
    (mm : Op) (n cap : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (Sign.program (Tst := Tst) mm).body
      ([n, cap] ++ offs) = 4 * (n * n) + 5 := by
  simp only [Sign.program, stmtPeak_alloc]
  rw [stmtPeak_zero_of_allocationFree (by rfl)]
  simp [IExp.eval]
  ring

end NLAlib.SpectralBisection
