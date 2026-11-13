/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Alg
public import NLAlib.Ops.AllocationFree
public import NLAlib.Ops.Workspace

/-!
# Storage for the full MGS tree

Two scalar cells suffice above the supplied matrix when local primitives reserve no
workspace. A common workspace ceiling adds one reservation, independently of matrix
rank, dimensions and the normalization branches.

## Main results

* `NLAlib.MGS.factor_peak_zero` gives the independent two-cell storage bound.
* `NLAlib.MGS.factor_peak_le` adds a primitive-workspace ceiling.
-/

@[expose] public section

namespace NLAlib.MGS

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- The factorization uses exactly two stored scratch cells with zero primitive workspace. -/
theorem factor_peak_zero (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (factor (Tst := Tst)).body idx = 2 := by
  unfold factor
  rw [stmtPeak_alloc]
  change 2 + stmtPeak (fun (_ : Op) _ => 0) _ idx = 2
  rw [stmtPeak_zero_of_allocationFree (by rfl)]

/-- A uniform primitive-workspace ceiling is reserved once above the two stored cells. -/
theorem factor_peak_le (W : Op → List ℕ → ℕ) (w : ℕ)
    (hW : ∀ o d, W o d ≤ w) (idx : List ℕ) :
    stmtPeak W (factor (Tst := Tst)).body idx ≤ 2 + w := by
  simpa only [factor_peak_zero] using
    stmtPeak_le_zero_add W w hW (factor (Tst := Tst)).body idx

end NLAlib.MGS
