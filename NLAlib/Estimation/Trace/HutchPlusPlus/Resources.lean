/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Alg
public import NLAlib.Matrix.Factorizations.MGS.Resources
public import NLAlib.Ops.AllocationFree
public import NLAlib.Ops.Workspace

/-!
# Hutch++ independent workspace accounting

The sketch temporary is released before projection and the second batch of matrix images.
The complete stored peak is two concatenated matrices and two scalar cells. Primitive
workspace contributes one common ceiling, independently of rank and all branch outcomes.

## Main results

* `NLAlib.HutchPlusPlus.estimate_peak_zero`: the explicit stored-payload polynomial.
* `NLAlib.HutchPlusPlus.estimate_peak_le`: a common primitive-workspace envelope.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]
  [Has SampleOp Op] [Has StoredOperatorOp Op] [Has IndexOp Op]

/-- The actual full estimator has exactly two matrix batches and two scalar cells at peak.
The sketch temporary and MGS temporary occur earlier and do not add to that peak. -/
theorem estimate_peak_zero (stream n k ell data out : ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (estimate (Tst := Tst) stream).body
      [n, k, ell, data, out] = 2 * n * (k + ell) + 2 := by
  have hSample (idx : List ℕ) := stmtPeak_zero_of_allocationFree
    (s := (sampleVector (Op := Op) (Tst := Tst) stream).body) (idx := idx) (by rfl)
  have hApply (idx : List ℕ) := stmtPeak_zero_of_allocationFree
    (s := (applyColumns (Op := Op) (Tst := Tst)).body) (idx := idx) (by rfl)
  have hProject (idx : List ℕ) := stmtPeak_zero_of_allocationFree
    (s := (projectProbes (Op := Op) (Tst := Tst)).body) (idx := idx) (by rfl)
  have hEval (idx : List ℕ) := stmtPeak_zero_of_allocationFree
    (s := (evaluate (Op := Op) (Tst := Tst)).body) (idx := idx) (by rfl)
  have hnk : n * k ≤ 2 + n * (k + ell) := by nlinarith
  have htwo : 2 * n * (k + ell) = n * (k + ell) + n * (k + ell) := by ring
  simp [estimate, prepare, sketch, finish, stmtPeak, Stmt.alloc, IExp.evalList, IExp.eval,
    hSample, hApply, hProject, hEval, MGS.factor_peak_zero, hnk]
  omega

/-- A common primitive-workspace ceiling is reserved once above the stored peak. -/
theorem estimate_peak_le (W : Op → List ℕ → ℕ) (w : ℕ)
    (hW : ∀ o d, W o d ≤ w) (stream n k ell data out : ℕ) :
    stmtPeak W (estimate (Tst := Tst) stream).body [n, k, ell, data, out] ≤
      2 * n * (k + ell) + 2 + w := by
  simpa only [estimate_peak_zero] using
    stmtPeak_le_zero_add W w hW (estimate (Tst := Tst) stream).body [n, k, ell, data, out]

end NLAlib.HutchPlusPlus
