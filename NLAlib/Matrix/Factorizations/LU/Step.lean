/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Column
public import NLAlib.Matrix.Factorizations.LU.Schur

/-!
# One stored Gaussian elimination step

The lower column and upper row are materialized before the residual changes. A guarded
saved-pivot Schur update then advances the residual, including a zero pivot where no division
is executed. Scalar and pivoted LU use the same routine and its word-level judgment.

## Main results

* `NLAlib.LU.step_meets`: actual factor materialization followed by total Schur elimination.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Materialize one factor column and row, then perform zero-safe scalar elimination. All
three matrix operands are updated and their shapes are retained. -/
def step : Routine Op Tst :=
  routine% [n, k] (R : n * n, L : n * n, U : n * n) → (R, L, U) {
    run materializeColumn [n, k] (R, L, U);
    run schurStepTotal [n, k] (R)
  }

variable [Inhabited K]

/-- The factor outputs are the actual materialization of the original residual, and the
residual output is its guarded Schur update. Both component specifications concern the same
original word blocks. -/
def stepSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n, k] tape t (rs, ls, us) → (rs', ls', us') requires k < n ensures
    (materializeColumnSpec M dec).post [n, k] t [rs, ls, us] [ls', us'] ∧
      (schurStepTotalSpec M dec).post [n, k] t [rs] [rs']

/-- One stored step meets its composed word specification. Zero pivots require no special
input premise, and no execution or factorization result is assumed. -/
theorem step_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) :
    (step (Op := Op) (Tst := Tst)).Meets I (stepSpec M dec) := by
  routine_intro [n, k] (R, L, U) reads (rs, ls, us)
  call (materializeColumn_meets hI hcmp) [n, k] (R, L, U) (pre := hpre)
    as m₁ hfr₁ hpos₁ (ls', us') hcol
  have hrs₁ : m₁.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  call (schurStepTotal_meets hI hcmp) [n, k] (R) (pre := hpre)
    as m₂ hfr₂ hpos₂ (rs') hschur
  routine_exit
  exact ⟨hcol, hschur⟩

end NLAlib.LU
