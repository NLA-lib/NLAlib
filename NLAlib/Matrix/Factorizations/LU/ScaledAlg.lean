/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledStep
public import NLAlib.Matrix.Factorizations.LU.RowScales
public import NLAlib.Matrix.Factorizations.LU.Initialize

/-!
# Actual fixed-initial-scale LU

The driver copies the original matrix into a scoped packed residual/scale arena before
zero-filling factors. Fixed row norms are initialized once from that original copy and
follow actual row exchanges. Every active step records its actual selected current row.
A dimension-only outer guard makes order zero skip all calls, frames and allocations.

## Main results

* `NLAlib.LU.scaledLoop`: the actual bounded stored pivot loop.
* `NLAlib.LU.factorScaled`: full fixed-initial-scale LU on one source matrix.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Execute all scaled pivots, writing one actual current-position row index per step. The
single selected-index word is caller-supplied unreported scratch, never an extra log. -/
def scaledLoop : Routine Op Tst :=
  routine% [n] (R : n * n + n, L : n * n, U : n * n) →
      (R, L, U, H : n, unreported selected : 1) {
    for k < n {
      run scaledStep [n, k] (R, L, U, H[k], selected)
    }
  }

/-- Full fixed-initial-scale LU with one scoped arena containing the residual and fixed
original row scales. Singular/zero-scale branches use the total column and Schur routines. -/
def factorScaled : Routine Op Tst :=
  routine% [n] (A : n * n) → (L : n * n, U : n * n, H : n) {
    ifPos n {
      let R ← alloc (n * n + n);
      let selected ← alloc 1;
      run initializeFactors [n] (A, R, L, U);
      run rowScales [n, n] (R, R[n * n]);
      run scaledLoop [n] (R, L, U, H, selected)
    }
  }

end NLAlib.LU
