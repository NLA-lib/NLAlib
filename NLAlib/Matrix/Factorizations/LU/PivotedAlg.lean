/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Initialize
public import NLAlib.Matrix.Factorizations.LU.Step
public import NLAlib.Matrix.Factorizations.LU.Pivot
public import NLAlib.Matrix.Factorizations.LU.PivotedLoop
public import NLAlib.Matrix.Factorizations.LU.PivotedSpec
public import NLAlib.Ops.Catalog.Index

/-!
# Scalar pivoted Gaussian elimination

The selector is a fixed scalar tree behind the declared pivot-choice interface. Every step
consumes its actual two output words, exchanges matching residual and factor rows or columns,
records both current-position indices, and runs the common guarded elimination step. The
column exchange includes all previously committed upper rows.

## Main definitions

* `NLAlib.LU.factorPivoted`: the common scalar driver with two actual pivot logs.
* `NLAlib.LU.factorPivotedSpec`: canonical factors of the matrix permuted by those logs.

## Main results

Concrete policies instantiate the selector tree; their certificates use its proved judgment.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- The common loop uses a dimension flag: zero reuses one column-history cell, while one
stores a complete independent column history. Concrete wrappers supply this flag literally. -/
def factorPivotedCore (choose : Stmt Op Tst) : Routine Op Tst :=
  routine% [n, columns] (A : n * n) →
      (L : n * n, U : n * n, H : n, Q : columns * n + (1 - columns) * (n - (n - 1))) {
    ifPos n {
      let R ← alloc (n * n);
      let selected ← alloc 2;
      run initializeFactors [n] (A, R, L, U);
      run (pivotedLoop choose) [n, columns] (R, L, U, H, Q, selected)
    }
  }

/-- Factor with a fixed scalar selector body. A fixed-column policy uses only one internal
column-history cell; independent column policies report the full log. Empty orders skip all
allocations and queries. The caller supplies only the matrix order. -/
def factorPivoted (choose : Stmt Op Tst) (fixedColumns : Bool := false) : Routine Op Tst :=
  if fixedColumns then
    routine% [n] (A : n * n) → (L : n * n, U : n * n, H : n, Q : n - (n - 1)) {
      run (factorPivotedCore choose) [n, 0] (A, L, U, H, Q)
    }
  else
    routine% [n] (A : n * n) → (L : n * n, U : n * n, H : n, Q : n) {
      run (factorPivotedCore choose) [n, 1] (A, L, U, H, Q)
    }

end NLAlib.LU
