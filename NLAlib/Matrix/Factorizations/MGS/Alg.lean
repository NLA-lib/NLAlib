/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeBlas
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.RoutineSyntax

/-!
# Full rank-revealing modified Gram–Schmidt

The fixed tree sweeps every column against previously normalized columns. A zero
residual stays zero, so normalization never requires a full-column-rank assumption.
The vector primitives are Hermitian products, axpy and division by a scalar.

## Main definitions

* `NLAlib.MGS.sweep`, `NLAlib.MGS.sweepRoutine`: reduce one vector against a column-major
  matrix prefix. The sweep is a routine because two routines run it: this factorization and the
  probe projection of Hutch++.
* `NLAlib.MGS.factor`, `NLAlib.MGS.factorRoutine`: the full in-place rank-revealing
  factorization.
* `NLAlib.MGS.factorProgram`: the factorization on the one matrix buffer of a problem.

The other trees (`reduce`, `normalizeGuard`, `normalize`, `factorColumn`, `factorWithScratch`)
are fragments: pieces of the sweep or of the factorization, run only inside them.
-/

@[expose] public section

namespace NLAlib.MGS

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- One MGS reduction computes the Hermitian coefficient from the current residual,
negates it and updates that same residual. -/
def reduce : Stmt Op Tst := ops% [n] (q, v, r) → () {
  call (Has.inj Blas1Op.dot) [n] (q, v) → (r);
  call (Has.inj ScalarOp.neg) [] (r) → (r);
  call (Has.inj Blas1Op.axpy) [n] (r, q, v) → (v)
}

/-- Reduce `v` against the first `k` columns of `Q`; `r` stores each negated
coefficient. The caller may supply disjoint subviews of a common matrix buffer. -/
def sweep : Stmt Op Tst := ops% [n, k] (Q, v, r) → () {
  for i < k {
    run reduce [n] (Q[n * i], v, r)
  }
}

/-- The sweep: `[n, k] (Q : k * n, v : n) → (v, unreported r : 1)`. The tree has one buffer
variable per operand, and its operands are separated by block, so the columns of `Q` and the
vector `v` may lie in one buffer. The final content of the scratch cell `r` is not part of the
claim. -/
def sweepRoutine : Routine Op Tst :=
  routine% [n, k] (Q : k * n, v : n) → (v, unreported r : 1) one variable by blocks := sweep

/-- Divide by the positive square root of a stored nonzero squared norm.
The guard compares `t[1]` with the zero stored in `t[0]` and leaves zero residuals alone. -/
def normalizeGuard : Stmt Op Tst := ops% [n] (v, t) → () {
  if (Has.inj CmpTst.eq) [] (t[1], t) {
    skip
  } else {
    call (Has.inj ScalarOp.sqrt) [] (t[1]) → (t[1]);
    call (Has.inj Blas1Op.scal) [n] (t[1], v) → (v)
  }
}

/-- Normalize a nonzero residual, leaving an exactly zero residual unchanged.
`t[0]` and `t[1]` hold zero and the Hermitian squared norm respectively. -/
def normalize : Stmt Op Tst := ops% [n] (v, t) → () {
  call (Has.inj Blas1Op.dot) [n] (v, v) → (t[1]);
  call (Has.inj (ScalarOp.lit 0)) [] () → (t);
  run normalizeGuard [n] (v, t)
}

/-- Sweep column `j` against its predecessors, then normalize its residual safely. -/
def factorColumn : Stmt Op Tst := ops% [n, j] (Y, t) → () {
  run sweepRoutine [n, j] (Y, Y[n * j], t);
  run normalize [n] (Y[n * j], t)
}

/-- The full column loop on caller-owned scalar workspace. Each completed column
is available to subsequent sweeps, including zero columns. -/
def factorWithScratch : Stmt Op Tst := ops% [n, k] (Y, t) → () {
  for j < k {
    run factorColumn [n, j] (Y, t)
  }
}

/-- Full in-place modified Gram–Schmidt, with two scoped scalar scratch cells.
The tree is fixed for every row count and column count, including zero dimensions. -/
def factor : Stmt Op Tst := ops% [n, k] (Y) → (Z) {
  let t ← alloc 2;
  run factorWithScratch [n, k] (Y, t)
}

/-- In-place modified Gram–Schmidt: `[n, k] (Y : update k * n)`. Its two scalar scratch cells
are allocated by the tree. -/
def factorRoutine : Routine Op Tst := routine% [n, k] (Y : k * n) → (Y) := factor

/-- The full factorization as one fixed two-dimension, one-buffer program: the routine on the
matrix buffer of a problem. -/
def factorProgram : Program Op Tst 2 1 := factorRoutine.close 2 1

end NLAlib.MGS
