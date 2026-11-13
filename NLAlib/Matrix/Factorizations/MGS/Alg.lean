/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeBlas
public import NLAlib.Ops.Logic.Builder

/-!
# Full rank-revealing modified Gram–Schmidt

The fixed tree sweeps every column against previously normalized columns. A zero
residual stays zero, so normalization never requires a full-column-rank assumption.
The vector primitives are Hermitian products, axpy and division by a scalar.

## Main definitions

* `NLAlib.MGS.sweep` reduces one vector against a column-major matrix prefix.
* `NLAlib.MGS.factor` performs the full in-place rank-revealing factorization.
-/

@[expose] public section

namespace NLAlib.MGS

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- One MGS reduction computes the Hermitian coefficient from the current residual,
negates it and updates that same residual. -/
def reduce : Impl Op Tst := opsImpl% [n] (q, v, r) → () {
  call (Has.inj Blas1Op.dot) [n] (q, v) → (r);
  call (Has.inj ScalarOp.neg) [] (r) → (r);
  call (Has.inj Blas1Op.axpy) [n] (r, q, v) → (v)
}

/-- Reduce `v` against the first `k` columns of `Q`; `r` stores each negated
coefficient. The caller may supply disjoint subviews of a common matrix buffer. -/
def sweep : Impl Op Tst := opsImpl% [n, k] (Q, v, r) → () {
  for i < k {
    run reduce.body [n] (Q[n * i], v, r)
  }
}

/-- Divide by the positive square root of a stored nonzero squared norm.
The guard compares `t[1]` with the zero stored in `t[0]` and leaves zero residuals alone. -/
def normalizeGuard : Impl Op Tst := opsImpl% [n] (v, t) → () {
  if (Has.inj CmpTst.eq) [] (t[1], t) {
    skip
  } else {
    call (Has.inj ScalarOp.sqrt) [] (t[1]) → (t[1]);
    call (Has.inj Blas1Op.scal) [n] (t[1], v) → (v)
  }
}

/-- Normalize a nonzero residual, leaving an exactly zero residual unchanged.
`t[0]` and `t[1]` hold zero and the Hermitian squared norm respectively. -/
def normalize : Impl Op Tst := opsImpl% [n] (v, t) → () {
  call (Has.inj Blas1Op.dot) [n] (v, v) → (t[1]);
  call (Has.inj (ScalarOp.lit 0)) [] () → (t);
  run normalizeGuard.body [n] (v, t)
}

/-- Sweep column `j` against its predecessors, then normalize its residual safely. -/
def factorColumn : Impl Op Tst := opsImpl% [n, j] (Y, t) → () {
  run sweep.body [n, j] (Y, Y[n * j], t);
  run normalize.body [n] (Y[n * j], t)
}

/-- The full column loop on caller-owned scalar workspace. Each completed column
is available to subsequent sweeps, including zero columns. -/
def factorWithScratch : Impl Op Tst := opsImpl% [n, k] (Y, t) → () {
  for j < k {
    run factorColumn.body [n, j] (Y, t)
  }
}

/-- Full in-place modified Gram–Schmidt, with two scoped scalar scratch cells.
The tree is fixed for every row count and column count, including zero dimensions. -/
def factor : Impl Op Tst := opsImpl% [n, k] (Y) → () {
  let t ← alloc 2;
  run factorWithScratch.body [n, k] (Y, t)
}

/-- The full factorization as one fixed two-dimension, one-buffer program. -/
def program : Program Op Tst 2 1 := factor.program 1 [⟨0, .const 0⟩] []

end NLAlib.MGS
