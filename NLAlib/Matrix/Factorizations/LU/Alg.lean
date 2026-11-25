/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Column
public import NLAlib.Matrix.Factorizations.LU.Initialize
public import NLAlib.Matrix.Factorizations.LU.Step
public import NLAlib.Ops.Blas.StridedCopy
public import NLAlib.Ops.Catalog.Orth
public import NLAlib.Matrix.Factorizations.LUEntries

/-!
# Stored Gaussian elimination without pivoting

The input is copied to a scoped residual. Each iteration materializes one lower column and
one upper row, then performs a full rank-one residual update. All arithmetic is implemented
by scalar routines; there is no factorization operation in the signature. The original input
is read only. The factors are initialized with literal zeros, so each iteration only writes
its lower diagonal and tail and its upper row tail.

## Main definitions

* `NLAlib.LU.factor`: the fixed scalar routine.
* `NLAlib.LU.factorSpec`: exact canonical factors under nonzero Gaussian pivots.

## Main results

The routine's judgment is proved in the companion routine module.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Gaussian elimination without pivoting on a column-major square matrix. The two output
factors are separate, and the residual is scoped scratch. Empty matrices execute no pivot
operation. -/
def factor : Routine Op Tst := routine% [n] (A : n * n) → (L : n * n, U : n * n) {
  let R ← alloc (n * n);
  run initializeFactors [n] (A, R, L, U);
  for k < n {
    run step [n, k] (R, L, U)
  }
}

variable [Inhabited K]

/-- The decoded output blocks are the canonical lower and upper factors of the decoded input.
Every canonical Gaussian pivot is required to be nonzero; the requirement is vacuous in
dimension zero. -/
def factorSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls, us) requires
    (∀ i : Fin n, gaussState (decodeMatrix dec n n as) i.val i i ≠ 0) ensures
    decodeMatrix dec n n ls = luLower (decodeMatrix dec n n as) ∧
      decodeMatrix dec n n us = luUpper (decodeMatrix dec n n as)

end NLAlib.LU
