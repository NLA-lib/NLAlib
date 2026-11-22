/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Sampling
public import NLAlib.Ops.Blas.Matrix
public import NLAlib.Ops.Catalog.Matrix
public import NLAlib.Ops.Stream

/-!
# Standalone randomized deflation

The program draws a square matrix of complex stored sample words, multiplies the supplied
projector by it, calls full QR and copies the requested leading basis columns. Sampling,
matrix operations and copying remain separate counted operations.

## Main results

* `NLAlib.Deflation.apply` performs projection, QR and leading-column selection.
* `NLAlib.Deflation.program` allocates the four square workspaces and samples explicitly.
-/

@[expose] public section

namespace NLAlib.Deflation

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has MatrixOp Op] [Has SampleOp Op]

/-- Deflation with caller-owned workspace. Dimensions are the matrix size and requested
rank. The sampled matrix uses two scalar words per complex entry, in column order. -/
def apply : Stmt Op Tst := ops% [n, r] (P, G, Y, Q, R) → (Qout) {
  run (sampleRoutine Stream.gauss) [2 * (n * n)] (G);
  call (Has.inj MatrixOp.mul) [n, n, n] (P, G) → (Y);
  call (Has.inj MatrixOp.qr) [n, n] (Y) → (Q, R);
  run PairMatrix.copy [n, r] (Q, Qout)
}

/-- A fixed standalone deflation implementation with explicit scalar draws and four scoped
square workspaces. Numerical subspace guarantees follow from the accuracy of its actual
matrix routines and the distribution of these same sample words.
[Shah2024, Algorithm 2]. -/
def program : Stmt Op Tst := ops% [n, r] (P) → (Qout) {
  let G ← alloc (2 * (n * n));
  let Y ← alloc (2 * (n * n));
  let Q ← alloc (2 * (n * n));
  let R ← alloc (2 * (n * n));
  run apply [n, r] (P, G, Y, Q, R, Qout)
}

end NLAlib.Deflation
