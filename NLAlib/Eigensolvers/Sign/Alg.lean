/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Hermitian
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.RoutineSyntax

/-!
# Newton–Schulz matrix sign over explicit scalar operations

The matrix product is the only matrix-level primitive. Hermitian shifts, scaling, completion,
and entry tests expand to scalar calls and primitive scalar comparisons. Complex matrices use
interleaved real/imaginary words in column-major order. The initial matrix, tolerance, and scale
are stored inputs; the threshold and all literals are computed by the program.

The loop returns its current iterate at the cap. Numerical convergence must be proved from
explicit precision, input, and cap assumptions; exhausting the cap never asserts convergence.

## Main results

* `NLAlib.Sign.test` computes the squared iterate and its entrywise stopping test.
* `NLAlib.Sign.step` performs the rounded Hermitian Newton–Schulz step.
* `NLAlib.Sign.program` is one fixed implementation for every dimension and iteration cap.
* `NLAlib.Sign.signRoutine` is that program with its interface.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Square the current iterate, subtract the identity by scalar operations and test every
real and imaginary word against stored bounds. The matrix product takes dimensions
`[rows, inner, columns]` and interleaved input/output blocks. -/
def test (mm : Op) : Stmt Op Tst := ops% [n] (X, one, lo, hi) → (W, V, flag) {
  call mm [n, n, n] (X, X) → (W);
  run Hermitian.shift [n] (W, one, V);
  run Hermitian.boxTest [n, n] (V, lo, hi, flag)
}

/-- One rounded Hermitian Newton–Schulz step, reusing the square left by the stopping test.
The literal three is subtracted from the square, the difference is negated, and the product
with the current iterate is added to its conjugate transpose and divided by the literal four.
The matrix and scalar workspace regions must be pairwise disjoint. -/
def step (mm : Op) : Stmt Op Tst := ops% [n] (X, W, V, c) → (X, W, V, c) {
  call (Has.inj (ScalarOp.lit 3)) [] () → (c);
  run Hermitian.shiftNegate [n] (W, c, V);
  call mm [n, n, n] (X, V) → (W);
  call (Has.inj (ScalarOp.lit 4)) [] () → (c);
  run Hermitian.average [n] (W, c, X)
}

/-- One matrix step followed by its actual stopping test and refreshed square cache. -/
def round (mm : Op) : Stmt Op Tst := ops% [n] (X, W, V, t) → (X, W, V, t) {
  run (step mm) [n] (X, W, V, t[2], X, W, V, t[2]);
  run (test mm) [n] (X, t[3], t[4], t, W, V, t[1])
}

/-- The capped iteration from an initialized iterate, cached square, threshold and failure
flag. It stops at the first passing test or returns the current iterate at the cap. -/
def loop (mm : Op) : Stmt Op Tst := ops% [n, cap] (X, W, V, t) → (X, W, V, t) {
  while k < cap, (Has.inj CmpTst.eq) [] (t[1], t[3]) {
    run (round mm) [n] (X, W, V, t, X, W, V, t)
  } then {
    skip
  }
}

/-- Compute the first stopping test, then execute the capped matrix loop. -/
def start (mm : Op) : Stmt Op Tst := ops% [n, cap] (X, W, V, t) → (X, W, V, t) {
  run (test mm) [n] (X, t[3], t[4], t, W, V, t[1]);
  run (loop mm) [n, cap] (X, W, V, t, X, W, V, t)
}

/-- Compute the threshold and its signed bounds by explicit scalar arithmetic. -/
def initialScalars : Stmt Op Tst := ops% [] (eps, den) → (t) {
  call (Has.inj ScalarOp.div) [] (eps, den) → (t);
  call (Has.inj ScalarOp.neg) [] (t) → (t[4]);
  call (Has.inj (ScalarOp.lit 1)) [] () → (t[3])
}

/-- Initialize caller-owned workspace and execute the capped iteration. -/
def initialized [Has IndexOp Op] (mm : Op) : Stmt Op Tst :=
    ops% [n, cap] (A, par, X, W, V, t) → (X, W, V, t) {
  call (Has.inj IndexOp.lit) [4 * n] () → (t[2]);
  run initialScalars [] (par, t[2], t);
  run Hermitian.scale [n] (A, par[1], X);
  run (start mm) [n, cap] (X, W, V, t, X, W, V, t)
}

/-- **Newton–Schulz sign iteration** with a finite cap. The matrix product is a parameter of the
operation signature. The natural-literal operation takes a dimension `[k]` and writes the
machine's rounded literal for `k`; it does not convert data into an index.

Dimensions are `n` and `cap`; input buffers contain the interleaved matrix and the two stored
parameters (tolerance followed by scale). The output contains the current Hermitian iterate.
Scratch is five scalar cells and two interleaved square matrices. An exhausted cap returns the
current iterate; a convergence theorem needs a cap justified by the input and operation model.
[Shah2024, Algorithm 1], with a cap and explicit Hermitian completion.
Algorithm: newton-schulz-sign -/
def program [Has IndexOp Op] (mm : Op) : Stmt Op Tst := ops% [n, cap] (A, par) → (X) {
  let t ← alloc 5;
  let W ← alloc (2 * (n * n));
  let V ← alloc (2 * (n * n));
  run (initialized mm) [n, cap] (A, par, X, W, V, t, X, W, V, t)
}

/-- The capped sign iteration with its interface:
`[n, cap] (A : 2 n², par : 2) → (X : 2 n²)`, separated by block. The written matrix is apart from
the matrix and the parameters, which may overlap each other; a caller may pass views of one
workspace buffer. -/
def signRoutine [Has IndexOp Op] (mm : Op) : Routine Op Tst :=
  routine% [n, k] (A : 2 * (n * n), par : 2) → (X : 2 * (n * n)) by blocks := program mm

end NLAlib.Sign
