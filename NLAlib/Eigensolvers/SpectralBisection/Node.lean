/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Alg
public import NLAlib.Ops.Blas.Matrix
public import NLAlib.Ops.Blas.Pair
public import NLAlib.Ops.Blas.Clamp
public import NLAlib.Ops.Catalog.Matrix

/-!
# Spectral bisection node programs

Deflation and compression are ordinary subprograms, expanded by frames into scalar operations
and multiplication/QR calls. Node sizes and split metadata are stored by dimension-literal
operations and read by bounded index queries. Samples are visible stored inputs drawn by the
level traversal. No primitive computes a bisection node or supplies its numerical conclusion.

The constants buffer contains one, two, one half, negative one and square root of one half,
in that order. They are computed by the outer program. Matrix arenas use word offset
`2 * n * n * d + 2 * n * lo` at depth `d` and slot `lo`.

## Main results

* `NLAlib.SpectralBisection.deflate` executes sampled projection, QR and basis selection.
* `NLAlib.SpectralBisection.compress` executes a Hermitian compression and shift.
* `NLAlib.SpectralBisection.split` constructs both children and their stored metadata.
* `NLAlib.SpectralBisection.node` executes one nonleaf node of the downward traversal.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has MatrixOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Scale the two stored component words of every selected Gaussian entry. The source
indexing selects a size-k submatrix from one side of a level's fixed Gaussian batch. -/
def deflateSamples : Impl Op Tst := opsImpl% [n, k, lo, side] (Sg, sq) → (G) {
  for j < k {
    for i < k {
      run Pair.multiply.body []
        (Sg[2 * (n * (2 * (lo + j) + side) + i)], sq, G[2 * (j * k + i)])
    }
  }
}

/-- Construct the sampled range of one projector and store its first `r` QR columns.
The side selects one of the two Gaussian submatrices in the level's stored sample block.
Every sample scaling, product, QR and copy is executed explicitly. -/
def deflate : Impl Op Tst := opsImpl% [n, k, r, lo, side] (Sg, sq, P) → (Qout) {
  let G ← alloc (2 * (k * k));
  let Y ← alloc (2 * (k * k));
  let Q ← alloc (2 * (k * k));
  let R ← alloc (2 * (k * k));
  run deflateSamples.body [n, k, lo, side] (Sg, sq, G);
  call (Has.inj MatrixOp.mul) [k, k, k] (P, G) → (Y);
  call (Has.inj MatrixOp.qr) [k, k] (Y) → (Q, R);
  run PairMatrix.copy.body [k, r] (Q, Qout)
}

/-- Compress the stored matrix by a rectangular basis, Hermitianize the computed product,
and subtract a stored real shift. Only matrix multiplication is a matrix-level primitive. -/
def compress : Impl Op Tst := opsImpl% [k, r] (Q, A, two, sigma) → (C) {
  let Qh ← alloc (2 * (k * r));
  let C1 ← alloc (2 * (r * k));
  let C2 ← alloc (2 * (r * r));
  let C3 ← alloc (2 * (r * r));
  run PairMatrix.conjTranspose.body [k, r] (Q, Qh);
  call (Has.inj MatrixOp.mul) [r, k, k] (Qh, A) → (C1);
  call (Has.inj MatrixOp.mul) [r, k, r] (C1, Q) → (C2);
  run Hermitian.average.body [r] (C2, two, C3);
  run Hermitian.shift.body [r] (C3, sigma, C)
}

/-- Store the two child bases, shifted compressions, sizes and parent split metadata.
The mathematical split is represented by the dimension `kp`; the caller obtains it from an
actual bounded query on a clamped computed trace. -/
def split : Stmt Op Tst := ops% [n, d, lo, k, kp] (Sg, Pp, Pm, Ma, Qa, Sz, Kd, Kp, c, t) → () {
  run deflate.body [n, k, kp, lo, 0]
    (Sg, c[4], Pp, Qa[2 * (n * n) * d + 2 * n * lo]);
  run deflate.body [n, k, k - kp, lo, 1]
    (Sg, c[4], Pm, Qa[2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)]);
  run compress.body [k, kp]
    (Qa[2 * (n * n) * d + 2 * n * lo], Ma[2 * (n * n) * d + 2 * n * lo], c[1], t,
      Ma[2 * (n * n) * (d + 1) + 2 * n * lo]);
  run compress.body [k, k - kp]
    (Qa[2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)],
      Ma[2 * (n * n) * d + 2 * n * lo], c[1], t[1],
      Ma[2 * (n * n) * (d + 1) + 2 * n * (lo + kp)]);
  call (Has.inj IndexOp.lit) [kp] () → (Sz[n * (d + 1) + lo]);
  call (Has.inj IndexOp.lit) [k - kp] () → (Sz[n * (d + 1) + lo + kp]);
  call (Has.inj IndexOp.lit) [4] () → (Kd[n * d + lo]);
  call (Has.inj IndexOp.lit) [kp] () → (Kp[n * d + lo])
}

/-- A single child occupies its parent's slot at the next level, with the selected shift
and a recorded parent kind. The program computes the shifted matrix before writing metadata. -/
def child : Stmt Op Tst := ops% [n, d, lo, k, kind] (Ma, Sz, Kd, sigma) → () {
  run Hermitian.shift.body [k]
    (Ma[2 * (n * n) * d + 2 * n * lo], sigma,
      Ma[2 * (n * n) * (d + 1) + 2 * n * lo]);
  call (Has.inj IndexOp.lit) [k] () → (Sz[n * (d + 1) + lo]);
  call (Has.inj IndexOp.lit) [kind] () → (Kd[n * d + lo])
}

/-- Compute the two signed half-radii, the stored level parameter and the sampled shift.
The literal level parameter is an index operation; all divisions and multiplications keep
exactly the node's machine-word evaluation order. -/
def nodeScalars : Impl Op Tst := opsImpl% [L, d, lo] (Lv, c, Su) → (t) {
  call (Has.inj ScalarOp.div) [] (Lv[2 * d], c[1]) → (t);
  call (Has.inj ScalarOp.neg) [] (t) → (t[1]);
  call (Has.inj IndexOp.lit) [L + d] () → (t[2]);
  call (Has.inj ScalarOp.div) [] (Lv[2 * d], t[2]) → (t[3]);
  call (Has.inj ScalarOp.mul) [] (t[3], Su[lo]) → (t[4])
}

/-- Store the supplied sign tolerance and the rounded doubled radius. -/
def signParameters : Impl Op Tst := opsImpl% [d] (Lv, par, two) → (sp) {
  call (Has.inj ScalarOp.copy) [] (par[2]) → (sp);
  call (Has.inj ScalarOp.mul) [] (two, Lv[2 * d]) → (sp[1])
}

/-- Construct both rounded spectral projectors from the actual capped sign iteration.
The supplied B and T scratch buffers retain the same ownership and operation order as the node. -/
def nodeProjectors : Impl Op Tst := opsImpl% [k, F] (W, sp, c) → (B, T, Pp, Pm) {
  run (Sign.program (Has.inj MatrixOp.mul)).body [k, F] (W, sp, B);
  run Hermitian.shift.body [k] (B, c[3], T);
  run Hermitian.scale.body [k] (T, c[1], Pp);
  run Hermitian.shiftNegate.body [k] (B, c, T);
  run Hermitian.scale.body [k] (T, c[1], Pm)
}

/-- Dispatch the bounded split size through the three explicit zero-or-one trip loops.
Each active branch runs its full child or split program; no branch is an operation primitive. -/
def nodeBranch : Stmt Op Tst := ops% [n, d, lo, k, kp]
    (Sg, Pp, Pm, Ma, Qa, Sz, Kd, Kp, c, t) → () {
  for positive < 1 - (k - kp) {
    run child [n, d, lo, k, 2] (Ma, Sz, Kd, t)
  };
  for negative < 1 - kp {
    run child [n, d, lo, k, 3] (Ma, Sz, Kd, t[1])
  };
  for both < 1 - (1 - (kp * (k - kp))) {
    run split [n, d, lo, k, kp] (Sg, Pp, Pm, Ma, Qa, Sz, Kd, Kp, c, t)
  }
}

/-- Compute and clamp the rounded projector trace before its bounded natural query.
Only cells two, three, five and six of the supplied temporary block are written. -/
def nodeSplitIndex : Impl Op Tst := opsImpl% [k] (Pp, c) → (t) {
  run PairMatrix.traceRe.body [k] (Pp, t[5]);
  call (Has.inj ScalarOp.add) [] (t[5], c[2]) → (t[6]);
  call (Has.inj IndexOp.lit) [0] () → (t[2]);
  call (Has.inj IndexOp.lit) [k] () → (t[3]);
  run clamp.body [] (t[2], t[3], t[6], t[6])
}

/-- Prepare both projectors and the retained signed shifts in caller-owned workspace. -/
def nodePrepare : Stmt Op Tst := ops% [n, L, F, d, lo, k]
    (par, Lv, Su, Sg, Ma, Qa, Sz, Kd, Kp, c, t, sp, W, B, T, Pp, Pm) → () {
  run nodeScalars.body [L, d, lo] (Lv, c, Su, t);
  run Hermitian.shift.body [k] (Ma[2 * (n * n) * d + 2 * n * lo], t[4], W);
  run signParameters.body [d] (Lv, par, c[1], sp);
  run nodeProjectors.body [k, F] (W, sp, c, B, T, Pp, Pm)
}

/-- The mathematical stages of a nonleaf node with caller-owned workspace. -/
def nodeBody : Stmt Op Tst := ops% [n, L, F, d, lo, k]
    (par, Lv, Su, Sg, Ma, Qa, Sz, Kd, Kp, c, t, sp, W, B, T, Pp, Pm) → () {
  run nodePrepare [n, L, F, d, lo, k]
    (par, Lv, Su, Sg, Ma, Qa, Sz, Kd, Kp, c, t, sp, W, B, T, Pp, Pm);
  run nodeSplitIndex.body [k] (Pp, c, t);
  let kp ← index (Has.inj IdxTst.toNat) (t[6]) ≤ k;
  run nodeBranch [n, d, lo, k, kp] (Sg, Pp, Pm, Ma, Qa, Sz, Kd, Kp, c, t)
}

/-- Execute one nonleaf bisection node. A stored uniform sample determines its shift, the
sign iteration constructs projectors, and the clamped rounded trace supplies a bounded split.
The node then executes exactly one of the positive-child, negative-child or two-child cases.
All decisions and conversions are primitive queries on the actual computed words. -/
def node : Stmt Op Tst := ops% [n, L, F, d, lo, k] (par, Lv, Su, Sg, Ma, Qa, Sz, Kd, Kp, c) → () {
  let t ← alloc 7;
  let sp ← alloc 2;
  let W ← alloc (2 * (k * k));
  let B ← alloc (2 * (k * k));
  let T ← alloc (2 * (k * k));
  let Pp ← alloc (2 * (k * k));
  let Pm ← alloc (2 * (k * k));
  run nodeBody [n, L, F, d, lo, k] (par, Lv, Su, Sg, Ma, Qa, Sz, Kd, Kp, c, t, sp, W, B, T, Pp, Pm)
}

end NLAlib.SpectralBisection
