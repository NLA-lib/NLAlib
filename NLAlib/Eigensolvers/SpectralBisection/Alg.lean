/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Matrix
public import NLAlib.Ops.Blas.Broadcast
public import NLAlib.Ops.Blas.Sampling
public import NLAlib.Ops.Catalog.Matrix
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Sampling
public import NLAlib.Eigensolvers.SpectralBisection.Arena
public import NLAlib.Eigensolvers.SpectralBisection.Node

/-!
# Spectral bisection by explicit downward and upward passes

The traversal keeps the node matrices, bases and outputs in level arenas. Slot sizes and kinds
are actual stored words read through bounded index queries. Every level draws a fixed batch of
uniform and Gaussian words. The tape has one shared position: from level start `p`, uniform
words use positions `p + i` and Gaussian words use positions `p + n + w`; the batch advances
by `n + 4 * (n * n)`. The downward pass and the upward pass are first-order loops; the
node body is an explicit subprogram inserted through a frame, rather than a solver primitive.

The shared constant buffer contains one, two, one half, minus one, and the square root of one
half at offsets zero to four. The node frame receives dimensions `[n, L, F, d, lo, k]` and
operands `[par, Lv, Su, Sg, Ma, Qa, Sz, Kd, Kp, c]`, in that order. Its parent has already tested
that `k > 1` and that the node's stopping window is larger than the requested tolerance.

## Main results

* `NLAlib.SpectralBisection.downLevel`: parameter computation, samples, leaves and node frames.
* `NLAlib.SpectralBisection.bottomLevel`: fully initialized output at the recursion boundary.
* `NLAlib.SpectralBisection.upLevel`: child and split assembly from the actual metadata.
* `NLAlib.SpectralBisection.solve`: the fixed arena program for an explicit node subprogram.
* `NLAlib.SpectralBisection.program`: the complete tree with the actual node implementation.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has SampleOp Op]
  [Has MatrixOp Op] [Has IdxTst Tst] [Has CmpTst Tst]

/-- The eigenvalues of a leaf: real diagonal words for a one-dimensional node, or literal zeros
when the stopping window has already reached the requested accuracy. -/
def leafValues (diagonal : Bool) : Stmt Op Tst :=
  if diagonal then (PairMatrix.diagonalReal).body else ops% [k] (A) → (E) {
    for i < k { call (Has.inj (ScalarOp.lit 0)) [] () → (E[i]) }
  }

/-- A terminal node writes its complete identity, eigenvalue block and the stored leaf kind. -/
def leaf (diagonal : Bool) : Stmt Op Tst := ops% [k] (A) → (U, E, Kind) {
  run (PairMatrix.identity).body [k] (U);
  run (leafValues diagonal) [k] (A, E);
  call (Has.inj IndexOp.lit) [1] () → (Kind)
}

/-- Compute the next radius and tolerance using the same explicit rounded scalar operations.
The caller supplies the five-word workspace used later by the level's node dispatch. -/
def levelParameters : Impl Op Tst := opsImpl% [L, d] (c, Lv, t) → (Lv, t) {
  call (Has.inj IndexOp.lit) [L + d] () → (t);
  call (Has.inj ScalarOp.div) [] (c[1], t) → (t[2]);
  call (Has.inj ScalarOp.add) [] (c[2], t[2]) → (t[3]);
  call (Has.inj ScalarOp.mul) [] (t[3], Lv[2 * d]) → (Lv[2 * (d + 1)]);
  call (Has.inj ScalarOp.div) [] (c, t) → (t[1]);
  call (Has.inj ScalarOp.sub) [] (c, t[1]) → (t[3]);
  call (Has.inj ScalarOp.mul) [] (t[3], Lv[2 * d + 1]) → (Lv[2 * (d + 1) + 1])
}

/-- Dispatch a slot of size at least two using the actual rounded tolerance comparison. -/
def downLargeImpl (node : Stmt Op Tst) : Impl Op Tst :=
    opsImpl% [n, L, F, d, lo, k] (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c, t) → () {
  call (Has.inj ScalarOp.mul) [] (Lv[2 * d + 1], par) → (t[4]);
  if (Has.inj CmpTst.le) [] (Lv[2 * d], t[4]) {
    run (leaf false) [k]
      (Ma[2 * (n * n) * d + 2 * n * lo], Ua[2 * (n * n) * d + 2 * n * lo],
        Ea[n * d + lo], Kd[n * d + lo])
  } else {
    run node [n, L, F, d, lo, k] (par, Lv, Su, Sg, Ma, Qa, Sz, Kd, Kp, c)
  }
}

/-- Dispatch an active slot to a diagonal leaf, a tolerance leaf or the explicit node body.
The scalar threshold product and comparison use the actual stored level words. -/
def downNodeImpl (node : Stmt Op Tst) : Impl Op Tst :=
    opsImpl% [n, L, F, d, lo, k] (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c, t) → () {
  ifPos (1 - (k - 1)) {
    run (leaf true) [k]
      (Ma[2 * (n * n) * d + 2 * n * lo], Ua[2 * (n * n) * d + 2 * n * lo],
        Ea[n * d + lo], Kd[n * d + lo])
  };
  ifPos (k - 1) {
    run (downLargeImpl node).body [n, L, F, d, lo, k]
      (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c, t)
  }
}

/-- Visit each stored size slot using its actual bounded index query and active-node dispatch. -/
def downNodesImpl (node : Stmt Op Tst) : Impl Op Tst :=
    opsImpl% [n, L, F, d] (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c, t) → () {
  for lo < n {
    let k ← index (Has.inj IdxTst.toNat) (Sz[n * d + lo]) ≤ n - lo;
    ifPos k {
      run (downNodeImpl node).body [n, L, F, d, lo, k]
        (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c, t)
    }
  }
}

/-- Compute the next parameters and store the two complete sampling batches in order. -/
def downPrepareImpl : Impl Op Tst := opsImpl% [n, L, d] (c, Lv, Su, Sg, t) → () {
  run levelParameters.body [L, d] (c, Lv, t, Lv, t);
  run (sampleVector Stream.unif).body [n] (Su);
  run (sampleVector Stream.gauss).body [4 * (n * n)] (Sg)
}

/-- Prepare and visit a downward level using caller-owned scalar scratch storage. -/
def downLevelImpl (node : Stmt Op Tst) : Impl Op Tst :=
  opsImpl% [n, L, F, d] (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c, t) → () {
    run downPrepareImpl.body [n, L, d] (c, Lv, Su, Sg, t);
    run (downNodesImpl node).body [n, L, F, d]
      (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c, t)
  }

/-- A downward level computes the next window and tolerance, stores all samples and visits each
slot using its stored bounded size. The explicit node body has the frame in the module header. -/
def downLevel (node : Stmt Op Tst) : Stmt Op Tst :=
  ops% [n, L, F, d] (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c) → () {
    let t ← alloc 5;
    run (downLevelImpl node).body [n, L, F, d]
      (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c, t)
  }

/-- Initialize the mathematical recursion-boundary result with actual machine literals. -/
def bottomResultImpl : Impl Op Tst := opsImpl% [k] () → (U, E) {
  run (PairMatrix.identity).body [k] (U);
  for i < k { call (Has.inj (ScalarOp.lit 0)) [] () → (E[i]) }
}

/-- At the final depth, each active node writes the identity and zero eigenvalues. No node
operation is called when the recursion budget is exhausted. -/
def bottomLevel : Stmt Op Tst := ops% [n, D] (Sz) → (Ua, Ea) {
  for lo < n {
    let k ← index (Has.inj IdxTst.toNat) (Sz[n * D + lo]) ≤ n - lo;
    ifPos k {
      run bottomResultImpl.body [k]
        (Ua[2 * (n * n) * D + 2 * n * lo], Ea[n * D + lo])
    }
  }
}

/-- Reconstruct a one-child node from its complete child output and stored signed shift. -/
def upShiftResultImpl : Impl Op Tst := opsImpl% [k] (Uc, ec, sigma) → (U, E) {
  run (PairMatrix.copy).body [k, k] (Uc, U);
  run (scalarBroadcast (Has.inj ScalarOp.add)).body [k] (ec, sigma, E)
}

/-- Reconstruct a split from the two child outputs and the stored half-radius. -/
def upSplitResultImpl : Impl Op Tst :=
    opsImpl% [k, kp] (Qp, Qm, Up, Um, ep, em, sigma) → (U, E) {
  call (Has.inj MatrixOp.mul) [k, kp, kp] (Qp, Up) → (U);
  call (Has.inj MatrixOp.mul) [k, k - kp, k - kp] (Qm, Um) → (U[2 * (k * kp)]);
  run (scalarBroadcast (Has.inj ScalarOp.add)).body [kp] (ep, sigma, E);
  run (scalarBroadcast (Has.inj ScalarOp.sub)).body [k - kp] (em, sigma, E[kp])
}

/-- Reconstruct one node from its actual stored kind and split size. The signed half-radius
words are supplied by the enclosing upward level. -/
def upNodeImpl : Impl Op Tst := opsImpl% [n, d, lo, k] (Ua, Qa, Ea, Kd, Kp, t) → () {
  let kind ← index (Has.inj IdxTst.toNat) (Kd[n * d + lo]) ≤ 4;
  ifZero ((kind - 2) + (2 - kind)) {
    run upShiftResultImpl.body [k]
      (Ua[2 * (n * n) * (d + 1) + 2 * n * lo], Ea[n * (d + 1) + lo], t,
        Ua[2 * (n * n) * d + 2 * n * lo], Ea[n * d + lo])
  };
  ifZero ((kind - 3) + (3 - kind)) {
    run upShiftResultImpl.body [k]
      (Ua[2 * (n * n) * (d + 1) + 2 * n * lo], Ea[n * (d + 1) + lo], t[1],
        Ua[2 * (n * n) * d + 2 * n * lo], Ea[n * d + lo])
  };
  ifZero ((kind - 4) + (4 - kind)) {
    let kp ← index (Has.inj IdxTst.toNat) (Kp[n * d + lo]) ≤ k;
    run upSplitResultImpl.body [k, kp]
      (Qa[2 * (n * n) * d + 2 * n * lo],
        Qa[2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)],
        Ua[2 * (n * n) * (d + 1) + 2 * n * lo],
        Ua[2 * (n * n) * (d + 1) + 2 * n * (lo + kp)],
        Ea[n * (d + 1) + lo], Ea[n * (d + 1) + lo + kp], t,
        Ua[2 * (n * n) * d + 2 * n * lo], Ea[n * d + lo])
  }
}

/-- Visit every stored node size and reconstruct the occupied nodes using shared shifts. -/
def upNodesImpl : Impl Op Tst := opsImpl% [n, d] (Ua, Qa, Ea, Sz, Kd, Kp, t) → () {
  for lo < n {
    let k ← index (Has.inj IdxTst.toNat) (Sz[n * d + lo]) ≤ n - lo;
    ifPos k {
      run upNodeImpl.body [n, d, lo, k] (Ua, Qa, Ea, Kd, Kp, t)
    }
  }
}

/-- An upward level reads the executed node kind. A one-child node copies its child's basis;
a split multiplies the two bases by the two child outputs. All shifts use stored scalar words. -/
def upLevel : Stmt Op Tst := ops% [n, d] (Lv, Ua, Qa, Ea, Sz, Kd, Kp, c) → () {
  let t ← alloc 2;
  call (Has.inj ScalarOp.div) [] (Lv[2 * d], c[1]) → (t);
  call (Has.inj ScalarOp.neg) [] (t) → (t[1]);
  run upNodesImpl.body [n, d] (Ua, Qa, Ea, Sz, Kd, Kp, t)
}

/-- Compute the five actual rounded constants shared by all nodes. -/
def initialConstants : Impl Op Tst := opsImpl% [] () → (c) {
  call (Has.inj (ScalarOp.lit 1)) [] () → (c);
  call (Has.inj IndexOp.lit) [2] () → (c[1]);
  call (Has.inj ScalarOp.div) [] (c, c[1]) → (c[2]);
  call (Has.inj ScalarOp.neg) [] (c) → (c[3]);
  call (Has.inj ScalarOp.sqrt) [] (c[2]) → (c[4])
}

/-- Initialize every size slot, then store the actual root size literal in the first slot. -/
def initialSizes : Impl Op Tst := opsImpl% [n, L] () → (Sz) {
  for w < n * (L + 2) + 1 { call (Has.inj IndexOp.lit) [0] () → (Sz[w]) };
  call (Has.inj IndexOp.lit) [n] () → (Sz)
}

/-- Copy the supplied root radius and tolerance into the level arena. -/
def initialParameters : Impl Op Tst := opsImpl% [] (par) → (Lv) {
  call (Has.inj ScalarOp.copy) [] (par) → (Lv);
  call (Has.inj ScalarOp.copy) [] (par[1]) → (Lv[1])
}

/-- Initialize the actual shared constants, root matrix, size slots and root level parameters.
All arena storage is caller-owned; the helpers preserve the order of the primitive calls. -/
def initializeArenas : Impl Op Tst := opsImpl% [n, L] (A, par) → (c, Ma, Sz, Lv) {
  run initialConstants.body [] (c);
  run initialSizes.body [n, L] (Sz);
  run (PairMatrix.copy).body [n, n] (A, Ma);
  run initialParameters.body [] (par, Lv)
}

/-- Reconstruct every level in reverse depth order from the initialized bottom results.
The frame preserves the scalar calls and node iteration of each upward level. -/
def upwardPass : Impl Op Tst := opsImpl% [n, L] (Lv, Ua, Qa, Ea, Sz, Kd, Kp, c) → () {
  for r < L + 1 { run upLevel [n, L - r] (Lv, Ua, Qa, Ea, Sz, Kd, Kp, c) }
}

/-- Visit all downward levels in increasing depth, with the fixed actual node tree. -/
def downwardPass (node : Stmt Op Tst) : Impl Op Tst :=
  opsImpl% [n, L, F] (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c) → () {
    for d < L + 1 {
      run (downLevel node) [n, L, F, d] (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c)
    }
  }

/-- Copy the reconstructed root basis and eigenvalues into the supplied output views. -/
def rootResultCopy : Impl Op Tst := opsImpl% [n] (Ua, Ea) → (U, dv) {
  run (PairMatrix.copy).body [n, n] (Ua, U);
  run (unaryMap (Has.inj ScalarOp.copy)).body [n] (Ea, dv)
}

/-- Initialize the bottom results and reconstruct the supplied root outputs. -/
def reconstructResult : Impl Op Tst :=
    opsImpl% [n, L] (c, Ua, Qa, Ea, Sz, Kd, Kp, Lv) → (U, dv) {
  run bottomLevel [n, L + 1] (Sz, Ua, Ea);
  run upwardPass.body [n, L] (Lv, Ua, Qa, Ea, Sz, Kd, Kp, c);
  run rootResultCopy.body [n] (Ua, Ea, U, dv)
}

/-- Execute initialization, the two traversals and the final result copies on caller-owned
arenas. The node argument is an explicit statement tree passed through counted frames. -/
def solveBody (node : Stmt Op Tst) : Stmt Op Tst :=
    ops% [n, L, F] (A, par, U, dv, c, Ma, Ua, Qa, Ea, Sz, Kd, Kp, Lv, Su, Sg) → () {
  run initializeArenas.body [n, L] (A, par, c, Ma, Sz, Lv);
  run (downwardPass node).body [n, L, F] (par, Lv, Su, Sg, Ma, Ua, Qa, Ea, Sz, Kd, Kp, c);
  run reconstructResult.body [n, L] (c, Ua, Qa, Ea, Sz, Kd, Kp, Lv, U, dv)
}

/-- The fixed spectral-bisection traversal around an explicit node subprogram. All supplied
output cells are written from the root arena, and every temporary arena is scoped locally.
The node argument is a statement tree, substituted through frames, with no additional primitive. -/
def solve (node : Stmt Op Tst) : Stmt Op Tst := ops% [n, L, F] (A, par) → (U, dv) {
  let c ← alloc 5;
  let Ma ← alloc (2 * (n * n) * (L + 2));
  let Ua ← alloc (2 * (n * n) * (L + 2));
  let Qa ← alloc (2 * (n * n) * (L + 1));
  let Ea ← alloc (n * (L + 2));
  let Sz ← alloc (n * (L + 2) + 1);
  let Kd ← alloc (n * (L + 1));
  let Kp ← alloc (n * (L + 1));
  let Lv ← alloc (2 * (L + 2));
  let Su ← alloc n;
  let Sg ← alloc (4 * (n * n));
  run (solveBody node) [n, L, F] (A, par, U, dv, c, Ma, Ua, Qa, Ea, Sz, Kd, Kp, Lv, Su, Sg)
}

/-- The traversal has three dimensions, two input blocks and two output blocks. -/
def solveImpl (node : Stmt Op Tst) : Impl Op Tst := ⟨3, 2, 2, solve node⟩

/-- The complete fixed first-order program: the explicit node tree is substituted before any
size or input is supplied. Numerical and resource certification are separate theorems. -/
def program : Program Op Tst 3 4 := ⟨solve node⟩

/-- The final program contains the explicit node statement through frames, with no node call
added to the operation signature and no input-dependent program construction. -/
theorem body_program_eq_solve :
    (program (Op := Op) (Tst := Tst)).body = solve node := rfl

end NLAlib.SpectralBisection
