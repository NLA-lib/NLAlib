/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.MGS.Alg
public import NLAlib.Ops.Blas.ColumnProducts
public import NLAlib.Ops.Blas.Sampling
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Sampling
public import NLAlib.Ops.Catalog.StoredOperator

/-!
# Hutch++ as one fixed program

The estimator samples a sketch and probes, performs rank-revealing modified
Gram–Schmidt, projects the probes and accumulates the two trace contributions.
The matrix-vector operation reads an explicit data operand. The oracle, dense and
sparse operation models assign that operand their declared storage meaning.

## Main definitions

* `NLAlib.HutchPlusPlus.applyColumns` batches explicit matrix-vector calls.
* `NLAlib.HutchPlusPlus.estimate` is the complete estimator implementation.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]
  [Has SampleOp Op] [Has StoredOperatorOp Op] [Has IndexOp Op]

/-- Apply the represented square matrix to each of `k` column-major vectors.
The input and output vector blocks may be disjoint subviews of larger buffers. -/
def applyColumns : Impl Op Tst := opsImpl% [n, k] (data, X) → (Y) {
  for j < k {
    call (Has.inj StoredOperatorOp.matvec) [n, n] (data, X[n * j]) → (Y[n * j])
  }
}

/-- Draw the sketch, form its image and release the sketch before later workspaces
are allocated. Sample words are read in column-major order. -/
def sketch (stream : ℕ) : Impl Op Tst := opsImpl% [n, k] (data) → (B) {
  let S ← alloc (n * k);
  run (sampleVector stream).body [n * k] (S);
  run applyColumns.body [n, k] (data, S, B)
}

/-- Sweep every probe against the computed sketch-image columns. The basis prefix
is retained and each probe is updated in its own column-major subview. -/
def projectProbes : Impl Op Tst := opsImpl% [n, k, ell] (B, t) → () {
  for j < ell {
    run MGS.sweep.body [n, k] (B, B[n * (k + j)], t)
  }
}

/-- Add the averaged residual sum to the retained low-rank trace contribution.
`t[1]` contains the residual sum; `out` contains the low-rank contribution. -/
def combineTrace : Impl Op Tst := opsImpl% [ell] (t, out) → () {
  call (Has.inj IndexOp.lit) [ell] () → (t);
  call (Has.inj ScalarOp.div) [] (t[1], t) → (t[1]);
  call (Has.inj ScalarOp.add) [] (out, t[1]) → (out)
}

/-- Accumulate the low-rank trace plus the averaged residual contribution.
The positive probe-count premise belongs to the total mathematical theorem. -/
def accumulate : Impl Op Tst := opsImpl% [n, k, ell] (B, C, t) → (out) {
  run ColumnProducts.sum.body [n, k] (B, C, t, out);
  run ColumnProducts.sum.body [n, ell] (B[n * k], C[n * k], t, t[1]);
  run combineTrace.body [ell] (t, out)
}

/-- Prepare the rank-revealing sketch-image basis followed by untouched probes.
The temporary sketch and MGS workspace are scoped inside their own procedures. -/
def prepare (stream : ℕ) : Impl Op Tst := opsImpl% [n, k, ell] (data) → (B) {
  run (sketch stream).body [n, k] (data, B);
  run (sampleVector stream).body [n * ell] (B[n * k]);
  run MGS.factor.body [n, k] (B)
}

/-- Apply the operator to the prepared basis and reduced probes, then evaluate the
trace contributions. All workspaces are supplied explicitly by the caller. -/
def evaluate : Impl Op Tst := opsImpl% [n, k, ell] (data, B, t, C) → (out) {
  run applyColumns.body [n, k + ell] (data, B, C);
  run accumulate.body [n, k, ell] (B, C, t, out)
}

/-- Finish from the prepared basis and probes, scoping the coefficient and operator-output
workspaces around probe projection and trace evaluation. -/
def finish : Impl Op Tst := opsImpl% [n, k, ell] (data, B) → (out) {
  let t ← alloc 2;
  run projectProbes.body [n, k, ell] (B, t);
  let C ← alloc (n * (k + ell));
  run evaluate.body [n, k, ell] (data, B, t, C, out)
}

/-- Full Hutch++, including zero-safe MGS for rank-deficient sketch images.
All matrix entries, samples, arithmetic and control operations are visible;
only local matrix-vector application is supplied by the operator model. -/
def estimate (stream : ℕ) : Impl Op Tst := opsImpl% [n, k, ell] (data) → (out) {
  let B ← alloc (n * (k + ell));
  run (prepare stream).body [n, k, ell] (data, B);
  run finish.body [n, k, ell] (data, B, out)
}

/-- A fixed three-dimension program with declared operator-data and output buffers. -/
def program (stream : ℕ) : Program Op Tst 3 2 :=
  (estimate stream).program 2 [⟨0, .const 0⟩] [⟨1, .const 0⟩]

end NLAlib.HutchPlusPlus
