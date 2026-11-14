/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.HalfNorm
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# The actual scalar binary search for a promising Ritz value

A six-word workspace stores the current window start, half length, exponent, two computed
half norms and their reusable singularity report. Index words use the standard dimension
literal operation and bounded toNat queries. Every half norm executes the scalar row solver.

## Main results

* `NLAlib.ShiftedQR.findRitzLevel`: one actual half-norm comparison and index update.
* `NLAlib.ShiftedQR.findRitzSearch`: the complete scoped binary search implementation.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Compute the two actual half norms into workspace words three and four. -/
def findRitzNorms : Impl Op Tst := opsImpl% [d, k, a, h, e] (H, SS, R) → (R) {
  run halfNorm.body [d, k, a, h, e] (H, SS, R[3], R[5]);
  run halfNorm.body [d, k, a + h, h, e] (H, SS, R[4], R[5])
}

/-- Keep the first half on a norm tie, updating the start only for a larger second half. -/
def findRitzChoice : Impl Op Tst := opsImpl% [a, h] (R) → (R) {
  if (Has.inj CmpTst.le) [] (R[4], R[3]) {
    skip
  } else {
    call (Has.inj IndexOp.lit) [a + h] () → (R)
  }
}

/-- Keep the larger-norm half and update the natural half length and exponent. -/
def findRitzDecision : Impl Op Tst := opsImpl% [a, h, e] (R) → (R) {
  run findRitzChoice.body [a, h] (R, R);
  call (Has.inj IndexOp.lit) [h / 2] () → (R[1]);
  call (Has.inj IndexOp.lit) [2 * e] () → (R[2])
}

/-- Compare the actual norms of a known pair of half windows and update the three indices. -/
def findRitzWindow : Impl Op Tst := opsImpl% [d, k, a, h, e] (H, SS, R) → (R) {
  run findRitzNorms.body [d, k, a, h, e] (H, SS, R, R);
  run findRitzDecision.body [a, h, e] (R, R)
}

/-- One binary-search level reads its bounded natural indices before evaluating its halves. -/
def findRitzLevel : Impl Op Tst := opsImpl% [d, k] (H, SS, R) → (R) {
  let a ← index (Has.inj IdxTst.toNat) (R) ≤ k;
  let h ← index (Has.inj IdxTst.toNat) (R[1]) ≤ k;
  let e ← index (Has.inj IdxTst.toNat) (R[2]) ≤ k;
  run findRitzWindow.body [d, k, a, h, e] (H, SS, R, R)
}

/-- Initialize the three natural state indices from the actual supplied list count. -/
def findRitzInitialize : Impl Op Tst := opsImpl% [k] (R) → (R) {
  call (Has.inj IndexOp.lit) [0] () → (R);
  call (Has.inj IndexOp.lit) [k / 2] () → (R[1]);
  call (Has.inj IndexOp.lit) [1] () → (R[2])
}

/-- Read the selected bounded index and copy the corresponding actual complex shift. -/
def findRitzCopy : Impl Op Tst := opsImpl% [k] (SS, R) → (Center) {
  let a ← index (Has.inj IdxTst.toNat) (R) ≤ k;
  run Hermitian.copyPair.body [] (SS[2 * a], Center)
}

/-- Execute the requested number of actual bounded-index binary-search levels. -/
def findRitzLevels : Impl Op Tst := opsImpl% [d, m, k] (H, SS, R) → (R) {
  for level < m {
    run findRitzLevel.body [d, k] (H, SS, R, R)
  }
}

/-- Initialize natural indices, perform the requested binary-search levels, then copy the
selected actual stored complex candidate. Six caller-owned words hold all search state. -/
def findRitzSearchWithScratch : Impl Op Tst := opsImpl% [d, m, k] (H, SS, R) → (Center) {
  run findRitzInitialize.body [k] (R, R);
  run findRitzLevels.body [d, m, k] (H, SS, R, R);
  run findRitzCopy.body [k] (SS, R, Center)
}

/-- Scope the six search-state words around the actual binary search.
Algorithm: shifted-qr (run model) -/
def findRitzSearch : Impl Op Tst := opsImpl% [d, m, k] (H, SS) → (Center) {
  let R ← alloc 6;
  run findRitzSearchWithScratch.body [d, m, k] (H, SS, R, Center)
}

end NLAlib.ShiftedQR
