/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Blas.MapCorrect

/-!
# The actual scalar copy with exact aliases

The existing scalar copy tree is the shared unary map of the copy operation. Its raw rule
admits an exact input/output alias or spatially disjoint blocks, including different offsets
of one buffer. No operand frame or live-handle condition is added to the raw loop.

## Main results

* `NLAlib.Ops.copyLoopRoutine_writes_of_disj_or_eq`: the unchanged copy tree's raw alias rule.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- The actual scalar copy preserves the original words and tape position, writing only its
output block. Exact aliases or disjoint blocks are admitted; shifted overlapping blocks are
excluded. Empty copies need neither valid handles nor capacities beyond the stated empty
output bound. This is the shared unary-map proof applied to the unchanged copy tree. -/
theorem copyLoopRoutine_writes_of_disj_or_eq {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {n : ℕ} {x y : ℕ × ℕ} {m : Mem K} {xs : List K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hx : m.store.readBlock x.1 x.2 n = some xs) (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I τ (copyLoopRoutine (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [x, y]) (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 n = some xs) m := by
  simpa only [copyLoopRoutine, copyLoop, unaryMap, List.map_id] using
    (unaryMap_writes_of_disj_or_eq (τ := τ) (f := id) (hI .copy) hxy hx hy)

end NLAlib.Ops
