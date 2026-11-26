/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.BlockedStep
public import NLAlib.Matrix.Factorizations.LU.Initialize
public import NLAlib.Ops.Blas.MatrixUpdate

/-!
# Stored blocked LU with scalar matrix-product trailing updates

Each clipped panel performs two saved-operand rank-one rectangle updates per pivot.
One trailing correction then packs the stored factor blocks, computes their scalar matrix
product, and subtracts it from the residual. The source is copied before either output is
initialized. There is no matrix-product or factorization primitive in the signature.

## Main results

* `NLAlib.LU.eval_factorBlocked_zero`: empty raw execution is handle- and model-independent.
* The complete exact routine judgment is proved in the companion blocked routine module.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- The complete clipped-panel loop on caller-owned residual scratch. The width is the
natural-number expression for `min b (n - b * block)`. -/
def blockedLoop : Stmt Op Tst := ops% [n, b, q] (R, L, U) → () {
  for block < q {
    run blockedStep [n, b * block, b - (b - (n - b * block))] (R, L, U)
  }
}

/-- Copy the complete source before clearing either factor, then execute the entire clipped
block loop on caller-owned residual scratch. This fragment also serves overlapping sources. -/
def blockedWithScratch : Stmt Op Tst := ops% [n, b, q] (A, R, L, U) → () {
  run initializeFactors [n] (A, R, L, U);
  run blockedLoop [n, b, q] (R, L, U)
}

/-- Copy the source before clearing either factor, then run all clipped panels and scalar
matrix-product corrections. The positive symbolic block size and exact ceiling count are
dimensions. The actual dimension guard bypasses all frames at order zero, including invalid
handles coinciding with fresh scratch. Positive-order scalar instruction order is unchanged;
the guard contributes ordinary structural charges. -/
def factorBlocked : Routine Op Tst :=
  routine% [n, b, q] (A : n * n) → (L : n * n, U : n * n) {
    ifPos n {
      let R ← alloc (n * n);
      run blockedWithScratch [n, b, q] (A, R, L, U)
    }
  }

/-- Empty order reads no operand and restores the entire memory for arbitrary handles,
offsets and aliases, independently of the arithmetic model and the supplied block dimensions. -/
theorem eval_factorBlocked_zero (I : Interp Op Tst K) (τ : Tape K) (B Q : ℕ)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (factorBlocked (Op := Op) (Tst := Tst)).body
      (Env.frame [0, B, Q] args) m = some m := by
  rfl

variable [Inhabited K]

/-- Positive block size and its exact ceiling count govern the actual loop. The original
matrix has nonzero canonical Gaussian pivots; the actual decoded outputs are its canonical
factors and satisfy the full LU identity. This includes the empty matrix. -/
def factorBlockedSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n, b, q] (as) → (ls, us) requires
    0 < b ∧ q = (n + b - 1) / b ∧
      (∀ i : Fin n, gaussState (decodeMatrix dec n n as) i.val i i ≠ 0) ensures
    decodeMatrix dec n n ls = luLower (decodeMatrix dec n n as) ∧
      decodeMatrix dec n n us = luUpper (decodeMatrix dec n n as) ∧
      IsLU (decodeMatrix dec n n as) (decodeMatrix dec n n ls) (decodeMatrix dec n n us)

end NLAlib.LU
