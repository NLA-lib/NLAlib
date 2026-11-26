/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.DiagonalChoice
public import NLAlib.Matrix.Factorizations.Cholesky.PivotedAdvance
public import NLAlib.Matrix.Factorizations.Cholesky.SemidefiniteSteps
public import NLAlib.Matrix.Factorizations.Cholesky.Initialize
public import NLAlib.Matrix.Factorizations.CholeskyDiagonalPivoting

/-!
# Scalar diagonal-pivoted semidefinite Cholesky

Each step gathers and scans the actual residual diagonal, reads its stored absolute pivot,
exchanges the residual symmetrically and the factor's full rows, records the pivot, and runs
the existing zero-safe Cholesky step. The copied residual and every scalar temporary are
scoped. No factorization or matrix-permutation operation is added to the operation signature.

## Main definitions

* `NLAlib.Cholesky.pivotedRightLooking`: the complete fixed scalar tree.
* `NLAlib.Cholesky.pivotedRightLookingSpec`: the actual log and semidefinite Gram guarantee.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Select, read and record the actual absolute diagonal pivot, apply both residual exchanges
and the full factor-row exchange, then materialize the next zero-safe factor column. -/
def pivotedStep : Stmt Op Tst := ops% [n, k] (R, L, H) → () {
  let selected ← alloc 1;
  run diagonalChoice [n, k] (R, selected);
  let row ← index (Has.inj IdxTst.toNat) (selected) ≤ n - 1;
  run pivotedAdvance [n, k, row] (R, L, H)
}

/-- The full loop of symmetric diagonal pivoting on an initialized factor and copied residual. -/
def pivotedLoop : Stmt Op Tst := ops% [n] (R, L, H) → () {
  for k < n {
    run pivotedStep [n, k] (R, L, H)
  }
}

/-- Copy the original matrix before every output write, then compute the factor and pivot log.
Only residual scratch must be separate from the source and both output buffers. -/
def pivotedWithScratch : Stmt Op Tst := ops% [n] (A, L, H, R) → () {
  run initializeLower [n] (A, R, L);
  run pivotedLoop [n] (R, L, H)
}

/-- Full first-maximum diagonal-pivoted Cholesky. The log contains absolute current-position
indices, one per actual symmetric exchange; singular zero pivots execute no division. -/
def pivotedRightLooking : Routine Op Tst :=
  routine% [n] (A : n * n) → (L : n * n, H : n) {
    ifPos n {
      let R ← alloc (n * n);
      run pivotedWithScratch [n] (A, L, H, R)
    }
  }

/-- At order zero the raw scalar body reads no operands and leaves the complete memory
unchanged, for arbitrary handles, offsets, aliases and even an empty caller store. -/
theorem eval_pivotedRightLooking_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (pivotedRightLooking (Op := Op) (Tst := Tst)).body
      (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The actual stored log determines a symmetric permutation. Its canonical lower factor has
nonnegative diagonal and reconstructs the permuted semidefinite input, with literal upper
zeros. The log also records the first maximal diagonal at every actual pivot step. -/
def pivotedRightLookingSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls, hs) requires (decodeMatrix dec n n as).PosSemidef ensures
    ∃ p : Fin n → Fin n,
      (∀ j : Fin n, dec (vec hs j.val) = (p j).val) ∧
      HasDiagonalPivotPrefix (decodeMatrix dec n n as) p n ∧
      let σ := luPivotPermutation p n
      let B := (decodeMatrix dec n n as).submatrix σ σ
      decodeMatrix dec n n ls = choleskyLower B ∧
        (decodeMatrix dec n n ls).IsLowerTriangular ∧
        (∀ i : Fin n, 0 ≤ decodeMatrix dec n n ls i i) ∧
        B = decodeMatrix dec n n ls * (decodeMatrix dec n n ls)ᴴ ∧
        (∀ i j : Fin n, i < j → vec ls (j.val * n + i.val) = M.lit 0)

/-- The empty factor and log satisfy the zero-order numerical postcondition without any
input-entry or pivot assumption. This is the postcondition of the handle-free empty body. -/
theorem pivotedRightLookingSpec_empty (M : Machine K) (dec : K → ℝ) (as : List K)
    (τ : Tape K) : (pivotedRightLookingSpec M dec).post [0] τ [as] [[], []] := by
  refine ⟨id, fun i => Fin.elim0 i, HasDiagonalPivotPrefix.initial _ _,
    ?_, ?_, fun i => Fin.elim0 i, ?_, fun i => Fin.elim0 i⟩
  · ext i j
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · ext i j
    exact Fin.elim0 i

end NLAlib.Cholesky
