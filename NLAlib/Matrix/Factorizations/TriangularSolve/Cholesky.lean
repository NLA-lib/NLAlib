/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Exact
public import NLAlib.Ops.Blas.Level1

/-!
# Solving with a stored Cholesky factor

Forward substitution and transposed-lower back substitution solve the Gram system of a
stored lower factor. A copy of the right-hand side is the only caller output, and no matrix
transpose is materialized. The specification uses the actual decoded factor's Gram matrix.

## Main results

* `NLAlib.TriangularSolve.cholesky_meets`: the actual scalar loops solve the Gram system.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Copy the right-hand side, solve with the stored lower triangle, then its transpose.
The factor and original right-hand side are retained, with one scalar scratch cell per solve.
The outer dimension guard bypasses every allocation and operand frame at order zero. -/
def cholesky : Routine Op Tst := routine% [n] (L : n * n, b : n) → (x : n) {
  ifPos n {
    run copyLoopRoutine [n] (b, x);
    run forward [n] (L, x);
    run backward [n] (L, x)
  }
}

/-- Empty execution reads no operands and restores the complete memory for arbitrary
handles, offsets and aliases, independently of all scalar laws. -/
theorem eval_cholesky_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (cholesky (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The actual decoded factor's Gram matrix maps the output to the original right-hand side.
Its lower triangle is used directly, with a nonzero diagonal at every stored position. -/
def choleskySpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (ls, bs) → (xs) requires
    ((decodeMatrix dec n n ls).IsLowerTriangular ∧
      ∀ i < n, dec (vec ls (i * n + i)) ≠ 0) ensures
    (decodeMatrix dec n n ls * (decodeMatrix dec n n ls)ᴴ) *ᵥ decv dec n xs = decv dec n bs

/-- The actual forward and backward loops solve the stored Gram system under exact scalar
arithmetic. The matrix may have order zero; no execution or solution is assumed. -/
theorem cholesky_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (cholesky (Op := Op) (Tst := Tst)).Meets I (choleskySpec dec) := by
  routine_intro [n] (L, b, x) reads (ls, bs)
  change Writes .total I τ _ (Env.frame [n] [L, b, x]) (Fp.blocks [x] [n]) _ m
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    obtain ⟨hL, hd⟩ := hpre
    call (copyLoopRoutine_meets hI (fun _ => True)) [n] (b, x)
      as m₁ hfr₁ hpos₁ (copied) hcopy
    obtain rfl : copied = bs := (List.cons.inj hcopy).1
    call (forward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hd)
      as m₂ hfr₂ hpos₂ (ys) hforward
    have hLy := forwardSpec_mulVec_eq (τ := τ.shift m₁.pos) hforward hL hd
    call (backward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hd)
      as m₃ hfr₃ hpos₃ (zs) hbackward
    have hLz := backwardSpec_mulVec_eq (τ := τ.shift m₂.pos) hbackward hL hd
    routine_exit
    change (decodeMatrix dec n n ls * (decodeMatrix dec n n ls)ᴴ) *ᵥ decv dec n zs = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mulVec_mulVec, hLz, hLy]
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, [[]], Mem.readBlocks_of_cons rfl rfl, ?_⟩
    ext i
    exact i.elim0

end NLAlib.TriangularSolve
