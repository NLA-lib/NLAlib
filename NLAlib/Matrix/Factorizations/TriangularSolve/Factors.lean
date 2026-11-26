/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Exact
public import NLAlib.Ops.Blas.Level1

/-!
# Solving with stored triangular factors

Copy the right-hand side once, then apply forward substitution and direct upper back
substitution. Both factors and the original right-hand side are retained. The specification
uses their actual decoded product, so it can be composed with a factorization judgment
without admitting a matrix that is absent from the input buffers.

## Main results

* `NLAlib.TriangularSolve.factors_meets`: the scalar routine solves the product system exactly.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Solve a lower-times-upper product system into a fresh output, using one copy of the
right-hand side and the actual in-place scalar substitution routines.
The outer dimension guard bypasses every allocation and operand frame at order zero. -/
def factors : Routine Op Tst :=
  routine% [n] (L : n * n, U : n * n, b : n) → (x : n) {
    ifPos n {
      run copyLoopRoutine [n] (b, x);
      run forward [n] (L, x);
      run upper [n] (U, x)
    }
  }

/-- Empty execution reads no operands and restores the complete memory for arbitrary
handles, offsets and aliases, independently of all scalar laws. -/
theorem eval_factors_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (factors (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

variable [Inhabited K]

/-- The product of the two actual decoded triangular factors maps the computed vector to
the original right-hand side. Both stored diagonals are required to be nonzero. -/
def factorsSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (ls, us, bs) → (xs) requires
    ((decodeMatrix dec n n ls).IsLowerTriangular ∧
      (decodeMatrix dec n n us).IsUpperTriangular ∧
      (∀ i < n, dec (vec ls (i * n + i)) ≠ 0) ∧
      (∀ i < n, dec (vec us (i * n + i)) ≠ 0)) ensures
    (decodeMatrix dec n n ls * decodeMatrix dec n n us) *ᵥ decv dec n xs = decv dec n bs

/-- The actual copy and two substitution loops solve the stored product system under exact
scalar arithmetic. No successful-execution or precomputed-solution hypothesis is needed. -/
theorem factors_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (factors (Op := Op) (Tst := Tst)).Meets I (factorsSpec dec) := by
  routine_intro [n] (L, U, b, x) reads (ls, us, bs)
  change Writes .total I τ _ (Env.frame [n] [L, U, b, x]) (Fp.blocks [x] [n]) _ m
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    obtain ⟨hL, hU, hdL, hdU⟩ := hpre
    call (copyLoopRoutine_meets hI (fun _ => True)) [n] (b, x)
      as m₁ hfr₁ hpos₁ (copied) hcopy
    obtain rfl : copied = bs := (List.cons.inj hcopy).1
    call (forward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hdL)
      as m₂ hfr₂ hpos₂ (ys) hforward
    have hLy := forwardSpec_mulVec_eq (τ := τ.shift m₁.pos) hforward hL hdL
    call (upper_meets hI hM.toStdModel_zero) [n] (U, x) (pre := hdU)
      as m₃ hfr₃ hpos₃ (zs) hupper
    have hUz := upperSpec_mulVec_eq (τ := τ.shift m₂.pos) hupper hU hdU
    routine_exit
    change (decodeMatrix dec n n ls * decodeMatrix dec n n us) *ᵥ decv dec n zs = _
    rw [← Matrix.mulVec_mulVec, hUz, hLy]
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, [[]], Mem.readBlocks_of_cons rfl rfl, ?_⟩
    ext i
    exact i.elim0

end NLAlib.TriangularSolve
