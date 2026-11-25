/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Exact
public import NLAlib.Matrix.Factorizations.LDL.DiagonalSolve
public import NLAlib.Ops.Blas.Level1

/-!
# Solving a stored LDL product system

The actual scalar tree copies the right-hand side, performs lower substitution, divides by
the stored diagonal, and performs transposed-lower substitution. Both factor operands are
retained. The specification uses the decoded factors themselves, without assuming a
factorization, a successful run or a supplied solution.

## Main results

* `NLAlib.TriangularSolve.ldlFactors_meets`: actual scalar solution of the three-factor system.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Solve a stored lower-diagonal-transposed-lower system with actual scalar substitutions
and diagonal division. Only the reported vector changes. -/
def ldlFactors : Routine Op Tst :=
  routine% [n] (L : n * n, d : n, b : n) → (x : n) {
    run copyLoopRoutine [n] (b, x);
    run forward [n] (L, x);
    run LDL.divideDiagonal [n] (d, x);
    run backward [n] (L, x)
  }

variable [Inhabited K]

/-- A lower triangular factor with nonzero diagonal and a nonzero stored diagonal define the
system. Definiteness and a precomputed factorization are unnecessary for this consumer. -/
def ldlFactorsSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (ls, ds, bs) → (xs) requires
    (decodeMatrix dec n n ls).IsLowerTriangular ∧
      (∀ i < n, dec (vec ls (i * n + i)) ≠ 0) ∧
      (∀ i : Fin n, dec (vec ds i.val) ≠ 0) ensures
    (decodeMatrix dec n n ls * Matrix.diagonal (decv dec n ds) *
      (decodeMatrix dec n n ls)ᴴ) *ᵥ decv dec n xs = decv dec n bs

/-- Exact local arithmetic proves success and the product-system equation for all orders.
Every scalar division uses the stated nonzero stored diagonal, rather than a run premise. -/
theorem ldlFactors_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (ldlFactors (Op := Op) (Tst := Tst)).Meets I (ldlFactorsSpec dec) := by
  routine_intro [n] (L, d, b, x) reads (ls, ds, bs)
  obtain ⟨hL, hdL, hd⟩ := hpre
  call (copyLoopRoutine_meets hI (fun _ => True)) [n] (b, x)
    as m₁ hfr₁ hpos₁ (copied) hcopy
  obtain rfl : copied = bs := (List.cons.inj hcopy).1
  call (forward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hdL)
    as m₂ hfr₂ hpos₂ (ys) hforward
  have hLy := forwardSpec_mulVec_eq (τ := τ.shift m₁.pos) hforward hL hdL
  call (LDL.divideDiagonal_meets hI) [n] (d, x)
    as m₃ hfr₃ hpos₃ (zs) hdivide
  have hDz := LDL.diagonal_mulVec_eq_of_divideDiagonalSpec hM hd hdivide
  call (backward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hdL)
    as m₄ hfr₄ hpos₄ (ws) hbackward
  have hLw := backwardSpec_mulVec_eq (τ := τ.shift m₃.pos) hbackward hL hdL
  routine_exit
  change (decodeMatrix dec n n ls * Matrix.diagonal (decv dec n ds) *
    (decodeMatrix dec n n ls)ᴴ) *ᵥ decv dec n ws = _
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mulVec_mulVec, hLw,
    ← Matrix.mulVec_mulVec, hDz, hLy]

end NLAlib.TriangularSolve
