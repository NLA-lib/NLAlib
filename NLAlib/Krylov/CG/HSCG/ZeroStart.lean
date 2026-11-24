/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Solve
public import NLAlib.Ops.Blas.Fill

/-!
# Conjugate gradient from the zero iterate

The routine `NLAlib.Krylov.CG.HSCG.zeroStartRoutine` reads the right-hand side and writes the
iterate, the residual and the direction: it fills the iterate with literal zeros and runs the
fixed-horizon solver `NLAlib.Krylov.CG.HSCG.solve` on it. Its specification mentions only the
dimensions, the right-hand side read and the three vectors written.

## Main definitions

* `NLAlib.Krylov.CG.HSCG.zeroStart`: the tree.
* `NLAlib.Krylov.CG.HSCG.zeroStartRoutine`, `NLAlib.Krylov.CG.HSCG.zeroStartSpec`: the routine
  and its specification.

## Main results

* `NLAlib.Krylov.CG.HSCG.zeroStartRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Zero the iterate, then solve. Index variables: `n`, `k`, then the offsets of `b`, `x`, `r`,
`p`. -/
def zeroStart : Stmt Op Tst := ops% [n, k] (B) → (X, R, P) {
  run (fillRoutine (Op := Op) (Tst := Tst) (Has.inj (ScalarOp.lit 0))) [n] (X);
  run (solveRoutine (Op := Op) (Tst := Tst)) [n, k] (B, X, R, P)
}

/-- Conjugate gradient from the zero iterate: the right-hand side is read, and the iterate, the
residual and the direction are written. -/
def zeroStartRoutine : Routine Op Tst :=
  routine% [n, k] (b : n) → (x : n, r : n, p : n) := zeroStart

/-- For the order `n` of the matrix and a horizon `k` at most the Krylov grade of the right-hand
side, the three written vectors are the conjugate gradient state after `k` steps from the zero
iterate. -/
noncomputable def zeroStartSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m, k] (bs) → (xs, rs, ps)
    requires m = n ∧ k ≤ krylovGrade A (decv dec n bs)
    ensures decodedState dec n xs rs ps = cgState A (decv dec n bs) 0 k

/-- Conjugate gradient from the zero iterate meets its specification for every exact operation
interpretation and every positive-definite matrix: the iterate is zeroed, then the solver runs,
each used by its judgment. -/
theorem zeroStartRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) (hPos : A.PosDef) :
    (zeroStartRoutine (Op := Op) (Tst := Tst)).Meets I (zeroStartSpec dec A) := by
  routine_intro [n', k] (b, x, r, p) reads (bs)
  obtain ⟨hn, hk⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hx0 : decv dec n (List.replicate n (M.lit 0)) = 0 := by
    have hz0 : dec (M.lit 0) = 0 := by simpa using hM.lit 0
    ext i
    simp [decv, vec, i.isLt, hz0]
  have hk' : k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n (List.replicate n (M.lit 0))) := by
    rw [hx0, Matrix.mulVec_zero, sub_zero]
    exact hk
  call (fillRoutine_meets (Tst := Tst) (hS (.lit 0))) [n] (x) as m₁ hfr₁ hpos₁ (xs₀) hzero
  obtain rfl : xs₀ = List.replicate n (M.lit 0) := hzero
  call (solveRoutine_meets hS hM hB hA hPos) [n, k] (b, x, r, p) (pre := ⟨rfl, hk'⟩)
    as m₂ hfr₂ hpos₂ (xs', rs, ps) hst
  routine_exit
  have hst : decodedState dec n xs' rs ps =
      cgState A (decv dec n bs) (decv dec n (List.replicate n (M.lit 0))) k := hst
  rw [hx0] at hst
  exact hst

end NLAlib.Krylov.CG.HSCG
