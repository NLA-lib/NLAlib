/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Solve
public import NLAlib.Ops.Blas.Fill

/-!
# Capped conjugate gradient from the zero iterate

The routine `NLAlib.Krylov.CG.HSCG.Carried.zeroStartRoutine` reads the right-hand side and writes
the iterate, the residual, the direction and the cell of the retained residual product: it fills
the iterate with literal zeros and runs the capped solver
`NLAlib.Krylov.CG.HSCG.Carried.solve` on it.

## Main definitions

* `NLAlib.Krylov.CG.HSCG.Carried.zeroStart`: the tree.
* `NLAlib.Krylov.CG.HSCG.Carried.zeroStartRoutine`,
  `NLAlib.Krylov.CG.HSCG.Carried.zeroStartSpec`: the routine and its specification.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.zeroStartRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Zero the iterate, then solve. Index variables: `n`, `cap`, then the offsets of `b`, `x`,
`r`, `p`, `v`. -/
def zeroStart : Stmt Op Tst := ops% [n, cap] (B) → (X, R, P, RHO) {
  run (fillRoutine (Op := Op) (Tst := Tst) (Has.inj (ScalarOp.lit 0))) [n] (X);
  run (solveRoutine (Op := Op) (Tst := Tst)) [n, cap] (B, X, R, P, RHO)
}

/-- Capped conjugate gradient from the zero iterate: the right-hand side is read, and the
iterate, the residual, the direction and the cell of the retained residual product are
written. -/
def zeroStartRoutine : Routine Op Tst :=
  routine% [n, cap] (b : n) → (x : n, r : n, p : n, rho : 1) := zeroStart

/-- For the order `n` and every cap, the written vectors are the conjugate gradient state from
the zero iterate at the earlier of the cap and exact convergence, and the written cell is the
carried residual product. -/
noncomputable def zeroStartSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m, cap] (bs) → (xs, rs, ps, [v])
    requires m = n
    ensures decodedState dec n xs rs ps = cgState A (decv dec n bs) 0
        (min cap (krylovGrade A (decv dec n bs))) ∧
      dec v = decv dec n rs ⬝ᵥ decv dec n rs

/-- Capped conjugate gradient from the zero iterate meets its specification for every exact
operation interpretation, every positive-definite matrix and every cap: the iterate is zeroed,
then the capped solver runs, each used by its judgment. -/
theorem zeroStartRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) :
    (zeroStartRoutine (Op := Op) (Tst := Tst)).Meets I (zeroStartSpec dec A) := by
  routine_intro [n', cap] (b, x, r, p, v) reads (bs)
  obtain rfl : n = n' := hpre.symm
  have hx0 : decv dec n (List.replicate n (M.lit 0)) = 0 := by
    have hz0 : dec (M.lit 0) = 0 := by simpa using hM.lit 0
    ext i
    simp [decv, vec, i.isLt, hz0]
  call (fillRoutine_meets (Tst := Tst) (hS (.lit 0))) [n] (x) as m₁ hfr₁ hpos₁ (xs₀) hzero
  obtain rfl : xs₀ = List.replicate n (M.lit 0) := hzero
  call (solveRoutine_meets (A := A) hS hM hB hA hCmp hPos) [n, cap] (b, x, r, p, v)
    (pre := rfl) as m₂ hfr₂ hpos₂ (xs', rs, ps, vs) hst
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  routine_exit
  have hst : decodedState dec n xs' rs ps = cgState A (decv dec n bs)
        (decv dec n (List.replicate n (M.lit 0)))
        (min cap (krylovGrade A (decv dec n bs -
          A *ᵥ decv dec n (List.replicate n (M.lit 0))))) ∧
      dec rr = decv dec n rs ⬝ᵥ decv dec n rs := hst
  rw [hx0, Matrix.mulVec_zero, sub_zero] at hst
  exact hst

end NLAlib.Krylov.CG.HSCG.Carried
