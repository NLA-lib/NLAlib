/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Initialization
public import NLAlib.Krylov.CG.HSCG.Carried.Exact

/-!
# Initialization of the retained-product conjugate gradient state

The routine runs the three-vector initialization
`NLAlib.Krylov.CG.HSCG.initializeRoutine` and then computes
the residual self-product that every round retains.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.initializeRoutine_meets`: the routine establishes the initial
  state with its retained residual product.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- At the dimension of the matrix, the written state is the initial state of the recurrence
with its retained residual product. -/
noncomputable def initializeSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m] (bs, xs) → (xs', rs, ps, [v])
    requires m = n
    ensures decodedState dec n xs' rs ps = cgState A (decv dec n bs) (decv dec n xs) 0 ∧
      dec v = decv dec n rs ⬝ᵥ decv dec n rs

/-- Initialization meets its specification under exact operation contracts: the three-vector
initialization, used by its judgment, then the residual self-product. -/
theorem initializeRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) :
    (initializeRoutine (Op := Op) (Tst := Tst)).Meets I (initializeSpec dec A) := by
  routine_intro [n'] (b, x, r, p, v) reads (bs, xs)
  obtain rfl : n = n' := hpre.symm
  call (HSCG.initializeRoutine_meets (Tst := Tst) (A := A) hS hM hB hA) [n] (b, x, r, p)
    (pre := rfl) as m₁ hfr₁ hpos₁ (ys, rs, ps) hst
  step hB.dot as m₂ hfr₂ ⟨hpos₂, rr, hrr, herr⟩
  routine_exit
  exact ⟨hst, dotExactRel_decoded herr⟩

end NLAlib.Krylov.CG.HSCG.Carried
