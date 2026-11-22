/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Step
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# The routine of one shifted QR step

`NLAlib.ShiftedQR.stepRoutine` is `[n] (A : 2 (n+1)², s : 2) → (Z : 2 (n+1)²)`:
at the size `n` it reads a packed complex matrix of order `n + 1` and a complex shift and
writes the packed shifted QR step. It runs `NLAlib.ShiftedQR.shiftedStepRoutine` at the order
`n + 1`: the size of the certified program is the order minus one, so that every size is the
order of a nonempty matrix, on which the step is defined.

## Main definitions

* `NLAlib.ShiftedQR.stepRoutine`, `NLAlib.ShiftedQR.stepSpec`.

## Main results

* `NLAlib.ShiftedQR.stepRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- One shifted QR step at order `n + 1`. The dimension `n` is one less than the order, so
that every dimension is the order of a nonempty matrix; it runs the step routine at `n + 1`. -/
def stepRoutine : Routine Op Tst :=
  routine% [n] (A : 2 * ((n + 1) * (n + 1)), s : 2) → (Z : 2 * ((n + 1) * (n + 1))) {
    run (shiftedStepRoutine (Op := Op) (Tst := Tst)) [n + 1] (A, s, Z)
  }

/-- The written block packs the shifted QR step of the matrix that the first block read packs,
at the shift whose real and imaginary parts are the second block read. -/
noncomputable def stepSpec : Routine.Spec ℝ :=
  spec% [n] (aw, sw) → (zw) ensures
    zw = matrixWords (shiftedQRStep (matrixOfWords (n + 1) aw) ⟨vec sw 0, vec sw 1⟩)

/-- One shifted QR step meets its specification for every exact scalar interpretation, at every
positive order, with no safe-run or nonzero-pivot assumption. -/
theorem stepRoutine_meets {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I) :
    (stepRoutine (Op := Op) (Tst := Tst)).Meets I stepSpec := by
  routine_intro [n] (a, s, z) reads (aw, sw)
  have hza : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := Fp.disj_inBlock_of_ne (by omega)
  have hzs : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 2) := Fp.disj_inBlock_of_ne (by omega)
  have hstep := shiftedStepRoutine_meets (Op := Op) (Tst := Tst) hS hE hCmp
  call hstep [n + 1] (a, s, z) (pre := Nat.succ_pos n) as μ hfr hpos (zs) hpost
  routine_exit
  exact hpost n rfl

end NLAlib.ShiftedQR
