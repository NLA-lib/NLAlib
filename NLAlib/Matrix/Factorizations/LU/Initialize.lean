/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Blas.Fill

/-!
# Initial storage of Gaussian elimination

The residual is a copy of the input, and both factors begin with zero literals. The scalar
and pivoted LU routines share this initialization. Its exact word specification needs no
decoding or error model.

## Main results

* `NLAlib.LU.initializeFactors_meets`: the residual and both initialized factor blocks.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Copy the matrix to the residual and initialize the two factor blocks with zero literals.
All four operands have the same column-major square shape. -/
def initializeFactors : Routine Op Tst :=
  routine% [n] (A : n * n) → (R : n * n, L : n * n, U : n * n) {
    run copyLoopRoutine [n * n] (A, R);
    run (fillRoutine (Has.inj (ScalarOp.lit 0))) [n * n] (L);
    run (fillRoutine (Has.inj (ScalarOp.lit 0))) [n * n] (U)
  }

/-- The residual retains the input words and each factor contains exactly the machine's zero
literal at every position, also for an empty matrix. -/
def initializeFactorsSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] (as) → (rs, ls, us) ensures
    rs = as ∧ ls = List.replicate (n * n) (M.lit 0) ∧
      us = List.replicate (n * n) (M.lit 0)

variable [Inhabited K]

/-- Initialization meets its word specification under scalar operations alone. No property
of the represented matrix or of the machine's arithmetic is needed. -/
theorem initializeFactors_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (initializeFactors (Op := Op) (Tst := Tst)).Meets I (initializeFactorsSpec M) := by
  routine_intro [n] (A, R, L, U) reads (as)
  call (copyLoopRoutine_meets hI (fun _ => True)) [n * n] (A, R)
    as m₁ hfr₁ hpos₁ (rs) hcopy
  call (fillRoutine_meets (hI (.lit 0))) [n * n] (L)
    as m₂ hfr₂ hpos₂ (ls) hL
  call (fillRoutine_meets (hI (.lit 0))) [n * n] (U)
    as m₃ hfr₃ hpos₃ (us) hU
  routine_exit
  exact ⟨(List.cons.inj hcopy).1, hL, hU⟩

end NLAlib.LU
