/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.NewtonSchulzSign

/-!
# Capped Newton–Schulz iteration as a mathematical iterate

A matrix whose stopping test passes is fixed by the stopped transition. Iterating that
transition therefore gives the capped Newton–Schulz loop, including early termination.
The statements use no program evaluator or memory representation.

## Main results

* `NLAlib.eighSignIter` is the stopped matrix transition.
* `NLAlib.newtonSchulzLoop_eq_iterate` identifies the capped loop with its iterate.
-/

@[expose] public section

namespace NLAlib

variable {K : Type}

/-- One step of the bounded Newton–Schulz loop on matrices: keep $\mathbf{B}$ if it passes the
test at threshold $\eta$, else take the rounded step. -/
def eighSignIter {Su Sg : Type} (M : FloatMachine K Su Sg) (η : K) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) (K × K)) : Matrix (Fin n) (Fin n) (K × K) :=
  if newtonSchulzTest M η B then B else newtonSchulzRounded M B

/-- The bounded Newton–Schulz loop is the iterate of its step: a matrix that passes the test
is a fixed point. -/
theorem newtonSchulzLoop_eq_iterate {Su Sg : Type} (M : FloatMachine K Su Sg) (η : K) {n : ℕ}
    (N : ℕ) (A : Matrix (Fin n) (Fin n) (K × K)) :
    newtonSchulzLoop M η N A = (eighSignIter M η)^[N] A := by
  induction N generalizing A with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, newtonSchulzLoop]
    by_cases ht : newtonSchulzTest M η A
    · rw [if_pos ht, show eighSignIter M η A = A from if_pos ht]
      exact (Function.iterate_fixed (show eighSignIter M η A = A from if_pos ht) N).symm
    · rw [if_neg ht, ih, show eighSignIter M η A = newtonSchulzRounded M A from if_neg ht]

end NLAlib
