/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGRecurrence

/-!
# Conjugate-gradient states and nonbreakdown

The mathematical specification reuses `NLAlib.CGState`, `NLAlib.cgStep` and `NLAlib.cgState`.
The existing recurrence theory identifies the iterate with `NLAlib.cgIterate` for a positive
definite matrix. A program round performs scalar division, so its contract states that both
denominators are nonzero.

## Main results

* `NLAlib.Krylov.CG.Nonbreakdown` states the domain of a round.
-/

@[expose] public section

namespace NLAlib.Krylov.CG

open scoped Matrix

/-- The two divisors of a Hestenes–Stiefel round are nonzero. The condition is stated on the
mathematical state, independently of a program or an arithmetic implementation. -/
def Nonbreakdown {n : Type*} [Fintype n] (A : Matrix n n ℝ) (s : CGState ℝ n) : Prop :=
  s.r ⬝ᵥ s.r ≠ 0 ∧ s.p ⬝ᵥ (A *ᵥ s.p) ≠ 0

end NLAlib.Krylov.CG
