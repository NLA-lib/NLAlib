/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.PCGRecurrence

/-!
# The preconditioned conjugate-gradient round

The preconditioner is applied as a matrix approximating the inverse of the system matrix.
The mathematical state and its exact recurrence are the existing PCG objects.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Nonbreakdown` identifies the two scalar divisors of a round.
* `NLAlib.Krylov.CG.HSPCG.pcgStep_eq` exposes the real componentwise recurrence.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open scoped Matrix

/-- Both divisors of a preconditioned Hestenes–Stiefel round are nonzero. -/
def Nonbreakdown {n : Type*} [Fintype n] (A : Matrix n n ℝ) (s : PCGState ℝ n) : Prop :=
  s.r ⬝ᵥ s.z ≠ 0 ∧ s.p ⬝ᵥ (A *ᵥ s.p) ≠ 0

/-- The real preconditioned recurrence computes its two scalar ratios and four vector updates.
The preconditioner is applied directly, as an approximation of the inverse system matrix. -/
theorem pcgStep_eq {n : Type*} [Fintype n] (A M : Matrix n n ℝ) (s : PCGState ℝ n) :
    pcgStep A M s =
      let ρ := s.r ⬝ᵥ s.z
      let α := ρ / (s.p ⬝ᵥ (A *ᵥ s.p))
      let r' := s.r - α • (A *ᵥ s.p)
      let z' := M *ᵥ r'
      ⟨s.x + α • s.p, r', z', z' + ((r' ⬝ᵥ z') / ρ) • s.p⟩ := by
  simp only [pcgStep, star_trivial, quadForm, RCLike.re_to_real]
  rfl

end NLAlib.Krylov.CG.HSPCG
