/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Samples

/-!
# Rounding ideal tape values

A mathematical coupling of ideal and stored samples, with explicit relative error, absolute
floor, range and uniform support. This predicate uses no interpretation or execution state.

## Main results

* `NLAlib.Computation.isTapeRounding_id`: exact storage meets the rounding relation.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K : Type}

/-- **The tape-rounding contract**: the stored draws are a rounding $\rho$ of the ideal tape.
For every distribution $d$, tape position $i$ and ideal value $x$ with $\lvert x \rvert \le \Omega$,
the stored value $\rho(d, i, x)$ at tag `p` decodes to within $c(d)\,u\max(\lvert x \rvert, \tau)$
of $x$: relative error $c(d)\,u$ above the floor $\tau$ (gradual underflow; $0$ with an unbounded
exponent), in the range $\Omega$ (overflow). A uniform draw of $x \in [-1, 1]$ decodes into
$[-1, 1]$. The rounding may depend on the position, as the state of a hardware sampler does; the
law of the ideal tape is fixed by the model that uses the contract. [Shah2024, Definition 1.3],
[Shah2024, Definition 1.4], the coupling of a computed and an ideal sample realised by the ideal
tape. -/
def IsTapeRounding (dec : P → K → ℝ) (p : P) (u τ Ω : ℝ) (c : Dist → ℝ)
    (ρ : Dist → ℕ → ℝ → K) : Prop :=
  (∀ (d : Dist) (i : ℕ) (x : ℝ), |x| ≤ Ω → |dec p (ρ d i x) - x| ≤ c d * u * max |x| τ) ∧
    ∀ (i : ℕ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 → dec p (ρ .uniform i x) ∈ Set.Icc (-1 : ℝ) 1

/-- The exact rounding of the tape: storing each ideal draw as itself in $\mathbb{R}$ meets
`NLAlib.Computation.IsTapeRounding` with the identity decoding, for every unit roundoff $u$,
floor $\tau$, range $\Omega$ and constants $c$ with $c(d)\,u \ge 0$. No printed source. -/
theorem isTapeRounding_id (p : P) (u τ Ω : ℝ) (c : Dist → ℝ) (hc : ∀ d, 0 ≤ c d * u) :
    IsTapeRounding (fun _ x => x) p u τ Ω c (fun _ _ x => x) := by
  refine ⟨fun d i x _ => ?_, fun i x hx => hx⟩
  simp only [sub_self, abs_zero]
  exact mul_nonneg (hc d) (le_max_of_le_left (abs_nonneg x))

end NLAlib.Computation
