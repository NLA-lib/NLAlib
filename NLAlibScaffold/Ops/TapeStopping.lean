/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.TapeLaw

/-!
# The tape after a stopping position

A program that reads its tape adaptively starts a subroutine at a position that depends on the
draws made so far. Such a position is a **stopping position**: whether it equals $q$ is decided by
the entries before $q$. For a tape with independent entries whose law depends only on the stream
(`NLAlib.Ops.IsTapeLaw`), the tape shifted to a stopping position has the same law and is
independent of everything decided before it (the strong Markov property of an i.i.d. sequence).
This is what lets a failure bound proved for a subroutine started from a fixed memory be used for
the same subroutine started at a random time.

## Main definitions

* `NLAlib.Ops.Tape.IsStoppingPos`: a random position decided by the past.

## Main results

* `NLAlib.Ops.IsTapeLaw.shiftAt`: the shifted tape at a stopping position is a tape with the same
  law, independent of any random variable decided before the position.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Ops

variable {K Ω : Type} [MeasurableSpace K] {mΩ : MeasurableSpace Ω}

/-- `p` is a **stopping position** of the random tape `ξ`: for every `q` the event `p = q` is
measurable with respect to the entries before `q` (`NLAlib.Ops.Tape.past`). -/
def Tape.IsStoppingPos (ξ : Ω → Tape K) (p : Ω → ℕ) : Prop :=
  ∀ q, MeasurableSet[Tape.past ξ q] {ω | p ω = q}

/-- **The strong Markov property of the tape**: let `p` be a stopping position of a tape `ξ`
with independent entries of law `law s` in the stream `s`, and let `X` be a measurable random
variable decided before `p` (on the event `p = q` it agrees with a function of the entries before
`q`). Then the tape shifted to `p` has the same law, and it is independent of `X`. -/
theorem IsTapeLaw.shiftAt {law : ℕ → Measure K} {P : Measure Ω} {ξ : Ω → Tape K}
    (h : IsTapeLaw law P ξ) {p : Ω → ℕ} (hp : Tape.IsStoppingPos ξ p) {γ : Type}
    [MeasurableSpace γ] {X : Ω → γ} (hXm : Measurable X)
    (hX : ∀ q, ∃ Y : Ω → γ, Measurable[Tape.past ξ q] Y ∧ ∀ ω, p ω = q → X ω = Y ω) :
    IsTapeLaw law P (fun ω => (ξ ω).shift (p ω)) ∧
      IndepFun X (fun ω => (ξ ω).shift (p ω)) P := by
  sorry

end NLAlib.Ops
