/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.TapeLaw
public import Mathlib.Probability.Process.Stopping

/-!
# The tape after a stopping time

A program that reads its tape adaptively starts a subroutine at a position that depends on the
draws made so far, and on some tapes it never gets there (an earlier part fails). Such a position
is a **stopping time** of the filtration of positions (`NLAlib.Ops.IsTapeLaw.filtration`), with
values in `WithTop ℕ`, `⊤` for "never": whether it is at most $q$ is decided by the entries before
$q$. For a tape with independent entries whose law depends only on the stream
(`NLAlib.Ops.IsTapeLaw`), the tape shifted to a stopping time, on the event that it is finite,
has the law of the tape and is independent of everything decided before it (the strong Markov
property of an i.i.d. sequence). A failure bound proved for a subroutine started from a fixed
memory thus transfers to the same subroutine started at a random time.

## Main results

* `NLAlib.Ops.IsTapeLaw.measure_inter_shift_mem`: for an event $S$ of the stopped σ-algebra and a
  measurable set $A$ of tapes,
  $\mathbb{P}(S \cap \{p < \top,\ \xi \text{ shifted to } p \in A\}) =
  \mathbb{P}(S \cap \{p < \top\})\,\mathbb{P}(\xi \in A)$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Ops

variable {K Ω : Type} [MeasurableSpace K] {mΩ : MeasurableSpace Ω}

/-- **The strong Markov property of the tape**: let `p` be a stopping time, with values in
`WithTop ℕ`, of the filtration of positions of a tape `ξ` with independent entries of law
`law s` in the stream `s`. For an event `S` decided at time `p` (measurable for the stopped
σ-algebra) and a measurable set `A` of tapes, the event "`p` is finite, `S` holds and the tape
shifted to `p` lies in `A`" has probability $\mathbb{P}(S \cap \{p < \top\})\,\mathbb{P}(\xi
\in A)$. -/
theorem IsTapeLaw.measure_inter_shift_mem {law : ℕ → Measure K} {P : Measure Ω}
    {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ) {p : Ω → WithTop ℕ}
    (hp : IsStoppingTime h.filtration p) {S : Set Ω} (hS : MeasurableSet[hp.measurableSpace] S)
    {A : Set (Tape K)} (hA : MeasurableSet A) :
    P (S ∩ {ω | ∃ q : ℕ, p ω = q ∧ (ξ ω).shift q ∈ A}) =
      P (S ∩ {ω | p ω ≠ ⊤}) * P.map ξ A := by
  sorry

end NLAlib.Ops
