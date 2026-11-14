/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw

/-!
# Adaptive union bound with measurable states

`NLAlib.measureReal_exists_mem_le_of_forall_measure_le_lintegral` bounds the probability that some
adaptively chosen call with a fresh sample fails, for states with countably many values (words of
a floating-point format). An algorithm whose words are real numbers has uncountably many states;
this file states the union bound for measurable states, with independence of the state before a
call from the fresh sample of that call. The number of calls before the first failure is bounded
by $N$; a call that is not made has an empty failure set.

## Main results

* `NLAlib.measureReal_exists_lt_mem_le`: $\mathbb{P}[\exists i < N,\ \zeta_i \in S_i(X_i)] \le
  N\varphi$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

/-- **Union bound over adaptively chosen calls with fresh samples, measurable states**: let
$\zeta_i$, $i < N$, be random samples of law $\nu$, and $X_i$ measurable random states (any
measurable space, not necessarily countable), each independent of $\zeta_i$ (the sample of call
$i$ is fresh; the state may depend on all earlier samples). If the failure sets are jointly
measurable and $\nu(S_i(y)) \le \varphi$ for every state $y$ (a call that is not made has
$S_i(y) = \emptyset$), then $\mathbb{P}[\exists i < N,\ \zeta_i \in S_i(X_i)] \le N\varphi$.
This is the form the floating-point shifted QR algorithm needs: its states are real words, and
the number of calls before the first failure is at most $N$
[BanksGarzaVargasSrivastava2022, proof of Theorem 6.3]. -/
theorem measureReal_exists_lt_mem_le {Ω β γ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [MeasurableSpace β] [MeasurableSpace γ] {ν : Measure β} {N : ℕ}
    {ζ : ℕ → Ω → β} {X : ℕ → Ω → γ} (hζ : ∀ i, HasLaw (ζ i) ν μ) (hX : ∀ i, Measurable (X i))
    (hind : ∀ i, IndepFun (X i) (ζ i) μ) {S : ℕ → γ → Set β}
    (hS : ∀ i, MeasurableSet {p : γ × β | p.2 ∈ S i p.1}) {φ : ℝ}
    (hφ : ∀ i y, ν.real (S i y) ≤ φ) :
    μ.real {ω | ∃ i < N, ζ i ω ∈ S i (X i ω)} ≤ N * φ := by
  sorry

end NLAlib
