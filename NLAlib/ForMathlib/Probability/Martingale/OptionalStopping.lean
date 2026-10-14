/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Ville's maximal inequality

For a nonnegative supermartingale `f` and `c > 0`, the probability that `f` ever reaches `c` is
at most `E f 0 / c`. Mathlib has Doob's finite-horizon maximal inequality for nonnegative
submartingales (`MeasureTheory.maximal_ineq`) and the optional stopping theorem
(`MeasureTheory.Submartingale.expected_stoppedValue_mono`), but no infinite-horizon form for
supermartingales. Upstream candidate for `Mathlib/Probability/Martingale/OptionalStopping.lean`.

## Main results

* `MeasureTheory.Supermartingale.measure_exists_ge_le`: Ville's inequality.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Ville's maximal inequality**: a nonnegative supermartingale `f` reaches the level `c > 0` at
some time with probability at most `E f 0 / c`. Due to Ville (1939); the time-uniform form of
Markov's inequality used for martingale tail bounds (the matrix Freedman inequality,
`NLAlib/Probability/MatrixConcentration/Freedman.lean`).
Proof: finite horizon `n` first, from Mathlib's `Submartingale.expected_stoppedValue_mono`
applied to `hf.neg` with `σ = 0` and `τ = hittingBtwn f (Set.Ici c) 0 n ⊓ n` (on the event
`{∃ k ≤ n, c ≤ f k}` the stopped value is at least `c`, elsewhere it is nonnegative), giving
`c · μ {∃ k ≤ n, c ≤ f k} ≤ E f 0`; then `n → ∞` by continuity of the measure from below
(`MeasureTheory.measure_iUnion_eq_iSup` on the increasing events). Medium.
Result: ville-inequality -/
theorem Supermartingale.measure_exists_ge_le [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    {f : ℕ → Ω → ℝ} (hf : Supermartingale f ℱ μ) (hf0 : ∀ k, 0 ≤ᵐ[μ] f k) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | ∃ k, c ≤ f k ω} ≤ (∫ ω, f 0 ω ∂μ) / c := by
  sorry

end MeasureTheory
