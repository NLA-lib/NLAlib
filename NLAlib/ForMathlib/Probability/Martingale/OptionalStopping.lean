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

open MeasureTheory Filter
open scoped Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Ville's maximal inequality**: a nonnegative supermartingale `f` reaches the level `c > 0` at
some time with probability at most `E f 0 / c`. Due to Ville (1939); the time-uniform form of
Markov's inequality used for martingale tail bounds (the matrix Freedman inequality,
`NLAlib/Probability/MatrixConcentration/Freedman.lean`).
Proof: finite horizon `n` first, from Mathlib's `Submartingale.expected_stoppedValue_mono`
applied to `hf.neg` with `σ = 0` and `τ = hittingBtwn f (Set.Ici c) 0 n`, at most `n` (on the
event `{∃ k ≤ n, c ≤ f k}` the stopped value is at least `c`, elsewhere it is nonnegative), giving
`c · μ {∃ k ≤ n, c ≤ f k} ≤ E f 0`; then `n → ∞` by continuity of the measure from below
(`MeasureTheory.measure_iUnion_eq_iSup` on the increasing events). Medium.
Result: ville-inequality -/
theorem Supermartingale.measure_exists_ge_le [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    {f : ℕ → Ω → ℝ} (hf : Supermartingale f ℱ μ) (hf0 : ∀ k, 0 ≤ᵐ[μ] f k) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | ∃ k, c ≤ f k ω} ≤ (∫ ω, f 0 ω ∂μ) / c := by
  let A : ℕ → Set Ω := fun n => {ω | ∃ k ≤ n, c ≤ f k ω}
  have hmono : Monotone A := fun a b hab ω ⟨k, hk, hck⟩ => ⟨k, hk.trans hab, hck⟩
  have hA : {ω | ∃ k, c ≤ f k ω} = ⋃ n, A n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, A]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, k, le_rfl, hk⟩, fun ⟨_, k, _, hk⟩ => ⟨k, hk⟩⟩
  have hall : ∀ᵐ ω ∂μ, ∀ k, 0 ≤ f k ω := ae_all_iff.mpr hf0
  have hbound : ∀ n, c * μ.real (A n) ≤ ∫ ω, f 0 ω ∂μ := by
    intro n
    let τ : Ω → ℕ := hittingBtwn f (Set.Ici c) 0 n
    have hτ : IsStoppingTime ℱ (fun ω => (τ ω : ℕ∞)) :=
      hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
    have hopt := hf.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hτ
      (fun ω => WithTop.coe_le_coe.mpr (Nat.zero_le _)) (N := n)
      fun ω => WithTop.coe_le_coe.mpr (hittingBtwn_le ω)
    have hopt' : ∫ ω, f (τ ω) ω ∂μ ≤ ∫ ω, f 0 ω ∂μ := by
      change ∫ ω, -f 0 ω ∂μ ≤ ∫ ω, -f (τ ω) ω ∂μ at hopt
      rwa [integral_neg, integral_neg, neg_le_neg_iff] at hopt
    have hint' : Integrable (fun ω => f (τ ω) ω) μ :=
      integrable_stoppedValue ℕ hτ hf.integrable (N := n)
        fun ω => WithTop.coe_le_coe.mpr (hittingBtwn_le ω)
    have hnn : 0 ≤ᵐ[μ] fun ω => f (τ ω) ω := hall.mono fun ω hω => hω _
    have hsub : A n ⊆ {ω | c ≤ f (τ ω) ω} := by
      intro ω ⟨k, hk, hck⟩
      exact stoppedValue_hittingBtwn_mem (s := Set.Ici c) ⟨k, ⟨Nat.zero_le _, hk⟩, hck⟩
    calc c * μ.real (A n) ≤ c * μ.real {ω | c ≤ f (τ ω) ω} :=
          mul_le_mul_of_nonneg_left (measureReal_mono hsub) hc.le
      _ ≤ ∫ ω, f (τ ω) ω ∂μ := mul_meas_ge_le_integral_of_nonneg hnn hint' c
      _ ≤ ∫ ω, f 0 ω ∂μ := hopt'
  have ht : Tendsto (fun n => μ.real (A n)) atTop (𝓝 (μ.real (⋃ n, A n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hmono)
  rw [hA]
  exact le_of_tendsto' ht fun n => (le_div_iff₀' hc).mpr (hbound n)

end MeasureTheory
