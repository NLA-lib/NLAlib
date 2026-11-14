/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# A union bound for adaptively chosen events with fresh samples

A randomized recursion
draws a fresh sample $\zeta_i$ at each node $i$ of a countable index set; the state $X_i$ of the
node (its input, or "not reached") is computed from earlier samples, takes countably many values
and is independent of $\zeta_i$. If for every state $y$ the bad set $S_i(y)$ of the node has
probability at most the mean of a charge $q_i(y, \cdot)$, and the charges along every run sum to
at most $\theta$, then some node fails with probability at most $\theta$. It is the bookkeeping of
[Shah2024, proof of Theorem 4.2] ("we apply union bound"), with the charge carrying the expected
number of nodes and of splits.

## Main results

* `NLAlib.measureReal_exists_mem_le_of_forall_measure_le_lintegral`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

/-- One node of the adaptive union bound: the bad event has probability at most the mean
charge, and the charge is a.e. measurable. -/
private lemma measure_mem_le_lintegral_of_indepFun {γ β Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [MeasurableSpace β] {ν : Measure β} {ζ : Ω → β} {X : Ω → γ}
    (hζ : HasLaw ζ ν μ) (hXc : (Set.range X).Countable)
    (hXm : ∀ y, MeasurableSet {ω | X ω = y}) (hind : ∀ y, IndepFun (fun ω => X ω = y) ζ μ)
    {S : γ → Set β} {q : γ → β → ℝ≥0∞} (hq : ∀ y, Measurable (q y))
    (hSq : ∀ y, ν (S y) ≤ ∫⁻ z, q y z ∂ν) :
    AEMeasurable (fun ω => q (X ω) (ζ ω)) μ ∧
      μ {ω | ζ ω ∈ S (X ω)} ≤ ∫⁻ ω, q (X ω) (ζ ω) ∂μ := by
  have := hXc.to_subtype
  have hdec : (fun ω => q (X ω) (ζ ω)) =
      fun ω => ∑' y : Set.range X, {ω | X ω = y}.indicator (fun ω => q y (ζ ω)) ω := by
    funext ω
    rw [tsum_eq_single ⟨X ω, Set.mem_range_self ω⟩]
    · simp
    · rintro ⟨y, hy⟩ hne
      simp only [Set.indicator_apply_eq_zero, Set.mem_ofPred_eq]
      intro h
      exact absurd (Subtype.ext h.symm) hne
  have hf : ∀ y : Set.range X,
      AEMeasurable ({ω | X ω = y}.indicator fun ω => q y (ζ ω)) μ := fun y =>
    ((hq y).comp_aemeasurable hζ.aemeasurable).indicator (hXm y)
  have hmap : ∀ y, (μ.restrict {ω | X ω = y}).map ζ = μ {ω | X ω = y} • ν := by
    intro y
    ext T hT
    rw [Measure.map_apply_of_aemeasurable hζ.aemeasurable.restrict hT,
      Measure.restrict_apply' (hXm y), Set.inter_comm, Measure.smul_apply, smul_eq_mul,
      ← hζ.map_eq, Measure.map_apply_of_aemeasurable hζ.aemeasurable hT]
    have h := (hind y).measure_inter_preimage_eq_mul {True} T MeasurableSpace.measurableSet_top hT
    simpa [Set.preimage] using h
  have hint : ∀ y : Set.range X, ∫⁻ ω, {ω | X ω = y}.indicator (fun ω => q y (ζ ω)) ω ∂μ =
      μ {ω | X ω = y} * ∫⁻ z, q y z ∂ν := by
    intro y
    rw [lintegral_indicator (hXm y), ← lintegral_map' (hq y).aemeasurable
      hζ.aemeasurable.restrict, hmap, lintegral_smul_measure, smul_eq_mul]
  have hmeas : ∀ y : Set.range X, μ ({ω | X ω = y} ∩ ζ ⁻¹' toMeasurable ν (S y)) =
      μ {ω | X ω = y} * ν (S y) := by
    intro y
    rw [Set.inter_comm, ← Measure.restrict_apply' (hXm y), ← Measure.map_apply_of_aemeasurable
      hζ.aemeasurable.restrict (measurableSet_toMeasurable _ _), hmap, Measure.smul_apply,
      smul_eq_mul, measure_toMeasurable]
  refine ⟨hdec ▸ AEMeasurable.tsum hf, ?_⟩
  calc μ {ω | ζ ω ∈ S (X ω)}
      ≤ μ (⋃ y : Set.range X, {ω | X ω = y} ∩ ζ ⁻¹' toMeasurable ν (S y)) :=
        measure_mono fun ω hω => Set.mem_iUnion.2
          ⟨⟨X ω, Set.mem_range_self ω⟩, rfl, subset_toMeasurable _ _ hω⟩
    _ ≤ ∑' y : Set.range X, μ ({ω | X ω = y} ∩ ζ ⁻¹' toMeasurable ν (S y)) :=
        measure_iUnion_le _
    _ ≤ ∑' y : Set.range X, ∫⁻ ω, {ω | X ω = y}.indicator (fun ω => q y (ζ ω)) ω ∂μ := by
        gcongr with y
        rw [hmeas, hint]
        gcongr
        exact hSq y
    _ = ∫⁻ ω, q (X ω) (ζ ω) ∂μ := by
        rw [← lintegral_tsum hf, hdec]

/-- **Union bound over adaptively chosen events with fresh samples**: let $\zeta_i$ ($i$ in a
countable set) be random samples of law $\nu$, and $X_i$ random states with countably many
values, each event $\{X_i = y\}$ measurable and independent of $\zeta_i$. Let $S_i(y)$ be
sets (not necessarily measurable) and $q_i(y, \cdot) \ge 0$ measurable charges with
$\nu(S_i(y)) \le \int q_i(y, z)\,d\nu(z)$ for every $y$, and suppose
$\sum_i q_i(X_i, \zeta_i) \le \theta$ surely. Then
$$\mathbb{P}[\exists i,\ \zeta_i \in S_i(X_i)] \le \theta \,.$$
No printed source; [Shah2024, proof of Theorem 4.2] applies the union bound informally. -/
theorem measureReal_exists_mem_le_of_forall_measure_le_lintegral {ι γ β Ω : Type*} [Countable ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace β]
    {ν : Measure β} {ζ : ι → Ω → β} {X : ι → Ω → γ} (hζ : ∀ i, HasLaw (ζ i) ν μ)
    (hXc : ∀ i, (Set.range (X i)).Countable) (hXm : ∀ i y, MeasurableSet {ω | X i ω = y})
    (hind : ∀ i y, IndepFun (fun ω => X i ω = y) (ζ i) μ) {S : ι → γ → Set β}
    {q : ι → γ → β → ℝ≥0∞} (hq : ∀ i y, Measurable (q i y))
    (hSq : ∀ i y, ν (S i y) ≤ ∫⁻ z, q i y z ∂ν) {θ : ℝ} (hθ : 0 ≤ θ)
    (hsum : ∀ ω, ∑' i, q i (X i ω) (ζ i ω) ≤ ENNReal.ofReal θ) :
    μ.real {ω | ∃ i, ζ i ω ∈ S i (X i ω)} ≤ θ := by
  have h := fun i => measure_mem_le_lintegral_of_indepFun (hζ i) (hXc i) (hXm i) (hind i)
    (hq i) (hSq i)
  refine ENNReal.toReal_le_of_le_ofReal hθ ?_
  calc μ {ω | ∃ i, ζ i ω ∈ S i (X i ω)}
      = μ (⋃ i, {ω | ζ i ω ∈ S i (X i ω)}) := by rw [Set.ofPred_exists]
    _ ≤ ∑' i, μ {ω | ζ i ω ∈ S i (X i ω)} := measure_iUnion_le _
    _ ≤ ∑' i, ∫⁻ ω, q i (X i ω) (ζ i ω) ∂μ := ENNReal.tsum_le_tsum fun i => (h i).2
    _ = ∫⁻ ω, ∑' i, q i (X i ω) (ζ i ω) ∂μ := (lintegral_tsum fun i => (h i).1).symm
    _ ≤ ∫⁻ _, ENNReal.ofReal θ ∂μ := lintegral_mono hsum
    _ = ENNReal.ofReal θ := by simp

end NLAlib
