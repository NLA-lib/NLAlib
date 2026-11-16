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

/-- One call: if $X$ is independent of $\zeta$ with law $\nu$, the failure set is jointly
measurable and $\nu(S(y)) \le \varphi$ for every $y$, then $\mathbb{P}[\zeta \in S(X)] \le
\varphi$ (Fubini on the joint law $\mu_X \otimes \nu$). -/
private lemma measureReal_mem_le_of_indep {Ω β γ : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure β} [IsProbabilityMeasure ν] {ζ : Ω → β} {X : Ω → γ} {S : γ → Set β}
    (hζ : HasLaw ζ ν μ) (hX : Measurable X) (hind : IndepFun X ζ μ)
    (hS : MeasurableSet {p : γ × β | p.2 ∈ S p.1}) {φ : ℝ} (hφ0 : 0 ≤ φ)
    (hφ : ∀ y, ν.real (S y) ≤ φ) :
    μ.real {ω | ζ ω ∈ S (X ω)} ≤ φ := by
  have hpair : AEMeasurable (fun ω => (X ω, ζ ω)) μ :=
    hX.aemeasurable.prodMk hζ.aemeasurable
  have hmap : μ {ω | ζ ω ∈ S (X ω)} = (μ.map X).prod ν {p : γ × β | p.2 ∈ S p.1} := by
    rw [show {ω | ζ ω ∈ S (X ω)} = (fun ω => (X ω, ζ ω)) ⁻¹' {p : γ × β | p.2 ∈ S p.1} from rfl,
      ← Measure.map_apply_of_aemeasurable hpair hS,
      (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hζ.aemeasurable).1 hind,
      hζ.map_eq]
  have hle : μ {ω | ζ ω ∈ S (X ω)} ≤ ENNReal.ofReal φ := by
    rw [hmap, Measure.prod_apply hS]
    have hfib (x : γ) : ν (Prod.mk x ⁻¹' {p : γ × β | p.2 ∈ S p.1}) ≤ ENNReal.ofReal φ := by
      rw [show Prod.mk x ⁻¹' {p : γ × β | p.2 ∈ S p.1} = S x from rfl]
      rw [← ENNReal.ofReal_toReal (measure_ne_top ν _)]
      exact ENNReal.ofReal_le_ofReal (hφ x)
    calc ∫⁻ x, ν (Prod.mk x ⁻¹' {p : γ × β | p.2 ∈ S p.1}) ∂(μ.map X)
        ≤ ∫⁻ _, ENNReal.ofReal φ ∂(μ.map X) := lintegral_mono fun x => hfib x
      _ = ENNReal.ofReal φ := by
        have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
        simp
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hφ0 hle

/-- **Union bound over adaptively chosen calls with fresh samples, measurable states**: let
$\zeta_i$, $i < N$, be random samples of law $\nu$, and $X_i$ measurable random states (any
measurable space, not necessarily countable), each independent of $\zeta_i$ (the sample of call
$i$ is fresh; the state may depend on all earlier samples). If the failure sets are jointly
measurable and $\nu(S_i(y)) \le \varphi$ for every state $y$ (a call that is not made has
$S_i(y) = \emptyset$), then $\mathbb{P}[\exists i < N,\ \zeta_i \in S_i(X_i)] \le N\varphi$.
For example, the union bound in [BanksGarzaVargasSrivastava2022, proof of Theorem 6.3] has
states that are real words and at most $N$ calls before the first failure. -/
theorem measureReal_exists_lt_mem_le {Ω β γ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [MeasurableSpace β] [MeasurableSpace γ] {ν : Measure β} {N : ℕ}
    {ζ : ℕ → Ω → β} {X : ℕ → Ω → γ} (hζ : ∀ i, HasLaw (ζ i) ν μ) (hX : ∀ i, Measurable (X i))
    (hind : ∀ i, IndepFun (X i) (ζ i) μ) {S : ℕ → γ → Set β}
    (hS : ∀ i, MeasurableSet {p : γ × β | p.2 ∈ S i p.1}) {φ : ℝ}
    (hφ : ∀ i y, ν.real (S i y) ≤ φ) :
    μ.real {ω | ∃ i < N, ζ i ω ∈ S i (X i ω)} ≤ N * φ := by
  have hν : IsProbabilityMeasure ν := by
    rw [← (hζ 0).map_eq]
    exact Measure.isProbabilityMeasure_map (hζ 0).aemeasurable
  obtain ⟨ω0, -⟩ := MeasureTheory.nonempty_of_measure_ne_zero (μ := μ) (s := Set.univ) (by simp)
  have hφ0 : 0 ≤ φ := measureReal_nonneg.trans (hφ 0 (X 0 ω0))
  have hset : {ω | ∃ i < N, ζ i ω ∈ S i (X i ω)} =
      ⋃ i ∈ Finset.range N, {ω | ζ i ω ∈ S i (X i ω)} := by
    ext ω
    simp
  rw [hset]
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ i ∈ Finset.range N, μ.real {ω | ζ i ω ∈ S i (X i ω)}
      ≤ ∑ _i ∈ Finset.range N, φ := Finset.sum_le_sum fun i _ =>
        measureReal_mem_le_of_indep (hζ i) (hX i) (hind i) (hS i) hφ0 (hφ i)
    _ = N * φ := by simp

end NLAlib
