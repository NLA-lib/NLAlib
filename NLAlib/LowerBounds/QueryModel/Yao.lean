/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Independence.Basic
public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowerBounds.QueryModel.Basic

/-!
# Yao's principle for query algorithms

A randomized algorithm is a measurable family of deterministic ones indexed by a seed
(`NLAlib.QueryAlgorithm.IsMeasurableFamily`). Two forms of Yao's minimax principle [Yao1977] (the
easy
direction, which is what lower bounds use), both Fubini on the product of the seed law and the
input law:

* distributional: if every measurable deterministic algorithm has failure probability at most
  $\delta$ on a random input, so does every randomized one whose seed is independent of the input;
* worst case: if every measurable deterministic algorithm fails with probability at least
  $\delta$ under an input law, every randomized algorithm fails with probability at least
  $\delta$ on some input.

Failure (or success) is membership of the pair (input, output) in a measurable set `B`.

## Main results

* `NLAlib.QueryAlgorithm.IsMeasurableFamily.measureReal_run_mem_le_of_indepFun`.
* `NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem`.
* `NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

namespace QueryAlgorithm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {Q R β S M : Type*} {q : ℕ}
  [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β] [MeasurableSpace S]
  [MeasurableSpace M]

/-- **Yao's principle, distributional form**: let the seed $s$ be independent of the random input
$X$, and let $B$ be a measurable set of (input, output) pairs. If every measurable deterministic
algorithm puts $(X, \text{output})$ in $B$ with probability at most $\delta$, then so does the
randomized algorithm with seed $s$:
$\mathbb{P}[(X, \mathcal{A}_s(X)) \in B] \le \delta$.
[BenDavidBlais2020, §1, classical minimax identity]; there as the minimax principle for finite
problems,
here the averaging half on a probability space, any seed and input spaces, any oracle depending
measurably on the input. -/
theorem IsMeasurableFamily.measureReal_run_mem_le_of_indepFun [IsProbabilityMeasure μ]
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) {s : Ω → S} {X : Ω → M} (hs : AEMeasurable s μ)
    (hX : AEMeasurable X μ) (hsX : IndepFun s X μ) {B : Set (M × β)} (hB : MeasurableSet B)
    {δ : ℝ}
    (h : ∀ a : QueryAlgorithm Q R q β, a.IsMeasurable →
      μ.real {ω | (X ω, a.run (O (X ω))) ∈ B} ≤ δ) :
    μ.real {ω | (X ω, (alg (s ω)).run (O (X ω))) ∈ B} ≤ δ := by
  have hE : MeasurableSet {p : M × S | (p.1, (alg p.2).run (O p.1)) ∈ B} :=
    (measurable_fst.prodMk ((halg.measurable_run hO).comp measurable_swap)) hB
  have hsec : ∀ y ∈ (Set.univ : Set S), μ.real {ω | (X ω, y) ∈
      {p : M × S | (p.1, (alg p.2).run (O p.1)) ∈ B}} ≤ δ := fun y _ =>
    h (alg y) (halg.isMeasurable y)
  have hGc : μ.real {ω | s ω ∉ (Set.univ : Set S)} ≤ 0 := by
    simp
  have hδ : 0 ≤ δ := by
    obtain ⟨ω⟩ : (Set.univ : Set Ω).Nonempty :=
      nonempty_of_measure_ne_zero (μ := μ) (by simp)
    exact measureReal_nonneg.trans (h (alg (s ω)) (halg.isMeasurable _))
  simpa using hsX.symm.measureReal_mem_le_add hX hs hE MeasurableSet.univ (δ₁ := δ) (δ₂ := 0)
    hδ hsec hGc

/-- **Yao's principle, worst-case form**: let $\rho$ be a seed law and $\nu$ an input law, both
probability measures, and $B$ a measurable set of (input, output) pairs. If every measurable
deterministic algorithm has $\nu$-probability at least $\delta$ of $(x, \text{output}) \in B$,
then for the randomized algorithm some input $x$ has
$\rho$-probability at least $\delta$ of $(x, \mathcal{A}_s(x)) \in B$. Read with $B$ the failure
set: a lower bound against one input distribution is a lower bound for randomized algorithms in
the worst case.
[BenDavidBlais2020, §1, classical minimax identity]; [ZhangEtAl2026, Section 8]; there for finite or
implicit input spaces. -/
theorem IsMeasurableFamily.exists_le_measureReal_run_mem {alg : S → QueryAlgorithm Q R q β}
    (halg : IsMeasurableFamily alg) {O : M → Q → R} (hO : Measurable (Function.uncurry O))
    (ρ : Measure S) [IsProbabilityMeasure ρ] (ν : Measure M) [IsProbabilityMeasure ν]
    {B : Set (M × β)} (hB : MeasurableSet B) {δ : ℝ}
    (h : ∀ a : QueryAlgorithm Q R q β, a.IsMeasurable → δ ≤ ν.real {x | (x, a.run (O x)) ∈ B}) :
    ∃ x, δ ≤ ρ.real {s | (x, (alg s).run (O x)) ∈ B} := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  set E : Set (S × M) := {p | (p.2, (alg p.1).run (O p.2)) ∈ B}
  have hE : MeasurableSet E :=
    hB.preimage (measurable_snd.prodMk (halg.measurable_run hO))
  have hlow : ∀ s, ENNReal.ofReal δ ≤ ν (Prod.mk s ⁻¹' E) := fun s => by
    have := h (alg s) (halg.isMeasurable s)
    rw [measureReal_def] at this
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 this
  have hup : ∀ x, ρ ((fun s => (s, x)) ⁻¹' E) < ENNReal.ofReal δ := fun x => by
    have := hcon x
    rw [measureReal_def] at this
    exact (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 this
  have h1 : ENNReal.ofReal δ ≤ (ρ.prod ν) E := by
    rw [Measure.prod_apply hE]
    calc ENNReal.ofReal δ = ∫⁻ _ : S, ENNReal.ofReal δ ∂ρ := by simp
      _ ≤ _ := lintegral_mono hlow
  have h2 : (ρ.prod ν) E < ENNReal.ofReal δ := by
    rw [Measure.prod_apply_symm hE]
    calc _ < ∫⁻ _ : M, ENNReal.ofReal δ ∂ν := by
          refine lintegral_strict_mono (IsProbabilityMeasure.ne_zero ν) aemeasurable_const ?_
            (ae_of_all _ hup)
          refine ne_top_of_le_ne_top (b := ∫⁻ _ : M, ENNReal.ofReal δ ∂ν) (by simp)
            (lintegral_mono fun x => (hup x).le)
      _ = ENNReal.ofReal δ := by simp
  exact h2.not_ge h1

end QueryAlgorithm

end NLAlib

open MeasureTheory ProbabilityTheory

namespace NLAlib

namespace QueryAlgorithm

variable {Q R β S M : Type*} {q : ℕ} [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β]
  [MeasurableSpace S] [MeasurableSpace M]

/-- **Yao's principle for a class of algorithms, worst-case form**: let $\rho$ be a seed law and
$\nu$ an input law, both probability measures, and $B$ a measurable set of (input, output) pairs.
If for every seed $s$ the deterministic algorithm $\mathcal{A}_s$ has $\nu$-probability at least
$\delta$ of $(x, \mathcal{A}_s(x)) \in B$, then some input $x$ has $\rho$-probability at least
$\delta$ of $(x, \mathcal{A}_s(x)) \in B$. The bound is needed only for the members of the family,
so a lower bound for a class of algorithms (pass-structured, one-sided) transfers to the
randomized algorithms of that class.
[BenDavidBlais2020, §1, classical minimax identity]; the averaging half, as
`NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem`, which follows from it. -/
theorem IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg) {O : M → Q → R}
    (hO : Measurable (Function.uncurry O)) (ρ : Measure S) [IsProbabilityMeasure ρ]
    (ν : Measure M) [IsProbabilityMeasure ν] {B : Set (M × β)} (hB : MeasurableSet B) {δ : ℝ}
    (h : ∀ s, δ ≤ ν.real {x | (x, (alg s).run (O x)) ∈ B}) :
    ∃ x, δ ≤ ρ.real {s | (x, (alg s).run (O x)) ∈ B} := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  set E : Set (S × M) := {p | (p.2, (alg p.1).run (O p.2)) ∈ B}
  have hE : MeasurableSet E :=
    hB.preimage (measurable_snd.prodMk (halg.measurable_run hO))
  have hlow : ∀ s, ENNReal.ofReal δ ≤ ν (Prod.mk s ⁻¹' E) := fun s => by
    have := h s
    rw [measureReal_def] at this
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 this
  have hup : ∀ x, ρ ((fun s => (s, x)) ⁻¹' E) < ENNReal.ofReal δ := fun x => by
    have := hcon x
    rw [measureReal_def] at this
    exact (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).2 this
  have h1 : ENNReal.ofReal δ ≤ (ρ.prod ν) E := by
    rw [Measure.prod_apply hE]
    calc ENNReal.ofReal δ = ∫⁻ _ : S, ENNReal.ofReal δ ∂ρ := by simp
      _ ≤ _ := lintegral_mono hlow
  have h2 : (ρ.prod ν) E < ENNReal.ofReal δ := by
    rw [Measure.prod_apply_symm hE]
    calc _ < ∫⁻ _ : M, ENNReal.ofReal δ ∂ν := by
          refine lintegral_strict_mono (IsProbabilityMeasure.ne_zero ν) aemeasurable_const ?_
            (ae_of_all _ hup)
          refine ne_top_of_le_ne_top (b := ∫⁻ _ : M, ENNReal.ofReal δ ∂ν) (by simp)
            (lintegral_mono fun x => (hup x).le)
      _ = ENNReal.ofReal δ := by simp
  exact h2.not_ge h1

end QueryAlgorithm

end NLAlib
