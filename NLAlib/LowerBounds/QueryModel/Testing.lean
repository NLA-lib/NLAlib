/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.InformationTheory.TotalVariation
public import NLAlib.LowerBounds.QueryModel.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Two-input testing by query algorithms

A measurable seeded query algorithm sees its seed and its response transcript. Under two input
laws and a common independent seed law, Le Cam bounds the sum of its actual decision errors by
the total variation of these observable laws. Pinsker turns a KL budget on those same laws into
an error bound. Keeping the seed in the observation permits arbitrary seed-dependent outputs.

These statements discharge the query execution and measurability bookkeeping. A concrete lower
bound must still supply its two input laws and control their observable divergence.

## Main results

* `NLAlib.QueryAlgorithm.IsMeasurableFamily.one_sub_tvDist_le_measureReal_run_add`.
* `NLAlib.QueryAlgorithm.IsMeasurableFamily.one_sub_le_measureReal_run_add_of_klDiv_le`.
-/

@[expose] public section

open MeasureTheory InformationTheory

namespace NLAlib.QueryAlgorithm

variable {Q R β S M : Type*} {q : ℕ}
    [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β]
    [MeasurableSpace S] [MeasurableSpace M]

/-- Le Cam for a jointly measurable seeded query family and oracle. With a common independent
probability seed law `ρ` and probability input laws `μ`, `ν`, any measurable output decision
region `B` has its two actual run errors summing to at least one minus the TV of the
(seed, response transcript) laws. Membership in `B` decides `ν`.
[Tsybakov2009, Theorem 2.2], specialized through query execution. -/
theorem IsMeasurableFamily.one_sub_tvDist_le_measureReal_run_add
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg)
    {O : M → Q → R} (hO : Measurable (Function.uncurry O))
    (ρ : Measure S) (μ ν : Measure M)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set β} (hB : MeasurableSet B) :
    1 - tvDist
        ((ρ.prod μ).map fun p => (p.1, (alg p.1).transcript (O p.2)))
        ((ρ.prod ν).map fun p => (p.1, (alg p.1).transcript (O p.2))) ≤
      (ρ.prod μ).real {p | (alg p.1).run (O p.2) ∈ B} +
      (ρ.prod ν).real {p | (alg p.1).run (O p.2) ∉ B} := by
  let T : S × M → S × (Fin q → R) := fun p =>
    (p.1, (alg p.1).transcript (O p.2))
  have hT : Measurable T :=
    measurable_fst.prodMk (halg.measurable_history hO q le_rfl)
  let D : Set (S × (Fin q → R)) := {z | (alg z.1).output z.2 ∈ B}
  have hD : MeasurableSet D := halg.measurable_output hB
  have : IsProbabilityMeasure ((ρ.prod μ).map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have : IsProbabilityMeasure ((ρ.prod ν).map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have h := one_sub_tvDist_le_measureReal_add_measureReal_compl
    (μ := (ρ.prod μ).map T) (ν := (ρ.prod ν).map T) hD
  rw [map_measureReal_apply hT hD, map_measureReal_apply hT hD.compl] at h
  exact h

/-- A KL budget for the actual (seed, response transcript) laws bounds the two run errors of
any measurable decision region. The seed has probability law `ρ`, independently of inputs
with probability laws `μ` and `ν`; the family and oracle are jointly measurable. If the KL is
at most $2\eta^2$ with $\eta \ge 0$, the sum of the errors is at least $1-\eta$.
The extended-real hypothesis also excludes infinite KL whenever this budget is finite.
[Tsybakov2009, Theorem 2.2 and Lemma 2.5], through query execution. -/
theorem IsMeasurableFamily.one_sub_le_measureReal_run_add_of_klDiv_le
    {alg : S → QueryAlgorithm Q R q β} (halg : IsMeasurableFamily alg)
    {O : M → Q → R} (hO : Measurable (Function.uncurry O))
    (ρ : Measure S) (μ ν : Measure M)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : Set β} (hB : MeasurableSet B) {η : ℝ} (hη : 0 ≤ η)
    (hKL : klDiv
        ((ρ.prod μ).map fun p => (p.1, (alg p.1).transcript (O p.2)))
        ((ρ.prod ν).map fun p => (p.1, (alg p.1).transcript (O p.2))) ≤
      ENNReal.ofReal (2 * η ^ 2)) :
    1 - η ≤ (ρ.prod μ).real {p | (alg p.1).run (O p.2) ∈ B} +
      (ρ.prod ν).real {p | (alg p.1).run (O p.2) ∉ B} := by
  let T : S × M → S × (Fin q → R) := fun p =>
    (p.1, (alg p.1).transcript (O p.2))
  have hT : Measurable T :=
    measurable_fst.prodMk (halg.measurable_history hO q le_rfl)
  have : IsProbabilityMeasure ((ρ.prod μ).map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have : IsProbabilityMeasure ((ρ.prod ν).map T) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have hsq := (ofReal_two_mul_tvDist_sq_le_klDiv
    ((ρ.prod μ).map T) ((ρ.prod ν).map T)).trans hKL
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2 * η ^ 2)).1 hsq
  have hTV : tvDist ((ρ.prod μ).map T) ((ρ.prod ν).map T) ≤ η := by
    nlinarith [tvDist_nonneg ((ρ.prod μ).map T) ((ρ.prod ν).map T)]
  have h := halg.one_sub_tvDist_le_measureReal_run_add hO ρ μ ν hB
  exact (sub_le_sub_left hTV 1).trans h

end NLAlib.QueryAlgorithm
