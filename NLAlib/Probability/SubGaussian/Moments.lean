/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import NLAlib.Probability.SubGaussian.Basic
public import NLAlib.Probability.Tail

/-!
# Moments and maxima of sub-Gaussian random variables

The absolute moments of a sub-Gaussian variable, obtained by integrating its two-sided tail, and
the maximal inequality for finitely many sub-Gaussian variables, which needs no independence.
Integrability of `|X| ^ p` is Mathlib's `ProbabilityTheory.HasSubgaussianMGF.memLp`.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.integral_abs_rpow_le`: `E |X| ^ p ≤ p (2c)^{p/2} Γ(p/2)`.
* `ProbabilityTheory.HasSubgaussianMGF.integral_iSup_le`: `E max_i X_i ≤ √(2 c log N)`.
* `ProbabilityTheory.HasSubgaussianMGF.integral_iSup_abs_le`: `E max_i |X_i| ≤ √(2 c log 2N)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- The absolute moments of a sub-Gaussian variable: `E |X| ^ p ≤ p (2c)^{p/2} Γ(p/2)` for
`p > 0`. The right side is the integral of the two-sided tail bound `2 exp (-t² / (2c))` against
`p t^{p-1} dt`, so it improves only with the tail. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_abs_rpow_le
    (h : HasSubgaussianMGF X c μ) {p : ℝ} (hp : 0 < p) :
    ∫ ω, |X ω| ^ p ∂μ ≤ p * (2 * c) ^ (p / 2) * Real.Gamma (p / 2) := by
  sorry

/-- The maximum of finitely many sub-Gaussian variables is integrable. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integrable_iSup {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    Integrable (fun ω => ⨆ i, X i ω) μ := by
  sorry

/-- **The maximal inequality** (Boucheron–Lugosi–Massart, Theorem 2.5): the mean of the maximum
of `N` sub-Gaussian variables with proxy `c` is at most `√(2 c log N)`. No independence is
assumed. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_iSup_le [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, X i ω ∂μ ≤ √(2 * c * Real.log (Fintype.card ι)) := by
  sorry

/-- The maximum of the absolute values of finitely many sub-Gaussian variables is integrable. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integrable_iSup_abs {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    Integrable (fun ω => ⨆ i, |X i ω|) μ := by
  sorry

/-- The maximal inequality for absolute values: `E max_i |X_i| ≤ √(2 c log 2N)`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_iSup_abs_le [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, |X i ω| ∂μ ≤ √(2 * c * Real.log (2 * Fintype.card ι)) := by
  sorry

end NLAlib
