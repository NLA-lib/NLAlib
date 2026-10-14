/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-Gaussian random variables

API for Mathlib's `ProbabilityTheory.HasSubgaussianMGF X c μ` (the moment generating function of
`X` is at most `exp (c t² / 2)`) that the probability layers use and Mathlib does not have:
monotonicity in the proxy, the proxy of a scalar multiple in the form `‖r‖₊ ^ 2 * c`, mean zero
and the second moment, lower and two-sided tails, weighted sums of independent variables, and
the union bound for a maximum. Proxies are `ℝ≥0` throughout (`docs/PORT_PROBABILITY.md` D2).

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.mono`: a larger proxy.
* `ProbabilityTheory.HasSubgaussianMGF.integral_eq_zero`, `.integral_sq_le`: mean zero and
  second moment at most the proxy.
* `ProbabilityTheory.HasSubgaussianMGF.measure_le_le`, `.measure_abs_ge_le`: lower and two-sided
  tails.
* `ProbabilityTheory.HasSubgaussianMGF.sum_mul_of_iIndepFun`: `∑ aᵢ Xᵢ` has proxy `∑ aᵢ² cᵢ`.
* `ProbabilityTheory.HasSubgaussianMGF.measure_exists_ge_le`: the union bound for a maximum.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- A sub-Gaussian variable is sub-Gaussian with any larger proxy. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.mono (h : HasSubgaussianMGF X c μ) {d : ℝ≥0}
    (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  sorry

/-- Mathlib's `HasSubgaussianMGF.const_mul` with the proxy written `‖r‖₊ ^ 2 * c`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.const_mul' (h : HasSubgaussianMGF X c μ)
    (r : ℝ) : HasSubgaussianMGF (fun ω => r * X ω) (‖r‖₊ ^ 2 * c) μ := by
  sorry

/-- A sub-Gaussian variable has mean zero. A probability measure is needed: if `μ univ < 1` the
moment generating function bound does not force the mean to vanish. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_eq_zero [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) : ∫ ω, X ω ∂μ = 0 := by
  sorry

/-- The second moment of a sub-Gaussian variable is at most its proxy. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.integral_sq_le [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) : ∫ ω, X ω ^ 2 ∂μ ≤ c := by
  sorry

/-- The lower tail of a sub-Gaussian variable. With `c = 0`, Lean's `t ^ 2 / 0 = 0` makes the
bound `1`; the variable is then `0` almost everywhere. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.measure_le_le (h : HasSubgaussianMGF X c μ)
    {t : ℝ} (ht : 0 ≤ t) : μ.real {ω | X ω ≤ -t} ≤ rexp (-t ^ 2 / (2 * c)) := by
  sorry

/-- The two-sided tail of a sub-Gaussian variable. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.measure_abs_ge_le
    (h : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * rexp (-t ^ 2 / (2 * c)) := by
  sorry

/-- A weighted sum of independent sub-Gaussian variables is sub-Gaussian with proxy
`∑ aᵢ² cᵢ`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.sum_mul_of_iIndepFun {ι : Type*}
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ι → ℝ≥0} {s : Finset ι}
    (h : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) (a : ι → ℝ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, a i * X i ω) (∑ i ∈ s, ‖a i‖₊ ^ 2 * c i) μ := by
  sorry

/-- The union bound for the maximum of finitely many sub-Gaussian variables with a common proxy.
No independence is assumed. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.measure_exists_ge_le {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, t ≤ X i ω} ≤ Fintype.card ι * rexp (-t ^ 2 / (2 * c)) := by
  sorry

end NLAlib
