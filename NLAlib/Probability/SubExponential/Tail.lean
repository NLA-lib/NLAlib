/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.SubExponential.Basic

/-!
# Tails of sub-exponential random variables

The tail of a sub-exponential variable, `P(t ≤ X) ≤ exp (-min (t²/(2v)) (t/(2b)))`, its two
regimes, the lower and two-sided tails, and Bernstein's inequality for sums of independent
sub-exponential variables.

## Main results

* `NLAlib.HasSubexponentialMGF.measure_ge_le` and its regimes
  `NLAlib.HasSubexponentialMGF.measure_ge_le_of_mul_le`,
  `NLAlib.HasSubexponentialMGF.measure_ge_le_of_le_mul`.
* `NLAlib.HasSubexponentialMGF.measure_le_le`, `NLAlib.HasSubexponentialMGF.measure_abs_ge_le`.
* `NLAlib.HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`: Bernstein's inequality.

## References

* [M. J. Wainwright, *High-Dimensional Statistics*][Wainwright2019], §2.1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {v b : ℝ≥0}

namespace HasSubexponentialMGF

/-- **The sub-exponential tail** ([Wainwright2019], Proposition 2.9):
`P(t ≤ X) ≤ exp (-min (t² / (2v)) (t / (2b)))`. If `b = 0` or `v = 0`, Lean's division by zero
makes the exponent `0` and the bound `1`; the regime forms are the usable statements then (for a
sub-Gaussian variable, `b = 0`, use `measure_ge_le_of_mul_le`). -/
theorem measure_ge_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
  sorry

/-- The sub-Gaussian regime of the sub-exponential tail: for `b t ≤ v`,
`P(t ≤ X) ≤ exp (-t² / (2v))`. With `b = 0` this is the sub-Gaussian tail. -/
theorem measure_ge_le_of_mul_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t)
    (hbt : b * t ≤ v) : μ.real {ω | t ≤ X ω} ≤ rexp (-t ^ 2 / (2 * v)) := by
  sorry

/-- The exponential regime of the sub-exponential tail: for `v ≤ b t`,
`P(t ≤ X) ≤ exp (-t / (2b))`. -/
theorem measure_ge_le_of_le_mul (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t)
    (hbt : v ≤ b * t) : μ.real {ω | t ≤ X ω} ≤ rexp (-t / (2 * b)) := by
  sorry

/-- The lower tail of a sub-exponential variable. -/
theorem measure_le_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | X ω ≤ -t} ≤ rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
  sorry

/-- The two-sided tail of a sub-exponential variable. -/
theorem measure_abs_ge_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b))) := by
  sorry

/-- **Bernstein's inequality** for independent sub-exponential variables
([Wainwright2019], §2.1.3). -/
theorem measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {v b : ι → ℝ≥0} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
      rexp (-min (t ^ 2 / (2 * ∑ i ∈ s, v i)) (t / (2 * s.sup b))) := by
  sorry

end HasSubexponentialMGF

end NLAlib
