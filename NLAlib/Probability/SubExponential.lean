/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-exponential random variables

`NLAlib.HasSubexponentialMGF X v b μ` says that the moment generating function of `X` is at most
`exp (v l² / 2)` on the window `b |l| < 1`, with `exp (l X)` integrable there. With `b = 0` the
window is all of `ℝ` and this is Mathlib's `HasSubgaussianMGF X v μ`. Centred squares of
sub-Gaussian variables are sub-exponential (`NLAlib/Probability/SubGaussian/Square.lean`), and
the tail of a sum of independent sub-exponential variables is Bernstein's inequality.

## Main definitions

* `NLAlib.HasSubexponentialMGF X v b μ`: variance proxy `v`, scale `b`.

## Main results

* `NLAlib.HasSubexponentialMGF.sum_of_iIndepFun`: sums of independent sub-exponential variables.
* `NLAlib.HasSubexponentialMGF.measure_ge_le`: `P(t ≤ X) ≤ exp (-min (t²/(2v)) (t/(2b)))`, and
  its two regimes `measure_ge_le_of_mul_le`, `measure_ge_le_of_le_mul`.
* `NLAlib.HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`: Bernstein's inequality.
* `NLAlib.hasSubexponentialMGF_zero_iff`: scale `0` is the sub-Gaussian case.

## References

* [M. J. Wainwright, *High-Dimensional Statistics*][Wainwright2019], §2.1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {v b : ℝ≥0}

/-- `X` has a sub-exponential moment generating function with variance proxy `v` and scale `b`
under `μ`: for every `l` with `b * |l| < 1`, `exp (l * X)` is integrable and
`mgf X μ l ≤ exp (v * l ^ 2 / 2)` ([Wainwright2019], Definition 2.7, with `ν² = v`, `α = b`).
With `b = 0` the window is all of `ℝ` and this is `HasSubgaussianMGF X v μ`
(`hasSubexponentialMGF_zero_iff`). -/
structure HasSubexponentialMGF (X : Ω → ℝ) (v b : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- `exp (l * X)` is integrable on the window. -/
  integrable_exp_mul : ∀ l : ℝ, b * |l| < 1 → Integrable (fun ω => rexp (l * X ω)) μ
  /-- The moment generating function is at most `exp (v * l ^ 2 / 2)` on the window. -/
  mgf_le : ∀ l : ℝ, b * |l| < 1 → mgf X μ l ≤ rexp (v * l ^ 2 / 2)

namespace HasSubexponentialMGF

/-- A sub-exponential variable is almost everywhere measurable. -/
theorem aemeasurable (h : HasSubexponentialMGF X v b μ) : AEMeasurable X μ := by
  sorry

/-- A larger variance proxy and a larger scale. -/
theorem mono (h : HasSubexponentialMGF X v b μ) {v' b' : ℝ≥0} (hv : v ≤ v') (hb : b ≤ b') :
    HasSubexponentialMGF X v' b' μ := by
  sorry

/-- The negative of a sub-exponential variable. -/
theorem neg (h : HasSubexponentialMGF X v b μ) : HasSubexponentialMGF (fun ω => -X ω) v b μ := by
  sorry

/-- A scalar multiple of a sub-exponential variable. -/
theorem const_mul (h : HasSubexponentialMGF X v b μ) (r : ℝ) :
    HasSubexponentialMGF (fun ω => r * X ω) (‖r‖₊ ^ 2 * v) (‖r‖₊ * b) μ := by
  sorry

/-- The sum of two independent sub-exponential variables. -/
theorem add_of_indepFun {Y : Ω → ℝ} {v' b' : ℝ≥0} (hX : HasSubexponentialMGF X v b μ)
    (hY : HasSubexponentialMGF Y v' b' μ) (hXY : IndepFun X Y μ) :
    HasSubexponentialMGF (fun ω => X ω + Y ω) (v + v') (max b b') μ := by
  sorry

/-- The sum of independent sub-exponential variables: the variance proxies add and the scale is
the largest scale. -/
theorem sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {v b : ι → ℝ≥0}
    {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ) :
    HasSubexponentialMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) (s.sup b) μ := by
  sorry

/-- A sub-exponential variable has mean zero under a probability measure. -/
theorem integral_eq_zero [IsProbabilityMeasure μ] (h : HasSubexponentialMGF X v b μ) :
    ∫ ω, X ω ∂μ = 0 := by
  sorry

/-- **The sub-exponential tail** ([Wainwright2019], Proposition 2.9):
`P(t ≤ X) ≤ exp (-min (t² / (2v)) (t / (2b)))`. If `b = 0` or `v = 0`, Lean's division by zero
makes the exponent `0` and the bound `1`; the regime forms `measure_ge_le_of_mul_le` and
`measure_ge_le_of_le_mul` are the usable statements then. -/
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

/-- A sub-Gaussian variable is sub-exponential with scale `0`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) : HasSubexponentialMGF X c 0 μ := by
  sorry

/-- Scale `0` is the sub-Gaussian case. -/
theorem hasSubexponentialMGF_zero_iff : HasSubexponentialMGF X v 0 μ ↔ HasSubgaussianMGF X v μ := by
  sorry

end NLAlib
