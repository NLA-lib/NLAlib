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
the tail of a sum of independent sub-exponential variables is Bernstein's inequality
(`NLAlib/Probability/SubExponential/Tail.lean`).

## Main definitions

* `NLAlib.HasSubexponentialMGF X v b μ`: variance proxy `v`, scale `b`.

## Main results

* `NLAlib.HasSubexponentialMGF.sum_of_iIndepFun`, `.sum_const_mul_of_iIndepFun`: sums and
  weighted sums of independent sub-exponential variables.
* `NLAlib.hasSubexponentialMGF_zero_iff_hasSubgaussianMGF`: scale `0` is the sub-Gaussian case.

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
(`hasSubexponentialMGF_zero_iff_hasSubgaussianMGF`). -/
structure HasSubexponentialMGF (X : Ω → ℝ) (v b : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- `exp (l * X)` is integrable on the window. -/
  integrable_exp_mul : ∀ l : ℝ, b * |l| < 1 → Integrable (fun ω => rexp (l * X ω)) μ
  /-- The moment generating function is at most `exp (v * l ^ 2 / 2)` on the window. -/
  mgf_le : ∀ l : ℝ, b * |l| < 1 → mgf X μ l ≤ rexp (v * l ^ 2 / 2)

namespace HasSubexponentialMGF

/-- A sub-exponential variable is almost everywhere measurable. -/
theorem aemeasurable (h : HasSubexponentialMGF X v b μ) : AEMeasurable X μ := by
  sorry

/-- A sub-exponential variable lives on a measure of total mass at most `1`. -/
theorem measure_univ_le_one (h : HasSubexponentialMGF X v b μ) : μ Set.univ ≤ 1 := by
  sorry

theorem isFiniteMeasure (h : HasSubexponentialMGF X v b μ) : IsFiniteMeasure μ := by
  sorry

/-- A sub-exponential variable has moments of every order. -/
theorem memLp (h : HasSubexponentialMGF X v b μ) (p : ℝ≥0) : MemLp X p μ := by
  sorry

theorem integrable (h : HasSubexponentialMGF X v b μ) : Integrable X μ := by
  sorry

/-- The cumulant generating function on the window. -/
theorem cgf_le (h : HasSubexponentialMGF X v b μ) {l : ℝ} (hl : b * |l| < 1) :
    cgf X μ l ≤ v * l ^ 2 / 2 := by
  sorry

/-- The property depends only on the almost-everywhere class of the variable. -/
theorem congr {Y : Ω → ℝ} (h : HasSubexponentialMGF X v b μ) (hXY : X =ᵐ[μ] Y) :
    HasSubexponentialMGF Y v b μ := by
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

/-- A weighted sum of independent sub-exponential variables. -/
theorem sum_const_mul_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {v b : ι → ℝ≥0} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ)
    (a : ι → ℝ) :
    HasSubexponentialMGF (fun ω => ∑ i ∈ s, a i * X i ω) (∑ i ∈ s, ‖a i‖₊ ^ 2 * v i)
      (s.sup fun i => ‖a i‖₊ * b i) μ := by
  sorry

/-- A sub-exponential variable has mean zero under a probability measure. -/
theorem integral_eq_zero [IsProbabilityMeasure μ] (h : HasSubexponentialMGF X v b μ) :
    ∫ ω, X ω ∂μ = 0 := by
  sorry

end HasSubexponentialMGF

/-- A sub-Gaussian variable is sub-exponential with scale `0`. -/
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) : HasSubexponentialMGF X c 0 μ := by
  sorry

/-- Scale `0` is the sub-Gaussian case. -/
theorem hasSubexponentialMGF_zero_iff_hasSubgaussianMGF :
    HasSubexponentialMGF X v 0 μ ↔ HasSubgaussianMGF X v μ := by
  sorry

end NLAlib
