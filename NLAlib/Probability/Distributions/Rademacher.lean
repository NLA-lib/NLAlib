/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Isotropic
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Rademacher variables and vectors

`NLAlib.rademacherMeasure` is the law of a random sign: `±1` with probability `1/2` each.
`NLAlib.rademacherVector n` is the law of a vector of independent signs, an `abbrev` for the
product. This file proves, for random variables with these laws, the interfaces and moments the
probability layers use: proxy `1`, `X² = 1` almost surely, `E X⁴ = 1`, the moment generating
function `cosh`, and isotropy of the vector.

`NLAlib.integrable_rademacherMeasure` and `NLAlib.integral_rademacherMeasure` are stated for the
measure: they are its constructors (as Mathlib's `integral_bernoulliMeasure` is), from which the
random-variable forms follow.

## Main definitions

* `NLAlib.rademacherMeasure`, `NLAlib.rademacherVector n`.

## Main results

* `NLAlib.integral_rademacherMeasure`: `∫ f = (f 1 + f (-1)) / 2`.
* `NLAlib.hasSubgaussianMGF_of_hasLaw_rademacherMeasure`: proxy `1`.
* `NLAlib.isIsotropic_of_hasLaw_rademacherVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]

/-- The Rademacher law: `±1` with probability `1/2` each. It is Mathlib's
`bernoulliMeasure 1 (-1)` at `1/2`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac 1 + Measure.dirac (-1))

instance isProbabilityMeasure_rademacherMeasure : IsProbabilityMeasure rademacherMeasure := by
  sorry

/-- The law of a vector of independent random signs. -/
noncomputable abbrev rademacherVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ : n => rademacherMeasure

/-- Every function is integrable for the Rademacher law. -/
theorem integrable_rademacherMeasure {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) :
    Integrable f rademacherMeasure := by
  sorry

/-- The integral against the Rademacher law is the average of the two values. -/
theorem integral_rademacherMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) :
    ∫ x, f x ∂rademacherMeasure = (2 : ℝ)⁻¹ • (f 1 + f (-1)) := by
  sorry

/-- A random sign is `1` or `-1` almost surely. -/
theorem ae_eq_one_or_neg_one_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1 := by
  sorry

/-- The moment generating function of a random sign is `cosh`. -/
theorem mgf_of_hasLaw_rademacherMeasure {X : Ω → ℝ} (hX : HasLaw X rademacherMeasure μ)
    (t : ℝ) : mgf X μ t = Real.cosh t := by
  sorry

/-- A random sign is sub-Gaussian with proxy `1`. -/
theorem hasSubgaussianMGF_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : HasSubgaussianMGF X 1 μ := by
  sorry

/-- A random sign has mean zero. -/
theorem integral_of_hasLaw_rademacherMeasure {X : Ω → ℝ} (hX : HasLaw X rademacherMeasure μ) :
    ∫ ω, X ω ∂μ = 0 := by
  sorry

/-- The second moment of a random sign is `1`. -/
theorem integral_sq_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : ∫ ω, X ω ^ 2 ∂μ = 1 := by
  sorry

/-- The fourth moment of a random sign is `1`. -/
theorem integral_pow_four_of_hasLaw_rademacherMeasure {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : ∫ ω, X ω ^ 4 ∂μ = 1 := by
  sorry

/-- A vector of independent random signs is isotropic. -/
theorem isIsotropic_of_hasLaw_rademacherVector [DecidableEq n] {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : IsIsotropic X μ := by
  sorry

/-- The squared coordinates of a vector of random signs are `1` almost surely. -/
theorem ae_sq_eq_one_of_hasLaw_rademacherVector {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : ∀ᵐ ω ∂μ, ∀ i, X ω i ^ 2 = 1 := by
  sorry

end NLAlib
