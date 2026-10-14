/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import NLAlib.Probability.Isotropic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Standard Gaussian vectors

`NLAlib.gaussianVector n` is the law of a vector in `ℝⁿ` with independent standard Gaussian
coordinates, the product `Measure.pi fun _ => gaussianReal 0 1`. It is an `abbrev`, so the
product-law lemmas of `NLAlib/Probability/Law.lean` apply to it directly; `rw` with a lemma
stated for one spelling does not fire on the other, so use `simp only` or `exact` across the two.
Its image in `EuclideanSpace ℝ n` is Mathlib's `stdGaussian`
(`ProbabilityTheory.map_pi_eq_stdGaussian`), and it is an `IsGaussian` measure, so Mathlib's
`HasGaussianLaw` API applies.

This file proves, for a random variable with a centred Gaussian law, the interfaces and moments
the probability layers use: the sub-Gaussian proxy, the second and fourth moments, isotropy of a
standard Gaussian vector and the law of its linear forms. The laws are real; a complex Gaussian
law will be a separate definition (`docs/design/Probability-P2.md` §7).

## Main definitions

* `NLAlib.gaussianVector n`.

## Main results

* `NLAlib.hasSubgaussianMGF_of_hasLaw_gaussianReal`: a centred Gaussian of variance `v` has proxy
  `v`.
* `NLAlib.integral_pow_four_of_hasLaw_gaussianReal`: `E X⁴ = 3 v²`.
* `NLAlib.isIsotropic_of_hasLaw_gaussianVector`.
* `NLAlib.hasLaw_dotProduct_of_hasLaw_gaussianVector`: `u ⬝ᵥ X` has law `N(0, ‖u‖²)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]

/-- The standard Gaussian law on `ℝⁿ`: independent coordinates, each `N(0, 1)`. -/
noncomputable abbrev gaussianVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ : n => gaussianReal 0 1

/-- The standard Gaussian vector is a Gaussian measure. -/
instance isGaussian_gaussianVector : IsGaussian (gaussianVector n) := by
  sorry

/-- A centred Gaussian of variance `v` is sub-Gaussian with proxy `v`. -/
theorem hasSubgaussianMGF_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  sorry

/-- A centred Gaussian has mean zero. -/
theorem integral_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ∂μ = 0 := by
  sorry

/-- The second moment of a centred Gaussian is its variance. -/
theorem integral_sq_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ^ 2 ∂μ = v := by
  sorry

/-- The fourth moment of a centred Gaussian of variance `v` is `3 v²`. -/
theorem integral_pow_four_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ^ 4 ∂μ = 3 * (v : ℝ) ^ 2 := by
  sorry

/-- A standard Gaussian vector is isotropic. -/
theorem isIsotropic_of_hasLaw_gaussianVector [DecidableEq n] {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) : IsIsotropic X μ := by
  sorry

/-- A linear form `u ⬝ᵥ X` of a standard Gaussian vector is a centred Gaussian of variance
`‖u‖²`. -/
theorem hasLaw_dotProduct_of_hasLaw_gaussianVector {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) (u : n → ℝ) :
    HasLaw (fun ω => u ⬝ᵥ X ω) (gaussianReal 0 (‖WithLp.toLp 2 u‖₊ ^ 2)) μ := by
  sorry

end NLAlib
