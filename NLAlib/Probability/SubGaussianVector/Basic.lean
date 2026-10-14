/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.SubGaussian.Basic

/-!
# Sub-Gaussian random vectors

`NLAlib.IsSubgaussianVector X c μ` says that every real linear functional `re (u ⬝ᵥ X)` of the
random vector `X : Ω → n → 𝕜` is sub-Gaussian with proxy `c ‖u‖²`. Every real-linear functional
of `𝕜ⁿ` has this form, so over `ℂ` the real and imaginary parts are constrained alike; over `ℝ`,
`re` is the identity (`RCLike.re_to_real`). It is the hypothesis of the tails of `‖X‖²` and of the
net argument for random matrices with sub-Gaussian rows.

Standard Gaussian and Rademacher vectors are sub-Gaussian vectors with proxy `1`, so are real
vectors with independent sub-Gaussian coordinates, and linear images of sub-Gaussian vectors are
sub-Gaussian vectors.

## Main definitions

* `NLAlib.IsSubgaussianVector X c μ`.

## Main results

* `NLAlib.IsSubgaussianVector.mulVec`: `A X` has proxy `c ‖A‖²`.
* `NLAlib.IsSubgaussianVector.of_iIndepFun`: independent real sub-Gaussian coordinates.
* `NLAlib.isSubgaussianVector_of_hasLaw_gaussianVector`,
  `NLAlib.isSubgaussianVector_of_hasLaw_rademacherVector`: proxy `1`.
* `ProbabilityTheory.HasLaw.isSubgaussianVector_iff`: the property depends only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {𝕜 : Type*} [RCLike 𝕜] {X : Ω → n → 𝕜} {c : ℝ≥0}

/-- `X` is a sub-Gaussian random vector with proxy `c` under `μ`: every real linear functional
`re (u ⬝ᵥ X)` is sub-Gaussian with proxy `c ‖u‖²`. -/
structure IsSubgaussianVector (X : Ω → n → 𝕜) (c : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- Every real linear functional of `X` is sub-Gaussian with proxy `c ‖u‖²`. -/
  hasSubgaussianMGF : ∀ u : n → 𝕜,
    HasSubgaussianMGF (fun ω => RCLike.re (u ⬝ᵥ X ω)) (c * ‖WithLp.toLp 2 u‖₊ ^ 2) μ

namespace IsSubgaussianVector

/-- A larger proxy. -/
theorem mono (h : IsSubgaussianVector X c μ) {d : ℝ≥0} (hcd : c ≤ d) :
    IsSubgaussianVector X d μ := by
  sorry

/-- The property depends only on the almost-everywhere class of the vector. -/
theorem congr {Y : Ω → n → 𝕜} (h : IsSubgaussianVector X c μ) (hXY : X =ᵐ[μ] Y) :
    IsSubgaussianVector Y c μ := by
  sorry

/-- The real part of each coordinate is sub-Gaussian with proxy `c`. -/
theorem hasSubgaussianMGF_re_apply (h : IsSubgaussianVector X c μ) (i : n) :
    HasSubgaussianMGF (fun ω => RCLike.re (X ω i)) c μ := by
  sorry

/-- The coordinates of a sub-Gaussian vector have moments of every order. -/
theorem memLp_apply (h : IsSubgaussianVector X c μ) (i : n) (p : ℝ≥0) :
    MemLp (fun ω => X ω i) p μ := by
  sorry

/-- A sub-Gaussian vector has mean zero. -/
theorem integral_apply_eq_zero [IsProbabilityMeasure μ] (h : IsSubgaussianVector X c μ)
    (i : n) : ∫ ω, X ω i ∂μ = 0 := by
  sorry

/-- A linear image of a sub-Gaussian vector is a sub-Gaussian vector with proxy `c ‖A‖²`. -/
theorem mulVec {m : Type*} [Fintype m] (h : IsSubgaussianVector X c μ) (A : Matrix m n 𝕜) :
    IsSubgaussianVector (fun ω => A *ᵥ X ω) (c * ‖specNorm A‖₊ ^ 2) μ := by
  sorry

/-- A real vector with independent coordinates, each sub-Gaussian with proxy `c`, is a
sub-Gaussian vector with proxy `c`. -/
theorem of_iIndepFun {X : Ω → n → ℝ} (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) : IsSubgaussianVector X c μ := by
  sorry

end IsSubgaussianVector

/-- Being a sub-Gaussian vector depends only on the law. -/
theorem _root_.ProbabilityTheory.HasLaw.isSubgaussianVector_iff {ν : Measure (n → 𝕜)}
    (hX : HasLaw X ν μ) : IsSubgaussianVector X c μ ↔ IsSubgaussianVector id c ν := by
  sorry

/-- A standard Gaussian vector is a sub-Gaussian vector with proxy `1`. -/
theorem isSubgaussianVector_of_hasLaw_gaussianVector {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) : IsSubgaussianVector X 1 μ := by
  sorry

/-- A vector of independent random signs is a sub-Gaussian vector with proxy `1`. -/
theorem isSubgaussianVector_of_hasLaw_rademacherVector {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : IsSubgaussianVector X 1 μ := by
  sorry

end NLAlib
