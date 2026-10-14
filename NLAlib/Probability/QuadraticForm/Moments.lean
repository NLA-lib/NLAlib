/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.Rademacher

/-!
# Second moments of quadratic forms

For a random vector `X` in `𝕜ⁿ` with independent coordinates of mean zero, `E |X i|² = 1`,
pseudo-variance `E X i² = s` and `E |X i|⁴ = m₄`, the quadratic form `Xᴴ A X` has mean `tr A`
(Hutchinson; `NLAlib.IsIsotropic.integral_quadForm`) and

`E |Xᴴ A X - tr A|² = ‖A‖_F² + |s|² re ⟨A, Aᵀ⟩_F + (m₄ - 2 - |s|²) ∑ |A i i|²`.

One statement covers real probes (`s = 1`: Gaussian `m₄ = 3`, Rademacher `m₄ = 1`) and complex
ones (`s = 0`: complex Gaussian `m₄ = 2`, Steinhaus `m₄ = 1`). For real symmetric `A` it is the
variance `2 ‖A‖_F² + (m₄ - 3) ∑ A i i²`, stated with its Gaussian and Rademacher cases.

## Main results

* `NLAlib.memLp_quadForm`: the quadratic form is square integrable.
* `NLAlib.integral_norm_quadForm_sub_trace_sq`: the second moment about the mean.
* `NLAlib.variance_quadForm_of_isHermitian`: the real symmetric case.
* `NLAlib.variance_quadForm_of_hasLaw_gaussianVector`,
  `NLAlib.variance_quadForm_of_hasLaw_rademacherVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {𝕜 : Type*} [RCLike 𝕜] {X : Ω → n → 𝕜}

/-- A quadratic form in a vector with fourth moments is square integrable. -/
theorem memLp_quadForm (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ) (A : Matrix n n 𝕜) :
    MemLp (fun ω => quadForm A (X ω)) 2 μ := by
  sorry

/-- **The second moment of a quadratic form** about its mean `tr A`, for independent
coordinates with mean zero, `E |X i|² = 1`, `E X i² = s` and `E |X i|⁴ = m₄`. -/
theorem integral_norm_quadForm_sub_trace_sq (hind : iIndepFun (fun i ω => X ω i) μ)
    (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1) {s : 𝕜} (hs : ∀ i, ∫ ω, X ω i ^ 2 ∂μ = s)
    {m₄ : ℝ} (hm₄ : ∀ i, ∫ ω, ‖X ω i‖ ^ 4 ∂μ = m₄) (A : Matrix n n 𝕜) :
    ∫ ω, ‖quadForm A (X ω) - A.trace‖ ^ 2 ∂μ =
      frobNorm A ^ 2 + ‖s‖ ^ 2 * frobInner A Aᵀ + (m₄ - 2 - ‖s‖ ^ 2) * ∑ i, ‖A i i‖ ^ 2 := by
  sorry

/-- The variance of a real quadratic form with symmetric `A`:
`Var (Xᵀ A X) = 2 ‖A‖_F² + (m₄ - 3) ∑ A i i²`. -/
theorem variance_quadForm_of_isHermitian {X : Ω → n → ℝ} (hind : iIndepFun (fun i ω => X ω i) μ)
    (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, X ω i ^ 2 ∂μ = 1) {m₄ : ℝ} (hm₄ : ∀ i, ∫ ω, X ω i ^ 4 ∂μ = m₄)
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (X ω)) μ =
      2 * frobNorm A ^ 2 + (m₄ - 3) * ∑ i, A i i ^ 2 := by
  sorry

/-- Hutchinson's variance with a Gaussian probe: `Var (Xᵀ A X) = 2 ‖A‖_F²` for symmetric `A`. -/
theorem variance_quadForm_of_hasLaw_gaussianVector {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (X ω)) μ = 2 * frobNorm A ^ 2 := by
  sorry

/-- Hutchinson's variance with a Rademacher probe:
`Var (Xᵀ A X) = 2 (‖A‖_F² - ∑ A i i²)` for symmetric `A`. -/
theorem variance_quadForm_of_hasLaw_rademacherVector {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (X ω)) μ = 2 * (frobNorm A ^ 2 - ∑ i, A i i ^ 2) := by
  sorry

end NLAlib
