/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.Probability.Measurability.Matrix

/-!
# The matrix Laplace transform method

For a random Hermitian matrix `Y`, the tail of its largest eigenvalue is bounded by the trace of
its matrix moment generating function, `P(t ≤ λ_max Y) ≤ e^{-θ t} E tr exp (θ Y)` for `θ > 0`, and
its mean by `θ⁻¹ log E tr exp (θ Y)` (Tropp 2015, Proposition 3.2.1). The smallest eigenvalue,
`eigenvalue Y k` with `k + 1 = card n`, is handled with `θ < 0`. The eigenvalue and spectral norm of
an integrable random matrix are integrable, so the means here are not junk values.

## Main results

* `NLAlib.measureReal_eigenvalue_zero_ge_le`, `NLAlib.measureReal_eigenvalue_le_le`: the tails.
* `NLAlib.integral_eigenvalue_zero_le`, `NLAlib.le_integral_eigenvalue`: the means.
* `NLAlib.integrable_eigenvalue`, `NLAlib.integrable_specNorm`.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], §3.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {Y : Ω → Matrix n n 𝕜}

/-- An eigenvalue of an integrable random matrix is integrable. -/
theorem integrable_eigenvalue [IsFiniteMeasure μ] (hY : Integrable Y μ) (k : ℕ) :
    Integrable (fun ω => eigenvalue (Y ω) k) μ := by
  sorry

/-- The spectral norm of an integrable random matrix is integrable. -/
theorem integrable_specNorm {m : Type*} [Fintype m] {S : Ω → Matrix m n 𝕜} (hS : Integrable S μ) :
    Integrable (fun ω => specNorm (S ω)) μ := by
  sorry

variable [IsProbabilityMeasure μ]

/-- **The matrix Laplace transform bound** for the largest eigenvalue ([Tropp2015],
Proposition 3.2.1). -/
theorem measureReal_eigenvalue_zero_ge_le [Nonempty n] (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (t : ℝ) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤
      Real.exp (-θ * t) * ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ := by
  sorry

/-- The matrix Laplace transform bound for the smallest eigenvalue, with `θ < 0`. -/
theorem measureReal_eigenvalue_le_le (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {k : ℕ}
    (hk : k + 1 = Fintype.card n) {θ : ℝ} (hθ : θ < 0)
    (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ) (t : ℝ) :
    μ.real {ω | eigenvalue (Y ω) k ≤ t} ≤
      Real.exp (-θ * t) * ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ := by
  sorry

/-- The matrix Laplace transform bound for the mean of the largest eigenvalue. -/
theorem integral_eigenvalue_zero_le [Nonempty n] (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hYi : Integrable Y μ) {θ : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ) :
    ∫ ω, eigenvalue (Y ω) 0 ∂μ ≤ θ⁻¹ * Real.log (∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ) := by
  sorry

/-- The matrix Laplace transform bound for the mean of the smallest eigenvalue, with `θ < 0`. -/
theorem le_integral_eigenvalue (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hYi : Integrable Y μ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) {θ : ℝ} (hθ : θ < 0)
    (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ) :
    θ⁻¹ * Real.log (∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ) ≤ ∫ ω, eigenvalue (Y ω) k ∂μ := by
  sorry

end NLAlib
