/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.Subadditivity

/-!
# Matrix moment generating function bounds and the master bounds

`NLAlib.HasMatrixMGFBound X g A s μ` says that the random matrix `X` is almost surely Hermitian
and that `E exp (θ X) ≤ exp (g θ • A)` in the Loewner order for every `θ ∈ s`, with `A` Hermitian.
Bounded positive semidefinite summands (Chernoff), bounded centred summands (Bernstein) and a
sub-Gaussian scalar times a fixed Hermitian matrix (series) all have such bounds. For independent
summands with these bounds, the trace of the matrix moment generating function of the sum is at
most `tr exp (g θ ∑ A k)` (through the subadditivity of matrix cumulant generating functions and
the operator monotonicity of the logarithm), which gives the master tail and mean bounds.

The bound is not monotone in `A`: the matrix exponential is not operator monotone. Monotonicity
in `A` holds after the trace (`NLAlib.re_trace_exp_le_re_trace_exp_of_le`), which is where the
consumers use it.

## Main definitions

* `NLAlib.HasMatrixMGFBound X g A s μ`.

## Main results

* `NLAlib.HasMatrixMGFBound.integral_re_trace_exp_sum_le`: the trace-level master bound.
* `NLAlib.HasMatrixMGFBound.measure_eigenvalue_zero_sum_ge_le`: the master tail bound.
* `NLAlib.HasMatrixMGFBound.integral_eigenvalue_zero_sum_le`: the master bound for the mean.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], §3.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The random matrix `X` is almost surely Hermitian and its matrix moment generating function is
bounded by `exp (g θ • A)` in the Loewner order for every `θ ∈ s`, with `A` Hermitian. -/
structure HasMatrixMGFBound (X : Ω → Matrix n n 𝕜) (g : ℝ → ℝ) (A : Matrix n n 𝕜) (s : Set ℝ)
    (μ : Measure Ω) : Prop where
  /-- `X` is almost surely Hermitian. -/
  ae_isHermitian : ∀ᵐ ω ∂μ, (X ω).IsHermitian
  /-- The bounding matrix is Hermitian. -/
  isHermitian_bound : A.IsHermitian
  /-- `exp (θ X)` is integrable for `θ ∈ s`. -/
  integrable_exp : ∀ θ ∈ s, Integrable (fun ω => exp (θ • X ω)) μ
  /-- The bound on the matrix moment generating function. -/
  integral_exp_le : ∀ θ ∈ s, ∫ ω, exp (θ • X ω) ∂μ ≤ exp (g θ • A)

namespace HasMatrixMGFBound

variable {X : Ω → Matrix n n 𝕜} {g : ℝ → ℝ} {A : Matrix n n 𝕜} {s : Set ℝ}

/-- A random matrix with a matrix MGF bound at some `θ ≠ 0` is almost everywhere measurable. -/
theorem aemeasurable (h : HasMatrixMGFBound X g A s μ) (hs : ∃ θ ∈ s, θ ≠ 0) :
    AEMeasurable X μ := by
  sorry

/-- The bound depends only on the almost-everywhere class of `X`. -/
theorem congr {Y : Ω → Matrix n n 𝕜} (h : HasMatrixMGFBound X g A s μ) (hXY : X =ᵐ[μ] Y) :
    HasMatrixMGFBound Y g A s μ := by
  sorry

/-- A bound on a set holds on every subset. -/
theorem mono_set (h : HasMatrixMGFBound X g A s μ) {s' : Set ℝ} (hs : s' ⊆ s) :
    HasMatrixMGFBound X g A s' μ := by
  sorry

/-- The bound for `-X`, which gives the lower tails. -/
theorem neg (h : HasMatrixMGFBound X g A s μ) :
    HasMatrixMGFBound (fun ω => -X ω) (fun θ => g (-θ)) A (-s) μ := by
  sorry

variable {ι : Type*} [Fintype ι] {X : ι → Ω → Matrix n n 𝕜} {A : ι → Matrix n n 𝕜}

/-- The trace exponential of `θ` times a sum of independent summands with matrix MGF bounds is
integrable. -/
theorem integrable_re_trace_exp_sum (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθ : θ ∈ s) :
    Integrable (fun ω => RCLike.re (exp (θ • ∑ k, X k ω)).trace) μ := by
  sorry

/-- **The trace-level master bound**: `E tr exp (θ ∑ X k) ≤ tr exp (g θ • ∑ A k)` for independent
summands with matrix MGF bounds and `θ ∈ s` ([Tropp2015], §3.6). -/
theorem integral_re_trace_exp_sum_le (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθ : θ ∈ s) :
    ∫ ω, RCLike.re (exp (θ • ∑ k, X k ω)).trace ∂μ ≤ RCLike.re (exp (g θ • ∑ k, A k)).trace := by
  sorry

/-- **The master tail bound** ([Tropp2015], Theorem 3.6.1):
`P(t ≤ λ_max (∑ X k)) ≤ e^{-θt} tr exp (g θ • ∑ A k)` for `θ ∈ s`, `θ > 0`. -/
theorem measure_eigenvalue_zero_sum_ge_le [Nonempty n] (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθs : θ ∈ s) (hθ : 0 < θ) (t : ℝ) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Real.exp (-θ * t) * RCLike.re (exp (g θ • ∑ k, A k)).trace := by
  sorry

/-- The master tail bound in the dimension form: `≤ d e^{-θt + g θ λ_max (∑ A k)}`. -/
theorem measure_eigenvalue_zero_sum_ge_le_card_mul_exp [Nonempty n] (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθs : θ ∈ s) (hθ : 0 < θ)
    (hg : 0 ≤ g θ) (t : ℝ) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * Real.exp (-θ * t + g θ * eigenvalue (∑ k, A k) 0) := by
  sorry

/-- **The master bound for the mean** ([Tropp2015], Theorem 3.6.1). -/
theorem integral_eigenvalue_zero_sum_le [Nonempty n] (hind : iIndepFun X μ)
    (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) (hX : ∀ k, Integrable (X k) μ) {θ : ℝ}
    (hθs : θ ∈ s) (hθ : 0 < θ) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      θ⁻¹ * Real.log (RCLike.re (exp (g θ • ∑ k, A k)).trace) := by
  sorry

end HasMatrixMGFBound

end NLAlib
