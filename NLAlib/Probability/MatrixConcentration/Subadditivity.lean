/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Lieb
public import NLAlib.Matrix.Functions.OperatorMonotone
public import NLAlib.Probability.MatrixConcentration.Laplace

/-!
# Subadditivity of matrix cumulant generating functions

Lieb's concavity theorem in expectation: for a fixed Hermitian `H` and a random Hermitian `X`,
`E tr exp (H + X) ≤ tr exp (H + log E e^X)` (Tropp 2015, Corollary 3.4.2). For independent
random Hermitian matrices it gives the subadditivity of matrix cumulant generating functions,
`E tr exp (∑ X k) ≤ tr exp (∑ log E e^{X k})` (Tropp 2015, Lemma 3.5.1), the step from one summand
to a sum in every matrix concentration inequality.

## Main results

* `NLAlib.integral_re_trace_exp_add_le`: Lieb's theorem in expectation.
* `NLAlib.integral_re_trace_exp_sum_le`: subadditivity of matrix cumulant generating functions.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], §3.4, §3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lieb's theorem in expectation** ([Tropp2015], Corollary 3.4.2). -/
theorem integral_re_trace_exp_add_le [IsProbabilityMeasure μ] {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) {X : Ω → Matrix n n 𝕜} (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hint : Integrable (fun ω => exp (X ω)) μ) :
    ∫ ω, RCLike.re (exp (H + X ω)).trace ∂μ ≤
      RCLike.re (exp (H + cfc Real.log (∫ ω, exp (X ω) ∂μ))).trace := by
  sorry

variable {ι : Type*} [Fintype ι] {X : ι → Ω → Matrix n n 𝕜}

/-- The trace exponential of a sum of independent random Hermitian matrices with integrable
exponentials is integrable. -/
theorem integrable_re_trace_exp_sum (hind : iIndepFun X μ)
    (hX : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) (hint : ∀ k, Integrable (fun ω => exp (X k ω)) μ) :
    Integrable (fun ω => RCLike.re (exp (∑ k, X k ω)).trace) μ := by
  sorry

/-- **Subadditivity of matrix cumulant generating functions** ([Tropp2015], Lemma 3.5.1). -/
theorem integral_re_trace_exp_sum_le (hind : iIndepFun X μ)
    (hX : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) (hint : ∀ k, Integrable (fun ω => exp (X k ω)) μ) :
    ∫ ω, RCLike.re (exp (∑ k, X k ω)).trace ∂μ ≤
      RCLike.re (exp (∑ k, cfc Real.log (∫ ω, exp (X k ω) ∂μ))).trace := by
  sorry

end NLAlib
