/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.Variance

/-!
# Jensen's inequality for the second moment

Under a probability measure the mean of a square-integrable real function is at most the square
root of its second moment, $\mathbb{E} f \le (\mathbb{E} f^2)^{1/2}$. This is the step that turns a
second-moment bound into a first-moment one; the library states the second moment and leaves the
first to this lemma (docs/contributing/statements.md §2, T15). Upstream candidate for
`Mathlib.Probability.Moments.Variance`.

## Main results

* `ProbabilityTheory.integral_le_sqrt_integral_sq`: $\mathbb{E} f \le \sqrt{\mathbb{E} f^2}$.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Jensen's inequality for the square**: under a probability measure, a real function with a
finite second moment satisfies $\mathbb{E} f \le \sqrt{\mathbb{E} f^2}$. From the nonnegativity of
the variance, `ProbabilityTheory.variance_eq_sub`. [Vershynin2018, §1.2]. -/
theorem integral_le_sqrt_integral_sq [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ∫ ω, f ω ∂μ ≤ √(∫ ω, f ω ^ 2 ∂μ) := by
  have hvar := variance_nonneg f μ
  rw [variance_eq_sub hf] at hvar
  simp only [Pi.pow_apply] at hvar
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

end ProbabilityTheory
