/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.GaussianConcentration
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Gaussian concentration for functions of Gaussian matrices

A function of a standard Gaussian matrix that is `L`-Lipschitz for the Frobenius distance is
sub-Gaussian about its mean with proxy `L²`. The Lipschitz hypothesis is the explicit inequality
`|f A - f B| ≤ L ‖A - B‖_F`: matrices carry no global metric in this library, and the singular
values satisfy exactly this inequality (`NLAlib.abs_singularValues_sub_le_frobNorm`). The proof
reads the matrix as a standard Gaussian vector indexed by `m × n`.

## Main results

* `NLAlib.hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix`.
* `NLAlib.measureReal_integral_add_le_of_hasLaw_gaussianMatrix`: the upper tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ} {f : Matrix m n ℝ → ℝ} {L : ℝ≥0}

/-- A Frobenius-Lipschitz function of a Gaussian matrix is integrable. -/
theorem integrable_comp_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    (hf : ∀ A B, |f A - f B| ≤ L * frobNorm (A - B)) : Integrable (fun ω => f (X ω)) μ := by
  sorry

/-- **Gaussian concentration** for a function of a Gaussian matrix that is `L`-Lipschitz for the
Frobenius distance: `f (G) - E f (G)` is sub-Gaussian with proxy `L²`. -/
theorem hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (hf : ∀ A B, |f A - f B| ≤ L * frobNorm (A - B)) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) (L ^ 2) μ := by
  sorry

/-- The upper tail: `P(E f(G) + t ≤ f(G)) ≤ exp (-t² / (2L²))`. -/
theorem measureReal_integral_add_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (hf : ∀ A B, |f A - f B| ≤ L * frobNorm (A - B))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∫ ω', f (X ω') ∂μ + t ≤ f (X ω)} ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
  sorry

end NLAlib
