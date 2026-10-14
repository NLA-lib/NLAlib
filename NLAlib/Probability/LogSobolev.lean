/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import NLAlib.Probability.Entropy

/-!
# Logarithmic Sobolev inequalities and concentration

`NLAlib.HasLogSobolev ν c` says that the law `ν` on a Euclidean space satisfies a logarithmic
Sobolev inequality with constant `c`: `Ent_ν (g²) ≤ 2 c E_ν ‖∇g‖²` for every bounded `C¹` function
`g` with bounded derivative. The class of test functions keeps every integral finite. Herbst's
argument turns it into concentration: a Lipschitz function of a law with such an inequality is
sub-Gaussian about its mean with proxy `c L²`. The standard Gaussian satisfies it with `c = 1`
(`NLAlib.hasLogSobolev_stdGaussian`).

## Main definitions

* `NLAlib.HasLogSobolev ν c`.

## Main results

* `NLAlib.HasLogSobolev.integrable_of_lipschitzWith`.
* `NLAlib.HasLogSobolev.hasSubgaussianMGF_sub_integral`: concentration of Lipschitz functions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `ν` satisfies a logarithmic Sobolev inequality with constant `c`: for every bounded `C¹`
function `g` with bounded derivative, `Ent_ν (g²) ≤ 2 c E_ν ‖∇g‖²`. -/
structure HasLogSobolev (ν : Measure E) (c : ℝ≥0) : Prop where
  /-- The inequality, for bounded `C¹` test functions with bounded derivative. -/
  entropy_sq_le : ∀ g : E → ℝ, ContDiff ℝ 1 g → (∃ M, ∀ x, |g x| ≤ M) →
    (∃ M, ∀ x, ‖fderiv ℝ g x‖ ≤ M) →
    entropy ν (fun x => g x ^ 2) ≤ 2 * c * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν

variable {ν : Measure E} {c : ℝ≥0}

/-- A Lipschitz function is integrable for a law with a logarithmic Sobolev inequality. -/
theorem HasLogSobolev.integrable_of_lipschitzWith [IsProbabilityMeasure ν]
    (h : HasLogSobolev ν c) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable f ν := by
  sorry

/-- **Concentration from a logarithmic Sobolev inequality**: a Lipschitz function of a law with
a logarithmic Sobolev inequality with constant `c` is sub-Gaussian about its mean with proxy
`c L²` (Herbst's argument, after smoothing and truncating `f`). -/
theorem HasLogSobolev.hasSubgaussianMGF_sub_integral [IsProbabilityMeasure ν]
    (h : HasLogSobolev ν c) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂ν) (c * L ^ 2) ν := by
  sorry

end NLAlib
