/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import NLAlib.Probability.Distributions.Gaussian

/-!
# Real moments of the chi-square law

For a standard Gaussian vector `X` in `ℝⁿ` (`d = card n`), `‖X‖²` has the `χ²_d` law, and
`E (‖X‖²)^s = 2^s Γ(d/2 + s) / Γ(d/2)` for every real `s > -d/2`, the integrability threshold.
The negative moments are what the inverse moments of Gaussian matrices rest on; in particular
`E 1 / ‖X‖² = 1 / (d - 2)` for `d ≥ 3`. At `X = 0` (probability zero) `0 ^ s` is Lean's junk value
for `s < 0`; the integrals are unaffected.

## Main results

* `NLAlib.integral_norm_sq_rpow_of_hasLaw_gaussianVector`.
* `NLAlib.integral_norm_sq_inv_of_hasLaw_gaussianVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ}

/-- `(‖X‖²)^s` is integrable for a standard Gaussian vector exactly in the range `s > -d/2`. -/
theorem integrable_norm_sq_rpow_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {s : ℝ} (hs : -((Fintype.card n : ℝ) / 2) < s) :
    Integrable (fun ω => (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ s) μ := by
  sorry

/-- **The real moments of `χ²_d`**: `E (‖X‖²)^s = 2^s Γ(d/2 + s) / Γ(d/2)` for `s > -d/2`. -/
theorem integral_norm_sq_rpow_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {s : ℝ} (hs : -((Fintype.card n : ℝ) / 2) < s) :
    ∫ ω, (‖WithLp.toLp 2 (X ω)‖ ^ 2) ^ s ∂μ =
      2 ^ s * Real.Gamma ((Fintype.card n : ℝ) / 2 + s) / Real.Gamma ((Fintype.card n : ℝ) / 2) := by
  sorry

/-- `E 1 / χ²_d = 1 / (d - 2)` for `d ≥ 3`. -/
theorem integral_norm_sq_inv_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    (hn : 3 ≤ Fintype.card n) :
    ∫ ω, (‖WithLp.toLp 2 (X ω)‖ ^ 2)⁻¹ ∂μ = 1 / ((Fintype.card n : ℝ) - 2) := by
  sorry

end NLAlib
