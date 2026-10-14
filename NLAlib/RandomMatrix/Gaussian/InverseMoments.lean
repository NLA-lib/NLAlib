/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.RandomMatrix.Gaussian.Invariance

/-!
# Inverse moments of Gaussian matrices

For a wide standard Gaussian matrix `G : r × k` (`r < k`), the moments of `(G Gᴴ)⁻¹` and of the
pseudoinverse `G† = Gᴴ (G Gᴴ)⁻¹` that the randomized range finder consumes (Halko, Martinsson and
Tropp 2011, Propositions 10.2 to 10.4): `E (G Gᴴ)⁻¹ = (k - r - 1)⁻¹ • 1`,
`E ‖G†‖_F² = r / (k - r - 1)`, the fourth moment of `‖G†‖_F`, and
`E ‖G†‖^q ≤ (e √((k + r - 1)/2) / (k - r))^q` for `0 < q ≤ k - r`. The diagonal entries of
`(G Gᴴ)⁻¹` are reciprocals of `χ²_{k-r+1}` variables (Schur complement and rotation invariance);
the spectral bound goes through the laws of the probes `u ⬝ (G Gᴴ)⁻¹ u`. The spectral constant is
not from the literature: it is what this proof reaches, and it is at most the source's
`e √k / (k - r)`.

`(G Gᴴ)⁻¹` is Lean's `0` on the null set where `G` does not have full row rank, and `pinv` is
total; the integrals are unaffected.

## Main results

* `NLAlib.integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_pinv_le_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {r k : Type*} [Fintype r]
  [Fintype k] {X : Ω → Matrix r k ℝ}

/-- `(G Gᴴ)⁻¹` is integrable for a standard Gaussian `G : r × k` with `r + 2 ≤ k`. -/
theorem integrable_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix [DecidableEq r]
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹) μ := by
  sorry

/-- **The mean of the inverse Wishart matrix**: `E (G Gᴴ)⁻¹ = (k - r - 1)⁻¹ • 1` for `r + 2 ≤ k`. -/
theorem integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix [DecidableEq r]
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, (X ω * (X ω)ᴴ)⁻¹ ∂μ =
      ((Fintype.card k : ℝ) - Fintype.card r - 1)⁻¹ • (1 : Matrix r r ℝ) := by
  sorry

/-- `‖G†‖_F²` is integrable for `r + 2 ≤ k`. -/
theorem integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω)) ^ 2) μ := by
  sorry

/-- **`E ‖G†‖_F² = r / (k - r - 1)`** (Halko, Martinsson and Tropp, Proposition 10.2). -/
theorem integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ^ 2 ∂μ =
      (Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  sorry

/-- `‖G†‖_F` is integrable for `r + 2 ≤ k`. -/
theorem integrable_frobNorm_pinv_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω))) μ := by
  sorry

/-- `E ‖G†‖_F ≤ √(r / (k - r - 1))`, by Jensen. -/
theorem integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ∂μ ≤
      √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) := by
  sorry

/-- `‖G†‖_F⁴` is integrable for `r + 4 ≤ k`. -/
theorem integrable_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 4 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω)) ^ 4) μ := by
  sorry

/-- The fourth moment of `‖G†‖_F` (Halko, Martinsson and Tropp, Proposition 10.3):
`E ‖G†‖_F⁴ = (r² (k - r) - 2 r (r - 1)) / ((k - r) (k - r - 1) (k - r - 3))` for `r + 4 ≤ k`. -/
theorem integral_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 4 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ^ 4 ∂μ =
      ((Fintype.card r : ℝ) ^ 2 * ((Fintype.card k : ℝ) - Fintype.card r) -
          2 * Fintype.card r * ((Fintype.card r : ℝ) - 1)) /
        (((Fintype.card k : ℝ) - Fintype.card r) * ((Fintype.card k : ℝ) - Fintype.card r - 1) *
          ((Fintype.card k : ℝ) - Fintype.card r - 3)) := by
  sorry

/-- `‖G†‖^q` is integrable for `0 < q ≤ k - r`. -/
theorem integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ (Fintype.card k : ℝ) - Fintype.card r) :
    Integrable (fun ω => specNorm (pinv (X ω)) ^ q) μ := by
  sorry

/-- **The spectral moments of `G†`**: `E ‖G†‖^q ≤ (e √((k + r - 1)/2) / (k - r))^q` for
`0 < q ≤ k - r` (Halko, Martinsson and Tropp, Proposition 10.4, in a sharper form: the constant
`√((k + r - 1)/2)` in place of `√k` is what the proof by probes reaches). -/
theorem integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ (Fintype.card k : ℝ) - Fintype.card r) :
    ∫ ω, specNorm (pinv (X ω)) ^ q ∂μ ≤
      (Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
        √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2)) ^ q := by
  sorry

/-- `E ‖G†‖ ≤ e √((k + r - 1)/2) / (k - r)` for `r < k`: the case `q = 1`. -/
theorem integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r < Fintype.card k) :
    ∫ ω, specNorm (pinv (X ω)) ∂μ ≤
      Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
        √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2) := by
  sorry

/-- The form of Halko, Martinsson and Tropp (Proposition 10.2), `E ‖G†‖ ≤ e √k / (k - r)`;
weaker in every regime and proved from `integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix`. -/
theorem integral_specNorm_pinv_le_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r < Fintype.card k) :
    ∫ ω, specNorm (pinv (X ω)) ∂μ ≤
      Real.exp 1 * √(Fintype.card k : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r) := by
  sorry

end NLAlib
