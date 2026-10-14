/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.InverseMoments
public import NLAlib.RandomMatrix.Gaussian.Moments
public import NLAlib.RandomMatrix.Gaussian.SpectralNorm

/-!
# The block bound of the randomized range finder

For a standard Gaussian test matrix `G : n × k`, orthogonal frames `V₁ : n × r`, `V₂ : n × s`
(`V₁ᴴ V₂ = 0`) and a fixed `S`, the blocks `G₁ = V₁ᴴ G` and `G₂ = V₂ᴴ G` are independent standard
Gaussian matrices, and `E ‖S G₂ G₁†‖_F² = ‖S‖_F² r / (k - r - 1)` (Halko, Martinsson and Tropp
2011, proof of Theorem 10.5). The spectral-norm analogue (their Theorem 10.6) is Chevet's
inequality with factors independent of the Gaussian matrix
(`NLAlib.integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun`) applied with
`T = G₁†`, followed by the moments of `G₁†`:
`E ‖S G₂ G₁†‖ ≤ ‖S‖ E ‖G₁†‖_F + ‖S‖_F E ‖G₁†‖`.

## Main results

* `NLAlib.integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix`: the spectral block bound;
  `NLAlib.integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`:
  the form of Halko, Martinsson and Tropp.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k r s a : Type*} [Fintype n]
  [Fintype k] [Fintype r] [Fintype s] [Fintype a] {X : Ω → Matrix n k ℝ}

/-- The squared norm in the range finder's block bound is integrable. -/
theorem integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    Integrable (fun ω => frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2) μ := by
  sorry

/-- **The range finder's block bound** (Halko, Martinsson and Tropp 2011, proof of
Theorem 10.5): `E ‖S (V₂ᴴ G) (V₁ᴴ G)†‖_F² = ‖S‖_F² r / (k - r - 1)`. -/
theorem integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2 ∂μ =
      frobNorm S ^ 2 * Fintype.card r / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  sorry

/-- The spectral norm in the range finder's block bound is integrable. -/
theorem integrable_specNorm_mul_mul_pinv_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    Integrable (fun ω => specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω))) μ := by
  sorry

/-- **The range finder's spectral block bound**: `E ‖S G₂ G₁†‖ ≤ ‖S‖ E ‖G₁†‖_F + ‖S‖_F E ‖G₁†‖`
with the moments of `G₁†`, that is
`E ‖S (V₂ᴴ G) (V₁ᴴ G)†‖ ≤ ‖S‖ √(r / (k - r - 1)) + ‖S‖_F e √((k + r - 1)/2) / (k - r)`.
[HalkoMartinssonTropp2011, proof of Theorem 10.6], there with `e √k / (k - r)` in the second term;
`NLAlib.integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`
is that form. -/
theorem integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ∂μ ≤
      specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
        frobNorm S * (Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
          √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2)) := by
  sorry

/-- The spectral block bound in the form of Halko, Martinsson and Tropp,
`E ‖S (V₂ᴴ G) (V₁ᴴ G)†‖ ≤ ‖S‖ √(r / (k - r - 1)) + ‖S‖_F e √k / (k - r)`.
[HalkoMartinssonTropp2011, Theorem 10.6]. It is dominated by
`NLAlib.integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix` and proved from it; it keeps
a name spelling its right side, as its moment bound
`NLAlib.integral_specNorm_pinv_le_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix` does, because
the range finder cites it (R4 §7 Q1, `docs/design/RandomMatrix-R4.md`). -/
theorem integral_specNorm_mul_mul_pinv_le_add_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix
    [DecidableEq r] [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ∂μ ≤
      specNorm S * √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) +
        frobNorm S * (Real.exp 1 * √(Fintype.card k : ℝ) /
          ((Fintype.card k : ℝ) - Fintype.card r)) := by
  sorry

end NLAlib
