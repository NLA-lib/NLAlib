/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.InverseMoments.Spectral
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
* `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix`: the transposed form.
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

omit [Fintype s] [Fintype a] in
private theorem hasLaw_conjTranspose_mul [DecidableEq r] (hX : HasLaw X (gaussianMatrix n k) μ)
    {V : Matrix n r ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => Vᴴ * X ω) (gaussianMatrix r k) μ :=
  hasLaw_const_mul_of_hasLaw_gaussianMatrix hX (by rwa [Matrix.conjTranspose_conjTranspose])

private theorem integrable_chevet_pinv [DecidableEq r] (hX : HasLaw X (gaussianMatrix n k) μ)
    {V₁ : Matrix n r ℝ} (hV₁ : HasOrthonormalCols V₁) (hrk : Fintype.card r + 2 ≤ Fintype.card k)
    (S : Matrix a s ℝ) :
    Integrable (fun ω => specNorm S * frobNorm (pinv (V₁ᴴ * X ω)) +
      frobNorm S * specNorm (pinv (V₁ᴴ * X ω))) μ := by
  have hY := hasLaw_conjTranspose_mul hX hV₁
  have hspec := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hY one_pos
    (q := 1) (by linarith [show (Fintype.card r : ℝ) + 2 ≤ Fintype.card k by exact_mod_cast hrk])
  simp only [Real.rpow_one] at hspec
  exact ((integrable_frobNorm_pinv_of_hasLaw_gaussianMatrix hY hrk).const_mul _).add
    (hspec.const_mul _)

/-- The squared norm in the range finder's block bound is integrable. -/
theorem integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    Integrable (fun ω => frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2) μ := by
  have hY := hasLaw_conjTranspose_mul hX hV₁
  refine (integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun
    (hasLaw_conjTranspose_mul hX hV₂) hY.aemeasurable
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv).2 ?_
  exact (integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hY hrk).const_mul _

/-- **The range finder's block bound** (Halko, Martinsson and Tropp 2011, proof of
Theorem 10.5): `E ‖S (V₂ᴴ G) (V₁ᴴ G)†‖_F² = ‖S‖_F² r / (k - r - 1)`. -/
theorem integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    ∫ ω, frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2 ∂μ =
      frobNorm S ^ 2 * Fintype.card r / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  have hY := hasLaw_conjTranspose_mul hX hV₁
  refine (integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun
    (hasLaw_conjTranspose_mul hX hV₂) hY.aemeasurable
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv).trans ?_
  rw [integral_const_mul, integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hY hrk, mul_div_assoc]

private theorem frobNorm_pinv_mul_mul_eq (A : Matrix n k ℝ) (V₁ : Matrix n r ℝ)
    (V₂ : Matrix n s ℝ) (S : Matrix s a ℝ) :
    frobNorm (pinv (Aᴴ * V₁) * (Aᴴ * V₂) * S) = frobNorm (Sᴴ * (V₂ᴴ * A) * pinv (V₁ᴴ * A)) := by
  rw [← frobNorm_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← pinv_conjTranspose,
    Matrix.mul_assoc]

/-- The squared norm in the transposed block bound is integrable. -/
theorem integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix s a ℝ) :
    Integrable (fun ω => frobNorm (pinv ((X ω)ᴴ * V₁) * ((X ω)ᴴ * V₂) * S) ^ 2) μ := by
  simp only [frobNorm_pinv_mul_mul_eq]
  exact integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk Sᴴ

/-- **The transposed block bound** (Halko, Martinsson and Tropp 2011, proof of Theorem 10.5,
conjugate-transposed): `E ‖(Gᴴ V₁)† (Gᴴ V₂) S‖_F² = ‖S‖_F² r / (k - r - 1)`. This is the form
the Nyström approximation's completion step uses. -/
theorem integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix s a ℝ) :
    ∫ ω, frobNorm (pinv ((X ω)ᴴ * V₁) * ((X ω)ᴴ * V₂) * S) ^ 2 ∂μ =
      frobNorm S ^ 2 * Fintype.card r / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  simp only [frobNorm_pinv_mul_mul_eq]
  rw [integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk Sᴴ,
    frobNorm_conjTranspose]

/-- The spectral norm in the range finder's block bound is integrable. -/
theorem integrable_specNorm_mul_mul_pinv_of_hasLaw_gaussianMatrix [DecidableEq r]
    [DecidableEq s] (hX : HasLaw X (gaussianMatrix n k) μ) {V₁ : Matrix n r ℝ}
    {V₂ : Matrix n s ℝ} (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (h₁₂ : V₁ᴴ * V₂ = 0) (hrk : Fintype.card r + 2 ≤ Fintype.card k) (S : Matrix a s ℝ) :
    Integrable (fun ω => specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω))) μ := by
  exact integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix_of_indepFun
    (hasLaw_conjTranspose_mul hX hV₁).aemeasurable (hasLaw_conjTranspose_mul hX hV₂)
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv (integrable_chevet_pinv hX hV₁ hrk S)

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
  have hY := hasLaw_conjTranspose_mul hX hV₁
  have hrk' : Fintype.card r < Fintype.card k := by omega
  refine (integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun hY.aemeasurable
    (hasLaw_conjTranspose_mul hX hV₂)
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂)
    (S := fun _ => S) measurable_const measurable_pinv
    (integrable_chevet_pinv hX hV₁ hrk S)).trans ?_
  have hspec := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hY one_pos
    (q := 1) (by linarith [show (Fintype.card r : ℝ) + 1 ≤ Fintype.card k by exact_mod_cast hrk'])
  simp only [Real.rpow_one] at hspec
  change ∫ ω, (specNorm S * frobNorm (pinv (V₁ᴴ * X ω)) +
    frobNorm S * specNorm (pinv (V₁ᴴ * X ω))) ∂μ ≤ _
  rw [integral_add ((integrable_frobNorm_pinv_of_hasLaw_gaussianMatrix hY hrk).const_mul _)
    (hspec.const_mul _), integral_const_mul, integral_const_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix hY hrk)
      (specNorm_nonneg _))
    (mul_le_mul_of_nonneg_left (integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix hY hrk')
      (frobNorm_nonneg _))

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
  have hrk' : (Fintype.card r : ℝ) + 2 ≤ Fintype.card k := by exact_mod_cast hrk
  refine (integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂ hrk S).trans ?_
  rw [div_mul_eq_mul_div]
  gcongr <;> linarith

end NLAlib
