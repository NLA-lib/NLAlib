/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Structured.Kronecker
public import NLAlib.Probability.Isotropic
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# Second moments of random sketches

If the entries of a random matrix `X`, read as a vector indexed by `m × n`, are isotropic, then
`E ‖S X T‖_F² = ‖S‖_F² ‖T‖_F²` for fixed `S` and `T` (Halko, Martinsson and Tropp 2011,
Proposition 10.1, for a Gaussian `X`); the proof writes `S X T` as `(S ⊗ Tᵀ)` applied to the
entries and uses `E ‖A Y‖² = ‖A‖_F²` for an isotropic `Y`. The same holds when `S` and `T` are
random but independent of `X`: `E ‖S X T‖_F² = E [‖S‖_F² ‖T‖_F²]`, which is the conditioning step
of the randomized range finder's error bound; the two sides are integrable together.

The isotropic statements are over `𝕜` and are stated at the root (their subject is
`Function.uncurry X`, so P0's `IsIsotropic` dot notation would not apply); the Gaussian ones are
their corollaries over `ℝ`.

## Main results

* `NLAlib.integral_frobNorm_mul_mul_sq_of_isIsotropic`.
* `NLAlib.integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix`.
* `NLAlib.integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun`,
  `NLAlib.integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun`.
* `NLAlib.integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Kronecker

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n a b : Type*} [Fintype m] [Fintype n] [Fintype a] [Fintype b]

section Isotropic

omit [Fintype a] [Fintype b] in
private theorem uncurry_mul_mul (S : Matrix a m 𝕜) (X : Matrix m n 𝕜) (T : Matrix n b 𝕜) :
    Function.uncurry (S * X * T) = (S ⊗ₖ Tᵀ) *ᵥ Function.uncurry X := by
  ext ⟨i, j⟩
  change (S * X * T) i j = ∑ x : m × n, (S ⊗ₖ Tᵀ) (i, j) x * X x.1 x.2
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

private theorem frobNorm_mul_mul_eq (S : Matrix a m 𝕜) (X : Matrix m n 𝕜) (T : Matrix n b 𝕜) :
    frobNorm (S * X * T) = ‖WithLp.toLp 2 ((S ⊗ₖ Tᵀ) *ᵥ Function.uncurry X)‖ := by
  rw [frobNorm_eq_norm_toLp_uncurry, uncurry_mul_mul]

variable [DecidableEq m] [DecidableEq n] {X : Ω → Matrix m n 𝕜}

/-- The squared Frobenius norm of a sketch with isotropic entries is integrable. -/
theorem integrable_frobNorm_mul_mul_sq_of_isIsotropic
    (hX : IsIsotropic (fun ω => Function.uncurry (X ω)) μ) (S : Matrix a m 𝕜) (T : Matrix n b 𝕜) :
    Integrable (fun ω => frobNorm (S * X ω * T) ^ 2) μ := by
  simp only [frobNorm_mul_mul_eq]
  exact hX.integrable_norm_mulVec_sq _

/-- **The second moment of a sketch with isotropic entries**: `E ‖S X T‖_F² = ‖S‖_F² ‖T‖_F²`. -/
theorem integral_frobNorm_mul_mul_sq_of_isIsotropic
    (hX : IsIsotropic (fun ω => Function.uncurry (X ω)) μ) (S : Matrix a m 𝕜) (T : Matrix n b 𝕜) :
    ∫ ω, frobNorm (S * X ω * T) ^ 2 ∂μ = frobNorm S ^ 2 * frobNorm T ^ 2 := by
  simp only [frobNorm_mul_mul_eq]
  rw [hX.integral_norm_mulVec_sq, frobNorm_kronecker, frobNorm_transpose, mul_pow]

variable [IsProbabilityMeasure μ] {ν : Measure (Matrix m n 𝕜)} {α : Type*} [MeasurableSpace α]
  {Y : Ω → α} {S : α → Matrix a m 𝕜} {T : α → Matrix n b 𝕜}

omit [DecidableEq m] [DecidableEq n] [IsProbabilityMeasure μ] in
private theorem measurable_frobNorm_mul_mul_sq (hS : Measurable S) (hT : Measurable T) :
    Measurable fun q : α × Matrix m n 𝕜 => frobNorm (S q.1 * q.2 * T q.1) ^ 2 :=
  (continuous_frobNorm.measurable.comp
    (((hS.comp measurable_fst).matrix_mul measurable_snd).matrix_mul
      (hT.comp measurable_fst))).pow_const 2

omit [DecidableEq m] [DecidableEq n] [IsProbabilityMeasure μ] in
private theorem measurable_frobNorm_sq_mul_frobNorm_sq (hS : Measurable S) (hT : Measurable T) :
    Measurable fun y => frobNorm (S y) ^ 2 * frobNorm (T y) ^ 2 :=
  ((continuous_frobNorm.measurable.comp hS).pow_const 2).mul
    ((continuous_frobNorm.measurable.comp hT).pow_const 2)

private theorem lintegral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun (hX : HasLaw X ν μ)
    (hν : IsIsotropic (fun x : Matrix m n 𝕜 => Function.uncurry x) ν) (hY : AEMeasurable Y μ)
    (hXY : IndepFun Y X μ) (hS : Measurable S) (hT : Measurable T) :
    ∫⁻ ω, ENNReal.ofReal (frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) ∂μ := by
  have : IsProbabilityMeasure ν := hX.isProbabilityMeasure_iff.1 inferInstance
  have hF := ENNReal.measurable_ofReal.comp (measurable_frobNorm_mul_mul_sq hS hT)
  have hG := ENNReal.measurable_ofReal.comp (measurable_frobNorm_sq_mul_frobNorm_sq hS hT)
  have hmap : μ.map (fun ω => (Y ω, X ω)) = (μ.map Y).prod ν := by
    rw [← hX.map_eq]
    exact (indepFun_iff_map_prod_eq_prod_map_map hY hX.aemeasurable).1 hXY
  have hinner (y : α) : ∫⁻ x, ENNReal.ofReal (frobNorm (S y * x * T y) ^ 2) ∂ν =
      ENNReal.ofReal (frobNorm (S y) ^ 2 * frobNorm (T y) ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_frobNorm_mul_mul_sq_of_isIsotropic (X := fun x => x) hν (S y) (T y))
      (ae_of_all _ fun _ => sq_nonneg _),
      integral_frobNorm_mul_mul_sq_of_isIsotropic (X := fun x => x) hν]
  calc ∫⁻ ω, ENNReal.ofReal (frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) ∂μ
      = ∫⁻ q, ENNReal.ofReal (frobNorm (S q.1 * q.2 * T q.1) ^ 2) ∂(μ.map fun ω => (Y ω, X ω)) :=
        (lintegral_map' hF.aemeasurable (hY.prodMk hX.aemeasurable)).symm
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (frobNorm (S y * x * T y) ^ 2) ∂ν ∂(μ.map Y) := by
        rw [hmap, lintegral_prod
          (fun q : α × Matrix m n 𝕜 => ENNReal.ofReal (frobNorm (S q.1 * q.2 * T q.1) ^ 2))
          hF.aemeasurable]
    _ = ∫⁻ y, ENNReal.ofReal (frobNorm (S y) ^ 2 * frobNorm (T y) ^ 2) ∂(μ.map Y) := by
        simp only [hinner]
    _ = ∫⁻ ω, ENNReal.ofReal (frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) ∂μ :=
        lintegral_map' hG.aemeasurable hY

/-- **The second moment with independent random factors**: if `X` has an isotropic law and is
independent of `Y`, then `E ‖S(Y) X T(Y)‖_F² = E [‖S(Y)‖_F² ‖T(Y)‖_F²]`. A consumer with random
factors `S T : Ω → Matrix` takes `Y := fun ω => (S ω, T ω)`. The identity holds as stated even
when the right side is not integrable (both sides are then `0`); integrability transfers by
`integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun`. -/
theorem integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun (hX : HasLaw X ν μ)
    (hν : IsIsotropic (fun x : Matrix m n 𝕜 => Function.uncurry x) ν) (hY : AEMeasurable Y μ)
    (hXY : IndepFun Y X μ) (hS : Measurable S) (hT : Measurable T) :
    ∫ ω, frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2 ∂μ =
      ∫ ω, frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2 ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      ((measurable_frobNorm_mul_mul_sq hS hT).comp_aemeasurable
        (hY.prodMk hX.aemeasurable)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      ((measurable_frobNorm_sq_mul_frobNorm_sq hS hT).comp_aemeasurable hY).aestronglyMeasurable,
    lintegral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun hX hν hY hXY hS hT]

/-- The two sides of `integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun` are integrable
together. -/
theorem integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun (hX : HasLaw X ν μ)
    (hν : IsIsotropic (fun x : Matrix m n 𝕜 => Function.uncurry x) ν) (hY : AEMeasurable Y μ)
    (hXY : IndepFun Y X μ) (hS : Measurable S) (hT : Measurable T) :
    Integrable (fun ω => frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) μ ↔
      Integrable (fun ω => frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) μ := by
  have hL : AEStronglyMeasurable (fun ω => frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) μ :=
    ((measurable_frobNorm_mul_mul_sq hS hT).comp_aemeasurable
      (hY.prodMk hX.aemeasurable)).aestronglyMeasurable
  have hR : AEStronglyMeasurable (fun ω => frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) μ :=
    ((measurable_frobNorm_sq_mul_frobNorm_sq hS hT).comp_aemeasurable hY).aestronglyMeasurable
  rw [Integrable, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _),
    hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    lintegral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun hX hν hY hXY hS hT]
  simp only [hL, hR, true_and]

end Isotropic

section Gaussian

variable {X : Ω → Matrix m n ℝ}

/-- **The second moment of a Gaussian sketch** (Halko, Martinsson and Tropp 2011,
Proposition 10.1): `E ‖S G T‖_F² = ‖S‖_F² ‖T‖_F²`. -/
theorem integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, frobNorm (S * X ω * T) ^ 2 ∂μ = frobNorm S ^ 2 * frobNorm T ^ 2 := by
  classical
  exact integral_frobNorm_mul_mul_sq_of_isIsotropic
    (isIsotropic_of_hasLaw_gaussianVector (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)) S T

variable {α : Type*} [MeasurableSpace α] {Y : Ω → α} {S : α → Matrix a m ℝ}
  {T : α → Matrix n b ℝ}

private theorem isIsotropic_uncurry_gaussianMatrix [DecidableEq m] [DecidableEq n] :
    IsIsotropic (fun x : Matrix m n ℝ => Function.uncurry x) (gaussianMatrix m n) :=
  isIsotropic_of_hasLaw_gaussianVector
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix m n)))

/-- The second moment of a Gaussian sketch with independent random factors. -/
theorem integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun
    (hX : HasLaw X (gaussianMatrix m n) μ) (hY : AEMeasurable Y μ) (hXY : IndepFun Y X μ)
    (hS : Measurable S) (hT : Measurable T) :
    ∫ ω, frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2 ∂μ =
      ∫ ω, frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2 ∂μ := by
  classical
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  exact integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun hX
    isIsotropic_uncurry_gaussianMatrix hY hXY hS hT

/-- The two sides are integrable together, for a Gaussian sketch. -/
theorem integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun
    (hX : HasLaw X (gaussianMatrix m n) μ) (hY : AEMeasurable Y μ) (hXY : IndepFun Y X μ)
    (hS : Measurable S) (hT : Measurable T) :
    Integrable (fun ω => frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) μ ↔
      Integrable (fun ω => frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) μ := by
  classical
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  exact integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun hX
    isIsotropic_uncurry_gaussianMatrix hY hXY hS hT

end Gaussian

end NLAlib
