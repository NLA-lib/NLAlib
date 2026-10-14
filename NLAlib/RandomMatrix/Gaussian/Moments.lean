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
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n a b : Type*} [Fintype m] [Fintype n] [Fintype a] [Fintype b]

section Isotropic

variable [DecidableEq m] [DecidableEq n] {X : Ω → Matrix m n 𝕜}

/-- The squared Frobenius norm of a sketch with isotropic entries is integrable. -/
theorem integrable_frobNorm_mul_mul_sq_of_isIsotropic
    (hX : IsIsotropic (fun ω => Function.uncurry (X ω)) μ) (S : Matrix a m 𝕜) (T : Matrix n b 𝕜) :
    Integrable (fun ω => frobNorm (S * X ω * T) ^ 2) μ := by
  sorry

/-- **The second moment of a sketch with isotropic entries**: `E ‖S X T‖_F² = ‖S‖_F² ‖T‖_F²`. -/
theorem integral_frobNorm_mul_mul_sq_of_isIsotropic
    (hX : IsIsotropic (fun ω => Function.uncurry (X ω)) μ) (S : Matrix a m 𝕜) (T : Matrix n b 𝕜) :
    ∫ ω, frobNorm (S * X ω * T) ^ 2 ∂μ = frobNorm S ^ 2 * frobNorm T ^ 2 := by
  sorry

variable [IsProbabilityMeasure μ] {ν : Measure (Matrix m n 𝕜)} {α : Type*} [MeasurableSpace α]
  {Y : Ω → α} {S : α → Matrix a m 𝕜} {T : α → Matrix n b 𝕜}

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
  sorry

/-- The two sides of `integral_frobNorm_mul_mul_sq_of_isIsotropic_of_indepFun` are integrable
together. -/
theorem integrable_frobNorm_mul_mul_sq_iff_of_isIsotropic_of_indepFun (hX : HasLaw X ν μ)
    (hν : IsIsotropic (fun x : Matrix m n 𝕜 => Function.uncurry x) ν) (hY : AEMeasurable Y μ)
    (hXY : IndepFun Y X μ) (hS : Measurable S) (hT : Measurable T) :
    Integrable (fun ω => frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) μ ↔
      Integrable (fun ω => frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) μ := by
  sorry

end Isotropic

section Gaussian

variable {X : Ω → Matrix m n ℝ}

/-- **The second moment of a Gaussian sketch** (Halko, Martinsson and Tropp 2011,
Proposition 10.1): `E ‖S G T‖_F² = ‖S‖_F² ‖T‖_F²`. -/
theorem integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, frobNorm (S * X ω * T) ^ 2 ∂μ = frobNorm S ^ 2 * frobNorm T ^ 2 := by
  sorry

variable {α : Type*} [MeasurableSpace α] {Y : Ω → α} {S : α → Matrix a m ℝ}
  {T : α → Matrix n b ℝ}

/-- The second moment of a Gaussian sketch with independent random factors. -/
theorem integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun
    (hX : HasLaw X (gaussianMatrix m n) μ) (hY : AEMeasurable Y μ) (hXY : IndepFun Y X μ)
    (hS : Measurable S) (hT : Measurable T) :
    ∫ ω, frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2 ∂μ =
      ∫ ω, frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2 ∂μ := by
  sorry

/-- The two sides are integrable together, for a Gaussian sketch. -/
theorem integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun
    (hX : HasLaw X (gaussianMatrix m n) μ) (hY : AEMeasurable Y μ) (hXY : IndepFun Y X μ)
    (hS : Measurable S) (hT : Measurable T) :
    Integrable (fun ω => frobNorm (S (Y ω) * X ω * T (Y ω)) ^ 2) μ ↔
      Integrable (fun ω => frobNorm (S (Y ω)) ^ 2 * frobNorm (T (Y ω)) ^ 2) μ := by
  sorry

end Gaussian

end NLAlib
