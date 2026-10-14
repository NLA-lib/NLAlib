/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.SingularValueInequalities
public import NLAlib.Probability.Distributions.ChiSquareMoments
public import NLAlib.RandomMatrix.Gaussian.SpectralNorm

/-!
# Extreme singular values of Gaussian matrices

For a standard Gaussian matrix `G : m × n` (`N = card m` rows, `n = card n` columns): Gordon's
lower bound `√N - √n ≤ E σ_min(G)` (the upper bound `E ‖G‖ ≤ √N + √n` is in
`NLAlib/RandomMatrix/Gaussian/SpectralNorm.lean`), Gaussian concentration of every singular value
with proxy `1`, the deviation tails `P(√N + √n + t ≤ ‖G‖) ≤ e^{-t²/2}` and
`P(σ_min(G) ≤ √N - √n - t) ≤ e^{-t²/2}`, and the same conclusions as Loewner bounds on `Gᴴ G`,
the shape of the subspace-embedding predicate.

The smallest singular value of a matrix with `n` columns is `singularValues (X ω) k` with
`k + 1 = card n`. When `n > N` it is the padding `0` and `√N - √n < 0`, so the lower bounds hold
trivially and no tallness hypothesis is stated; the lower Loewner forms carry the hypothesis
`t ≤ √N - √n` that makes the squared base meaningful.

Gordon's lower bound compares, over nets of the unit spheres, the process `⟨g, u⟩ + ⟨h, v⟩`
(the `X` side of `NLAlib.integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw`) with
`⟨v, G u⟩` (its `Y` side), and uses
`NLAlib.le_integral_norm_sub_integral_norm_of_hasLaw_gaussianVector`.

## Main results

* `NLAlib.le_integral_singularValues_of_hasLaw_gaussianMatrix`: `√N - √n ≤ E σ_min(G)`.
* `NLAlib.hasSubgaussianMGF_singularValues_sub_integral_of_hasLaw_gaussianMatrix`.
* `NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix`: the deviation tails.
* The Gaussian Gram sandwich, with its one-sided forms (in namespace `NLAlib`):
  `measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- Every singular value of a standard Gaussian matrix is integrable. -/
theorem integrable_singularValues_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    (k : ℕ) : Integrable (fun ω => singularValues (X ω) k) μ := by
  sorry

/-- **Gordon's lower bound**: `√N - √n ≤ E σ_min(G)` for a standard Gaussian matrix `G : N × n`,
`σ_min` the singular value of index `k` with `k + 1 = n`.
[Vershynin2018, Exercise 7.3.4]; [DavidsonSzarek2001, Theorem II.13]; no tallness hypothesis
(for `n > N` the left side is negative and `σ_k` is the padding `0`). The upper bound is
`NLAlib.integral_specNorm_le_of_hasLaw_gaussianMatrix`.
Result: gaussian-matrix-extreme-singular-values -/
theorem le_integral_singularValues_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {k : ℕ} (hk : k + 1 = Fintype.card n) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) ≤ ∫ ω, singularValues (X ω) k ∂μ := by
  sorry

/-- Every singular value of a standard Gaussian matrix is sub-Gaussian about its mean with
proxy `1`: Gaussian concentration (`NLAlib.hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix`)
with the Frobenius-Lipschitz bound `NLAlib.abs_singularValues_sub_le_frobNorm`.
[Vershynin2018, proof of Corollary 7.3.3]. -/
theorem hasSubgaussianMGF_singularValues_sub_integral_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (k : ℕ) :
    HasSubgaussianMGF (fun ω => singularValues (X ω) k - ∫ ω', singularValues (X ω') k ∂μ) 1
      μ := by
  sorry

/-- The upper deviation tail of the spectral norm: `P(√N + √n + t ≤ ‖G‖) ≤ e^{-t²/2}` for
`t ≥ 0`. [Vershynin2018, Corollary 7.3.3]; one-sided, hence without the factor `2` of the
source's two-sided form. -/
theorem measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t ≤ specNorm (X ω)} ≤
      Real.exp (-t ^ 2 / 2) := by
  sorry

/-- The lower deviation tail of the smallest singular value:
`P(σ_min(G) ≤ √N - √n - t) ≤ e^{-t²/2}` for `t ≥ 0`. [Vershynin2018, Corollary 7.3.3];
one-sided, hence without the factor `2` of the source's two-sided form. -/
theorem measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {k : ℕ} (hk : k + 1 = Fintype.card n) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | singularValues (X ω) k ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t} ≤
      Real.exp (-t ^ 2 / 2) := by
  sorry

variable [DecidableEq n]

/-- The upper Gram bound: `Gᴴ G ≤ (√N + √n + t)² • 1` outside probability `e^{-t²/2}`, for
`t ≥ 0`. [Vershynin2018, Corollary 7.3.3], one-sided and in Loewner form. -/
theorem measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ¬ (X ω)ᴴ * X ω ≤
      (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ^ 2 • (1 : Matrix n n ℝ)} ≤
      Real.exp (-t ^ 2 / 2) := by
  sorry

/-- The lower Gram bound: `(√N - √n - t)² • 1 ≤ Gᴴ G` outside probability `e^{-t²/2}`, for
`0 ≤ t ≤ √N - √n` (the base must be nonnegative, or squaring it would make the bound false).
[Vershynin2018, Corollary 7.3.3], one-sided and in Loewner form. -/
theorem measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t) ^ 2 •
      (1 : Matrix n n ℝ) ≤ (X ω)ᴴ * X ω} ≤ Real.exp (-t ^ 2 / 2) := by
  sorry

/-- **The Gaussian Gram sandwich**: `(√N - √n - t)² • 1 ≤ Gᴴ G ≤ (√N + √n + t)² • 1` outside
probability `2 e^{-t²/2}`, for `0 ≤ t ≤ √N - √n`; the shape of the subspace-embedding predicate.
[Vershynin2018, Corollary 7.3.3], in Loewner form. -/
theorem
measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ)) :
    μ.real {ω | ¬ ((√(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) - t) ^ 2 •
      (1 : Matrix n n ℝ) ≤ (X ω)ᴴ * X ω ∧ (X ω)ᴴ * X ω ≤
      (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ^ 2 • (1 : Matrix n n ℝ))} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  sorry

end NLAlib
