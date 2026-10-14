/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Net
public import NLAlib.Probability.Distributions.GaussianComparison
public import NLAlib.Probability.Isotropic
public import NLAlib.RandomMatrix.Gaussian.Concentration

/-!
# The spectral norm of Gaussian matrices: Chevet's inequality

For a standard Gaussian matrix `G : m × n` and fixed `S : a × m`, `T : n × b`, Chevet's inequality
`E ‖S G T‖ ≤ ‖S‖ ‖T‖_F + ‖S‖_F ‖T‖`, its form with random factors independent of `G`, the tail of
`‖S G T‖` above that bound, and Gordon's upper bound `E ‖G‖ ≤ √N + √n` (`N = card m`,
`n = card n`) as the case `S = 1`, `T = 1`. Real throughout: the Gaussian matrix law is real.

The proof of Chevet's inequality compares, over finite symmetric nets of the unit spheres, the
process `⟨u, S G T v⟩ = ⟨Sᴴ u, G (T v)⟩` with `‖Sᴴ u‖ ⟨g, T v⟩ + ‖T v‖ ⟨h, Sᴴ u⟩` (`g`, `h`
independent standard Gaussian vectors) through the Sudakov–Fernique inequality
(`NLAlib.integral_iSup_le_integral_iSup_of_hasGaussianLaw`), then bounds the comparison process
by `NLAlib.IsIsotropic.integral_norm_mulVec_le`.

## Main results

* `NLAlib.integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix`: Chevet's inequality.
* `NLAlib.integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun`: Chevet's inequality
  with random factors independent of the Gaussian matrix.
* `NLAlib.measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix`: the tail of `‖S G T‖`.
* `NLAlib.integral_specNorm_le_of_hasLaw_gaussianMatrix`: `E ‖G‖ ≤ √N + √n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n a b : Type*} [Fintype m]
  [Fintype n] [Fintype a] [Fintype b] {X : Ω → Matrix m n ℝ}

section Fixed

/-- `‖S G T‖` is integrable for a standard Gaussian matrix `G`. -/
theorem integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ)
    (S : Matrix a m ℝ) (T : Matrix n b ℝ) : Integrable (fun ω => specNorm (S * X ω * T)) μ := by
  sorry

/-- **Chevet's inequality**: for a standard Gaussian matrix `G` and fixed `S`, `T`,
`E ‖S G T‖ ≤ ‖S‖ ‖T‖_F + ‖S‖_F ‖T‖`.
[Vershynin2018, Theorem 8.7.1]; [HalkoMartinssonTropp2011, Proposition 10.1]; Vershynin states
it for a general bilinear supremum over two sets, here the matrix form of Halko, Martinsson and
Tropp, over any finite index types.
Result: chevet-inequality -/
theorem integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) :
    ∫ ω, specNorm (S * X ω * T) ∂μ ≤ specNorm S * frobNorm T + frobNorm S * specNorm T := by
  sorry

/-- The tail of `‖S G T‖` above Chevet's bound:
`P(‖S‖ ‖T‖_F + ‖S‖_F ‖T‖ + t ≤ ‖S G T‖) ≤ exp (-t² / (2 ‖S‖² ‖T‖²))` for `t ≥ 0`, by Gaussian
concentration (`NLAlib.measureReal_integral_add_le_of_hasLaw_gaussianMatrix`) with Lipschitz
constant `‖S‖ ‖T‖` and Chevet's inequality. [HalkoMartinssonTropp2011, proof of Theorem 10.8],
the deviation step of the range finder's spectral tail. If `S = 0` or `T = 0` the right side is
`exp 0 = 1` (Lean's `x / 0 = 0`). -/
theorem measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix m n) μ) (S : Matrix a m ℝ) (T : Matrix n b ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | specNorm S * frobNorm T + frobNorm S * specNorm T + t ≤
      specNorm (S * X ω * T)} ≤ Real.exp (-t ^ 2 / (2 * (specNorm S * specNorm T) ^ 2)) := by
  sorry

/-- `‖G‖` is integrable for a standard Gaussian matrix `G`. -/
theorem integrable_specNorm_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    Integrable (fun ω => specNorm (X ω)) μ := by
  sorry

/-- **Gordon's upper bound**: `E ‖G‖ ≤ √N + √n` for a standard Gaussian matrix `G : N × n`, the
case `S = 1`, `T = 1` of Chevet's inequality.
[Vershynin2018, Theorem 7.3.1]; [DavidsonSzarek2001, Theorem II.13]; the lower bound
`√N - √n ≤ E σ_min(G)` is `NLAlib.le_integral_singularValues_of_hasLaw_gaussianMatrix`.
Result: gaussian-matrix-extreme-singular-values -/
theorem integral_specNorm_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∫ ω, specNorm (X ω) ∂μ ≤ √(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) := by
  sorry

end Fixed

section Independent

variable {α : Type*} [MeasurableSpace α] {Y : Ω → α} {S : α → Matrix a m ℝ}
  {T : α → Matrix n b ℝ}

/-- `‖S G T‖` is integrable when the random factors `S`, `T` are functions of a variable `Y`
independent of the Gaussian matrix `G` and Chevet's bound for them is integrable. -/
theorem integrable_specNorm_mul_mul_of_hasLaw_gaussianMatrix_of_indepFun (hY : AEMeasurable Y μ)
    (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ) (hS : Measurable S)
    (hT : Measurable T)
    (hST : Integrable (fun ω => specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
      frobNorm (S (Y ω)) * specNorm (T (Y ω))) μ) :
    Integrable (fun ω => specNorm (S (Y ω) * X ω * T (Y ω))) μ := by
  sorry

/-- **Chevet's inequality with random factors** independent of the Gaussian matrix:
`E ‖S G T‖ ≤ E [‖S‖ ‖T‖_F + ‖S‖_F ‖T‖]` when `S`, `T` are functions of a variable `Y`
independent of `G`. [HalkoMartinssonTropp2011, proof of Theorem 10.6], where it is applied
conditionally on the independent block. The integrability hypothesis `hST` excludes the junk
value `0` of a non-integrable right side. -/
theorem integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix_of_indepFun (hY : AEMeasurable Y μ)
    (hX : HasLaw X (gaussianMatrix m n) μ) (hXY : IndepFun Y X μ) (hS : Measurable S)
    (hT : Measurable T)
    (hST : Integrable (fun ω => specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
      frobNorm (S (Y ω)) * specNorm (T (Y ω))) μ) :
    ∫ ω, specNorm (S (Y ω) * X ω * T (Y ω)) ∂μ ≤
      ∫ ω, (specNorm (S (Y ω)) * frobNorm (T (Y ω)) +
        frobNorm (S (Y ω)) * specNorm (T (Y ω))) ∂μ := by
  sorry

end Independent

end NLAlib
