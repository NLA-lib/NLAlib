/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Dilation
public import NLAlib.Probability.MatrixConcentration.MGFBound

/-!
# The matrix Bernstein inequality

For independent centred random Hermitian matrices with `X k ≤ L • 1` almost surely and variance
`v = ‖∑ E X k²‖`, `P(t ≤ λ_max (∑ X k)) ≤ d exp (-(t²/2) / (v + L t / 3))` and
`E λ_max (∑ X k) ≤ √(2 v log d) + L log d / 3` (Tropp 2015, Theorem 6.6.1). Rectangular summands go
through the dilation, with `v` the larger of the two variances and dimension `m + n`
(Tropp 2015, Theorem 6.1.1); for square Hermitian summands this is also the two-sided
Hermitian form. The `1 × 1` case is Bernstein's inequality for bounded centred real variables.

## Main results

* `NLAlib.hasMatrixMGFBound_of_integral_eq_zero_of_le`: the Bernstein matrix MGF bound.
* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein`,
  `NLAlib.integral_eigenvalue_zero_sum_le_bernstein`: Hermitian summands.
* `NLAlib.measureReal_specNorm_sum_ge_le_bernstein`, `NLAlib.integral_specNorm_sum_le_bernstein`:
  rectangular summands.
* `NLAlib.measureReal_sum_ge_le_bernstein`: the scalar Bernstein inequality.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {L : ℝ}

/-- **The Bernstein matrix MGF bound** ([Tropp2015], Lemma 6.6.2): a centred random matrix with
`X ≤ L • 1` almost surely has `E exp (θ X) ≤ exp (θ²/2 / (1 - Lθ/3) • E X²)` for `0 < θ < 3/L`. -/
theorem hasMatrixMGFBound_of_integral_eq_zero_of_le [IsProbabilityMeasure μ]
    {X : Ω → Matrix n n 𝕜} (hL : 0 < L) (hX2 : MemLp X 2 μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) :
    HasMatrixMGFBound X (fun θ => θ ^ 2 / 2 / (1 - L * θ / 3)) (∫ ω, X ω ^ 2 ∂μ)
      (Set.Ioo 0 (3 / L)) μ := by
  sorry

variable {ι : Type*} [Fintype ι]

section Hermitian

variable {X : ι → Ω → Matrix n n 𝕜}

/-- **Matrix Bernstein**, Hermitian summands ([Tropp2015], Theorem 6.6.1). -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein [Nonempty n] (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) /
        (specNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ) + L * t / 3)) := by
  sorry

/-- **Matrix Bernstein** for the mean, Hermitian summands ([Tropp2015], Theorem 6.6.1). -/
theorem integral_eigenvalue_zero_sum_le_bernstein [Nonempty n] (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      √(2 * specNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ) * Real.log (Fintype.card n)) +
        L * Real.log (Fintype.card n) / 3 := by
  sorry

end Hermitian

section Rectangular

variable {m : Type*} [Fintype m] [DecidableEq m] {S : ι → Ω → Matrix m n 𝕜}

/-- **Matrix Bernstein**, rectangular summands ([Tropp2015], Theorem 6.1.1), with variance
`v = max ‖∑ E S Sᴴ‖ ‖∑ E Sᴴ S‖`. For square Hermitian summands this is the two-sided form. -/
theorem measureReal_specNorm_sum_ge_le_bernstein [Nonempty m] [Nonempty n]
    (hind : iIndepFun S μ) (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ)
    (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0) (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, S k ω)} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-(t ^ 2 / 2) /
        (max (specNorm (∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ))
          (specNorm (∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ)) + L * t / 3)) := by
  sorry

/-- **Matrix Bernstein** for the mean, rectangular summands ([Tropp2015], Theorem 6.1.1). -/
theorem integral_specNorm_sum_le_bernstein [Nonempty m] [Nonempty n] (hind : iIndepFun S μ)
    (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) :
    ∫ ω, specNorm (∑ k, S k ω) ∂μ ≤
      √(2 * max (specNorm (∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ))
          (specNorm (∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ)) *
        Real.log (Fintype.card m + Fintype.card n)) +
      L * Real.log (Fintype.card m + Fintype.card n) / 3 := by
  sorry

end Rectangular

/-- **Bernstein's inequality** for bounded centred real variables, the `1 × 1` case of matrix
Bernstein: `P(t ≤ ∑ X k) ≤ exp (-(t²/2) / (∑ E X k² + L t / 3))`. -/
theorem measureReal_sum_ge_le_bernstein {X : ι → Ω → ℝ} (hind : iIndepFun X μ) (hL : 0 < L)
    (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ k, X k ω} ≤
      Real.exp (-(t ^ 2 / 2) / (∑ k, ∫ ω, X k ω ^ 2 ∂μ + L * t / 3)) := by
  sorry

end NLAlib
