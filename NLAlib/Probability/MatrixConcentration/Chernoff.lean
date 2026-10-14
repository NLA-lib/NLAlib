/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.MGFBound

/-!
# The matrix Chernoff inequalities: the trace form

A random positive semidefinite matrix `0 ≤ X ≤ L • 1` has the matrix MGF bound
`E exp (θ X) ≤ exp ((e^{θL} - 1)/L • E X)` (Tropp 2015, Lemma 5.4.1). The Chernoff tails follow
from the trace form of such a bound alone: if `E tr exp (θ Y) ≤ tr exp ((e^{θL} - 1)/L • V)` for
every `θ > 0` (resp. `θ < 0`), with `V` positive semidefinite, then the largest (resp. smallest)
eigenvalue of `Y` has the Chernoff upper (resp. lower) tail relative to that of `V`. Sums of
independent bounded positive semidefinite matrices are the main instance
(`NLAlib/Probability/MatrixConcentration/ChernoffSum.lean`); sampling without replacement is
another, which is why the tails are stated from the trace bound.

## Main results

* `NLAlib.hasMatrixMGFBound_of_posSemidef_of_le`: the Chernoff MGF bound.
* `NLAlib.measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le`,
  `NLAlib.measureReal_eigenvalue_le_le_chernoff_of_integral_le`: the tails, source form.
* `NLAlib.measureReal_eigenvalue_zero_ge_le_card_mul_exp_of_integral_le`,
  `NLAlib.measureReal_eigenvalue_le_le_card_mul_exp_of_integral_le`: the simplified forms.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The Chernoff matrix MGF bound** ([Tropp2015], Lemma 5.4.1): a random matrix with
`0 ≤ X ≤ L • 1` almost surely has `E exp (θ X) ≤ exp ((e^{θL} - 1)/L • E X)` for every `θ`. -/
theorem hasMatrixMGFBound_of_posSemidef_of_le {X : Ω → Matrix n n 𝕜} (hXm : AEMeasurable X μ)
    {L : ℝ} (hL : 0 < L) (hpsd : ∀ᵐ ω ∂μ, (X ω).PosSemidef)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) :
    HasMatrixMGFBound X (fun θ => (Real.exp (θ * L) - 1) / L) (∫ ω, X ω ∂μ) Set.univ μ := by
  sorry

variable {Y : Ω → Matrix n n 𝕜} {V : Matrix n n 𝕜} {L : ℝ}

/-- **The matrix Chernoff upper tail** from a trace bound ([Tropp2015], Theorem 5.1.1):
`P((1 + δ) λ_max V ≤ λ_max Y) ≤ d (e^δ / (1 + δ)^{1+δ})^{λ_max V / L}`. -/
theorem measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le [Nonempty n]
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hV : V.PosSemidef) (hL : 0 < L)
    (hint : ∀ θ, 0 < θ → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ, 0 < θ → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue V 0 ≤ eigenvalue (Y ω) 0} ≤
      Fintype.card n * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue V 0 / L) := by
  sorry

/-- **The matrix Chernoff lower tail** from a trace bound ([Tropp2015], Theorem 5.1.1):
`P(λ_min Y ≤ (1 - δ) λ_min V) ≤ d (e^{-δ} / (1 - δ)^{1-δ})^{λ_min V / L}` for `0 ≤ δ < 1`. -/
theorem measureReal_eigenvalue_le_le_chernoff_of_integral_le (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    (hV : V.PosSemidef) (hL : 0 < L) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (hint : ∀ θ, θ < 0 → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ, θ < 0 → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (Y ω) k ≤ (1 - δ) * eigenvalue V k} ≤
      Fintype.card n * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (eigenvalue V k / L) := by
  sorry

/-- The simplified Chernoff upper tail from a trace bound, `≤ d e^{-δ² λ_max V / (3L)}` for
`0 ≤ δ ≤ 1`; weaker than the source form in every regime and proved from it. -/
theorem measureReal_eigenvalue_zero_ge_le_card_mul_exp_of_integral_le [Nonempty n]
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hV : V.PosSemidef) (hL : 0 < L)
    (hint : ∀ θ, 0 < θ → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ, 0 < θ → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    μ.real {ω | (1 + δ) * eigenvalue V 0 ≤ eigenvalue (Y ω) 0} ≤
      Fintype.card n * Real.exp (-δ ^ 2 * eigenvalue V 0 / (3 * L)) := by
  sorry

/-- The simplified Chernoff lower tail from a trace bound, `≤ d e^{-δ² λ_min V / (2L)}` for
`0 ≤ δ < 1`; weaker than the source form in every regime and proved from it. -/
theorem measureReal_eigenvalue_le_le_card_mul_exp_of_integral_le
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hV : V.PosSemidef) (hL : 0 < L) {k : ℕ}
    (hk : k + 1 = Fintype.card n)
    (hint : ∀ θ, θ < 0 → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ, θ < 0 → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (Y ω) k ≤ (1 - δ) * eigenvalue V k} ≤
      Fintype.card n * Real.exp (-δ ^ 2 * eigenvalue V k / (2 * L)) := by
  sorry

end NLAlib
