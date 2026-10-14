/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.TraceFunctions
public import NLAlib.Probability.MatrixConcentration.Bernstein
public import NLAlib.Probability.MatrixConcentration.ChernoffSum
public import NLAlib.Probability.MatrixConcentration.LaplaceGeneral

/-!
# Matrix concentration in the intrinsic dimension

The matrix Chernoff and Bernstein inequalities with the ambient dimension `d` replaced by the
intrinsic dimension `intrinsicDimension V = tr V / ‖V‖ ≤ rank V` of a variance proxy `V` (Tropp
2015, chapter 7). The proxy is any deterministic `V` above the variance statistic in Loewner
order (`∑ E X k ≤ M` for Chernoff, `∑ E X k² ≤ V` for Bernstein), entering after the trace, so a
user trades `‖V‖` against `intrinsicDimension V`. The trace forms take a single random matrix with
a trace MGF bound, as `NLAlib/Probability/MatrixConcentration/Chernoff.lean` does; the
independent-sum forms are corollaries.

The bounds are better than the dimensional ones (`ChernoffSum.lean`, `Bernstein.lean`) when
`2 intdim M < d`, respectively `4 intdim V < d`, and the Bernstein tails hold only above the
threshold `t ≥ √‖V‖ + L / 3`.

## Main results

* `NLAlib.measureReal_eigenvalue_zero_ge_le_chernoff_intrinsicDim_of_integral_le`,
  `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_chernoff_intrinsicDim`,
  `NLAlib.integral_eigenvalue_zero_sum_le_chernoff_intrinsicDim`: intrinsic Chernoff.
* `NLAlib.measureReal_eigenvalue_zero_ge_le_bernstein_intrinsicDim_of_integral_le`,
  `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein_intrinsicDim`,
  `NLAlib.measureReal_specNorm_sum_ge_le_bernstein_intrinsicDim`: intrinsic Bernstein tails.
* `NLAlib.integral_eigenvalue_zero_sum_le_bernstein_intrinsicDim`,
  `NLAlib.integral_specNorm_sum_le_bernstein_intrinsicDim`: the means, with the constant
  `NLAlib.intrinsicBernsteinMeanConstant`.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι] {L : ℝ}

/-! ### Chernoff -/

section Chernoff

/-- **Intrinsic-dimension matrix Chernoff, trace form**: for an almost surely positive
semidefinite `Y` with `E tr exp (θ Y) ≤ tr exp ((e^{θL} - 1)/L • V)` for every `θ > 0`, a nonzero
positive semidefinite `V` and `δ ≥ L / λ_max V`,
`P((1 + δ) λ_max V ≤ λ_max Y) ≤ 2 intdim V (e^δ / (1 + δ)^{1+δ})^{λ_max V / L}`.
[Tropp2015, Theorem 7.2.1]; there for independent sums, here from the trace bound alone, so any
`Y` with that bound (sampling without replacement) gets the tail. `V ≠ 0` is needed: at `V = 0`
the event is everything and the bound `0`. -/
theorem measureReal_eigenvalue_zero_ge_le_chernoff_intrinsicDim_of_integral_le
    [IsProbabilityMeasure μ] {Y : Ω → Matrix n n 𝕜} {V : Matrix n n 𝕜}
    (hY : ∀ᵐ ω ∂μ, (Y ω).PosSemidef) (hV : V.PosSemidef) (hV0 : V ≠ 0) (hL : 0 < L)
    (hint : ∀ θ : ℝ, 0 < θ → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ : ℝ, 0 < θ → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace)
    {δ : ℝ} (hδ : L / eigenvalue V 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue V 0 ≤ eigenvalue (Y ω) 0} ≤
      2 * intrinsicDimension V * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue V 0 / L) := by
  sorry

variable {X : ι → Ω → Matrix n n 𝕜}

/-- **Intrinsic-dimension matrix Chernoff**: for independent random positive semidefinite
`0 ≤ X k ≤ L • 1`, a matrix `M ≠ 0` above `∑ E X k` and `δ ≥ L / λ_max M`,
`P((1 + δ) λ_max M ≤ λ_max (∑ X k)) ≤ 2 intdim M (e^δ / (1 + δ)^{1+δ})^{λ_max M / L}`.
[Tropp2015, Theorem 7.2.1]; here with any upper bound `M` in Loewner order in place of
`∑ E X k`. Better than `measureReal_eigenvalue_zero_sum_ge_le_chernoff` when
`2 intdim M < card n`, but only for `δ ≥ L / λ_max M`.
Result: intrinsic-matrix-chernoff -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff_intrinsicDim (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {M : Matrix n n 𝕜}
    (hM : ∑ k, ∫ ω, X k ω ∂μ ≤ M) (hM0 : M ≠ 0) {δ : ℝ} (hδ : L / eigenvalue M 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue M 0 ≤ eigenvalue (∑ k, X k ω) 0} ≤
      2 * intrinsicDimension M * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue M 0 / L) := by
  sorry

/-- **Intrinsic-dimension matrix Chernoff for the mean**: for independent random positive
semidefinite `0 ≤ X k ≤ L • 1`, a matrix `M` above `∑ E X k` and every `θ > 0`,
`E λ_max (∑ X k) ≤ (e^θ - 1)/θ · λ_max M + L/θ · log (2 intdim M)`.
[Tropp2015, Theorem 7.2.1]; here with any upper bound `M` in Loewner order and a free `θ`. No
`M ≠ 0`: at `M = 0` both sides are `0` (`Real.log 0 = 0`). Proof: for positive semidefinite `Y`,
`e^{s λ_max Y} - 1 ≤ tr (e^{s Y} - 1)`; Jensen; the trace bound at `s = θ / L` and monotonicity
after the trace; the intrinsic dimension lemma
(`Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul`); then
`1 + d (e^a - 1) ≤ 2 d e^a` from `Matrix.PosSemidef.one_le_intrinsicDimension` (case split on
`M = 0`).
Result: intrinsic-matrix-chernoff -/
theorem integral_eigenvalue_zero_sum_le_chernoff_intrinsicDim (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {M : Matrix n n 𝕜}
    (hM : ∑ k, ∫ ω, X k ω ∂μ ≤ M) {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      (Real.exp θ - 1) / θ * eigenvalue M 0 + L / θ * Real.log (2 * intrinsicDimension M) := by
  sorry

end Chernoff

/-! ### Bernstein -/

section Bernstein

/-- **Intrinsic-dimension matrix Bernstein, trace form**: for a centred, integrable, almost
surely Hermitian `Y` with `E tr exp (θ Y) ≤ tr exp (θ²/2/(1 - Lθ/3) • V)` for `θ ∈ (0, 3/L)`, a
positive semidefinite `V`, and `t ≥ √‖V‖ + L/3`,
`P(t ≤ λ_max Y) ≤ 4 intdim V exp (-(t²/2) / (‖V‖ + L t / 3))`.
[Tropp2015, Theorem 7.7.1]; here from the trace bound alone. No `V ≠ 0`: at `V = 0` the bound
`0` holds because `E tr (e^{θY} - θY - 1) ≤ 0` forces `Y = 0` almost surely. -/
theorem measureReal_eigenvalue_zero_ge_le_bernstein_intrinsicDim_of_integral_le
    [IsProbabilityMeasure μ] {Y : Ω → Matrix n n 𝕜} {V : Matrix n n 𝕜}
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hYi : Integrable Y μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (hV : V.PosSemidef) (hL : 0 < L)
    (hint : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) →
      Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • V)).trace)
    {t : ℝ} (ht : √(specNorm V) + L / 3 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤
      4 * intrinsicDimension V * Real.exp (-(t ^ 2 / 2) / (specNorm V + L * t / 3)) := by
  sorry

section Hermitian

variable {X : ι → Ω → Matrix n n 𝕜}

/-- **Intrinsic-dimension matrix Bernstein**, Hermitian summands: for independent centred
`X k ≤ L • 1` in `L²`, a matrix `V` above `∑ E X k²` and `t ≥ √‖V‖ + L/3`,
`P(t ≤ λ_max (∑ X k)) ≤ 4 intdim V exp (-(t²/2) / (‖V‖ + L t / 3))`.
[Tropp2015, Corollary 7.3.2; Theorem 7.7.1]; here with any upper bound `V` in Loewner order and a
one-sided bound on the summands. Better than `measureReal_eigenvalue_zero_sum_ge_le_bernstein`
when `4 intdim V < card n`, and only for `t` above the threshold.
Result: intrinsic-matrix-bernstein -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein_intrinsicDim (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {V : Matrix n n 𝕜}
    (hV : ∑ k, ∫ ω, X k ω ^ 2 ∂μ ≤ V) {t : ℝ} (ht : √(specNorm V) + L / 3 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      4 * intrinsicDimension V * Real.exp (-(t ^ 2 / 2) / (specNorm V + L * t / 3)) := by
  sorry

end Hermitian

section Rectangular

variable {m : Type*} [Fintype m] [DecidableEq m] {S : ι → Ω → Matrix m n 𝕜}

/-- **Intrinsic-dimension matrix Bernstein**, rectangular summands: for independent centred
`S k` in `L²` with `‖S k‖ ≤ L`, matrices `V₁ ≥ ∑ E S Sᴴ`, `V₂ ≥ ∑ E Sᴴ S`, `v = max ‖V₁‖ ‖V₂‖`
and `t ≥ √v + L/3`, `P(t ≤ ‖∑ S k‖) ≤ 4 intdim (V₁ ⊕ V₂) exp (-(t²/2) / (v + L t / 3))`.
[Tropp2015, Theorem 7.3.1]; through the Hermitian dilation, with any upper bounds `V₁`, `V₂`.
Better than `measureReal_specNorm_sum_ge_le_bernstein` when
`4 intdim (V₁ ⊕ V₂) < card m + card n`.
Result: intrinsic-matrix-bernstein -/
theorem measureReal_specNorm_sum_ge_le_bernstein_intrinsicDim (hind : iIndepFun S μ)
    (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) {V₁ : Matrix m m 𝕜} {V₂ : Matrix n n 𝕜}
    (hV₁ : ∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ ≤ V₁) (hV₂ : ∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ ≤ V₂)
    {t : ℝ} (ht : √(max (specNorm V₁) (specNorm V₂)) + L / 3 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, S k ω)} ≤
      4 * intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂) *
        Real.exp (-(t ^ 2 / 2) / (max (specNorm V₁) (specNorm V₂) + L * t / 3)) := by
  sorry

end Rectangular

/-- The absolute constant of the intrinsic-dimension Bernstein means. [Tropp2015, Theorem 7.3.1]
leaves it unspecified; the prototype's proof reached `20`, the value here. A smaller value is a
better bound. Use only `intrinsicBernsteinMeanConstant_pos` and
`intrinsicBernsteinMeanConstant_le`. -/
noncomputable irreducible_def intrinsicBernsteinMeanConstant : ℝ := 20

/-- The intrinsic Bernstein mean constant is positive. -/
theorem intrinsicBernsteinMeanConstant_pos : 0 < intrinsicBernsteinMeanConstant := by
  sorry

/-- An explicit upper bound on `intrinsicBernsteinMeanConstant`. -/
theorem intrinsicBernsteinMeanConstant_le : intrinsicBernsteinMeanConstant ≤ 20 := by
  sorry

section Hermitian

variable {X : ι → Ω → Matrix n n 𝕜}

/-- **Intrinsic-dimension matrix Bernstein for the mean**, Hermitian summands: for independent
centred `X k ≤ L • 1` in `L²` and a matrix `V` above `∑ E X k²`,
`E λ_max (∑ X k) ≤ C (√(‖V‖ log (1 + intdim V)) + L log (1 + intdim V))` with
`C = intrinsicBernsteinMeanConstant`. [Tropp2015, Corollary 7.3.2]; here with any upper bound `V`
in Loewner order. Better than `integral_eigenvalue_zero_sum_le_bernstein` when `intdim V` is
much smaller than `card n`; its constant is worse. Proof: integrate the tail above the
threshold.
Result: intrinsic-matrix-bernstein -/
theorem integral_eigenvalue_zero_sum_le_bernstein_intrinsicDim (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {V : Matrix n n 𝕜}
    (hV : ∑ k, ∫ ω, X k ω ^ 2 ∂μ ≤ V) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤ intrinsicBernsteinMeanConstant *
      (√(specNorm V * Real.log (1 + intrinsicDimension V)) +
        L * Real.log (1 + intrinsicDimension V)) := by
  sorry

end Hermitian

section Rectangular

variable {m : Type*} [Fintype m] [DecidableEq m] {S : ι → Ω → Matrix m n 𝕜}

/-- **Intrinsic-dimension matrix Bernstein for the mean**, rectangular summands: for independent
centred `S k` in `L²` with `‖S k‖ ≤ L` and matrices `V₁ ≥ ∑ E S Sᴴ`, `V₂ ≥ ∑ E Sᴴ S`, with
`v = max ‖V₁‖ ‖V₂‖` and `D = intdim (V₁ ⊕ V₂)`, `E ‖∑ S k‖ ≤ C (√(v log (1 + D)) + L log (1 + D))`
with `C = intrinsicBernsteinMeanConstant`. [Tropp2015, Theorem 7.3.1]; here with any upper
bounds `V₁`, `V₂`. Better than `integral_specNorm_sum_le_bernstein` when `D` is much smaller than
`card m + card n`.
Result: intrinsic-matrix-bernstein -/
theorem integral_specNorm_sum_le_bernstein_intrinsicDim (hind : iIndepFun S μ)
    (hL : 0 < L) (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) {V₁ : Matrix m m 𝕜} {V₂ : Matrix n n 𝕜}
    (hV₁ : ∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ ≤ V₁) (hV₂ : ∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ ≤ V₂) :
    ∫ ω, specNorm (∑ k, S k ω) ∂μ ≤ intrinsicBernsteinMeanConstant *
      (√(max (specNorm V₁) (specNorm V₂) *
          Real.log (1 + intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂))) +
        L * Real.log (1 + intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂))) := by
  sorry

end Rectangular

end Bernstein

end NLAlib
