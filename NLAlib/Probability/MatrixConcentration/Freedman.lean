/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import NLAlib.ForMathlib.Probability.Martingale.OptionalStopping
public import NLAlib.Probability.MatrixConcentration.ConditionalMGFBound

/-!
# Freedman's inequality for matrix martingales

For increments `X j` adapted to a filtration `ℱ` (`X j` is `ℱ (j + 1)`-measurable) with
conditional matrix MGF bounds `NLAlib.HasCondMatrixMGFBound (ℱ j) _ (X j) g (A j) s μ`, the trace
potential `tr exp (θ Yₖ - g θ Wₖ)`, with `Yₖ = ∑_{j<k} X j` and `Wₖ = ∑_{j<k} A j`, is a
supermartingale (conditional Lieb). Ville's maximal inequality for it is the martingale master
tail: the probability that for some `k` both `λ_max Yₖ ≥ t` and `Wₖ ≤ w • 1` is at most
`d e^{-θt + g θ w}`. With the conditional Bernstein bound this is Freedman's inequality: for
conditionally centred increments with `X j ≤ L • 1`, the probability that for some `k` both
`λ_max Yₖ ≥ t` and the predictable quadratic variation `‖∑_{j<k} E[X j² | ℱ j]‖ ≤ v` is at most
`d exp (-(t²/2) / (v + L t / 3))`. The sub-Gaussian bridge
`NLAlib.hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF` gives matrix Azuma-type tails from
the same master tail.

Index convention: the increments are `X j = Y (j + 1) - Y j` with `Y 0 = 0` (Tropp's), so the
partial sums are `∑ j ∈ Finset.range k, X j ω` and there is no special first term. Mathlib's
Azuma conditions `Y (i + 1)` on `ℱ i` and treats `Y 0` apart; the two agree under `X j =
Y (j + 1)`. A finite horizon `N` is the case `X j = 0` for `j ≥ N`.

## Main results

* `NLAlib.HasCondMatrixMGFBound.supermartingale_re_trace_exp`: the trace supermartingale.
* `NLAlib.HasCondMatrixMGFBound.measure_exists_eigenvalue_zero_sum_ge_le`: the martingale master
  tail.
* `NLAlib.measureReal_exists_eigenvalue_zero_sum_ge_le_freedman`: Freedman's inequality.
* `NLAlib.measureReal_exists_eigenvalue_zero_sum_ge_le_freedman_of_ae_le`: with an almost sure
  bound on the predictable quadratic variation (the martingale matrix Bernstein inequality).
* `NLAlib.measureReal_exists_specNorm_sum_ge_le_freedman`: rectangular increments.

## References

* [J. A. Tropp, *Freedman's inequality for matrix martingales*][Tropp2011].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {ℱ : Filtration ℕ mΩ}

namespace HasCondMatrixMGFBound

variable {X A : ℕ → Ω → Matrix n n 𝕜} {g : ℝ → ℝ} {s : Set ℝ}

/-- **The trace supermartingale**: for increments with conditional matrix MGF bounds, the
potential `tr exp (θ Yₖ - g θ Wₖ)`, with `Yₖ = ∑_{j<k} X j`, `Wₖ = ∑_{j<k} A j` and `θ ∈ s`, is
a supermartingale. Its integrability is a hypothesis here (it is derived in Freedman's
inequality from boundedness). [Tropp2011, §2].
Proof: adaptedness from `hX` and the `ℱ j`-measurability of `A j`. One step suffices
(`Supermartingale` from the one-step inequality and the tower property): with
`H = θ Yₖ - g θ W_{k+1}`, `ℱ k`-measurable because `A k` is,
`NLAlib.condExp_re_trace_exp_add_le` gives
`E[tr exp (H + θ X k) | ℱ k] ≤ tr exp (H + log E[exp (θ X k) | ℱ k])`; the bound
`E[exp (θ X k) | ℱ k] ≤ exp (g θ • A k)`, almost surely positive definite, and the operator
monotonicity of the logarithm give `log E[…] ≤ g θ • A k`; then monotonicity of `tr exp`
(`NLAlib.re_trace_exp_le_re_trace_exp_of_le`) returns `tr exp (θ Yₖ - g θ Wₖ)`. Medium. -/
theorem supermartingale_re_trace_exp (hX : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (h : ∀ j, HasCondMatrixMGFBound (ℱ j) (ℱ.le j) (X j) g (A j) s μ) {θ : ℝ} (hθ : θ ∈ s)
    (hint : ∀ k, Integrable (fun ω => RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω -
      g θ • ∑ j ∈ Finset.range k, A j ω)).trace) μ) :
    Supermartingale (fun k ω => RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω -
      g θ • ∑ j ∈ Finset.range k, A j ω)).trace) ℱ μ := by
  sorry

/-- **The martingale master tail**: for increments with conditional matrix MGF bounds,
`θ ∈ s`, `θ > 0` and `g θ ≥ 0`, the probability that for some `k` both `t ≤ λ_max Yₖ` and
`Wₖ ≤ w • 1` is at most `d e^{-θt + g θ w}`. [Tropp2011, §2]; the martingale form of
`NLAlib.HasMatrixMGFBound.measure_eigenvalue_zero_sum_ge_le_card_mul_exp`.
Proof: on the event the potential of `supermartingale_re_trace_exp` is at least
`e^{θt - g θ w}` (`θ Yₖ - g θ Wₖ ≥ θ Yₖ - g θ w • 1` since `g θ ≥ 0`, and
`tr exp M ≥ e^{λ_max M}`); Ville's inequality
(`MeasureTheory.Supermartingale.measure_exists_ge_le`) with the potential at `k = 0` equal to
`tr 1 = d`. Easy given the supermartingale. -/
theorem measure_exists_eigenvalue_zero_sum_ge_le [Nonempty n]
    (hX : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (h : ∀ j, HasCondMatrixMGFBound (ℱ j) (ℱ.le j) (X j) g (A j) s μ) {θ : ℝ} (hθs : θ ∈ s)
    (hθ : 0 < θ) (hg : 0 ≤ g θ)
    (hint : ∀ k, Integrable (fun ω => RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω -
      g θ • ∑ j ∈ Finset.range k, A j ω)).trace) μ) (t w : ℝ) :
    μ.real {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
        ∑ j ∈ Finset.range k, A j ω ≤ w • (1 : Matrix n n 𝕜)} ≤
      Fintype.card n * Real.exp (-θ * t + g θ * w) := by
  sorry

end HasCondMatrixMGFBound

/-- **Freedman's inequality for matrix martingales.** For increments `X j`, `ℱ (j + 1)`-measurable,
square-integrable, conditionally centred (`E[X j | ℱ j] = 0`) and with `X j ≤ L • 1` almost
surely, the probability that for some `k` both `t ≤ λ_max (∑_{j<k} X j)` and the predictable
quadratic variation satisfies `‖∑_{j<k} E[X j² | ℱ j]‖ ≤ v` is at most
`d exp (-(t²/2) / (v + L t / 3))`. [Tropp2011, Theorem 1.2]; stated there for Hermitian
martingales over `ℂ` with the conditional variance as the predictable quadratic variation, here
over any `RCLike` field, any finite index type, with square-integrable increments. The source's
constant. No hypothesis on `v`: for `v < 0` the event is empty.
Proof: case split `v < 0` first (the event is empty, the left side is `0`); `t = 0` (the right
side is `d ≥ 1`). Otherwise the conditional Bernstein bound
`NLAlib.hasCondMatrixMGFBound_of_condExp_eq_zero_of_le`, the master tail
`NLAlib.HasCondMatrixMGFBound.measure_exists_eigenvalue_zero_sum_ge_le` at `w = v` with
`θ` from P5a's `exists_bernstein_exponent` (which needs `0 ≤ v`; to be made public in
`Bernstein.lean`); on the event `specNorm Wₖ ≤ v` gives `Wₖ ≤ v • 1` (`Wₖ` is almost surely
positive semidefinite, `Matrix.ae_posSemidef_condExp`). The potential's integrability: it is
almost surely at most `tr exp (θ Yₖ) ≤ d e^{θ k L}`, since `Wₖ ≥ 0`, `g θ ≥ 0` and
`Yₖ ≤ k L • 1`, and it is measurable. Medium.
Result: matrix-freedman -/
theorem measureReal_exists_eigenvalue_zero_sum_ge_le_freedman [Nonempty n]
    {X : ℕ → Ω → Matrix n n 𝕜} (hX : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (hX2 : ∀ j, MemLp (X j) 2 μ) (hmean : ∀ j, μ[X j | ℱ j] =ᵐ[μ] 0) {L : ℝ} (hL : 0 < L)
    (hle : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ L • (1 : Matrix n n 𝕜)) {t v : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
        specNorm (∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω) ≤ v} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  sorry

/-- **The martingale matrix Bernstein inequality**: Freedman's inequality with an almost sure
bound `v` on the predictable quadratic variation at every time, so that the event is only
`t ≤ λ_max (∑_{j<k} X j)` for some `k`. [Tropp2011, Theorem 1.2]; the form used for adaptive
sampling and streaming. A finite horizon is `X j = 0` for `j ≥ N`.
Proof: `hv` holds for all `k` simultaneously almost surely (countable intersection), so the
event agrees almost everywhere with the event of
`NLAlib.measureReal_exists_eigenvalue_zero_sum_ge_le_freedman`. Easy. -/
theorem measureReal_exists_eigenvalue_zero_sum_ge_le_freedman_of_ae_le [Nonempty n]
    {X : ℕ → Ω → Matrix n n 𝕜} (hX : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (hX2 : ∀ j, MemLp (X j) 2 μ) (hmean : ∀ j, μ[X j | ℱ j] =ᵐ[μ] 0) {L : ℝ} (hL : 0 < L)
    (hle : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ L • (1 : Matrix n n 𝕜)) {t v : ℝ}
    (hv : ∀ k, ∀ᵐ ω ∂μ, specNorm (∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω) ≤ v)
    (ht : 0 ≤ t) :
    μ.real {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  sorry

/-- **Freedman's inequality for rectangular matrix martingales.** For rectangular increments
`S j`, `ℱ (j + 1)`-measurable, square-integrable, conditionally centred and with
`‖S j‖ ≤ L` almost surely, the probability that for some `k` both `t ≤ ‖∑_{j<k} S j‖` and the
larger of the two predictable quadratic variations `‖∑_{j<k} E[S j S jᴴ | ℱ j]‖`,
`‖∑_{j<k} E[S jᴴ S j | ℱ j]‖` is at most `v` is at most
`(d₁ + d₂) exp (-(t²/2) / (v + L t / 3))`. [Tropp2011, Corollary 1.3]; over any `RCLike` field
and finite index types. The source's constant.
Proof (may be scaffolded): the Hermitian Freedman inequality for the dilations
`dilation (S j)`, with `Matrix.condExp_dilation` (centring), `Matrix.condExp_dilation_sq` (the
predictable quadratic variation is block diagonal, so its norm is the `max`),
`λ_max (dilation M) = ‖M‖` and `dilation (S j) ≤ L • 1` from `‖S j‖ ≤ L`. Medium. -/
theorem measureReal_exists_specNorm_sum_ge_le_freedman [Nonempty n] {r : Type*} [Fintype r]
    [DecidableEq r] {S : ℕ → Ω → Matrix r n 𝕜} (hS : ∀ j, StronglyMeasurable[ℱ (j + 1)] (S j))
    (hS2 : ∀ j, MemLp (S j) 2 μ) (hmean : ∀ j, μ[S j | ℱ j] =ᵐ[μ] 0) {L : ℝ} (hL : 0 < L)
    (hle : ∀ j, ∀ᵐ ω ∂μ, specNorm (S j ω) ≤ L) {t v : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ k, t ≤ specNorm (∑ j ∈ Finset.range k, S j ω) ∧
        max (specNorm (∑ j ∈ Finset.range k, μ[fun ω' => S j ω' * (S j ω')ᴴ | ℱ j] ω))
          (specNorm (∑ j ∈ Finset.range k, μ[fun ω' => (S j ω')ᴴ * S j ω' | ℱ j] ω)) ≤ v} ≤
      (Fintype.card r + Fintype.card n) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  sorry

end NLAlib
