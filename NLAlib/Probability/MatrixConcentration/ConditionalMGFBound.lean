/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import NLAlib.ForMathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import NLAlib.Probability.MatrixConcentration.Bernstein
public import NLAlib.Probability.MatrixConditionalExpectation

/-!
# Conditional matrix moment generating function bounds

`NLAlib.HasCondMatrixMGFBound m hm X g A s μ` is the conditional form of
`NLAlib.HasMatrixMGFBound`: `X` is almost surely Hermitian and, conditionally on the
σ-algebra `m`, `E[exp (θ X) | m] ≤ exp (g θ • A)` in the Loewner order almost surely, for every
`θ ∈ s`, with `A` an `m`-measurable, almost surely Hermitian random matrix. It is spelled with
Mathlib's conditional expectation `μ[· | m]`, not with the conditional expectation kernel of
Mathlib's `HasCondSubgaussianMGF`, so that no statement carries `[StandardBorelSpace Ω]`
(`docs/design/Mathlib-deviations.md` entry 17); the bridge from `HasCondSubgaussianMGF` is
`NLAlib.hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF`, the only statement here that
needs a standard Borel space.

Conditional Lieb (`NLAlib.condExp_re_trace_exp_add_le`) turns the interface into a trace
supermartingale, which gives Freedman's inequality
(`NLAlib/Probability/MatrixConcentration/Freedman.lean`). Its input is the conditional
Bernstein bound `NLAlib.hasCondMatrixMGFBound_of_condExp_eq_zero_of_le`.

## Main definitions

* `NLAlib.HasCondMatrixMGFBound m hm X g A s μ`.

## Main results

* `NLAlib.condExp_re_trace_exp_const_add_le`, `NLAlib.condExp_re_trace_exp_add_le`:
  conditional Lieb, for a fixed and for an `m`-measurable `H`.
* `NLAlib.hasCondMatrixMGFBound_of_condExp_eq_zero_of_le`: the conditional Bernstein bound.
* `NLAlib.hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF`: the bridge from Mathlib's
  conditionally sub-Gaussian scalars.

## References

* [J. A. Tropp, *Freedman's inequality for matrix martingales*][Tropp2011], §2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder NNReal
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The random matrix `X` is almost surely Hermitian and, conditionally on `m`, its matrix
moment generating function is bounded by `exp (g θ • A)` in the Loewner order, almost surely,
for every `θ ∈ s`, with `A` an `m`-measurable, almost surely Hermitian random matrix. The
conditional form of `NLAlib.HasMatrixMGFBound`. The hypothesis `hm` is a parameter, as in
Mathlib's `HasCondSubgaussianMGF`: without it `μ[· | m]` would be `0` and the bound vacuous.
The quantifier `∀ θ` is outside the almost-everywhere statement (the supermartingale uses one
`θ`); `docs/design/Mathlib-deviations.md` entry 17. -/
structure HasCondMatrixMGFBound (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (X : Ω → Matrix n n 𝕜)
    (g : ℝ → ℝ) (A : Ω → Matrix n n 𝕜) (s : Set ℝ) (μ : @Measure Ω mΩ) : Prop where
  /-- `X` is almost surely Hermitian. -/
  ae_isHermitian : ∀ᵐ ω ∂μ, (X ω).IsHermitian
  /-- The bounding matrix is `m`-measurable. -/
  stronglyMeasurable_bound : StronglyMeasurable[m] A
  /-- The bounding matrix is almost surely Hermitian. -/
  ae_isHermitian_bound : ∀ᵐ ω ∂μ, (A ω).IsHermitian
  /-- `exp (θ X)` is integrable for `θ ∈ s`. -/
  integrable_exp : ∀ θ ∈ s, Integrable (fun ω => exp (θ • X ω)) μ
  /-- The bound on the conditional matrix moment generating function. -/
  condExp_exp_le : ∀ θ ∈ s, μ[fun ω => exp (θ • X ω) | m] ≤ᵐ[μ] fun ω => exp (g θ • A ω)

namespace HasCondMatrixMGFBound

variable {hm : m ≤ mΩ} {X : Ω → Matrix n n 𝕜} {g : ℝ → ℝ} {A : Ω → Matrix n n 𝕜} {s : Set ℝ}

/-- The bound depends only on the almost-everywhere class of `X`.
Proof: as `NLAlib.HasMatrixMGFBound.congr`, with `condExp_congr_ae`. Easy. -/
theorem congr {Y : Ω → Matrix n n 𝕜} (h : HasCondMatrixMGFBound m hm X g A s μ)
    (hXY : X =ᵐ[μ] Y) : HasCondMatrixMGFBound m hm Y g A s μ := by
  sorry

/-- A bound on a set holds on every subset.
Proof: restrict each field. Easy. -/
theorem mono_set (h : HasCondMatrixMGFBound m hm X g A s μ) {s' : Set ℝ} (hs : s' ⊆ s) :
    HasCondMatrixMGFBound m hm X g A s' μ := by
  sorry

end HasCondMatrixMGFBound

variable [IsProbabilityMeasure μ]

/-- **Conditional Lieb inequality, fixed `H`**: for a fixed Hermitian `H`,
`E[tr exp (H + X) | m] ≤ tr exp (H + log E[exp X | m])` almost surely. [Tropp2011, §2]; the
conditional form of `NLAlib.integral_re_trace_exp_add_le` ([Tropp2015, Corollary 3.4.2]).
No integrability of `tr exp (H + X)` is assumed: if it fails the left side is `0`.
Proof: with `f = exp X`, almost surely positive definite, `tr exp (H + X) = φ (f)` for Lieb's
concave map `φ = fun M => re (tr exp (H + log M))` on the positive definite cone
(`NLAlib.concaveOn_re_trace_exp_add_cfc_log`), continuous there; the conditional mean
`μ[f | m]` is almost surely positive definite (`Matrix.ae_posDef_condExp`), so
`ConcaveOn.condExp_map_le_of_condExp_mem` applies. Integrability of `φ ∘ f` by the case split
above. Medium. -/
theorem condExp_re_trace_exp_const_add_le (hm : m ≤ mΩ) {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {X : Ω → Matrix n n 𝕜} (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hint : Integrable (fun ω => exp (X ω)) μ) :
    μ[fun ω => RCLike.re (exp (H + X ω)).trace | m] ≤ᵐ[μ]
      fun ω => RCLike.re (exp (H + cfc Real.log (μ[fun ω => exp (X ω) | m] ω))).trace := by
  sorry

/-- **Conditional Lieb inequality**: for `H` `m`-measurable and almost surely Hermitian,
`E[tr exp (H + X) | m] ≤ tr exp (H + log E[exp X | m])` almost surely. [Tropp2011, §2]; there
for `H` measurable with respect to the past of a martingale. No integrability of
`tr exp (H + X)` is assumed: if it fails the left side is `0` and the right side is positive.
Proof (the random-`H` step; may be scaffolded): approximate `H` by the `m`-measurable,
countably valued `Hₖ` obtained by rounding each entry of `H` to the grid `(1/k) ℤ` (real and
imaginary parts) and taking the Hermitian part, so `Hₖ → H` uniformly; on each of the countably
many `m`-measurable pieces where `Hₖ` is constant, `NLAlib.condExp_re_trace_exp_const_add_le`
holds after localisation (`condExp_indicator`); pass to the limit with the domination
`NLAlib.re_trace_exp_le_exp_specNorm_sub_mul` and conditional dominated convergence. This is
simpler than `StronglyMeasurable.approx`. The conditional expectation kernel would not shorten
it: `condExpKernel_ae_eq_condExp` holds per measurable set, so an `m`-measurable `H` is constant
under `condExpKernel μ m ω'` only through the same approximation. High. -/
theorem condExp_re_trace_exp_add_le (hm : m ≤ mΩ) {H X : Ω → Matrix n n 𝕜}
    (hHm : StronglyMeasurable[m] H) (hH : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hint : Integrable (fun ω => exp (X ω)) μ) :
    μ[fun ω => RCLike.re (exp (H ω + X ω)).trace | m] ≤ᵐ[μ]
      fun ω => RCLike.re (exp (H ω + cfc Real.log (μ[fun ω => exp (X ω) | m] ω))).trace := by
  sorry

/-- **The conditional Bernstein bound**: a conditionally centred, square-integrable random
matrix with `X ≤ L • 1` almost surely has
`E[exp (θ X) | m] ≤ exp (θ²/2 / (1 - Lθ/3) • E[X² | m])` for `0 < θ < 3/L`. The input of
Freedman's inequality. [Tropp2011, §2]; the conditional form of
`NLAlib.hasMatrixMGFBound_of_integral_eq_zero_of_le` ([Tropp2015, Lemma 6.6.2]).
Proof: as the unconditional bound: the pointwise `exp (θ X) ≤ 1 + θ X + g θ X²` (P5a's
`exp_mul_le_bernstein` through `exp_smul_le_one_add_smul_add_smul_sq`), `condExp_mono`,
linearity (`condExp_add`, `condExp_smul`, `condExp_const hm`), `hmean`, then
`1 + B ≤ exp B` (`Matrix.IsHermitian.one_add_le_exp`) for the a.s. Hermitian
`B = g θ • μ[X² | m]`. Needs `exp_mul_le_bernstein` public in `Bernstein.lean`. Easy to
medium. -/
theorem hasCondMatrixMGFBound_of_condExp_eq_zero_of_le (hm : m ≤ mΩ) {X : Ω → Matrix n n 𝕜}
    {L : ℝ} (hL : 0 < L) (hX2 : MemLp X 2 μ) (hmean : μ[X | m] =ᵐ[μ] 0)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) :
    HasCondMatrixMGFBound m hm X (fun θ => θ ^ 2 / 2 / (1 - L * θ / 3))
      (μ[fun ω => X ω ^ 2 | m]) (Set.Ioo 0 (3 / L)) μ := by
  sorry

omit [IsProbabilityMeasure μ] in
/-- **The bridge from Mathlib's conditionally sub-Gaussian scalars**: if `γ` has a conditionally
sub-Gaussian moment generating function with proxy `c` (Mathlib's `HasCondSubgaussianMGF`,
through the conditional expectation kernel) and `B` is a fixed Hermitian matrix, then `γ • B`
has the conditional matrix MGF bound `E[exp (θ γ B) | m] ≤ exp (θ²/2 • c B²)` for every `θ`.
The bridge of `docs/design/Mathlib-deviations.md` entry 17, and the only statement of the
conditional interface that needs `[StandardBorelSpace Ω]`. With it, matrix Azuma-type tails
follow from the master tail of `NLAlib/Probability/MatrixConcentration/Freedman.lean`.
Proof: diagonalise `B = ∑ λᵢ Pᵢ` (spectral projections); `exp (θ γ B) = ∑ e^{θ λᵢ γ} Pᵢ`, so
`μ[exp (θ γ B) | m] = ∑ μ[e^{θ λᵢ γ} | m] Pᵢ` almost surely by linearity, and each scalar
conditional expectation is at most `e^{c θ² λᵢ² / 2}` almost surely by Mathlib's
`HasCondSubgaussianMGF.ae_condExp_le` (finitely many `i`); the difference is a nonnegative
combination of the `Pᵢ`. Integrability from `HasCondSubgaussianMGF.integrable_exp_mul`. Medium. -/
theorem hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] {hm : m ≤ mΩ} {γ : Ω → ℝ} {c : ℝ≥0}
    (hγ : HasCondSubgaussianMGF m hm γ c μ) {B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    HasCondMatrixMGFBound m hm (fun ω => γ ω • B) (fun θ => θ ^ 2 / 2)
      (fun _ => (c : ℝ) • B ^ 2) Set.univ μ := by
  sorry

end NLAlib
