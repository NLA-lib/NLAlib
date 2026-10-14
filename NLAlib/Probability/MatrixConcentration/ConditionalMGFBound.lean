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

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder NNReal Topology
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
  have he : ∀ θ : ℝ, (fun ω => exp (θ • X ω)) =ᵐ[μ] fun ω => exp (θ • Y ω) := fun θ =>
    hXY.mono fun ω hω => by simp only [hω]
  refine ⟨?_, h.stronglyMeasurable_bound, h.ae_isHermitian_bound,
    fun θ hθ => (h.integrable_exp θ hθ).congr (he θ),
    fun θ hθ => (condExp_congr_ae (he θ)).symm.trans_le (h.condExp_exp_le θ hθ)⟩
  filter_upwards [h.ae_isHermitian, hXY] with ω h1 h2
  rwa [← h2]

/-- A bound on a set holds on every subset.
Proof: restrict each field. Easy. -/
theorem mono_set (h : HasCondMatrixMGFBound m hm X g A s μ) {s' : Set ℝ} (hs : s' ⊆ s) :
    HasCondMatrixMGFBound m hm X g A s' μ :=
  ⟨h.ae_isHermitian, h.stronglyMeasurable_bound, h.ae_isHermitian_bound,
    fun θ hθ => h.integrable_exp θ (hs hθ), fun θ hθ => h.condExp_exp_le θ (hs hθ)⟩

end HasCondMatrixMGFBound

/-! ### Helpers -/

/-- The trace exponential of a Hermitian matrix is nonnegative. -/
private theorem re_trace_exp_nonneg {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    0 ≤ RCLike.re (exp M).trace := by
  rw [hM.re_trace_exp]
  exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

omit [Fintype n] [DecidableEq n] in
/-- Conditional expectations are monotone on an `m`-measurable set. -/
private theorem ae_condExp_le_condExp_of_mem (hm : m ≤ mΩ) {f g : Ω → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) {C : Set Ω} (hC : MeasurableSet[m] C)
    (hle : ∀ᵐ ω ∂μ, ω ∈ C → f ω ≤ g ω) : ∀ᵐ ω ∂μ, ω ∈ C → μ[f | m] ω ≤ μ[g | m] ω := by
  have hmono := condExp_mono (m := m) (hf.indicator (hm C hC)) (hg.indicator (hm C hC))
    (hle.mono fun ω hω => by
      by_cases hωC : ω ∈ C
      · simp only [Set.indicator_of_mem hωC, hω hωC]
      · simp only [Set.indicator_of_notMem hωC, le_refl])
  filter_upwards [hmono, condExp_indicator hf hC, condExp_indicator hg hC] with ω h h1 h2 hωC
  rw [h1, h2, Set.indicator_of_mem hωC, Set.indicator_of_mem hωC] at h
  exact h

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
  have hpd : ∀ᵐ ω ∂μ, (exp (X ω)).PosDef := hX.mono fun ω hω => hω.posDef_exp
  have hmean := Matrix.ae_posDef_condExp hm hint hpd
  have heq : (fun ω => RCLike.re (exp (H + cfc Real.log (exp (X ω)))).trace) =ᵐ[μ]
      fun ω => RCLike.re (exp (H + X ω)).trace :=
    hX.mono fun ω hω => by simp only [hω.cfc_log_exp]
  have hi : Integrable (fun ω => RCLike.re (exp (H + X ω)).trace) μ :=
    integrable_re_trace_exp_add_of_le hH (aemeasurable_of_integrable_exp hX hint) hX hint.norm
      (ae_of_all _ fun ω => (specNorm_eq_norm _).le)
  have hJ := (concaveOn_re_trace_exp_add_cfc_log hH).condExp_map_le_of_condExp_mem hm
    (continuousOn_re_trace_exp_add_cfc_log H) hpd hint (hi.congr heq.symm) hmean
  filter_upwards [hJ, condExp_congr_ae (m := m) heq] with ω h1 h2
  rw [← h2]
  exact h1

omit [IsProbabilityMeasure μ] in
/-- On the `m`-measurable set where `H` is within `δ` of a fixed Hermitian `p`, the conditional
trace exponential with offset `H` is at most `e^δ` times the one with offset `p`. -/
private theorem ae_condExp_re_trace_exp_add_le_exp_mul (hm : m ≤ mΩ) {H X : Ω → Matrix n n 𝕜}
    (hHm : StronglyMeasurable[m] H) (hH : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hint : Integrable (fun ω => exp (X ω)) μ)
    (hi : Integrable (fun ω => RCLike.re (exp (H ω + X ω)).trace) μ)
    {p : Matrix n n 𝕜} (hp : p.IsHermitian) (δ : ℝ) :
    ∀ᵐ ω ∂μ, ‖H ω - p‖ < δ →
      μ[fun ω => RCLike.re (exp (H ω + X ω)).trace | m] ω ≤
        Real.exp δ * μ[fun ω => RCLike.re (exp (p + X ω)).trace | m] ω := by
  let C : Set Ω := {ω | ‖H ω - p‖ < δ}
  have hC : MeasurableSet[m] C :=
    measurableSet_lt (hHm.sub stronglyMeasurable_const).norm.measurable measurable_const
  have hip : Integrable (fun ω => RCLike.re (exp (p + X ω)).trace) μ :=
    integrable_re_trace_exp_add_of_le hp (aemeasurable_of_integrable_exp hX hint) hX hint.norm
      (ae_of_all _ fun ω => (specNorm_eq_norm _).le)
  have hpt : ∀ᵐ ω ∂μ, ω ∈ C → RCLike.re (exp (H ω + X ω)).trace ≤
      Real.exp δ * RCLike.re (exp (p + X ω)).trace := by
    filter_upwards [hH, hX] with ω hHω hXω hωC
    have h := re_trace_exp_le_exp_specNorm_sub_mul (hHω.add hXω) (hp.add hXω)
    rw [add_sub_add_right_eq_sub, specNorm_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_of_lt hωC))
      (re_trace_exp_nonneg (hp.add hXω)))
  filter_upwards [ae_condExp_le_condExp_of_mem hm hi (hip.const_mul (Real.exp δ)) hC hpt,
    condExp_smul (m := m) (Real.exp δ) (fun ω => RCLike.re (exp (p + X ω)).trace)]
    with ω h hs hωC
  have hs' : μ[fun ω => Real.exp δ * RCLike.re (exp (p + X ω)).trace | m] ω =
      Real.exp δ * μ[fun ω => RCLike.re (exp (p + X ω)).trace | m] ω := hs
  rw [← hs']
  exact h hωC

/-- **Conditional Lieb inequality**: for `H` `m`-measurable and almost surely Hermitian,
`E[tr exp (H + X) | m] ≤ tr exp (H + log E[exp X | m])` almost surely. [Tropp2011, §2]; there
for `H` measurable with respect to the past of a martingale. No integrability of
`tr exp (H + X)` is assumed: if it fails the left side is `0` and the right side is nonnegative.
Proof: if `tr exp (H + X)` is not integrable the left side is `0`. Otherwise take a dense
sequence `uⱼ` of Hermitian matrices; `NLAlib.condExp_re_trace_exp_const_add_le` holds for all `uⱼ`
on one null set. On the `m`-measurable set `{‖H - uⱼ‖ < δ}`,
`tr exp (H + X) ≤ e^δ tr exp (uⱼ + X)` (`NLAlib.re_trace_exp_le_exp_specNorm_sub_mul`), and
conditional expectations are monotone on `m`-measurable sets (`condExp_indicator`); the same
perturbation bound on the right side gives the inequality up to a factor `e^{2δ}`, and `δ → 0`.
This replaces the rounding of `H` to a grid suggested by the design note: no limit of conditional
expectations is taken. The conditional expectation kernel would not shorten it:
`condExpKernel_ae_eq_condExp` holds per measurable set, so an `m`-measurable `H` is constant
under `condExpKernel μ m ω'` only through the same approximation. -/
theorem condExp_re_trace_exp_add_le (hm : m ≤ mΩ) {H X : Ω → Matrix n n 𝕜}
    (hHm : StronglyMeasurable[m] H) (hH : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hint : Integrable (fun ω => exp (X ω)) μ) :
    μ[fun ω => RCLike.re (exp (H ω + X ω)).trace | m] ≤ᵐ[μ]
      fun ω => RCLike.re (exp (H ω + cfc Real.log (μ[fun ω => exp (X ω) | m] ω))).trace := by
  by_cases hi : Integrable (fun ω => RCLike.re (exp (H ω + X ω)).trace) μ
  swap
  · rw [condExp_of_not_integrable hi]
    filter_upwards [hH] with ω hω
    exact re_trace_exp_nonneg (hω.add (cfc_predicate Real.log _))
  let S := {A : Matrix n n 𝕜 // A.IsHermitian}
  have : Nonempty S := ⟨⟨0, Matrix.isHermitian_zero⟩⟩
  let u : ℕ → Matrix n n 𝕜 := fun j => (TopologicalSpace.denseSeq S j).1
  have hu : ∀ j, (u j).IsHermitian := fun j => (TopologicalSpace.denseSeq S j).2
  have hdense : ∀ A : Matrix n n 𝕜, A.IsHermitian → ∀ ε > 0, ∃ j, ‖A - u j‖ < ε := by
    intro A hA ε hε
    obtain ⟨j, hj⟩ := (TopologicalSpace.denseRange_denseSeq S).exists_dist_lt (⟨A, hA⟩ : S) hε
    exact ⟨j, by rwa [Subtype.dist_eq, dist_eq_norm] at hj⟩
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hJ : ∀ᵐ ω ∂μ, ∀ j, μ[fun ω => RCLike.re (exp (u j + X ω)).trace | m] ω ≤
      RCLike.re (exp (u j + cfc Real.log (μ[fun ω => exp (X ω) | m] ω))).trace :=
    ae_all_iff.mpr fun j => condExp_re_trace_exp_const_add_le hm (hu j) hX hint
  have hcuts : ∀ᵐ ω ∂μ, ∀ j k, ‖H ω - u j‖ < δ k →
      μ[fun ω => RCLike.re (exp (H ω + X ω)).trace | m] ω ≤
        Real.exp (δ k) * μ[fun ω => RCLike.re (exp (u j + X ω)).trace | m] ω :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k =>
      ae_condExp_re_trace_exp_add_le_exp_mul hm hHm hH hX hint hi (hu j) (δ k)
  filter_upwards [hJ, hcuts, hH] with ω hJω hcω hHω
  set L := cfc Real.log (μ[fun ω => exp (X ω) | m] ω)
  have hL : L.IsHermitian := cfc_predicate _ _
  set R := RCLike.re (exp (H ω + L)).trace
  have hbound : ∀ k, μ[fun ω => RCLike.re (exp (H ω + X ω)).trace | m] ω ≤
      Real.exp (2 * δ k) * R := by
    intro k
    obtain ⟨j, hj⟩ := hdense (H ω) hHω (δ k) (by positivity)
    have hrev := re_trace_exp_le_exp_specNorm_sub_mul ((hu j).add hL) (hHω.add hL)
    rw [add_sub_add_right_eq_sub, specNorm_eq_norm, norm_sub_rev] at hrev
    calc μ[fun ω => RCLike.re (exp (H ω + X ω)).trace | m] ω
        ≤ Real.exp (δ k) * μ[fun ω => RCLike.re (exp (u j + X ω)).trace | m] ω := hcω j k hj
      _ ≤ Real.exp (δ k) * RCLike.re (exp (u j + L)).trace :=
        mul_le_mul_of_nonneg_left (hJω j) (Real.exp_pos _).le
      _ ≤ Real.exp (δ k) * (Real.exp (δ k) * R) :=
        mul_le_mul_of_nonneg_left (hrev.trans (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr hj.le) (re_trace_exp_nonneg (hHω.add hL)))) (Real.exp_pos _).le
      _ = Real.exp (2 * δ k) * R := by rw [← mul_assoc, ← Real.exp_add, two_mul]
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun k => Real.exp (2 * δ k) * R) atTop (𝓝 R) := by
    have h2 : Tendsto (fun k => 2 * δ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using hδ.const_mul 2
    have := ((Real.continuous_exp.tendsto 0).comp h2).mul_const R
    simpa only [Function.comp_def, mul_zero, Real.exp_zero, one_mul] using this
  exact ge_of_tendsto' hlim hbound

/-- **The conditional Bernstein bound**: a conditionally centred, square-integrable random
matrix with `X ≤ L • 1` almost surely has
`E[exp (θ X) | m] ≤ exp (θ²/2 / (1 - Lθ/3) • E[X² | m])` for `0 < θ < 3/L`. The input of
Freedman's inequality. [Tropp2011, §2]; the conditional form of
`NLAlib.hasMatrixMGFBound_of_integral_eq_zero_of_le` ([Tropp2015, Lemma 6.6.2]).
Proof: as the unconditional bound: the pointwise `exp (θ X) ≤ 1 + θ X + g θ X²` (P5a's
`exp_mul_le_bernstein` through `exp_smul_le_one_add_smul_add_smul_sq`), `condExp_mono`,
linearity (`condExp_add`, `condExp_smul`, `condExp_const hm`), `hmean`, then
`1 + B ≤ exp B` (`Matrix.IsHermitian.one_add_le_exp`) for the a.s. Hermitian
`B = g θ • μ[X² | m]`. Easy to medium. -/
theorem hasCondMatrixMGFBound_of_condExp_eq_zero_of_le (hm : m ≤ mΩ) {X : Ω → Matrix n n 𝕜}
    {L : ℝ} (hL : 0 < L) (hX2 : MemLp X 2 μ) (hmean : μ[X | m] =ᵐ[μ] 0)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) :
    HasCondMatrixMGFBound m hm X (fun θ => θ ^ 2 / 2 / (1 - L * θ / 3))
      (μ[fun ω => X ω ^ 2 | m]) (Set.Ioo 0 (3 / L)) μ := by
  have hH : ∀ᵐ ω ∂μ, (X ω).IsHermitian := hle.mono fun ω h => isHermitian_of_le_smul_one h
  have hXi : Integrable X μ := hX2.integrable one_le_two
  have hX2i : Integrable (fun ω => X ω ^ 2) μ := by
    refine (hX2.integrable_norm_pow two_ne_zero).mono'
      ((continuous_pow 2).comp_aestronglyMeasurable hX2.1) (ae_of_all _ fun ω => ?_)
    rw [sq, sq]
    exact norm_mul_le _ _
  have hexpc : Continuous (exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  have hQ : ∀ θ c : ℝ, Integrable (fun ω => 1 + θ • X ω + c • X ω ^ 2) μ := fun θ c =>
    ((integrable_const 1).add (hXi.smul θ)).add (hX2i.smul c)
  have hpt : ∀ θ ∈ Set.Ioo 0 (3 / L), ∀ᵐ ω ∂μ,
      exp (θ • X ω) ≤ 1 + θ • X ω + (θ ^ 2 / 2 / (1 - L * θ / 3)) • X ω ^ 2 := by
    intro θ hθ
    filter_upwards [hle, hH] with ω hω hωH
    refine exp_smul_le_one_add_smul_add_smul_sq (a := -specNorm (X ω)) ?_ hω
      fun x hx => exp_mul_le_bernstein hθ.1 (bernsteinCoeff_nonneg hL hθ).1 hx.2
    rw [neg_smul]
    exact hωH.neg_specNorm_smul_one_le
  have hint : ∀ θ ∈ Set.Ioo 0 (3 / L), Integrable (fun ω => exp (θ • X ω)) μ := by
    intro θ hθ
    refine (hQ θ (θ ^ 2 / 2 / (1 - L * θ / 3))).norm.mono'
      (hexpc.comp_aestronglyMeasurable (hX2.1.const_smul θ)) ?_
    filter_upwards [hpt θ hθ, hH] with ω hω hωH
    rw [← specNorm_eq_norm, ← specNorm_eq_norm]
    have hθX : (θ • X ω).IsHermitian := (IsSelfAdjoint.all θ).smul hωH
    exact hθX.posDef_exp.posSemidef.specNorm_le_specNorm_of_le hω
  have hS := Matrix.ae_isHermitian_condExp (m := m) (hH.mono fun ω h => h.pow 2)
  refine ⟨hH, stronglyMeasurable_condExp, hS, hint, fun θ hθ => ?_⟩
  set c := θ ^ 2 / 2 / (1 - L * θ / 3)
  have h1 := condExp_mono (m := m) (hint θ hθ) (hQ θ c) (hpt θ hθ)
  have hA : Integrable (fun ω => (1 : Matrix n n 𝕜) + θ • X ω) μ :=
    (integrable_const 1).add (hXi.smul θ)
  filter_upwards [h1, condExp_add (m := m) hA (hX2i.smul c),
    condExp_add (m := m) (integrable_const (1 : Matrix n n 𝕜)) (hXi.smul θ),
    condExp_smul (m := m) θ X, condExp_smul (m := m) c (fun ω => X ω ^ 2), hmean, hS]
    with ω h1 h2 h3 h4 h5 h6 h7
  have h2' : μ[fun ω => 1 + θ • X ω + c • X ω ^ 2 | m] ω =
      μ[fun ω => 1 + θ • X ω | m] ω + μ[fun ω => c • X ω ^ 2 | m] ω := h2
  have h3' : μ[fun ω => 1 + θ • X ω | m] ω =
      μ[fun _ => (1 : Matrix n n 𝕜) | m] ω + μ[fun ω => θ • X ω | m] ω := h3
  have h4' : μ[fun ω => θ • X ω | m] ω = θ • μ[X | m] ω := h4
  have h5' : μ[fun ω => c • X ω ^ 2 | m] ω = c • μ[fun ω => X ω ^ 2 | m] ω := h5
  rw [h2', h3', h4', h5', condExp_const hm, h6, Pi.zero_apply, smul_zero, add_zero] at h1
  exact h1.trans (Matrix.IsHermitian.one_add_le_exp ((IsSelfAdjoint.all c).smul h7))

/-- The exponential of a function of a Hermitian matrix. -/
private theorem exp_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    exp (cfc f B) = cfc (fun x => Real.exp (f x)) B := by
  have hH : (cfc f B).IsHermitian := cfc_predicate f B
  rw [hH.exp_eq_cfc]
  exact (cfc_comp' Real.exp f B ((B.finite_real_spectrum.image _).continuousOn _)
    (B.finite_real_spectrum.continuousOn _) hB).symm

omit [IsProbabilityMeasure μ] in
/-- The conditional expectation of a random function of a fixed Hermitian matrix is the function
of the matrix with the conditional expectations of the values, through a unitary diagonalisation.
The conditional form of `Matrix.IsHermitian.cfc_integral`. -/
private theorem condExp_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian) {f : Ω → ℝ → ℝ}
    (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    μ[fun ω => cfc (f ω) B | m] =ᵐ[μ] fun ω' => cfc (fun x => μ[fun ω => f ω x | m] ω') B := by
  obtain ⟨U, hU, hBU⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  let Lc : (Fin (Fintype.card n) → ℝ) →L[ℝ] Matrix n n 𝕜 := LinearMap.toContinuousLinearMap
    { toFun := fun v => U * Matrix.diagonal (fun i => ((v i : ℝ) : 𝕜)) * Uᴴ
      map_add' := fun v w => by
        simp only [Pi.add_apply, RCLike.ofReal_add, ← Matrix.diagonal_add, Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := fun a v => by
        have hd : (fun i => (((a • v) i : ℝ) : 𝕜)) = (a : 𝕜) • fun i => ((v i : ℝ) : 𝕜) := by
          funext i
          simp only [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul]
        rw [RingHom.id_apply, hd, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul,
          ← RCLike.real_smul_eq_coe_smul] }
  have hcfc : ∀ g : ℝ → ℝ, cfc g B = Lc (fun i => g (eigenvalue B i)) := fun g =>
    cfc_eq_mul_diagonal_mul_conjTranspose hU hr hBU g
  let v : Ω → Fin (Fintype.card n) → ℝ := fun ω i => f ω (eigenvalue B i)
  have hv : Integrable v μ := integrable_pi_iff.2 fun i => hf _
  have hcomp : (fun ω => cfc (f ω) B) = Lc ∘ v := funext fun ω => hcfc (f ω)
  have hproj : ∀ᵐ ω' ∂μ, ∀ i, μ[v | m] ω' i = μ[fun ω => f ω (eigenvalue B i) | m] ω' :=
    ae_all_iff.mpr fun i =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp_condExp_comm (m := m) hv
  rw [hcomp]
  filter_upwards [(Lc.comp_condExp_comm (m := m) hv).symm, hproj] with ω' h1 h2
  rw [h1, Function.comp_apply, hcfc]
  exact congrArg Lc (funext h2)

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
  have hsa : IsSelfAdjoint B := hB
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ B) := fun g =>
    B.finite_real_spectrum.continuousOn g
  have hexp : ∀ (θ : ℝ) (ω : Ω),
      exp (θ • γ ω • B) = cfc (fun x => Real.exp (θ * γ ω * x)) B := fun θ ω => by
    rw [smul_smul, ← exp_cfc hB, cfc_const_mul _ (fun x => x) B (hcont _), cfc_id' ℝ B hsa]
  have hf : ∀ θ x : ℝ, Integrable (fun ω => Real.exp (θ * γ ω * x)) μ := fun θ x => by
    refine (hγ.integrable_exp_mul (θ * x)).congr (ae_of_all _ fun ω => ?_)
    simp only
    ring_nf
  refine ⟨ae_of_all _ fun ω => (IsSelfAdjoint.all _).smul hB, stronglyMeasurable_const,
    ae_of_all _ fun _ => (IsSelfAdjoint.all _).smul (hB.pow 2), fun θ _ => ?_, fun θ _ => ?_⟩
  · simp only [hexp]
    exact hB.integrable_cfc (hf θ)
  · simp only [hexp]
    have hR : (θ ^ 2 / 2) • ((c : ℝ) • B ^ 2) =
        cfc (fun x : ℝ => θ ^ 2 / 2 * ((c : ℝ) * x ^ 2)) B := by
      rw [cfc_const_mul _ _ B (hcont _), cfc_const_mul _ _ B (hcont _),
        cfc_pow (fun x : ℝ => x) 2 B (hcont _) hsa, cfc_id' ℝ B hsa]
    have hsub : ∀ᵐ ω' ∂μ, ∀ i : Fin (Fintype.card n),
        μ[fun ω => Real.exp (θ * γ ω * eigenvalue B i) | m] ω' ≤
          Real.exp (θ ^ 2 / 2 * ((c : ℝ) * eigenvalue B i ^ 2)) := by
      refine ae_all_iff.mpr fun i => ?_
      have hce : (fun ω => Real.exp (θ * eigenvalue B i * γ ω)) =
          fun ω => Real.exp (θ * γ ω * eigenvalue B i) := funext fun ω => by ring_nf
      filter_upwards [hγ.ae_condExp_le (θ * eigenvalue B i)] with ω' h
      rw [hce] at h
      refine h.trans_eq ?_
      congr 1
      ring
    filter_upwards [condExp_cfc (m := m) hB (hf θ), hsub] with ω' h1 h2
    rw [h1, hR, exp_cfc hB]
    refine cfc_mono (fun x hx => ?_) (hcont _) (hcont _)
    have hsp := (hB.spectrum_subset_iff (s := {x | μ[fun ω => Real.exp (θ * γ ω * x) | m] ω' ≤
      Real.exp (θ ^ 2 / 2 * ((c : ℝ) * x ^ 2))})).mpr fun i hi => h2 ⟨i, hi⟩
    exact hsp hx

end NLAlib
