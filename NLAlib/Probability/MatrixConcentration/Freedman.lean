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

/-- Monotonicity of `μ.real` along an almost-everywhere inclusion. -/
private theorem measureReal_mono_ae' {s t : Set Ω} (h : s ≤ᵐ[μ] t) : μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono (measure_ne_top μ t) (measure_mono_ae h)

/-- The trace exponential of a Hermitian matrix is nonnegative. -/
private theorem re_trace_exp_nonneg {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    0 ≤ RCLike.re (exp M).trace := by
  rw [hM.re_trace_exp]
  exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

namespace HasCondMatrixMGFBound

variable {X A : ℕ → Ω → Matrix n n 𝕜} {g : ℝ → ℝ} {s : Set ℝ}

omit [IsProbabilityMeasure μ] in
/-- The exponent of the trace potential is almost surely Hermitian, at every time at once. -/
private theorem ae_isHermitian_potential
    (h : ∀ j, HasCondMatrixMGFBound (ℱ j) (ℱ.le j) (X j) g (A j) s μ) (θ : ℝ) :
    ∀ᵐ ω ∂μ, ∀ k, (θ • ∑ j ∈ Finset.range k, X j ω -
      g θ • ∑ j ∈ Finset.range k, A j ω).IsHermitian := by
  filter_upwards [ae_all_iff.mpr fun j => (h j).ae_isHermitian,
    ae_all_iff.mpr fun j => (h j).ae_isHermitian_bound] with ω h1 h2 k
  exact ((IsSelfAdjoint.all θ).smul (isSelfAdjoint_sum _ fun j _ => h1 j)).sub
    ((IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun j _ => h2 j))

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
  have hYm : ∀ k i, k ≤ i → StronglyMeasurable[ℱ i] (fun ω => ∑ j ∈ Finset.range k, X j ω) :=
    fun k i hki => Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      (hX j).mono (ℱ.mono (by rw [Finset.mem_range] at hj; omega))
  have hWm : ∀ k i, k ≤ i + 1 →
      StronglyMeasurable[ℱ i] (fun ω => ∑ j ∈ Finset.range k, A j ω) :=
    fun k i hki => Finset.stronglyMeasurable_fun_sum _ fun j hj =>
      (h j).stronglyMeasurable_bound.mono (ℱ.mono (by rw [Finset.mem_range] at hj; omega))
  refine supermartingale_nat (fun k => ?_) hint fun k => ?_
  · exact continuous_re_trace_exp.comp_stronglyMeasurable
      (((hYm k k le_rfl).const_smul θ).sub ((hWm k k (by omega)).const_smul (g θ)))
  let H : Ω → Matrix n n 𝕜 := fun ω =>
    θ • ∑ j ∈ Finset.range k, X j ω - g θ • ∑ j ∈ Finset.range (k + 1), A j ω
  have hHm : StronglyMeasurable[ℱ k] H :=
    ((hYm k k le_rfl).const_smul θ).sub ((hWm (k + 1) k le_rfl).const_smul (g θ))
  have hHH : ∀ᵐ ω ∂μ, (H ω).IsHermitian := by
    filter_upwards [ae_all_iff.mpr fun j => (h j).ae_isHermitian,
      ae_all_iff.mpr fun j => (h j).ae_isHermitian_bound] with ω h1 h2
    exact ((IsSelfAdjoint.all θ).smul (isSelfAdjoint_sum _ fun j _ => h1 j)).sub
      ((IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun j _ => h2 j))
  have hm : ∀ ω, θ • ∑ j ∈ Finset.range (k + 1), X j ω -
      g θ • ∑ j ∈ Finset.range (k + 1), A j ω = H ω + θ • X k ω := fun ω => by
    simp only [H, Finset.sum_range_succ, smul_add]
    abel
  have heq : (fun ω => RCLike.re (exp (θ • ∑ j ∈ Finset.range (k + 1), X j ω -
      g θ • ∑ j ∈ Finset.range (k + 1), A j ω)).trace) =
      fun ω => RCLike.re (exp (H ω + θ • X k ω)).trace := funext fun ω => by rw [hm ω]
  have hXk : ∀ᵐ ω ∂μ, (θ • X k ω).IsHermitian :=
    (h k).ae_isHermitian.mono fun ω hω => (IsSelfAdjoint.all θ).smul hω
  have hL := condExp_re_trace_exp_add_le (ℱ.le k) hHm hHH hXk ((h k).integrable_exp θ hθ)
  have hpd := Matrix.ae_posDef_condExp (ℱ.le k) ((h k).integrable_exp θ hθ)
    (hXk.mono fun ω hω => hω.posDef_exp)
  rw [heq]
  filter_upwards [hL, hpd, (h k).condExp_exp_le θ hθ, hHH, (h k).ae_isHermitian_bound]
    with ω h1 h2 h3 h4 h5
  refine h1.trans ?_
  have hlog : cfc Real.log (μ[fun ω => exp (θ • X k ω) | ℱ k] ω) ≤ g θ • A k ω := by
    have := h2.cfc_log_le_cfc_log h3
    rwa [Matrix.IsHermitian.cfc_log_exp ((IsSelfAdjoint.all (g θ)).smul h5)] at this
  have hfin : H ω + g θ • A k ω =
      θ • ∑ j ∈ Finset.range k, X j ω - g θ • ∑ j ∈ Finset.range k, A j ω := by
    simp only [H, Finset.sum_range_succ, smul_add]
    abel
  rw [← hfin]
  exact re_trace_exp_le_re_trace_exp_of_le (h4.add (cfc_predicate Real.log _))
    (add_le_add le_rfl hlog)

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
  have hsup := supermartingale_re_trace_exp hX h hθs hint
  have hherm := ae_isHermitian_potential h θ
  have hΦ0 : ∀ k, 0 ≤ᵐ[μ] fun ω => RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω -
      g θ • ∑ j ∈ Finset.range k, A j ω)).trace := fun k =>
    hherm.mono fun ω hω => re_trace_exp_nonneg (hω k)
  have hV := hsup.measure_exists_ge_le hΦ0 (Real.exp_pos (θ * t - g θ * w))
  have h0 : ∫ ω, RCLike.re (exp (θ • ∑ j ∈ Finset.range 0, X j ω -
      g θ • ∑ j ∈ Finset.range 0, A j ω)).trace ∂μ = Fintype.card n := by
    simp only [Finset.range_zero, Finset.sum_empty, smul_zero, sub_zero, NormedSpace.exp_zero,
      Matrix.trace_one, RCLike.natCast_re, integral_const, probReal_univ, one_smul]
  have hsub : {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
      ∑ j ∈ Finset.range k, A j ω ≤ w • (1 : Matrix n n 𝕜)} ≤ᵐ[μ]
      {ω | ∃ k, Real.exp (θ * t - g θ * w) ≤ RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω -
        g θ • ∑ j ∈ Finset.range k, A j ω)).trace} := by
    filter_upwards [ae_all_iff.mpr fun j => (h j).ae_isHermitian, hherm] with ω h1 h2
    rintro ⟨k, hk1, hk2⟩
    refine ⟨k, ?_⟩
    have hY : (∑ j ∈ Finset.range k, X j ω).IsHermitian := isSelfAdjoint_sum _ fun j _ => h1 j
    have hθY : (θ • ∑ j ∈ Finset.range k, X j ω).IsHermitian := (IsSelfAdjoint.all θ).smul hY
    have hle : θ • ∑ j ∈ Finset.range k, X j ω + (-(g θ * w)) • (1 : Matrix n n 𝕜) ≤
        θ • ∑ j ∈ Finset.range k, X j ω - g θ • ∑ j ∈ Finset.range k, A j ω := by
      rw [neg_smul, ← sub_eq_add_neg, ← smul_smul]
      exact sub_le_sub_left (smul_le_smul_of_nonneg_left hk2 hg) _
    calc Real.exp (θ * t - g θ * w) = Real.exp (-(g θ * w)) * Real.exp (θ * t) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ Real.exp (-(g θ * w)) * Real.exp (θ * eigenvalue (∑ j ∈ Finset.range k, X j ω) 0) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk1 hθ.le))
            (Real.exp_pos _).le
      _ ≤ Real.exp (-(g θ * w)) * RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω)).trace :=
          mul_le_mul_of_nonneg_left (exp_mul_eigenvalue_le_re_trace_exp hY θ Fintype.card_pos)
            (Real.exp_pos _).le
      _ = RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω +
            (-(g θ * w)) • (1 : Matrix n n 𝕜))).trace :=
          (re_trace_exp_add_real_smul_one _ _).symm
      _ ≤ _ := re_trace_exp_le_re_trace_exp_of_le
          (hθY.add ((IsSelfAdjoint.all _).smul (Matrix.isHermitian_one))) hle
  refine (measureReal_mono_ae' hsub).trans (hV.trans_eq ?_)
  rw [h0, div_eq_mul_inv, ← Real.exp_neg]
  ring_nf

/-- The trace potential is integrable when the increments are bounded above, `A j ≥ 0` and
`θ, g θ ≥ 0`: it is at most `d e^{θ k L}`. -/
private theorem integrable_potential (hX : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (h : ∀ j, HasCondMatrixMGFBound (ℱ j) (ℱ.le j) (X j) g (A j) s μ) {θ L : ℝ} (hθ : 0 ≤ θ)
    (hg : 0 ≤ g θ) (hle : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ L • (1 : Matrix n n 𝕜))
    (hA : ∀ j, ∀ᵐ ω ∂μ, (A j ω).PosSemidef) (k : ℕ) :
    Integrable (fun ω => RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω -
      g θ • ∑ j ∈ Finset.range k, A j ω)).trace) μ := by
  have hYm : StronglyMeasurable (fun ω => ∑ j ∈ Finset.range k, X j ω) :=
    Finset.stronglyMeasurable_fun_sum _ fun j _ => (hX j).mono (ℱ.le (j + 1))
  have hWm : StronglyMeasurable (fun ω => ∑ j ∈ Finset.range k, A j ω) :=
    Finset.stronglyMeasurable_fun_sum _ fun j _ => (h j).stronglyMeasurable_bound.mono (ℱ.le j)
  have hmeas := continuous_re_trace_exp.comp_stronglyMeasurable
    ((hYm.const_smul θ).sub (hWm.const_smul (g θ)))
  refine (integrable_const (Real.exp (θ * (k * L)) * Fintype.card n)).mono'
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_isHermitian_potential h θ, ae_all_iff.mpr hle, ae_all_iff.mpr hA]
    with ω h1 h2 h3
  rw [Real.norm_eq_abs, abs_of_nonneg (re_trace_exp_nonneg (h1 k))]
  have hY : ∑ j ∈ Finset.range k, X j ω ≤ (k * L) • (1 : Matrix n n 𝕜) := by
    refine (Finset.sum_le_sum fun j _ => h2 j).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hW : 0 ≤ g θ • ∑ j ∈ Finset.range k, A j ω :=
    smul_nonneg hg (Finset.sum_nonneg fun j _ => (h3 j).nonneg)
  have hle' : θ • ∑ j ∈ Finset.range k, X j ω - g θ • ∑ j ∈ Finset.range k, A j ω ≤
      0 + (θ * (k * L)) • (1 : Matrix n n 𝕜) := by
    rw [zero_add, ← smul_smul]
    exact (sub_le_self _ hW).trans (smul_le_smul_of_nonneg_left hY hθ)
  refine (re_trace_exp_le_re_trace_exp_of_le (h1 k) hle').trans_eq ?_
  rw [re_trace_exp_add_real_smul_one, NormedSpace.exp_zero, Matrix.trace_one, RCLike.natCast_re]

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
`θ` from P5a's `NLAlib.exists_bernstein_exponent` (which needs `0 ≤ v`); on the event
`specNorm Wₖ ≤ v` gives `Wₖ ≤ v • 1` (`Wₖ` is almost surely Hermitian). The potential's
integrability: it is almost surely at most `tr exp (θ Yₖ) ≤ d e^{θ k L}`, since `Wₖ ≥ 0`,
`g θ ≥ 0` and `Yₖ ≤ k L • 1`, and it is measurable. Medium.
Result: matrix-freedman -/
theorem measureReal_exists_eigenvalue_zero_sum_ge_le_freedman [Nonempty n]
    {X : ℕ → Ω → Matrix n n 𝕜} (hX : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (hX2 : ∀ j, MemLp (X j) 2 μ) (hmean : ∀ j, μ[X j | ℱ j] =ᵐ[μ] 0) {L : ℝ} (hL : 0 < L)
    (hle : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ L • (1 : Matrix n n 𝕜)) {t v : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
        specNorm (∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω) ≤ v} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have hd : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  rcases lt_or_ge v 0 with hv | hv
  · have hE : {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
        specNorm (∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω) ≤ v} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω ⟨_, _, hk⟩ =>
        absurd (hk.trans_lt hv) (not_lt.mpr (specNorm_nonneg _))
    rw [hE, measureReal_empty]
    positivity
  rcases ht.eq_or_lt with rfl | ht'
  · rw [show -((0 : ℝ) ^ 2 / 2) / (v + L * 0 / 3) = 0 by ring, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans hd
  obtain ⟨θ, hθ, hθb⟩ := exists_bernstein_exponent hL hv ht'
  have h : ∀ j, HasCondMatrixMGFBound (ℱ j) (ℱ.le j) (X j) (fun θ => θ ^ 2 / 2 / (1 - L * θ / 3))
      (μ[fun ω' => X j ω' ^ 2 | ℱ j]) (Set.Ioo 0 (3 / L)) μ := fun j =>
    hasCondMatrixMGFBound_of_condExp_eq_zero_of_le (ℱ.le j) hL (hX2 j) (hmean j) (hle j)
  have hg := sq_div_two_div_nonneg_of_mem_Ioo hL hθ
  have hA : ∀ j, ∀ᵐ ω ∂μ, (μ[fun ω' => X j ω' ^ 2 | ℱ j] ω).PosSemidef := fun j =>
    Matrix.ae_posSemidef_condExp ((h j).ae_isHermitian.mono fun ω hω => by
      have h2 := Matrix.posSemidef_conjTranspose_mul_self (X j ω)
      rwa [hω.eq, ← sq] at h2)
  have hM := HasCondMatrixMGFBound.measure_exists_eigenvalue_zero_sum_ge_le hX h hθ hθ.1 hg
    (HasCondMatrixMGFBound.integrable_potential hX h hθ.1.le hg hle hA) t v
  have hsub : {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
      specNorm (∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω) ≤ v} ≤ᵐ[μ]
      {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
        ∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω ≤ v • (1 : Matrix n n 𝕜)} := by
    filter_upwards [ae_all_iff.mpr fun j => (h j).ae_isHermitian_bound] with ω hω
    rintro ⟨k, hk1, hk2⟩
    exact ⟨k, hk1, Matrix.IsHermitian.le_smul_one_of_specNorm_le
      (isSelfAdjoint_sum _ fun j _ => hω j) hk2⟩
  refine (measureReal_mono_ae' hsub).trans (hM.trans ?_)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθb) (Nat.cast_nonneg _)

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
  have hsub : {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0} ≤ᵐ[μ]
      {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
        specNorm (∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω) ≤ v} := by
    filter_upwards [ae_all_iff.mpr hv] with ω hω
    rintro ⟨k, hk⟩
    exact ⟨k, hk, hω k⟩
  exact (measureReal_mono_ae' hsub).trans
    (measureReal_exists_eigenvalue_zero_sum_ge_le_freedman hX hX2 hmean hL hle ht)

/-- **Freedman's inequality for rectangular matrix martingales.** For rectangular increments
`S j`, `ℱ (j + 1)`-measurable, square-integrable, conditionally centred and with
`‖S j‖ ≤ L` almost surely, the probability that for some `k` both `t ≤ ‖∑_{j<k} S j‖` and the
larger of the two predictable quadratic variations `‖∑_{j<k} E[S j S jᴴ | ℱ j]‖`,
`‖∑_{j<k} E[S jᴴ S j | ℱ j]‖` is at most `v` is at most
`(d₁ + d₂) exp (-(t²/2) / (v + L t / 3))`. [Tropp2011, Corollary 1.3]; over any `RCLike` field
and finite index types. The source's constant.
Proof: the Hermitian Freedman inequality for the dilations
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
  let D : Matrix r n 𝕜 →L[ℝ] Matrix (r ⊕ n) (r ⊕ n) 𝕜 := LinearMap.toContinuousLinearMap
    { toFun := dilation
      map_add' := dilation_add
      map_smul' := dilation_smul_real }
  have hDm : ∀ j, StronglyMeasurable[ℱ (j + 1)] (fun ω => dilation (S j ω)) := fun j =>
    D.continuous.comp_stronglyMeasurable (hS j)
  have hD2 : ∀ j, MemLp (fun ω => dilation (S j ω)) 2 μ := fun j => D.comp_memLp' (hS2 j)
  have hDmean : ∀ j, μ[fun ω => dilation (S j ω) | ℱ j] =ᵐ[μ] 0 := fun j => by
    filter_upwards [Matrix.condExp_dilation (m := ℱ j) ((hS2 j).integrable one_le_two),
      hmean j] with ω h1 h2
    rw [h1, h2, Pi.zero_apply, Pi.zero_apply, dilation_zero]
  have hDle : ∀ j, ∀ᵐ ω ∂μ, dilation (S j ω) ≤ L • (1 : Matrix (r ⊕ n) (r ⊕ n) 𝕜) := fun j =>
    (hle j).mono fun ω hω =>
      (isHermitian_dilation _).le_smul_one_of_specNorm_le (by rwa [specNorm_dilation])
  have hF := measureReal_exists_eigenvalue_zero_sum_ge_le_freedman (v := v) hDm hD2 hDmean hL
    hDle ht
  have hsq : ∀ᵐ ω ∂μ, ∀ j, μ[fun ω' => dilation (S j ω') ^ 2 | ℱ j] ω =
      Matrix.fromBlocks (μ[fun ω' => S j ω' * (S j ω')ᴴ | ℱ j] ω) 0 0
        (μ[fun ω' => (S j ω')ᴴ * S j ω' | ℱ j] ω) :=
    ae_all_iff.mpr fun j => Matrix.condExp_dilation_sq (hS2 j)
  have hsub : {ω | ∃ k, t ≤ specNorm (∑ j ∈ Finset.range k, S j ω) ∧
      max (specNorm (∑ j ∈ Finset.range k, μ[fun ω' => S j ω' * (S j ω')ᴴ | ℱ j] ω))
        (specNorm (∑ j ∈ Finset.range k, μ[fun ω' => (S j ω')ᴴ * S j ω' | ℱ j] ω)) ≤ v} ≤ᵐ[μ]
      {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, dilation (S j ω)) 0 ∧
        specNorm (∑ j ∈ Finset.range k, μ[fun ω' => dilation (S j ω') ^ 2 | ℱ j] ω) ≤ v} := by
    filter_upwards [hsq] with ω hω
    rintro ⟨k, hk1, hk2⟩
    refine ⟨k, ?_, ?_⟩
    · rwa [← dilation_sum, eigenvalue_zero_dilation]
    · rwa [Finset.sum_congr rfl fun j _ => hω j, Matrix.sum_fromBlocks, Finset.sum_const_zero,
        Finset.sum_const_zero, specNorm_fromBlocks_zero₁₂_zero₂₁]
  refine (measureReal_mono_ae' hsub).trans (hF.trans_eq ?_)
  rw [Fintype.card_sum, Nat.cast_add]

end NLAlib
