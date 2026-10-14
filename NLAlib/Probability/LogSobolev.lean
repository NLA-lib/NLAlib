/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import NLAlib.ForMathlib.Analysis.Calculus.BumpFunction.Convolution
public import NLAlib.Probability.Entropy

/-!
# Logarithmic Sobolev inequalities and concentration

`NLAlib.HasLogSobolev ν c` says that the law `ν` on a Euclidean space satisfies a logarithmic
Sobolev inequality with constant `c`: `Ent_ν (g²) ≤ 2 c E_ν ‖∇g‖²` for every bounded `C¹` function
`g` with bounded derivative. The class of test functions keeps every integral finite. Herbst's
argument turns it into concentration: a Lipschitz function of a law with such an inequality is
sub-Gaussian about its mean with proxy `c L²`. The standard Gaussian satisfies it with `c = 1`
(`NLAlib.hasLogSobolev_stdGaussian`).

## Main definitions

* `NLAlib.HasLogSobolev ν c`.

## Main results

* `NLAlib.HasLogSobolev.integrable_of_lipschitzWith`.
* `NLAlib.HasLogSobolev.hasSubgaussianMGF_sub_integral`: concentration of Lipschitz functions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real
open scoped NNReal ENNReal Topology

namespace NLAlib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `ν` satisfies a logarithmic Sobolev inequality with constant `c`: for every bounded `C¹`
function `g` with bounded derivative, `Ent_ν (g²) ≤ 2 c E_ν ‖∇g‖²`. -/
structure HasLogSobolev (ν : Measure E) (c : ℝ≥0) : Prop where
  /-- The inequality, for bounded `C¹` test functions with bounded derivative. -/
  entropy_sq_le : ∀ g : E → ℝ, ContDiff ℝ 1 g → (∃ M, ∀ x, |g x| ≤ M) →
    (∃ M, ∀ x, ‖fderiv ℝ g x‖ ≤ M) →
    entropy ν (fun x => g x ^ 2) ≤ 2 * c * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν

variable {ν : Measure E} {c : ℝ≥0}

/-! ### Auxiliary facts -/

section Aux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

private theorem integrable_of_abs_le [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : Continuous F)
    {M : ℝ} (hM : ∀ x, |F x| ≤ M) : Integrable F μ :=
  (integrable_const M).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hM x)

private theorem integrable_exp_mul_of_abs_le [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [IsFiniteMeasure μ] {F : Ω → ℝ} (hF : Continuous F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) (s : ℝ) :
    Integrable (fun x => rexp (s * F x)) μ := by
  refine integrable_of_abs_le (by fun_prop) (M := rexp (|s| * M)) fun x => ?_
  rw [abs_of_pos (exp_pos _), exp_le_exp]
  calc s * F x ≤ |s * F x| := le_abs_self _
    _ = |s| * |F x| := abs_mul _ _
    _ ≤ |s| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg s)

private theorem exp_mul_sub (s m u : ℝ) : rexp (s * (u - m)) = rexp (s * u) * rexp (-(s * m)) := by
  rw [← exp_add]; ring_nf

/-- From a sub-Gaussian bound on `X - m` to the uncentred bound on `E e^{s X}`. -/
private theorem integral_exp_le_of_hasSubgaussianMGF {X : Ω → ℝ} {m : ℝ} {q : ℝ≥0}
    (hX : HasSubgaussianMGF (fun x => X x - m) q μ) (s : ℝ) :
    ∫ x, rexp (s * X x) ∂μ ≤ rexp (s * m + q * s ^ 2 / 2) := by
  have h1 := hX.mgf_le s
  rw [mgf] at h1
  simp only [exp_mul_sub] at h1
  rw [integral_mul_const] at h1
  calc ∫ x, rexp (s * X x) ∂μ = (∫ x, rexp (s * X x) ∂μ) * rexp (-(s * m)) * rexp (s * m) := by
        rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    _ ≤ rexp (q * s ^ 2 / 2) * rexp (s * m) := mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = _ := by rw [← exp_add, add_comm]

/-- From the uncentred bound on `E e^{s X}` to a sub-Gaussian bound on `X - m`. -/
private theorem hasSubgaussianMGF_of_integral_exp_le {X : Ω → ℝ} {m : ℝ} {q : ℝ≥0}
    (h : ∀ s, Integrable (fun x => rexp (s * X x)) μ ∧
      ∫ x, rexp (s * X x) ∂μ ≤ rexp (s * m + q * s ^ 2 / 2)) :
    HasSubgaussianMGF (fun x => X x - m) q μ := by
  refine ⟨fun s => ?_, fun s => ?_⟩
  · simp only [exp_mul_sub]
    exact (h s).1.mul_const _
  · rw [mgf]
    simp only [exp_mul_sub]
    rw [integral_mul_const]
    calc (∫ x, rexp (s * X x) ∂μ) * rexp (-(s * m))
        ≤ rexp (s * m + q * s ^ 2 / 2) * rexp (-(s * m)) :=
          mul_le_mul_of_nonneg_right (h s).2 (exp_pos _).le
      _ = rexp (q * s ^ 2 / 2) := by rw [← exp_add]; ring_nf

/-- Fatou's lemma in the form used twice below: nonnegative integrable `F n → g` pointwise with
`∫ F n ≤ b n → B` gives `g` integrable with `∫ g ≤ B`. -/
private theorem integrable_and_integral_le_of_tendsto {F : ℕ → Ω → ℝ} {g : Ω → ℝ} {b : ℕ → ℝ}
    {B : ℝ} (hg : AEStronglyMeasurable g μ) (hint : ∀ n, Integrable (F n) μ)
    (hpos : ∀ n x, 0 ≤ F n x) (hconv : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (g x)))
    (hbound : ∀ n, ∫ x, F n x ∂μ ≤ b n) (hb : Tendsto b atTop (𝓝 B)) :
    Integrable g μ ∧ ∫ x, g x ∂μ ≤ B := by
  have hg0 : ∀ x, 0 ≤ g x := fun x => ge_of_tendsto' (hconv x) fun n => hpos n x
  have hB : 0 ≤ B := ge_of_tendsto' hb fun n => (integral_nonneg (hpos n)).trans (hbound n)
  have hf := lintegral_liminf_le' (u := (atTop : Filter ℕ))
    (f := fun n x => ENNReal.ofReal (F n x))
    (fun n => (hint n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have heq : ∀ x, liminf (fun n => ENNReal.ofReal (F n x)) atTop = ENNReal.ofReal (g x) :=
    fun x => (ENNReal.tendsto_ofReal (hconv x)).liminf_eq
  simp only [heq] at hf
  have hle : ∫⁻ x, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal B := by
    refine hf.trans ?_
    refine (liminf_le_liminf (Eventually.of_forall fun n => ?_)).trans_eq
      (ENNReal.tendsto_ofReal hb).liminf_eq
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (hpos n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hgi : Integrable g μ :=
    ⟨hg, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2 (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hgi, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff hB, ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0)]
  exact hle

/-- A uniform bound for the mean of `F` from the uncentred sub-Gaussian bound, using a set of
positive mass on which `F` is bounded. -/
private theorem abs_integral_le_of_integral_exp_le [IsProbabilityMeasure μ] {F : Ω → ℝ}
    (hexp : ∀ s, Integrable (fun x => rexp (s * F x)) μ) {q : ℝ}
    (hraw : ∀ s, ∫ x, rexp (s * F x) ∂μ ≤ rexp (s * ∫ x, F x ∂μ + q * s ^ 2 / 2))
    {A : Set Ω} (hA : MeasurableSet A) (hδ : 0 < μ.real A) {a : ℝ} (hOnA : ∀ x ∈ A, |F x| ≤ a) :
    |∫ x, F x ∂μ| ≤ a + q / 2 - Real.log (μ.real A) := by
  have hlog (s : ℝ) (hs : |s| = 1) :
      Real.log (μ.real A) - a ≤ s * ∫ x, F x ∂μ + q / 2 := by
    have hpoint : ∀ x, A.indicator (fun _ => rexp (-a)) x ≤ rexp (s * F x) := by
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, exp_le_exp]
        have habs : |s * F x| ≤ a := by rw [abs_mul, hs, one_mul]; exact hOnA x hx
        exact (abs_le.mp habs).1
      · rw [Set.indicator_of_notMem hx]
        exact (exp_pos _).le
    have hi := integral_mono ((integrable_const (rexp (-a))).indicator hA) (hexp s) hpoint
    rw [integral_indicator_const _ hA, smul_eq_mul] at hi
    have h := Real.log_le_log (mul_pos hδ (exp_pos _)) (hi.trans (hraw s))
    have hs2 : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
    rw [Real.log_mul hδ.ne' (exp_pos _).ne', Real.log_exp, Real.log_exp, hs2] at h
    linarith
  have hup := hlog (-1) (by norm_num)
  have hlo := hlog 1 (by norm_num)
  rw [abs_le]
  constructor <;> linarith

private theorem abs_le_exp_add_exp_neg (u : ℝ) : |u| ≤ rexp (1 * u) + rexp (-1 * u) := by
  rw [one_mul, neg_one_mul]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    linarith [add_one_le_exp u, exp_pos (-u)]
  · rw [abs_of_nonpos hu]
    linarith [add_one_le_exp (-u), exp_pos u]

end Aux

/-! ### Bounded smooth Lipschitz functions -/

omit [FiniteDimensional ℝ E] in
/-- Herbst's argument for a bounded `C¹` `L`-Lipschitz `f`: the predicate applied to
`exp (s f / 2)` gives `Ent (e^{s f}) ≤ c L² s² / 2 · E e^{s f}`. -/
private theorem HasLogSobolev.hasSubgaussianMGF_of_bounded [IsProbabilityMeasure ν]
    (h : HasLogSobolev ν c) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hfc : ContDiff ℝ 1 f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂ν) (c * L ^ 2) ν := by
  have hint := integrable_exp_mul_of_abs_le (μ := ν) hfc.continuous hM
  refine hasSubgaussianMGF_sub_integral_of_entropy_le hint fun s => ?_
  set g : E → ℝ := fun x => rexp (s / 2 * f x) with hgdef
  have hgc : ContDiff ℝ 1 g := contDiff_exp.comp (contDiff_const.mul hfc)
  have hg2 : ∀ x, g x ^ 2 = rexp (s * f x) := fun x => by
    rw [hgdef, ← exp_nat_mul]; congr 1; push_cast; ring
  have hdf : ∀ x, fderiv ℝ g x = rexp (s / 2 * f x) • (s / 2) • fderiv ℝ f x := fun x =>
    (((hfc.differentiable one_ne_zero x).hasFDerivAt.const_mul (s / 2)).exp).fderiv
  have hnf : ∀ x, ‖fderiv ℝ g x‖ = g x * (|s| / 2 * ‖fderiv ℝ f x‖) := fun x => by
    rw [hdf, norm_smul, norm_smul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs,
      abs_div, abs_two]
  have hLf : ∀ x, ‖fderiv ℝ f x‖ ≤ L := fun x => norm_fderiv_le_of_lipschitz ℝ hf
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hgB : ∀ x, g x ≤ rexp (|s| * M) := fun x => by
    rw [hgdef, exp_le_exp]
    have := abs_le.mp (hM x)
    have := abs_nonneg s
    rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hs]; nlinarith
    · rw [abs_of_nonpos hs]; nlinarith
  have hsq : ∀ x, ‖fderiv ℝ g x‖ ^ 2 ≤ s ^ 2 / 4 * L ^ 2 * rexp (s * f x) := fun x => by
    rw [hnf, ← hg2, mul_pow, mul_pow, div_pow, sq_abs]
    have : ‖fderiv ℝ f x‖ ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hLf x) 2
    have h0 : 0 ≤ g x ^ 2 * (s ^ 2 / 2 ^ 2) := by positivity
    nlinarith
  have hbd : ∃ B, ∀ x, ‖fderiv ℝ g x‖ ≤ B := ⟨rexp (|s| * M) * (|s| / 2 * L), fun x => by
    rw [hnf]
    exact mul_le_mul (hgB x) (mul_le_mul_of_nonneg_left (hLf x) (by positivity))
      (by positivity) (exp_pos _).le⟩
  have hgabs : ∃ B, ∀ x, |g x| ≤ B :=
    ⟨rexp (|s| * M), fun x => by rw [abs_of_pos (exp_pos _)]; exact hgB x⟩
  have key := h.entropy_sq_le g hgc hgabs hbd
  simp only [hg2] at key
  have hdi : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) ν := by
    refine ((hint s).const_mul (s ^ 2 / 4 * L ^ 2)).mono'
      ((hgc.continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hsq x
  refine key.trans ?_
  calc 2 * (c : ℝ) * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν
      ≤ 2 * c * ∫ x, s ^ 2 / 4 * L ^ 2 * rexp (s * f x) ∂ν :=
        mul_le_mul_of_nonneg_left (integral_mono hdi ((hint s).const_mul _) hsq) (by positivity)
    _ = _ := by rw [integral_const_mul]; push_cast; ring

/-! ### Smooth bounded approximation -/

private theorem abs_clamp_le {a : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    |max (-a) (min a u)| ≤ a ∧ |max (-a) (min a u)| ≤ |u| := by
  refine ⟨abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩,
    abs_le.2 ⟨le_max_of_le_right (le_min (by linarith [abs_nonneg u]) (neg_abs_le u)),
      max_le (by linarith [abs_nonneg u]) ((min_le_right _ _).trans (le_abs_self u))⟩⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- An `L`-Lipschitz `f` is the pointwise limit of `C¹` `L`-Lipschitz functions `F n` with
`|F n| ≤ n + 2` and `|F n| ≤ |f| + 1`: clamp to `[-(n + 1), n + 1]`, then mollify. -/
private theorem exists_bounded_contDiff_lipschitzWith_tendsto {f : E → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) :
    ∃ F : ℕ → E → ℝ, (∀ n, ContDiff ℝ 1 (F n)) ∧ (∀ n, LipschitzWith L (F n)) ∧
      (∀ n x, |F n x| ≤ n + 2) ∧ (∀ n x, |F n x| ≤ |f x| + 1) ∧
      ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
  have hH : ∀ n : ℕ, LipschitzWith L fun x => max (-((n : ℝ) + 1)) (min ((n : ℝ) + 1) (f x)) :=
    fun n => (hf.const_min _).const_max _
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose F hFc hFL hFd using fun n => (hH n).exists_contDiff_lipschitzWith_dist_le (hε n)
  have hε1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n =>
    (div_le_one (by positivity)).2 (by linarith [n.cast_nonneg (α := ℝ)])
  have hdist : ∀ n x, |F n x - max (-((n : ℝ) + 1)) (min ((n : ℝ) + 1) (f x))| ≤ 1 :=
    fun n x => (by simpa only [Real.dist_eq] using hFd n x : _ ≤ _).trans (hε1 n)
  refine ⟨F, fun n => (hFc n).of_le (by exact_mod_cast le_top), hFL, fun n x => ?_,
    fun n x => ?_, fun x => ?_⟩
  · have := (abs_clamp_le (by positivity : (0 : ℝ) ≤ n + 1) (f x)).1
    have := abs_sub_abs_le_abs_sub (F n x) (max (-((n : ℝ) + 1)) (min ((n : ℝ) + 1) (f x)))
    linarith [hdist n x]
  · have := (abs_clamp_le (by positivity : (0 : ℝ) ≤ n + 1) (f x)).2
    have := abs_sub_abs_le_abs_sub (F n x) (max (-((n : ℝ) + 1)) (min ((n : ℝ) + 1) (f x)))
    linarith [hdist n x]
  · obtain ⟨N, hN⟩ := exists_nat_ge |f x|
    have hap : ∀ᶠ n : ℕ in atTop, dist (F n x) (f x) ≤ 1 / ((n : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
      obtain ⟨hlo, hhi⟩ := abs_le.mp (show |f x| ≤ (n : ℝ) + 1 by linarith)
      have := hFd n x
      rwa [min_eq_right hhi, max_eq_right hlo] at this
    exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun n =>
      dist_nonneg) hap tendsto_one_div_add_atTop_nhds_zero_nat)


/-- A Lipschitz function is integrable for a law with a logarithmic Sobolev inequality. -/
theorem HasLogSobolev.integrable_of_lipschitzWith [IsProbabilityMeasure ν]
    (h : HasLogSobolev ν c) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable f ν := by
  obtain ⟨F, hFc, hFL, hFb, hDom, hConv⟩ := exists_bounded_contDiff_lipschitzWith_tendsto hf
  have hInt n : Integrable (F n) ν := integrable_of_abs_le (hFc n).continuous (hFb n)
  have hExp n := integrable_exp_mul_of_abs_le (μ := ν) (hFc n).continuous (hFb n)
  have hRaw n := integral_exp_le_of_hasSubgaussianMGF
    (h.hasSubgaussianMGF_of_bounded (hFL n) (hFc n) (hFb n))
  set q : ℝ := ((c * L ^ 2 : ℝ≥0) : ℝ)
  have hUnion : (⋃ n : ℕ, {x | |f x| ≤ n}) = Set.univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (exists_nat_ge |f x|)
  obtain ⟨a, ha⟩ := exists_measure_pos_of_not_measure_iUnion_null (μ := ν)
    (s := fun n : ℕ => {x | |f x| ≤ n}) (by rw [hUnion]; simp)
  have hA : MeasurableSet {x | |f x| ≤ (a : ℝ)} :=
    measurableSet_le hf.continuous.abs.measurable measurable_const
  have hδ : 0 < ν.real {x | |f x| ≤ (a : ℝ)} := ENNReal.toReal_pos ha.ne' (measure_ne_top _ _)
  set U := (a : ℝ) + 1 + q / 2 - Real.log (ν.real {x | |f x| ≤ (a : ℝ)})
  have hMean n : |∫ x, F n x ∂ν| ≤ U :=
    abs_integral_le_of_integral_exp_le (hExp n) (hRaw n) hA hδ fun x (hx : |f x| ≤ a) =>
      (hDom n x).trans (by linarith)
  have hAbs n : ∫ x, |F n x| ∂ν ≤ 2 * rexp (U + q / 2) := by
    have h1 := (hRaw n 1).trans (exp_le_exp.2 (by linarith [(abs_le.mp (hMean n)).2]) :
      _ ≤ rexp (U + q / 2))
    have h2 := (hRaw n (-1)).trans (exp_le_exp.2 (by linarith [(abs_le.mp (hMean n)).1]) :
      _ ≤ rexp (U + q / 2))
    calc ∫ x, |F n x| ∂ν ≤ ∫ x, rexp (1 * F n x) + rexp (-1 * F n x) ∂ν :=
          integral_mono (hInt n).abs ((hExp n 1).add (hExp n (-1)))
            fun x => abs_le_exp_add_exp_neg _
      _ ≤ _ := by rw [integral_add (hExp n 1) (hExp n (-1))]; linarith
  have hfa := (integrable_and_integral_le_of_tendsto hf.continuous.abs.aestronglyMeasurable
    (fun n => (hInt n).abs) (fun n x => abs_nonneg (F n x)) (fun x => (hConv x).abs) hAbs
    tendsto_const_nhds).1
  exact hfa.mono' hf.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => (Real.norm_eq_abs _).le)

/-- **Concentration from a logarithmic Sobolev inequality**: a Lipschitz function of a law with
a logarithmic Sobolev inequality with constant `c` is sub-Gaussian about its mean with proxy
`c L²` (Herbst's argument, after smoothing and truncating `f`). -/
theorem HasLogSobolev.hasSubgaussianMGF_sub_integral [IsProbabilityMeasure ν]
    (h : HasLogSobolev ν c) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂ν) (c * L ^ 2) ν := by
  have hfi := h.integrable_of_lipschitzWith hf
  obtain ⟨F, hFc, hFL, hFb, hDom, hConv⟩ := exists_bounded_contDiff_lipschitzWith_tendsto hf
  have hMean : Tendsto (fun n => ∫ x, F n x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun x => |f x| + 1)
      (fun n => (hFc n).continuous.aestronglyMeasurable) (hfi.abs.add (integrable_const 1))
      (fun n => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hDom n x)
      (ae_of_all _ hConv)
  refine hasSubgaussianMGF_of_integral_exp_le fun s => ?_
  refine integrable_and_integral_le_of_tendsto (by fun_prop)
    (fun n => integrable_exp_mul_of_abs_le (hFc n).continuous (hFb n) s)
    (fun n x => (exp_pos _).le)
    (fun x => (continuous_exp.tendsto _).comp ((hConv x).const_mul s))
    (fun n => integral_exp_le_of_hasSubgaussianMGF
      (h.hasSubgaussianMGF_of_bounded (hFL n) (hFc n) (hFb n)) s) ?_
  exact (continuous_exp.tendsto _).comp ((hMean.const_mul s).add_const _)

end NLAlib
