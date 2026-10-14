/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
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
* `NLAlib.HasLogSobolev.integrable_sq_mul_log_sq`,
  `NLAlib.HasLogSobolev.entropy_sq_le_of_integrable`: the inequality extends to every `C¹`
  function `g` with `g²` and `‖∇g‖²` integrable, and `g² log g²` is then integrable.
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

/-! ### Finite-energy test functions -/

section FiniteEnergy

omit [MeasurableSpace E] [BorelSpace E] in
/-- Smooth cutoffs `χ n = φ ((n + 1)⁻¹ • ·)`: `C¹`, compactly supported, with values in `[0, 1]`
and derivatives bounded uniformly in `n`, and eventually equal to `1` near every point. -/
private theorem exists_cutoff : ∃ (χ : ℕ → E → ℝ) (K : ℝ), (∀ n, ContDiff ℝ 1 (χ n)) ∧
    (∀ n, HasCompactSupport (χ n)) ∧ (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
    (∀ n x, ‖fderiv ℝ (χ n) x‖ ≤ K) ∧ (∀ x, ∀ᶠ n in atTop, χ n =ᶠ[𝓝 x] fun _ => 1) := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  have hφc : ContDiff ℝ 1 (fun x => φ x) := φ.contDiff
  obtain ⟨K, hK⟩ := (hφc.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have ha (n : ℕ) : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have ha1 (n : ℕ) : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hnorm (n : ℕ) (x : E) : ‖((n : ℝ) + 1)⁻¹ • x‖ = ((n : ℝ) + 1)⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (ha n).le]
  refine ⟨fun n x => φ (((n : ℝ) + 1)⁻¹ • x), K,
    fun n => hφc.comp (contDiff_const_smul _), fun n => ?_, fun n x => ⟨φ.nonneg, φ.le_one⟩,
    fun n x => ?_, fun x => ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * ((n : ℝ) + 1)))
      fun x hx => φ.zero_of_le_dist ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    rw [dist_zero_right, hnorm, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    exact hx.le
  · have h := ((hφc.differentiable one_ne_zero) (((n : ℝ) + 1)⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul ((n : ℝ) + 1)⁻¹)
    change ‖fderiv ℝ ((fun x => φ x) ∘ HSMul.hSMul ((n : ℝ) + 1)⁻¹) x‖ ≤ K
    rw [h.fderiv]
    calc ‖(fderiv ℝ (fun x => φ x) (((n : ℝ) + 1)⁻¹ • x)).comp
          (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E)‖
        ≤ ‖fderiv ℝ (fun x => φ x) (((n : ℝ) + 1)⁻¹ • x)‖ *
          ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * 1 := by
          gcongr
          · exact hK _
          · rw [norm_smul, Real.norm_of_nonneg (ha n).le]
            exact (mul_le_mul (ha1 n) (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
              zero_le_one).trans_eq (one_mul 1)
      _ = K := mul_one K
  · obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hx : ‖x‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    refine φ.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_zero_right, hnorm, ← div_eq_inv_mul,
      div_le_one (by positivity)]
    exact (show ‖y‖ < (n : ℝ) + 1 from hy).le

/-- The inequality for a bounded `C¹` function of finite energy, from the defining class by the
cutoffs `g χ n` and dominated convergence. -/
private theorem HasLogSobolev.entropy_sq_le_of_abs_le [IsProbabilityMeasure ν]
    (h : HasLogSobolev ν c) {g : E → ℝ} (hg : ContDiff ℝ 1 g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) ν) :
    entropy ν (fun x => g x ^ 2) ≤ 2 * c * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν := by
  obtain ⟨χ, K, hχc, hχs, hχ01, hχd, hχ1⟩ := exists_cutoff (E := E)
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  let gn : ℕ → E → ℝ := fun n x => g x * χ n x
  have hgnc (n : ℕ) : ContDiff ℝ 1 (gn n) := hg.mul (hχc n)
  have hgn_abs (n : ℕ) (x : E) : |gn n x| ≤ M := by
    obtain ⟨h0, h1⟩ := hχ01 n x
    rw [abs_mul, abs_of_nonneg h0]
    exact (mul_le_of_le_one_right (abs_nonneg _) h1).trans (hM x)
  have hgn_d (n : ℕ) : ∃ M', ∀ x, ‖fderiv ℝ (gn n) x‖ ≤ M' :=
    ((hgnc n).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      ((hχs n).mul_left.fderiv (𝕜 := ℝ))
  have hgn_dsq (n : ℕ) (x : E) :
      ‖fderiv ℝ (gn n) x‖ ^ 2 ≤ 2 * ‖fderiv ℝ g x‖ ^ 2 + 2 * (M * K) ^ 2 := by
    have hd : fderiv ℝ (gn n) x = g x • fderiv ℝ (χ n) x + χ n x • fderiv ℝ g x :=
      fderiv_fun_mul (hgd x) (((hχc n).differentiable one_ne_zero) x)
    obtain ⟨h0, h1⟩ := hχ01 n x
    have hb : ‖fderiv ℝ (gn n) x‖ ≤ M * K + ‖fderiv ℝ g x‖ := by
      rw [hd]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hM x) (hχd n x) (norm_nonneg _) ((abs_nonneg _).trans (hM x))
      · rw [norm_smul, Real.norm_of_nonneg h0]
        exact mul_le_of_le_one_left (norm_nonneg _) h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith [sq_nonneg (M * K - ‖fderiv ℝ g x‖)]
  have hev (x : E) : ∀ᶠ n in atTop, gn n x = g x ∧ fderiv ℝ (gn n) x = fderiv ℝ g x := by
    filter_upwards [hχ1 x] with n hn
    have : gn n =ᶠ[𝓝 x] g := hn.mono fun y hy => by simp only [gn, hy, mul_one]
    exact ⟨this.eq_of_nhds, this.fderiv_eq⟩
  have hineq (n : ℕ) : entropy ν (fun x => gn n x ^ 2) ≤
      2 * c * ∫ x, ‖fderiv ℝ (gn n) x‖ ^ 2 ∂ν :=
    h.entropy_sq_le (gn n) (hgnc n) ⟨M, hgn_abs n⟩ (hgn_d n)
  have hconst {F : ℕ → E → ℝ} {f : E → ℝ} (hF : ∀ x, ∀ᶠ n in atTop, F n x = f x) :
      ∀ᵐ x ∂ν, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    ae_of_all _ fun x => tendsto_const_nhds.congr' ((hF x).mono fun n hn => hn.symm)
  have hsq (n : ℕ) (x : E) : gn n x ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hgn_abs n x) 2
  have L1 : Tendsto (fun n => ∫ x, gn n x ^ 2 ∂ν) atTop (𝓝 (∫ x, g x ^ 2 ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M ^ 2)
      (fun n => ((hgnc n).continuous.pow 2).aestronglyMeasurable) (integrable_const _)
      (fun n => ae_of_all _ fun x => ?_) (hconst fun x => (hev x).mono fun n hn => by rw [hn.1])
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq n x
  have L2 : Tendsto (fun n => ∫ x, gn n x ^ 2 * Real.log (gn n x ^ 2) ∂ν) atTop
      (𝓝 (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (M ^ 2) ^ 2 + 1)
      (fun n => (Real.continuous_mul_log.comp ((hgnc n).continuous.pow 2)).aestronglyMeasurable)
      (integrable_const _) (fun n => ae_of_all _ fun x => ?_)
      (hconst fun x => (hev x).mono fun n hn => by rw [hn.1])
    rw [Real.norm_eq_abs]
    refine (Real.abs_mul_log_le_sq_add_one (sq_nonneg _)).trans ?_
    have := pow_le_pow_left₀ (sq_nonneg _) (hsq n x) 2
    linarith
  have L3 : Tendsto (fun n => ∫ x, ‖fderiv ℝ (gn n) x‖ ^ 2 ∂ν) atTop
      (𝓝 (∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * ‖fderiv ℝ g x‖ ^ 2 + 2 * (M * K) ^ 2)
      (fun n => (((hgnc n).continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable)
      ((hdg.const_mul 2).add (integrable_const _)) (fun n => ae_of_all _ fun x => ?_)
      (hconst fun x => (hev x).mono fun n hn => by rw [hn.2])
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hgn_dsq n x
  exact le_of_tendsto_of_tendsto (L2.sub ((Real.continuous_mul_log.tendsto _).comp L1))
    (L3.const_mul _) (Eventually.of_forall hineq)

variable [IsProbabilityMeasure ν] {g : E → ℝ}

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure ν] in
/-- The sine truncations `g_N = (N + 1) sin (g / (N + 1))` of a finite-energy `C¹` function: they
are bounded, `C¹`, with `g_N² ≤ g²` and `‖∇g_N‖² ≤ ‖∇g‖²`, and tend to `g` pointwise. -/
private theorem sineTrunc_facts (hg : ContDiff ℝ 1 g) (hg2 : Integrable (fun x => g x ^ 2) ν)
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) ν) (n : ℕ) :
    let gN : E → ℝ := fun x => ((n : ℝ) + 1) * Real.sin (((n : ℝ) + 1)⁻¹ * g x)
    ContDiff ℝ 1 gN ∧ (∀ x, |gN x| ≤ (n : ℝ) + 1) ∧ (∀ x, gN x ^ 2 ≤ g x ^ 2) ∧
      Integrable (fun x => gN x ^ 2) ν ∧
      (∀ x, ‖fderiv ℝ gN x‖ ^ 2 ≤ ‖fderiv ℝ g x‖ ^ 2) ∧
      Integrable (fun x => ‖fderiv ℝ gN x‖ ^ 2) ν := by
  intro gN
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcd : ContDiff ℝ 1 gN := contDiff_const.mul ((contDiff_const.mul hg).sin)
  have hsq (x : E) : gN x ^ 2 ≤ g x ^ 2 := sq_le_sq.2 (Real.abs_mul_sin_inv_mul_le _ _)
  have hdf (x : E) : ‖fderiv ℝ gN x‖ ^ 2 ≤ ‖fderiv ℝ g x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
    (norm_fderiv_mul_sin_inv_mul_le ((hg.differentiable one_ne_zero) x) _) 2
  refine ⟨hcd, fun x => ?_, hsq, ?_, hdf, ?_⟩
  · rw [abs_mul, abs_of_pos hc]
    exact mul_le_of_le_one_right hc.le (Real.abs_sin_le_one _)
  · refine hg2.mono' (hcd.continuous.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq x
  · refine hdg.mono' ((hcd.continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hdf x

/-- **A logarithmic Sobolev inequality controls the entropy of every finite-energy function.** If
`ν` satisfies `HasLogSobolev ν c` and `g` is `C¹` with `g²` and `‖∇g‖²` integrable, then
`g² log g²` is integrable, so `Ent_ν (g²)` is not a junk value. The proof applies the inequality
to the bounded truncations `(N + 1) sin (g / (N + 1))`, whose energy is at most that of `g`, and
uses Fatou's lemma. For the standard Gaussian this is
`NLAlib.integrable_sq_mul_log_sq_stdGaussian`.
Port of `NLAlib.HasEuclideanLogSobolev.integrable_sq_mul_log_sq`. -/
theorem HasLogSobolev.integrable_sq_mul_log_sq (h : HasLogSobolev ν c) (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) ν) (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) ν) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) ν := by
  let gN : ℕ → E → ℝ := fun n x => ((n : ℝ) + 1) * Real.sin (((n : ℝ) + 1)⁻¹ * g x)
  have hF (n : ℕ) := sineTrunc_facts hg hg2 hdg n
  have hNlog (n : ℕ) : Integrable (fun x => gN n x ^ 2 * Real.log (gN n x ^ 2)) ν := by
    obtain ⟨hcd, habs, -⟩ := hF n
    refine Integrable.of_bound
      (Real.continuous_mul_log.comp (hcd.continuous.pow 2)).aestronglyMeasurable
      ((((n : ℝ) + 1) ^ 2) ^ 2 + 1) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (Real.abs_mul_log_le_sq_add_one (sq_nonneg _)).trans ?_
    have h1 : gN n x ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (habs x) 2
    have := pow_le_pow_left₀ (sq_nonneg _) h1 2
    linarith
  set M := ∫ x, g x ^ 2 ∂ν
  set B := 2 * c * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν + M ^ 2 + 2
  let Fx : E → ℝ := fun x => g x ^ 2 * Real.log (g x ^ 2) + 1
  let FN : ℕ → E → ℝ := fun n x => gN n x ^ 2 * Real.log (gN n x ^ 2) + 1
  have hF0 (x : E) : 0 ≤ Fx x := by
    have h := Real.self_sub_one_le_mul_log (sq_nonneg (g x))
    simp only [Fx]
    nlinarith [sq_nonneg (g x)]
  have hFN0 (n : ℕ) (x : E) : 0 ≤ FN n x := by
    have h := Real.self_sub_one_le_mul_log (sq_nonneg (gN n x))
    simp only [FN]
    nlinarith [sq_nonneg (gN n x)]
  have hFNbound (n : ℕ) : ∫ x, FN n x ∂ν ≤ B := by
    obtain ⟨hcd, habs, hsq, hN2, hdf, hNdf⟩ := hF n
    have hlsi := h.entropy_sq_le_of_abs_le hcd habs hNdf
    rw [entropy] at hlsi
    have hm0 : 0 ≤ ∫ x, gN n x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have hmLog := Real.abs_mul_log_le_sq_add_one hm0
    have hmSq := pow_le_pow_left₀ hm0 (integral_mono hN2 hg2 hsq) 2
    have he := mul_le_mul_of_nonneg_left (integral_mono hNdf hdg hdf)
      (by positivity : (0 : ℝ) ≤ 2 * c)
    have ha := le_abs_self ((∫ x, gN n x ^ 2 ∂ν) * Real.log (∫ x, gN n x ^ 2 ∂ν))
    simp only [FN]
    rw [integral_add (hNlog n) (integrable_const _), integral_const, probReal_univ, one_smul]
    linarith
  have hFatou : ∫⁻ x, ENNReal.ofReal (Fx x) ∂ν ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (FN n x) ∂ν) atTop := by
    calc ∫⁻ x, ENNReal.ofReal (Fx x) ∂ν
        = ∫⁻ x, liminf (fun n => ENNReal.ofReal (FN n x)) atTop ∂ν := by
          refine lintegral_congr fun x => (Tendsto.liminf_eq ?_).symm
          have hlim : Tendsto (fun n => gN n x) atTop (𝓝 (g x)) :=
            Real.tendsto_natCast_add_one_mul_sin_inv_mul (g x)
          exact (ENNReal.continuous_ofReal.tendsto _).comp
            (((Real.continuous_mul_log.tendsto _).comp (hlim.pow 2)).add tendsto_const_nhds)
      _ ≤ _ := lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp
          ((Real.continuous_mul_log.comp ((hF n).1.continuous.pow 2)).add
            continuous_const).measurable
  have hLiminf : liminf (fun n => ∫⁻ x, ENNReal.ofReal (FN n x) ∂ν) atTop ≤ ENNReal.ofReal B := by
    refine (liminf_le_liminf (Eventually.of_forall fun n => ?_)).trans_eq (liminf_const _)
    have hi : Integrable (FN n) ν := (hNlog n).add (integrable_const _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hFN0 n))]
    exact ENNReal.ofReal_le_ofReal (hFNbound n)
  have hFi := (lintegral_ofReal_ne_top_iff_integrable
    ((Real.continuous_mul_log.comp (hg.continuous.pow 2)).add continuous_const).aestronglyMeasurable
    (ae_of_all _ hF0)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hFatou.trans hLiminf))
  exact (hFi.sub (integrable_const (1 : ℝ))).congr (ae_of_all _ fun x => by simp)

/-- **The logarithmic Sobolev inequality for finite-energy functions.** If `ν` satisfies
`HasLogSobolev ν c`, then `Ent_ν (g²) ≤ 2 c E_ν ‖∇g‖²` for every `C¹` function `g` with `g²` and
`‖∇g‖²` integrable, not only for the bounded test functions of the definition; `g² log g²` is then
integrable (`NLAlib.HasLogSobolev.integrable_sq_mul_log_sq`). The truncations
`(N + 1) sin (g / (N + 1))` and dominated convergence. For the standard Gaussian this is
`NLAlib.entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian`.
Port of `NLAlib.HasEuclideanLogSobolev.inequality_of_integrable`. -/
theorem HasLogSobolev.entropy_sq_le_of_integrable (h : HasLogSobolev ν c) (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) ν) (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) ν) :
    entropy ν (fun x => g x ^ 2) ≤ 2 * c * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν := by
  let gN : ℕ → E → ℝ := fun n x => ((n : ℝ) + 1) * Real.sin (((n : ℝ) + 1)⁻¹ * g x)
  have hF (n : ℕ) := sineTrunc_facts hg hg2 hdg n
  have hglog := h.integrable_sq_mul_log_sq hg hg2 hdg
  have hlim (x : E) : Tendsto (fun n => gN n x) atTop (𝓝 (g x)) :=
    Real.tendsto_natCast_add_one_mul_sin_inv_mul (g x)
  have hineq (n : ℕ) : entropy ν (fun x => gN n x ^ 2) ≤
      2 * c * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν := by
    obtain ⟨hcd, habs, hsq, hN2, hdf, hNdf⟩ := hF n
    exact (h.entropy_sq_le_of_abs_le hcd habs hNdf).trans
      (mul_le_mul_of_nonneg_left (integral_mono hNdf hdg hdf) (by positivity))
  have L1 : Tendsto (fun n => ∫ x, gN n x ^ 2 ∂ν) atTop (𝓝 (∫ x, g x ^ 2 ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => g x ^ 2)
      (fun n => ((hF n).1.continuous.pow 2).aestronglyMeasurable) hg2
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => (hlim x).pow 2)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact (hF n).2.2.1 x
  have L2 : Tendsto (fun n => ∫ x, gN n x ^ 2 * Real.log (gN n x ^ 2) ∂ν) atTop
      (𝓝 (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |g x ^ 2 * Real.log (g x ^ 2)| + g x ^ 2)
      (fun n => (Real.continuous_mul_log.comp ((hF n).1.continuous.pow 2)).aestronglyMeasurable)
      (hglog.abs.add hg2) (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => (Real.continuous_mul_log.tendsto _).comp ((hlim x).pow 2))
    rw [Real.norm_eq_abs]
    have hsq := (hF n).2.2.1 x
    by_cases hx : g x = 0
    · have h0 : gN n x = 0 := by simp only [gN, hx, mul_zero, Real.sin_zero]
      simp only [h0, hx]
      norm_num
    have hpos : 0 < g x ^ 2 := by positivity
    have e : gN n x ^ 2 = g x ^ 2 * (gN n x ^ 2 / g x ^ 2) := by field_simp
    rw [e]
    exact Real.abs_mul_mul_log_mul_le hpos.le (by positivity) ((div_le_one hpos).2 hsq)
  exact le_of_tendsto (L2.sub ((Real.continuous_mul_log.tendsto _).comp L1))
    (Eventually.of_forall hineq)

end FiniteEnergy

end NLAlib
