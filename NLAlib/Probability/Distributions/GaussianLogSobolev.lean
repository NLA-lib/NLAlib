/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import NLAlib.Probability.Distributions.Gaussian
public import NLAlib.Probability.Distributions.GaussianLogSobolevOneDim
public import NLAlib.Probability.EntropyTensorization
public import NLAlib.Probability.LogSobolev

/-!
# Gross's logarithmic Sobolev inequality

For the standard Gaussian, `Ent (g²) ≤ 2 E ‖∇g‖²` for every `C¹` function `g` with `g²` and
`‖∇g‖²` integrable; then `g² log g²` is integrable too, so the entropy is not a junk value. The
one-dimensional inequality is proved first and tensorized. The standard Gaussian on a Euclidean
space therefore satisfies `NLAlib.HasLogSobolev` with constant `1`.

## Main results

* `NLAlib.entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal`: Gross's inequality on `ℝ`.
* `NLAlib.entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian`: on a Euclidean space.
* `NLAlib.hasLogSobolev_stdGaussian`.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Theorem 5.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace NLAlib
private lemma norm_fderiv_sq_eq (g : ℝ → ℝ) (x : ℝ) : ‖fderiv ℝ g x‖ ^ 2 = deriv g x ^ 2 := by
  rw [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs, sq_abs]

/-! ### From compact support to the integrable case on the line -/

/-- `|(G s) log (G s)| ≤ |G log G| + G` for `G ≥ 0` and `s ∈ [0, 1]`. -/
private lemma abs_mul_mul_log_le {G s : ℝ} (hG : 0 ≤ G) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |G * s * Real.log (G * s)| ≤ |G * Real.log G| + G := by
  rcases hG.eq_or_lt with rfl | hG'
  · simp
  rcases hs0.eq_or_lt with rfl | hs'
  · simp only [mul_zero, zero_mul, abs_zero]; positivity
  rw [Real.log_mul hG'.ne' hs'.ne']
  have e : G * s * (Real.log G + Real.log s) = s * (G * Real.log G) + G * (Real.log s * s) := by
    ring
  rw [e]
  have h1 := Real.abs_log_mul_self_lt s hs' hs1
  calc |s * (G * Real.log G) + G * (Real.log s * s)|
      ≤ |s * (G * Real.log G)| + |G * (Real.log s * s)| := abs_add_le _ _
    _ = s * |G * Real.log G| + G * |Real.log s * s| := by
        rw [abs_mul s (G * Real.log G), abs_mul G (Real.log s * s), abs_of_nonneg hs0,
          abs_of_nonneg hG]
    _ ≤ 1 * |G * Real.log G| + G * 1 := by gcongr
    _ = |G * Real.log G| + G := by ring

/-- Smooth cutoffs `c n = χ (· / (n + 1))`: `C¹`, compactly supported, with values in `[0, 1]`
and derivatives bounded uniformly in `n`, and eventually equal to `1` near every point. -/
private lemma exists_cutoff : ∃ (c : ℕ → ℝ → ℝ) (K : ℝ), (∀ n, ContDiff ℝ 1 (c n)) ∧
    (∀ n, HasCompactSupport (c n)) ∧ (∀ n x, 0 ≤ c n x ∧ c n x ≤ 1) ∧
    (∀ n x, |deriv (c n) x| ≤ K) ∧ (∀ x, ∀ᶠ n in atTop, c n =ᶠ[𝓝 x] fun _ => 1) := by
  -- a fixed smooth cutoff `χ`, equal to `1` on `[-1,1]` and supported in `[-2,2]`
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hχc : ContDiff ℝ 1 (fun x => χ x) := χ.contDiff
  obtain ⟨K, hK⟩ := (hχc.continuous_deriv le_rfl).bounded_above_of_compact_support
    χ.hasCompactSupport.deriv
  have hnpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hc_one : ∀ (n : ℕ) (x : ℝ), |x| < (n : ℝ) + 1 → χ (x / ((n : ℝ) + 1)) = 1 := by
    intro n x hx
    apply χ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_div,
      abs_of_pos (hnpos n), div_le_one (hnpos n)]
    exact hx.le
  refine ⟨fun n x => χ (x / ((n : ℝ) + 1)), K, fun n => hχc.comp (contDiff_id.div_const _),
    fun n => ?_, fun n x => ⟨χ.nonneg, χ.le_one⟩, fun n x => ?_, fun x => ?_⟩
  · apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * ((n : ℝ) + 1)))
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    apply χ.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos (hnpos n), le_div_iff₀ (hnpos n)]
    exact hx.le
  · have h1 : HasDerivAt (fun x : ℝ => x / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) x :=
      (hasDerivAt_id x).div_const _
    have h2 := ((hχc.differentiable one_ne_zero) (x / ((n : ℝ) + 1))).hasDerivAt.comp x h1
    have h2' : deriv (fun x => χ (x / ((n : ℝ) + 1))) x =
        deriv (fun x => χ x) (x / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) := h2.deriv
    rw [h2', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]
    have := hK (x / ((n : ℝ) + 1))
    rw [Real.norm_eq_abs] at this
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (hnpos n)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    nlinarith [abs_nonneg (deriv (fun x => χ x) (x / ((n : ℝ) + 1)))]
  · refine eventually_atTop.2 ⟨⌈|x|⌉₊, fun n hn => ?_⟩
    have hx : |x| < (n : ℝ) + 1 := by
      have := Nat.le_ceil |x|
      have : (⌈|x|⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
    exact hc_one n y hy

/-- Gross's inequality on `ℝ` for `g` with `g²`, `g² log g²` and `g'²` integrable, from the
compactly supported case by a smooth cutoff `g χ(·/(n+1))` and dominated convergence. -/
private lemma entropy_sq_le_gaussianReal_of_integrable {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    entropy (gaussianReal 0 1) (fun x => g x ^ 2) ≤ 2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 := by
  obtain ⟨c, K, hc_contDiff, hc_supp, hc01, hc_deriv_bound, hc_one⟩ := exists_cutoff
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  let gn : ℕ → ℝ → ℝ := fun n x => g x * c n x
  have hgn_contDiff : ∀ n, ContDiff ℝ 1 (gn n) := fun n => hg.mul (hc_contDiff n)
  have hgn_deriv_sq : ∀ n x, deriv (gn n) x ^ 2 ≤ 2 * deriv g x ^ 2 + 2 * K ^ 2 * g x ^ 2 := by
    intro n x
    have hd : deriv (gn n) x = deriv g x * c n x + g x * deriv (c n) x :=
      ((hgd x).hasDerivAt.mul (((hc_contDiff n).differentiable one_ne_zero) x).hasDerivAt).deriv
    rw [hd]
    obtain ⟨h0, h1⟩ := hc01 n x
    have hc2 : c n x ^ 2 ≤ 1 := by nlinarith
    have e1 : (deriv g x * c n x) ^ 2 ≤ deriv g x ^ 2 := by
      rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg (deriv g x))]
    have hd2 : deriv (c n) x ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hc_deriv_bound n x) 2
    have e2 : (g x * deriv (c n) x) ^ 2 ≤ K ^ 2 * g x ^ 2 := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
    nlinarith [sq_nonneg (deriv g x * c n x - g x * deriv (c n) x)]
  -- pointwise eventual equality
  have hev : ∀ x, ∀ᶠ n in atTop, gn n x = g x ∧ deriv (gn n) x = deriv g x := by
    intro x
    filter_upwards [hc_one x] with n hn
    have : gn n =ᶠ[𝓝 x] g := hn.mono fun y hy => by simp only [gn, hy, mul_one]
    exact ⟨this.eq_of_nhds, this.deriv_eq⟩
  have hineq : ∀ n, entropy (gaussianReal 0 1) (fun x => gn n x ^ 2) ≤
      2 * ∫ x, deriv (gn n) x ^ 2 ∂gaussianReal 0 1 := fun n =>
    entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal_of_hasCompactSupport (hgn_contDiff n)
      (hc_supp n).mul_left
  have hgn_cont : ∀ n, Continuous (gn n) := fun n => (hgn_contDiff n).continuous
  have hconst : ∀ {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}, (∀ x, ∀ᶠ n in atTop, F n x = f x) →
      ∀ᵐ x ∂gaussianReal 0 1, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := fun h =>
    ae_of_all _ fun x => tendsto_const_nhds.congr' ((h x).mono fun n hn => hn.symm)
  have L1 : Tendsto (fun n => ∫ x, gn n x ^ 2 ∂gaussianReal 0 1) atTop
      (𝓝 (∫ x, g x ^ 2 ∂gaussianReal 0 1)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => g x ^ 2)
      (fun n => ((hgn_cont n).pow 2).aestronglyMeasurable) hg2 (fun n => ae_of_all _ fun x => ?_)
      (hconst fun x => (hev x).mono fun n hn => by rw [hn.1])
    obtain ⟨h0, h1⟩ := hc01 n x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [gn, mul_pow]
    have hc2 : c n x ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hc2 (sq_nonneg (g x))]
  have L2 : Tendsto (fun n => ∫ x, gn n x ^ 2 * Real.log (gn n x ^ 2) ∂gaussianReal 0 1) atTop
      (𝓝 (∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂gaussianReal 0 1)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |g x ^ 2 * Real.log (g x ^ 2)| + g x ^ 2)
      (fun n => (Real.continuous_mul_log.comp ((hgn_cont n).pow 2)).aestronglyMeasurable)
      (hglog.abs.add hg2) (fun n => ae_of_all _ fun x => ?_)
      (hconst fun x => (hev x).mono fun n hn => by rw [hn.1])
    obtain ⟨h0, h1⟩ := hc01 n x
    rw [Real.norm_eq_abs, show gn n x ^ 2 = g x ^ 2 * c n x ^ 2 by simp only [gn, mul_pow]]
    exact abs_mul_mul_log_le (sq_nonneg _) (sq_nonneg _) (by nlinarith)
  have L3 : Tendsto (fun n => ∫ x, deriv (gn n) x ^ 2 ∂gaussianReal 0 1) atTop
      (𝓝 (∫ x, deriv g x ^ 2 ∂gaussianReal 0 1)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => 2 * deriv g x ^ 2 + 2 * K ^ 2 * g x ^ 2)
      (fun n => ((measurable_deriv _).pow_const 2).aestronglyMeasurable)
      ((hdg.const_mul 2).add (hg2.const_mul _)) (fun n => ae_of_all _ fun x => ?_)
      (hconst fun x => (hev x).mono fun n hn => by rw [hn.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgn_deriv_sq n x
  exact le_of_tendsto_of_tendsto (L2.sub ((Real.continuous_mul_log.tendsto _).comp L1))
    (L3.const_mul 2) (Eventually.of_forall hineq)

/-! ### Integrability of `g² log g²`, by sine truncation -/

/-- The sine truncation `c sin (f / c)` of a `C¹` function `f`, for `c > 0`: its square is at
most `f²` and `c²`, and its gradient norm is at most that of `f`. -/
private lemma sineTrunc_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : F → ℝ}
    (hf : ContDiff ℝ 1 f) {c : ℝ} (hc : 0 < c) (x : F) :
    (c * Real.sin (c⁻¹ * f x)) ^ 2 ≤ f x ^ 2 ∧ (c * Real.sin (c⁻¹ * f x)) ^ 2 ≤ c ^ 2 ∧
      ‖fderiv ℝ (fun x => c * Real.sin (c⁻¹ * f x)) x‖ ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have : |c * Real.sin (c⁻¹ * f x)| ≤ |f x| := by
      rw [abs_mul, abs_of_pos hc]
      calc c * |Real.sin (c⁻¹ * f x)| ≤ c * |c⁻¹ * f x| :=
            mul_le_mul_of_nonneg_left Real.abs_sin_le_abs hc.le
        _ = |f x| := by
            rw [abs_mul, abs_inv, abs_of_pos hc, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
  · have : |c * Real.sin (c⁻¹ * f x)| ≤ c := by
      rw [abs_mul, abs_of_pos hc]
      exact mul_le_of_le_one_right hc.le (Real.abs_sin_le_one _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
  · have h := ((((hf.differentiable one_ne_zero) x).hasFDerivAt.const_mul c⁻¹).sin.const_mul
      c).fderiv
    have h' : ‖fderiv ℝ (fun x => c * Real.sin (c⁻¹ * f x)) x‖ ≤ ‖fderiv ℝ f x‖ := by
      rw [h, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_inv, abs_of_pos hc]
      calc c * (|Real.cos (c⁻¹ * f x)| * (c⁻¹ * ‖fderiv ℝ f x‖))
          = (c * c⁻¹) * (|Real.cos (c⁻¹ * f x)| * ‖fderiv ℝ f x‖) := by ring
        _ = |Real.cos (c⁻¹ * f x)| * ‖fderiv ℝ f x‖ := by rw [mul_inv_cancel₀ hc.ne', one_mul]
        _ ≤ 1 * ‖fderiv ℝ f x‖ :=
            mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)
        _ = ‖fderiv ℝ f x‖ := one_mul _
    exact pow_le_pow_left₀ (norm_nonneg _) h' 2

/-- The sine truncations at scales `n + 1` converge pointwise to the identity. -/
private lemma tendsto_sineTrunc (y : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.sin (((n : ℝ) + 1)⁻¹ * y)) atTop (𝓝 y) := by
  have hs : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * y) atTop (𝓝 0) := by
    simpa only [one_div, zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const y
  have h := (tendsto_const_nhds (x := y)).mul ((Real.continuous_sinc.tendsto 0).comp hs)
  rw [Real.sinc_zero, mul_one] at h
  refine h.congr fun n => ?_
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  by_cases hy : y = 0
  · simp [hy]
  · simp only [Function.comp]
    rw [Real.sinc_of_ne_zero (mul_ne_zero (inv_ne_zero hn) hy)]
    field_simp

/-- If Gross's inequality holds with constant `2` for every `C¹` function with `h²`, `h² log h²`
and `‖∇h‖²` integrable, then `f² log f²` is integrable as soon as `f²` and `‖∇f‖²` are: apply it
to the bounded truncations `c sin (f / c)`, whose energy is at most that of `f`, and use Fatou. -/
private lemma integrable_sq_mul_log_sq_of_entropy_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [MeasurableSpace F] [OpensMeasurableSpace F] {ν : Measure F}
    [IsProbabilityMeasure ν]
    (hLSI : ∀ h : F → ℝ, ContDiff ℝ 1 h → Integrable (fun x => h x ^ 2) ν →
      Integrable (fun x => h x ^ 2 * Real.log (h x ^ 2)) ν →
      Integrable (fun x => ‖fderiv ℝ h x‖ ^ 2) ν →
      entropy ν (fun x => h x ^ 2) ≤ 2 * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂ν)
    {f : F → ℝ} (hf : ContDiff ℝ 1 f) (hf2 : Integrable (fun x => f x ^ 2) ν)
    (hdf : Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) ν) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) ν := by
  let c : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hc (n : ℕ) : 0 < c n := by positivity
  let fN : ℕ → F → ℝ := fun n x => c n * Real.sin ((c n)⁻¹ * f x)
  have hNcd (n : ℕ) : ContDiff ℝ 1 (fN n) := contDiff_const.mul ((contDiff_const.mul hf).sin)
  have hNsq (n : ℕ) (x : F) : fN n x ^ 2 ≤ f x ^ 2 := (sineTrunc_le hf (hc n) x).1
  have hNscale (n : ℕ) (x : F) : fN n x ^ 2 ≤ c n ^ 2 := (sineTrunc_le hf (hc n) x).2.1
  have hN2 (n : ℕ) : Integrable (fun x => fN n x ^ 2) ν := by
    refine hf2.mono' ((hNcd n).continuous.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hNsq n x
  have hNlog (n : ℕ) : Integrable (fun x => fN n x ^ 2 * Real.log (fN n x ^ 2)) ν := by
    refine Integrable.of_bound
      (Real.continuous_mul_log.comp ((hNcd n).continuous.pow 2)).aestronglyMeasurable
      ((c n ^ 2) ^ 2 + 1) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (Real.abs_mul_log_le_sq_add_one (sq_nonneg _)).trans ?_
    have := pow_le_pow_left₀ (sq_nonneg _) (hNscale n x) 2
    linarith
  have hNdf_le (n : ℕ) (x : F) : ‖fderiv ℝ (fN n) x‖ ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2 :=
    (sineTrunc_le hf (hc n) x).2.2
  have hNdf (n : ℕ) : Integrable (fun x => ‖fderiv ℝ (fN n) x‖ ^ 2) ν := by
    refine hdf.mono' (((hNcd n).continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hNdf_le n x
  set M := ∫ x, f x ^ 2 ∂ν
  set B := 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν + M ^ 2 + 2
  let Fx : F → ℝ := fun x => f x ^ 2 * Real.log (f x ^ 2) + 1
  let FN : ℕ → F → ℝ := fun n x => fN n x ^ 2 * Real.log (fN n x ^ 2) + 1
  have hF0 (x : F) : 0 ≤ Fx x := by
    have h := Real.self_sub_one_le_mul_log (sq_nonneg (f x))
    simp only [Fx]
    nlinarith [sq_nonneg (f x)]
  have hFN0 (n : ℕ) (x : F) : 0 ≤ FN n x := by
    have h := Real.self_sub_one_le_mul_log (sq_nonneg (fN n x))
    simp only [FN]
    nlinarith [sq_nonneg (fN n x)]
  have hFNbound (n : ℕ) : ∫ x, FN n x ∂ν ≤ B := by
    have hlsi := hLSI (fN n) (hNcd n) (hN2 n) (hNlog n) (hNdf n)
    rw [entropy] at hlsi
    have hm0 : 0 ≤ ∫ x, fN n x ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have hmLog := Real.abs_mul_log_le_sq_add_one hm0
    have hmSq := pow_le_pow_left₀ hm0 (integral_mono (hN2 n) hf2 (hNsq n)) 2
    have he := integral_mono (hNdf n) hdf (hNdf_le n)
    have ha := le_abs_self ((∫ x, fN n x ^ 2 ∂ν) * Real.log (∫ x, fN n x ^ 2 ∂ν))
    simp only [FN]
    rw [integral_add (hNlog n) (integrable_const _), integral_const, probReal_univ, one_smul]
    linarith
  have hFatou : ∫⁻ x, ENNReal.ofReal (Fx x) ∂ν ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (FN n x) ∂ν) atTop := by
    calc ∫⁻ x, ENNReal.ofReal (Fx x) ∂ν
        = ∫⁻ x, liminf (fun n => ENNReal.ofReal (FN n x)) atTop ∂ν := by
          refine lintegral_congr fun x => (Tendsto.liminf_eq ?_).symm
          have hlim : Tendsto (fun n => fN n x) atTop (𝓝 (f x)) := tendsto_sineTrunc (f x)
          exact (ENNReal.continuous_ofReal.tendsto _).comp
            (((Real.continuous_mul_log.tendsto _).comp (hlim.pow 2)).add tendsto_const_nhds)
      _ ≤ _ := lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp
          ((Real.continuous_mul_log.comp ((hNcd n).continuous.pow 2)).add
            continuous_const).measurable
  have hLiminf : liminf (fun n => ∫⁻ x, ENNReal.ofReal (FN n x) ∂ν) atTop ≤ ENNReal.ofReal B := by
    refine (liminf_le_liminf (Eventually.of_forall fun n => ?_)).trans_eq (liminf_const _)
    have hi : Integrable (FN n) ν := (hNlog n).add (integrable_const _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hFN0 n))]
    exact ENNReal.ofReal_le_ofReal (hFNbound n)
  have hFi := (lintegral_ofReal_ne_top_iff_integrable
    ((Real.continuous_mul_log.comp (hf.continuous.pow 2)).add continuous_const).aestronglyMeasurable
    (ae_of_all _ hF0)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hFatou.trans hLiminf))
  exact (hFi.sub (integrable_const (1 : ℝ))).congr (ae_of_all _ fun x => by simp)

/-! ### Gross's inequality on the line -/

/-- `g² log g²` is integrable for the standard Gaussian on `ℝ` when `g` is `C¹` with `g²` and
`g'²` integrable. -/
theorem integrable_sq_mul_log_sq_gaussianReal {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (gaussianReal 0 1) := by
  refine integrable_sq_mul_log_sq_of_entropy_le (fun h hh h2 hlog hd => ?_) hg hg2
    (by simpa only [norm_fderiv_sq_eq] using hdg)
  simp only [norm_fderiv_sq_eq] at hd ⊢
  exact entropy_sq_le_gaussianReal_of_integrable hh h2 hlog hd

/-- **Gross's logarithmic Sobolev inequality** on `ℝ`: `Ent (g²) ≤ 2 E g'²` for the standard
Gaussian. -/
theorem entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    entropy (gaussianReal 0 1) (fun x => g x ^ 2) ≤ 2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 :=
  entropy_sq_le_gaussianReal_of_integrable hg hg2 (integrable_sq_mul_log_sq_gaussianReal hg hg2 hdg)
    hdg

/-! ### Tensorization and transport to a Euclidean space -/

/-- Gross's inequality for the standard Gaussian on `ι → ℝ`, with `g² log g²` integrable. -/
private lemma entropy_sq_le_gaussianVector {ι : Type*} [Fintype ι] [DecidableEq ι] {G : (ι → ℝ) → ℝ}
    (hG : ContDiff ℝ 1 G) (hG2 : Integrable (fun x => G x ^ 2) (gaussianVector ι))
    (hGlog : Integrable (fun x => G x ^ 2 * Real.log (G x ^ 2)) (gaussianVector ι))
    (hdG : Integrable (fun x => ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2) (gaussianVector ι)) :
    entropy (gaussianVector ι) (fun x => G x ^ 2) ≤
      2 * ∫ x, ∑ i, fderiv ℝ G x (Pi.single i 1) ^ 2 ∂gaussianVector ι := by
  set P := gaussianVector ι with hP
  have hDi : ∀ i, Integrable (fun x => fderiv ℝ G x (Pi.single i 1) ^ 2) P := by
    intro i
    refine hdG.mono' ((((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow
      2).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun j => fderiv ℝ G x (Pi.single j 1) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  refine (entropy_pi_le_sum (fun _ : ι => gaussianReal 0 1) (f := fun x => G x ^ 2)
    (hG.continuous.pow 2).measurable (fun x => sq_nonneg _) hG2 hGlog).trans ?_
  rw [integral_finsetSum _ fun i _ => hDi i, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hae : ∀ᵐ x ∂P, entropy (gaussianReal 0 1) (fun y => G (Function.update x i y) ^ 2) ≤
      2 * ∫ t, fderiv ℝ G (Function.update x i t) (Pi.single i 1) ^ 2 ∂gaussianReal 0 1 := by
    filter_upwards [ae_integrable_comp_update_pi (fun _ : ι => gaussianReal 0 1) i hG2,
      ae_integrable_comp_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)] with x h1 h2
    have hd : deriv (fun t => G (Function.update x i t)) =
        fun t => fderiv ℝ G (Function.update x i t) (Pi.single i 1) := funext fun t =>
      (((hG.differentiable one_ne_zero) (Function.update x i t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update x i t)).deriv
    have := entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal
      (g := fun t => G (Function.update x i t)) (hG.comp (contDiff_update 1 x i)) h1
      (by rw [hd]; exact h2)
    rwa [hd] at this
  have hR : Integrable (fun x => 2 * ∫ t, fderiv ℝ G (Function.update x i t) (Pi.single i 1) ^ 2
      ∂gaussianReal 0 1) P :=
    (integrable_integral_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)).const_mul 2
  calc _ ≤ ∫ x, 2 * ∫ t, fderiv ℝ G (Function.update x i t) (Pi.single i 1) ^ 2
        ∂gaussianReal 0 1 ∂P := by
        by_cases hE : Integrable
          (fun x => entropy (gaussianReal 0 1) (fun y => G (Function.update x i y) ^ 2)) P
        · exact integral_mono_ae hE hR hae
        · rw [integral_undef hE]
          exact integral_nonneg fun x =>
            mul_nonneg zero_le_two (integral_nonneg fun t => sq_nonneg _)
    _ = 2 * ∫ x, fderiv ℝ G x (Pi.single i 1) ^ 2 ∂P := by
        rw [integral_const_mul,
          integral_integral_update_pi (fun _ : ι => gaussianReal 0 1) i (hDi i)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Gross's inequality for the standard Gaussian on a Euclidean space, with `g² log g²`
integrable: transport of the product case through an orthonormal basis. -/
private lemma entropy_sq_le_stdGaussian_of_integrable {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hglog : Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    entropy (stdGaussian E) (fun x => g x ^ 2) ≤ 2 * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂stdGaussian E := by
  set b := stdOrthonormalBasis ℝ E
  let L : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] E :=
    ∑ i, (ContinuousLinearMap.proj i).smulRight (b i)
  have hL : (⇑L : (Fin (Module.finrank ℝ E) → ℝ) → E) = fun x => ∑ i, x i • b i := by
    funext x; simp [L]
  have hstd : stdGaussian E = (gaussianVector (Fin (Module.finrank ℝ E))).map L := by
    rw [hL]; rfl
  have hLm : AEMeasurable L (gaussianVector (Fin (Module.finrank ℝ E))) :=
    L.continuous.measurable.aemeasurable
  have hfd : ∀ x, fderiv ℝ (fun x => g (L x)) x = (fderiv ℝ g (L x)).comp L := fun x =>
    (((hg.differentiable one_ne_zero) (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  have hen : ∀ x, ∑ i, fderiv ℝ (fun x => g (L x)) x (Pi.single i 1) ^ 2 =
      ‖fderiv ℝ g (L x)‖ ^ 2 := fun x => by
    have hLs : ∀ i, L (Pi.single i 1) = b i := fun i => by
      rw [hL]; simp [Pi.single_apply]
    simp only [hfd, ContinuousLinearMap.comp_apply, hLs]
    exact (b.norm_dual _).symm
  have hc2 : Continuous (fun x => g x ^ 2) := hg.continuous.pow 2
  have hclog : Continuous (fun x => g x ^ 2 * Real.log (g x ^ 2)) :=
    Real.continuous_mul_log.comp hc2
  have hcd : Continuous (fun x => ‖fderiv ℝ g x‖ ^ 2) :=
    ((hg.continuous_fderiv one_ne_zero).norm.pow 2)
  rw [hstd] at hg2 hglog hdg ⊢
  rw [integrable_map_measure hc2.aestronglyMeasurable hLm] at hg2
  rw [integrable_map_measure hclog.aestronglyMeasurable hLm] at hglog
  rw [integrable_map_measure hcd.aestronglyMeasurable hLm] at hdg
  simp only [Function.comp_def] at hg2 hglog hdg
  have key := entropy_sq_le_gaussianVector (G := fun x => g (L x)) (hg.comp L.contDiff) hg2 hglog
    (by simpa only [hen] using hdg)
  simp only [hen] at key
  rw [entropy, integral_map hLm hclog.aestronglyMeasurable,
    integral_map hLm hc2.aestronglyMeasurable, integral_map hLm hcd.aestronglyMeasurable]
  exact key

/-- `g² log g²` is integrable for the standard Gaussian on a Euclidean space when `g` is `C¹`
with `g²` and `‖∇g‖²` integrable. -/
theorem integrable_sq_mul_log_sq_stdGaussian {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) (stdGaussian E) :=
  integrable_sq_mul_log_sq_of_entropy_le
    (fun _ hh h2 hlog hd => entropy_sq_le_stdGaussian_of_integrable hh h2 hlog hd) hg hg2 hdg

/-- **Gross's logarithmic Sobolev inequality** for the standard Gaussian on a Euclidean space:
`Ent (g²) ≤ 2 E ‖∇g‖²` ([BoucheronLugosiMassart2013], Theorem 5.4).
Result: gaussian-log-sobolev -/
theorem entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    entropy (stdGaussian E) (fun x => g x ^ 2) ≤
      2 * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂stdGaussian E :=
  entropy_sq_le_stdGaussian_of_integrable hg hg2 (integrable_sq_mul_log_sq_stdGaussian hg hg2 hdg)
    hdg

/-- The standard Gaussian satisfies a logarithmic Sobolev inequality with constant `1`. -/
theorem hasLogSobolev_stdGaussian : HasLogSobolev (stdGaussian E) 1 := by
  refine ⟨fun g hg ⟨M, hM⟩ ⟨M', hM'⟩ => ?_⟩
  rw [NNReal.coe_one, mul_one]
  refine entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian hg ?_ ?_
  · refine Integrable.of_bound (hg.continuous.pow 2).aestronglyMeasurable (M ^ 2)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  · refine Integrable.of_bound ((hg.continuous_fderiv one_ne_zero).norm.pow 2).aestronglyMeasurable
      (M' ^ 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM' x) 2

end NLAlib
