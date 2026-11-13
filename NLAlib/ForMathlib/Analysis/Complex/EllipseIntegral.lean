/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import NLAlib.ForMathlib.MeasureTheory.Integral.CurveIntegral.PrimitiveHomotopy
public import NLAlib.ForMathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Deformation of circle integrals to ellipses

For a function analytic off a real segment, deformation to a thin ellipse relates a contour
integral to a signed boundary value. Upstream candidate for Mathlib.

The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `Complex.neg_exp_circleIntegral_re_nonneg`.
-/
@[expose] public section

section

open Filter MeasureTheory Set

open scoped Topology

open scoped Interval ComplexConjugate

namespace Complex

/-- Rotating a complex number with nonnegative imaginary part through an
angle whose cosine is nonnegative gives an imaginary part bounded below by
`-|sin θ|` times its norm. -/
private theorem neg_abs_sin_mul_norm_le_im_exp_mul {θ : ℝ} {z : ℂ}
    (hcos : 0 ≤ Real.cos θ) (hz : 0 ≤ z.im) :
    -(|Real.sin θ| * ‖z‖) ≤ (exp (θ * I) * z).im := by
  have hre := abs_re_le_norm z
  have hs : -(Real.sin θ * z.re) ≤ |Real.sin θ| * ‖z‖ :=
    (neg_le_abs _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hre (abs_nonneg _))
  have hc := mul_nonneg hcos hz
  simpa only [mul_im, exp_re, exp_im, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_zero, zero_mul, add_zero, Real.exp_zero, one_mul]
    using (show -(|Real.sin θ| * ‖z‖) ≤ Real.cos θ * z.im + Real.sin θ * z.re by linarith)

end Complex

end

section

open Filter MeasureTheory Set

open scoped Interval Topology ComplexConjugate

namespace Complex

/-- The standard counterclockwise ellipse with horizontal semiaxis `M` and
vertical semiaxis `ε`; it degenerates to a segment when `ε = 0`. -/
noncomputable def ellipseMap (M ε : ℝ) (θ : ℝ) : ℂ :=
  (M * Real.cos θ : ℝ) + (ε * Real.sin θ : ℝ) * I

/-- The ellipse's actual tangent vector is the derivative of its standard
trigonometric parametrization. -/
theorem hasDerivAt_ellipseMap (M ε θ : ℝ) :
    HasDerivAt (ellipseMap M ε)
      (((-M * Real.sin θ : ℝ) : ℂ) + (ε * Real.cos θ : ℝ) * I) θ := by
  simpa only [ellipseMap, Pi.add_apply, mul_neg, neg_mul] using!
    (((Real.hasDerivAt_cos θ).const_mul M).ofReal_comp.add
      (((Real.hasDerivAt_sin θ).const_mul ε).ofReal_comp.mul_const I))

/-- The closed disk of radius $\max(M,\varepsilon)$ contains the ellipse with nonnegative
semiaxes $M$ and $\varepsilon$. -/
theorem norm_ellipseMap_le_max {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (θ : ℝ) :
    ‖ellipseMap M ε θ‖ ≤ max M ε := by
  have hs := mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ hM (hM.trans (le_max_left M ε))).mpr (le_max_left M ε))
    (sq_nonneg (Real.cos θ))
  have ht := mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ hε (hε.trans (le_max_right M ε))).mpr (le_max_right M ε))
    (sq_nonneg (Real.sin θ))
  apply (sq_le_sq₀ (norm_nonneg _) (hM.trans (le_max_left M ε))).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [ellipseMap, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero,
    add_im, mul_I_im, zero_add]
  have hcircle := congrArg (fun x : ℝ => (max M ε) ^ 2 * x) (Real.sin_sq_add_cos_sq θ)
  nlinarith

/-- The sum of the nonnegative semiaxes also bounds the norm of every point of the ellipse. -/
theorem norm_ellipseMap_le {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (θ : ℝ) :
    ‖ellipseMap M ε θ‖ ≤ M + ε :=
  (norm_ellipseMap_le_max hM hε θ).trans (max_le (le_add_of_nonneg_right hε)
    (le_add_of_nonneg_left hM))

/-- The contour integral on the standard ellipse, using its actual derivative.
Integrability and positive semiaxes are supplied by theorems using this total
definition. -/
noncomputable def ellipseIntegral (f : ℂ → ℂ) (M ε : ℝ) : ℂ :=
  ∫ θ in 0..2 * Real.pi, deriv (ellipseMap M ε) θ * f (ellipseMap M ε θ)

private theorem ellipseMap_two_pi_sub (M ε θ : ℝ) :
    ellipseMap M ε (2 * Real.pi - θ) = conj (ellipseMap M ε θ) := by
  simp only [ellipseMap, Real.cos_two_pi_sub, Real.sin_two_pi_sub, map_add, map_mul,
    conj_ofReal, conj_I, ofReal_neg, mul_neg]
  ring

private theorem ellipse_tangent_reflection (M ε θ : ℝ) :
    deriv (ellipseMap M ε) (2 * Real.pi - θ) = -conj (deriv (ellipseMap M ε) θ) := by
  rw [(hasDerivAt_ellipseMap _ _ _).deriv, (hasDerivAt_ellipseMap _ _ _).deriv]
  simp only [Real.cos_two_pi_sub, Real.sin_two_pi_sub, map_add, map_mul,
    conj_ofReal, conj_I]
  push_cast
  ring

private theorem neg_normalized_re (z : ℂ) :
    (-((2 * Real.pi * I : ℂ)⁻¹ * z)).re = -z.im / (2 * Real.pi) := by
  rw [show (2 * Real.pi * I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * I by push_cast; rfl]
  rw [mul_inv_rev, inv_I, ← ofReal_inv]
  simp only [neg_mul, neg_neg, mul_re, mul_im, I_re, I_im, ofReal_re,
    ofReal_im, mul_zero, zero_mul, sub_zero, zero_sub, neg_mul]
  ring

/-- Schwarz reflection pairs the two halves of a counterclockwise ellipse.
The real part of the negatively normalized contour integral is an ordinary
upper-half integral with the orientation signs displayed explicitly. -/
private theorem neg_normalized_ellipseIntegral_re_eq
    {f : ℂ → ℂ} {M ε : ℝ}
    (hc : ContinuousOn (fun θ => f (ellipseMap M ε θ)) (Icc 0 (2 * Real.pi)))
    (hconj : ∀ θ ∈ Icc 0 Real.pi,
      f (conj (ellipseMap M ε θ)) = conj (f (ellipseMap M ε θ))) :
    (-((2 * Real.pi * I : ℂ)⁻¹ * ellipseIntegral f M ε)).re =
      (∫ θ in 0..Real.pi,
        M * Real.sin θ * (f (ellipseMap M ε θ)).im -
          ε * Real.cos θ * (f (ellipseMap M ε θ)).re) / Real.pi := by
  let Q : ℝ → ℂ := fun θ => deriv (ellipseMap M ε) θ * f (ellipseMap M ε θ)
  have hQcont : ContinuousOn Q (Icc 0 (2 * Real.pi)) := by
    apply ContinuousOn.mul _ hc
    have hd : deriv (ellipseMap M ε) = fun θ =>
        (((-M * Real.sin θ : ℝ) : ℂ) + (ε * Real.cos θ : ℝ) * I) := by
      funext θ
      exact (hasDerivAt_ellipseMap _ _ _).deriv
    rw [hd]
    fun_prop
  have hQ : IntervalIntegrable Q volume 0 (2 * Real.pi) :=
    hQcont.intervalIntegrable_of_Icc Real.two_pi_pos.le
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have hπ2 : Real.pi ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have hup : IntervalIntegrable Q volume 0 Real.pi :=
    hQ.mono_set (by simpa only [uIcc_of_le hπ, uIcc_of_le Real.two_pi_pos.le] using
      Icc_subset_Icc le_rfl hπ2)
  have hlo : IntervalIntegrable Q volume Real.pi (2 * Real.pi) :=
    hQ.mono_set (by simpa only [uIcc_of_le hπ2, uIcc_of_le Real.two_pi_pos.le] using
      Icc_subset_Icc hπ le_rfl)
  have hreflection (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
      Q (2 * Real.pi - θ) = -conj (Q θ) := by
    dsimp only [Q]
    rw [ellipseMap_two_pi_sub, hconj θ hθ, ellipse_tangent_reflection, map_mul, neg_mul]
  have hlow : (∫ θ in Real.pi..2 * Real.pi, Q θ) =
      -conj (∫ θ in 0..Real.pi, Q θ) := by
    have hchange := intervalIntegral.integral_comp_sub_left
      (a := 0) (b := Real.pi) Q (2 * Real.pi)
    have hends : 2 * Real.pi - Real.pi = Real.pi := by ring
    rw [hends, sub_zero] at hchange
    rw [← hchange]
    calc
      _ = ∫ θ in 0..Real.pi, -conj (Q θ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        exact hreflection θ (by simpa only [uIcc_of_le hπ] using hθ)
      _ = _ := by rw [intervalIntegral.integral_neg, intervalIntegral.intervalIntegral_conj]
  have hfull : ellipseIntegral f M ε =
      (∫ θ in 0..Real.pi, Q θ) - conj (∫ θ in 0..Real.pi, Q θ) := by
    change (∫ θ in 0..2 * Real.pi, Q θ) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hup hlo, hlow, sub_eq_add_neg]
  rw [hfull, neg_normalized_re]
  simp only [sub_im, conj_im]
  have hi := Complex.imCLM.intervalIntegral_comp_comm hup
  change (∫ θ in 0..Real.pi, (Q θ).im) = (∫ θ in 0..Real.pi, Q θ).im at hi
  rw [← hi]
  have hpoint (θ : ℝ) : -(Q θ).im =
      M * Real.sin θ * (f (ellipseMap M ε θ)).im -
        ε * Real.cos θ * (f (ellipseMap M ε θ)).re := by
    dsimp only [Q]
    rw [(hasDerivAt_ellipseMap _ _ _).deriv]
    simp only [mul_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, I_re, I_im,
      mul_zero, sub_zero, mul_one, zero_add, add_zero]
    ring
  rw [show -((∫ θ in 0..Real.pi, (Q θ).im) - -(∫ θ in 0..Real.pi, (Q θ).im)) =
    2 * -(∫ θ in 0..Real.pi, (Q θ).im) by ring]
  rw [← intervalIntegral.integral_neg]
  simp_rw [hpoint]
  field_simp

private theorem neg_mul_le_im_exp_mul_of_im_le {z v : ℂ} {M ε C : ℝ}
    (hre : z.re ≤ M) (him : 0 ≤ z.im) (himε : z.im ≤ ε) (hε : ε ≤ 1)
    (hC : 0 ≤ C) (hv : 0 ≤ v.im) (hvC : ‖v‖ ≤ C) :
    -(Real.exp M * C * ε) ≤ (exp z * v).im := by
  have he0 : 0 ≤ ε := him.trans himε
  have hcos : 0 ≤ Real.cos z.im :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) ((himε.trans hε).trans Real.one_le_pi_div_two)
  have hphase := neg_abs_sin_mul_norm_le_im_exp_mul hcos hv
  have hs : |Real.sin z.im| ≤ ε :=
    (Real.abs_sin_le_abs.trans_eq (abs_of_nonneg him)).trans himε
  have hsC : |Real.sin z.im| * ‖v‖ ≤ ε * C :=
    mul_le_mul hs hvC (norm_nonneg _) he0
  have hrot : -(ε * C) ≤ (exp (z.im * I) * v).im := by linarith
  have heq : (exp z * v).im = Real.exp z.re * (exp (z.im * I) * v).im := by
    conv_lhs => rw [← re_add_im z, exp_add, mul_assoc]
    simp only [mul_im, exp_ofReal_re, exp_ofReal_im, zero_mul, add_zero]
  rw [heq]
  have h₁ := mul_le_mul_of_nonneg_left hrot (Real.exp_pos z.re).le
  have h₂ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre)
    (mul_nonneg he0 hC)
  nlinarith

/-- For a bounded Schwarz-symmetric function with nonnegative imaginary part
along the upper ellipse, the negatively normalized exponential moment is
bounded below by `-(M+1) exp(M) C ε`. Its possible negative part therefore
vanishes with the vertical semiaxis, without boundary limits on the real segment. -/
private theorem neg_normalized_exp_ellipseIntegral_re_ge
    {h : ℂ → ℂ} {M ε C : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    (hc : ContinuousOn (fun θ => h (ellipseMap M ε θ)) (Icc 0 (2 * Real.pi)))
    (hconj : ∀ θ ∈ Icc 0 Real.pi,
      h (conj (ellipseMap M ε θ)) = conj (h (ellipseMap M ε θ)))
    (him : ∀ θ ∈ Ioo 0 Real.pi, 0 ≤ (h (ellipseMap M ε θ)).im)
    (hbound : ∀ θ ∈ Icc 0 Real.pi, ‖h (ellipseMap M ε θ)‖ ≤ C) :
    -((M + 1) * Real.exp M * C) * ε ≤
      (-((2 * Real.pi * I : ℂ)⁻¹ * ellipseIntegral (fun z => exp z * h z) M ε)).re := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0 ⟨le_rfl, Real.pi_pos.le⟩)
  have hγ : Continuous (ellipseMap M ε) := by unfold ellipseMap; fun_prop
  have hfc : ContinuousOn (fun θ => exp (ellipseMap M ε θ) * h (ellipseMap M ε θ))
      (Icc 0 (2 * Real.pi)) := (continuous_exp.comp hγ).continuousOn.mul hc
  have hfconj (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
      exp (conj (ellipseMap M ε θ)) * h (conj (ellipseMap M ε θ)) =
        conj (exp (ellipseMap M ε θ) * h (ellipseMap M ε θ)) := by
    rw [exp_conj, hconj θ hθ, map_mul]
  rw [neg_normalized_ellipseIntegral_re_eq hfc hfconj]
  let D : ℝ := Real.exp M * C
  have hD : 0 ≤ D := mul_nonneg (Real.exp_pos _).le hC
  let F : ℝ → ℝ := fun θ =>
    M * Real.sin θ * (exp (ellipseMap M ε θ) * h (ellipseMap M ε θ)).im -
      ε * Real.cos θ * (exp (ellipseMap M ε θ) * h (ellipseMap M ε θ)).re
  have hpoint (θ : ℝ) (hθ : θ ∈ Ioo 0 Real.pi) : -((M + 1) * D) * ε ≤ F θ := by
    have hs0 : 0 ≤ Real.sin θ := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le
    have hs1 := Real.sin_le_one θ
    have hx : (ellipseMap M ε θ).re ≤ M := by
      simp only [ellipseMap, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero]
      nlinarith [Real.cos_le_one θ]
    have hy0 : 0 ≤ (ellipseMap M ε θ).im := by
      simpa only [ellipseMap, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, zero_add, add_zero] using mul_nonneg hε hs0
    have hyε : (ellipseMap M ε θ).im ≤ ε := by
      simpa only [ellipseMap, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, zero_add, add_zero] using mul_le_of_le_one_right hε hs1
    have hlower := neg_mul_le_im_exp_mul_of_im_le hx hy0 hyε hε' hC
      (him θ hθ) (hbound θ ⟨hθ.1.le, hθ.2.le⟩)
    have hnorm : ‖exp (ellipseMap M ε θ) * h (ellipseMap M ε θ)‖ ≤ D := by
      rw [norm_mul, norm_exp]
      exact mul_le_mul (Real.exp_le_exp.mpr hx) (hbound θ ⟨hθ.1.le, hθ.2.le⟩)
        (norm_nonneg _) (Real.exp_pos _).le
    have hre : |(exp (ellipseMap M ε θ) * h (ellipseMap M ε θ)).re| ≤ D :=
      (abs_re_le_norm _).trans hnorm
    have hvertical : ε * Real.cos θ * (exp (ellipseMap M ε θ) * h (ellipseMap M ε θ)).re ≤
        ε * D := by
      apply (le_abs_self _).trans
      rw [abs_mul, abs_mul, abs_of_nonneg hε]
      have hh := mul_le_mul (Real.abs_cos_le_one θ) hre (abs_nonneg _) zero_le_one
      nlinarith [mul_le_mul_of_nonneg_left hh hε]
    have hmain0 : 0 ≤ M * Real.sin θ := mul_nonneg hM hs0
    have hmain1 : M * Real.sin θ ≤ M := mul_le_of_le_one_right hM hs1
    have hp := mul_le_mul_of_nonneg_left hlower hmain0
    have hp' := mul_le_mul_of_nonneg_right hmain1 (mul_nonneg hD hε)
    dsimp only [F]
    dsimp only [D] at *
    nlinarith
  have hFcont : ContinuousOn F (Icc 0 Real.pi) := by
    have hcf := hfc.mono (Icc_subset_Icc le_rfl (by linarith [Real.pi_pos]))
    have hre : ContinuousOn (fun θ => (exp (ellipseMap M ε θ) * h (ellipseMap M ε θ)).re)
        (Icc 0 Real.pi) := continuous_re.comp_continuousOn hcf
    have him : ContinuousOn (fun θ => (exp (ellipseMap M ε θ) * h (ellipseMap M ε θ)).im)
        (Icc 0 Real.pi) := continuous_im.comp_continuousOn hcf
    exact (by fun_prop : ContinuousOn (fun θ => M * Real.sin θ) (Icc 0 Real.pi)).mul him |>.sub
      ((by fun_prop : ContinuousOn (fun θ => ε * Real.cos θ) (Icc 0 Real.pi)).mul hre)
  have hint := intervalIntegral.integral_mono_on_of_le_Ioo Real.pi_pos.le
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => -((M + 1) * D) * ε) volume 0 Real.pi)
    (hFcont.intervalIntegrable_of_Icc Real.pi_pos.le) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  apply (le_div_iff₀ Real.pi_pos).mpr
  dsimp only [F, D] at hint
  nlinarith

/-- A fixed moment represented by all sufficiently thin exponential ellipse
integrals is nonnegative. The representation premise can be supplied by a smooth
free-loop homotopy from one fixed exterior circle. Only upper-half-plane values
and bounds on the ellipses occur, with no real-axis limiting values required. -/
private theorem nonneg_of_neg_normalized_exp_ellipseIntegral_re_eq
    {h : ℂ → ℂ} {M C δ w : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hc : ∀ ε ∈ Ioo 0 δ,
      ContinuousOn (fun θ => h (ellipseMap M ε θ)) (Icc 0 (2 * Real.pi)))
    (hconj : ∀ ε ∈ Ioo 0 δ, ∀ θ ∈ Icc 0 Real.pi,
      h (conj (ellipseMap M ε θ)) = conj (h (ellipseMap M ε θ)))
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    (hbound : ∀ ε ∈ Ioo 0 δ, ∀ θ ∈ Icc 0 Real.pi,
      ‖h (ellipseMap M ε θ)‖ ≤ C)
    (hw : ∀ ε ∈ Ioo 0 δ,
      (-((2 * Real.pi * I : ℂ)⁻¹ * ellipseIntegral (fun z => exp z * h z) M ε)).re = w) :
    0 ≤ w := by
  let K : ℝ := (M + 1) * Real.exp M * C
  have hest : ∀ᶠ ε in 𝓝[>] (0 : ℝ), -K * ε ≤ w := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ zero_lt_one)] with ε hε
    have heδ : ε ∈ Ioo 0 δ := ⟨hε.1, (lt_min_iff.mp hε.2).1⟩
    rw [← hw ε heδ]
    apply neg_normalized_exp_ellipseIntegral_re_ge hM hε.1.le (lt_min_iff.mp hε.2).2.le
      (hc ε heδ) (hconj ε heδ)
    · intro θ hθ
      apply him
      have hsin := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
      simpa only [ellipseMap, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, zero_add, add_zero] using mul_pos hε.1 hsin
    · exact hbound ε heδ
  have hlim : Tendsto (fun ε : ℝ => -K * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_const_nhds.mul ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)))
  exact le_of_tendsto hlim hest

end Complex

end

section

open Set Metric MeasureTheory

open scoped unitInterval Topology

namespace Complex

/-- The standard ellipse as a native closed path on the unit interval. -/
noncomputable def ellipsePath (M ε : ℝ) : Path (M : ℂ) (M : ℂ) :=
  Path.ofLine (f := fun t : ℝ => ellipseMap M ε (2 * Real.pi * t))
    (by unfold ellipseMap; fun_prop)
    (by simp [ellipseMap]) (by simp [ellipseMap])

/-- The ellipse path agrees with its angular parametrization through angle
`2πt` on the full closed unit interval. -/
theorem ellipsePath_extend_apply {M ε t : ℝ} (ht : t ∈ I) :
    (ellipsePath M ε).extend t = ellipseMap M ε (2 * Real.pi * t) := by
  rw [Path.extend_apply _ ht]
  rfl

private theorem contDiff_ellipse_param (M ε : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => ellipseMap M ε (2 * Real.pi * t)) := by
  have hr : ContDiff ℝ 1 (fun t : ℝ => M * Real.cos (2 * Real.pi * t)) := by fun_prop
  have hi : ContDiff ℝ 1 (fun t : ℝ => ε * Real.sin (2 * Real.pi * t)) := by fun_prop
  simpa only [ellipseMap, ofRealCLM_apply, Pi.add_apply, Function.comp_def] using!
    (ofRealCLM.contDiff.comp hr).add ((ofRealCLM.contDiff.comp hi).mul contDiff_const)

/-- Native ellipse paths are continuously differentiable at both endpoints. -/
theorem contDiffOn_ellipsePath_extend (M ε : ℝ) :
    ContDiffOn ℝ 1 (ellipsePath M ε).extend I := by
  have h := contDiff_ellipse_param M ε
  exact h.contDiffOn.congr (fun t ht => ellipsePath_extend_apply ht)

/-- The native ellipse path integral is its angular ellipse integral, with
counterclockwise orientation and no change in its normalization. -/
theorem integral_ellipsePath_eq_ellipseIntegral (f : ℂ → ℂ) (M ε : ℝ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) (ellipsePath M ε) =
      ellipseIntegral f M ε := by
  have hγ := contDiff_ellipse_param M ε
  rw [Path.integral_eq_intervalIntegral_of_eqOn_extend _ hγ
    (fun _ ht => ellipsePath_extend_apply ht)]
  have hd (t : ℝ) : deriv (fun t : ℝ => ellipseMap M ε (2 * Real.pi * t)) t =
      (2 * Real.pi) • deriv (ellipseMap M ε) (2 * Real.pi * t) := by
    simpa only [Function.comp_def, mul_one, (hasDerivAt_ellipseMap _ _ _).deriv] using!
      ((hasDerivAt_ellipseMap M ε (2 * Real.pi * t)).scomp t
        ((hasDerivAt_id t).const_mul (2 * Real.pi))).deriv
  simp_rw [hd, smul_mul_assoc]
  rw [intervalIntegral.integral_smul]
  have hs := intervalIntegral.smul_integral_comp_mul_left
    (fun θ : ℝ => deriv (ellipseMap M ε) θ * f (ellipseMap M ε θ)) (2 * Real.pi)
    (a := (0 : ℝ)) (b := 1)
  simpa only [mul_zero, mul_one, ellipseIntegral, smul_eq_mul] using hs

private theorem ellipseMap_self (M θ : ℝ) : ellipseMap M M θ = circleMap 0 M θ := by
  apply Complex.ext <;>
    simp only [ellipseMap, circleMap, add_re, add_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im, mul_zero, zero_mul, mul_one, zero_add, add_zero,
      sub_zero, exp_re, exp_im, Real.exp_zero, one_mul]

/-- Every point of a nondegenerate ellipse with real semiaxis outside a disk
is either nonreal or outside that disk. Thus its flattening avoids every branch
cut contained in the smaller real segment. -/
private theorem ellipseMap_mem_off_real_or_exterior {M ε R θ : ℝ}
    (hM : 0 < M) (hε : 0 < ε) (hRM : R < M) :
    (ellipseMap M ε θ).im ≠ 0 ∨ R < ‖ellipseMap M ε θ‖ := by
  by_cases hs : Real.sin θ = 0
  · right
    have hn : ‖ellipseMap M ε θ‖ = M := by
      rcases Real.sin_eq_zero_iff_cos_eq.mp hs with hc | hc <;>
        simp only [ellipseMap, hs, hc, mul_one, mul_neg, mul_zero, ofReal_zero,
          zero_mul, add_zero, ofReal_neg, norm_neg, norm_real, Real.norm_eq_abs,
          abs_of_pos hM]
    rwa [hn]
  · left
    simpa only [ellipseMap, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
      mul_one, mul_zero, zero_add, add_zero] using mul_ne_zero hε.ne' hs

/-- A circle of radius `M` deforms through smooth ellipses to any positive
vertical semiaxis inside the union of the nonreal plane and the exterior of a
smaller disk. Holomorphy on that actual domain identifies the contour integrals.
No real-axis boundary values inside the disk are assumed. -/
theorem circleIntegral_eq_ellipseIntegral_of_differentiableOn_off_real_or_exterior
    {f : ℂ → ℂ} {R M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) (hRM : R < M)
    (hf : DifferentiableOn ℂ f {z | z.im ≠ 0 ∨ R < ‖z‖}) :
    (∮ z in C(0, M), f z) = ellipseIntegral f M ε := by
  let ψ : ℝ × ℝ → ℂ := fun p =>
    ellipseMap M ((1 - p.1) * M + p.1 * ε) (2 * Real.pi * p.2)
  have hψ : Continuous ψ := by unfold ψ ellipseMap; fun_prop
  have hΩ : IsOpen {z : ℂ | z.im ≠ 0 ∨ R < ‖z‖} :=
    (isOpen_ne_fun continuous_im continuous_const).union
      (isOpen_lt continuous_const continuous_norm)
  have hm (p : ℝ × ℝ) (hp : p ∈ Icc (0 : ℝ × ℝ) 1) :
      0 < (1 - p.1) * M + p.1 * ε := by
    have ht0 : 0 ≤ p.1 := hp.1.1
    have ht1 : p.1 ≤ 1 := hp.2.1
    by_cases ht : p.1 = 1
    · simpa only [ht, sub_self, zero_mul, one_mul, zero_add] using hε
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht1 ht)) hM)
        (mul_nonneg ht0 hε.le)
  have hc := integral_eq_of_differentiableOn_of_freeHomotopy
    (circlePath 0 M) (ellipsePath M ε) hψ hΩ hf
    (fun p hp => ellipseMap_mem_off_real_or_exterior hM (hm p hp) hRM)
    (fun t ht => by rw [circlePath_extend_apply ht]; simp only [ψ, sub_zero, one_mul,
      zero_mul, add_zero]; exact (ellipseMap_self M _).symm)
    (fun t ht => by rw [ellipsePath_extend_apply ht]; simp only [ψ, sub_self, zero_mul,
      one_mul, zero_add])
    (fun t _ => by simp [ψ, ellipseMap])
    (contDiffOn_circlePath_extend 0 M) (contDiffOn_ellipsePath_extend M ε)
  rwa [integral_circlePath_eq_circleIntegral,
      integral_ellipsePath_eq_ellipseIntegral] at hc

end Complex

end

section

open Set Filter

open scoped Topology ComplexConjugate

namespace Complex

/-- A Schwarz-symmetric holomorphic function off a compact real segment, with
nonnegative upper-half-plane imaginary part and a uniform bound on the closed disk of
radius $M>R$ with $M>0$, satisfies
$-\Re((2\pi i)^{-1}\oint_{\lvert z\rvert=M}e^z h(z)\,dz)\ge 0$.
This is the scalar positivity step for the density in [Stahl2013, Theorem 2]. -/
theorem neg_exp_circleIntegral_re_nonneg
    {h : ℂ → ℂ} {R M C : ℝ} (hM : 0 < M) (hRM : R < M)
    (hh : DifferentiableOn ℂ h {z | z.im ≠ 0 ∨ R < ‖z‖})
    (href : ∀ z : ℂ, h (conj z) = conj (h z))
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (h z).im)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ M → ‖h z‖ ≤ C) :
    0 ≤ (-((2 * Real.pi * I : ℂ)⁻¹ *
      (∮ z in C(0, M), exp z * h z))).re := by
  apply nonneg_of_neg_normalized_exp_ellipseIntegral_re_eq
    (h := h) (M := M) (C := C) (δ := M) hM.le hM
  · intro ε hε
    apply hh.continuousOn.comp (by unfold ellipseMap; fun_prop)
    intro θ _
    exact ellipseMap_mem_off_real_or_exterior hM hε.1 hRM
  · intro ε _ θ _
    exact href _
  · exact him
  · intro ε hε θ _
    apply hbound
    exact (norm_ellipseMap_le_max hM.le hε.1.le θ).trans (max_le le_rfl hε.2.le)
  · intro ε hε
    rw [← circleIntegral_eq_ellipseIntegral_of_differentiableOn_off_real_or_exterior
      (f := fun z => exp z * h z) hM hε.1 hRM (differentiable_exp.differentiableOn.mul hh)]

end Complex

end
