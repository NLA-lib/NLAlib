/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Order.IsLUB
public import NLAlib.ForMathlib.Analysis.Complex.JensenFormula
public import NLAlib.ForMathlib.Analysis.Complex.Poisson

/-!
# A weighted three-lines inequality

The Stein–Hirschman interpolation bound against explicit probability measures on the
boundaries of a vertical strip. Bounded measurable logarithmic majorants give a bound even
when the holomorphic function vanishes. Upstream candidates for `Mathlib.Analysis.Complex.Hadamard`.

The proof adapts the original formalization in `tchen-research/NLAlib@77514ce`.

## Main results

* `Complex.circleAverage_eq_integral_cauchyPDFReal`: Cayley transport of the unit circle.
* `Complex.norm_le_exp_integral_stripHarmonicMeasure`: the strip inequality with boundary majorants.
-/

@[expose] public section

section

open Set

namespace Real

/-- The left strip harmonic-measure density is exactly `(1-r)β_(1-r)`. -/
private theorem one_sub_mul_stripPoissonDensity_one_sub {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (1 - r) * stripPoissonDensity (1 - r) t =
      sin (π * r) / (2 * (cosh (π * t) - cos (π * r))) := by
  unfold stripPoissonDensity
  rw [show π * (1 - r) = π - π * r by ring, sin_pi_sub, cos_pi_sub]
  have hr1 : 1 - r ≠ 0 := by linarith [hr.2]
  field_simp [hr1]
  ring

/-- The right strip harmonic-measure density is exactly `rβ_r`. -/
private theorem mul_stripPoissonDensity {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    r * stripPoissonDensity r t = sin (π * r) / (2 * (cosh (π * t) + cos (π * r))) := by
  unfold stripPoissonDensity
  field_simp [hr]

end Real

end

section

open Real Set Metric

namespace Complex

/-- The Cayley map with prescribed upper-half-plane center `a + ib`. -/
private noncomputable def hirschmanDiskToHalfPlane (a b : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) + (b : ℂ) * I * ((1 + z) / (1 - z))

/-- The real part of the basic Cayley quotient. -/
private theorem cayleyQuotient_re (z : ℂ) :
    ((1 + z) / (1 - z)).re = (1 - normSq z) / normSq (1 - z) := by
  rw [div_re]
  simp only [add_re, sub_re, one_re, add_im, sub_im, one_im, zero_add, zero_sub, normSq_apply]
  ring

/-- The imaginary part records positivity on the disk exactly. -/
private theorem hirschmanDiskToHalfPlane_im (a b : ℝ) (z : ℂ) :
    (hirschmanDiskToHalfPlane a b z).im = b * (1 - normSq z) / normSq (1 - z) := by
  simp only [hirschmanDiskToHalfPlane, add_im, ofReal_im, zero_add, mul_im, mul_re,
    ofReal_re, I_im, I_re, mul_one, mul_zero, zero_mul, sub_zero, add_zero]
  rw [cayleyQuotient_re]
  ring

/-- The entire open unit disk maps into the upper half-plane. -/
private theorem hirschmanDiskToHalfPlane_im_pos (a : ℝ) {b : ℝ} (hb : 0 < b)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 < (hirschmanDiskToHalfPlane a b z).im := by
  have hzn : ‖z‖ < 1 := by simpa using hz
  have hz1 : z ≠ 1 := by intro h; subst z; simp at hzn
  have hden : 0 < normSq (1 - z) := normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)
  have hnum : 0 < 1 - normSq z := by
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  rw [hirschmanDiskToHalfPlane_im]
  exact div_pos (mul_pos hb hnum) hden

/-- The explicit logarithmic map to the vertical strip `0 < Re z < 1`. -/
private noncomputable def hirschmanDiskToStrip (r : ℝ) (z : ℂ) : ℂ :=
  log (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) z) * (-I) / (π : ℂ)

/-- Its real part is the normalized half-plane argument. -/
private theorem hirschmanDiskToStrip_re (r : ℝ) (z : ℂ) :
    (hirschmanDiskToStrip r z).re =
      arg (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) z) / π := by
  simp [hirschmanDiskToStrip, div_ofReal_re, mul_re, log_im]

/-- Every point of the open disk maps strictly inside the vertical strip. -/
private theorem hirschmanDiskToStrip_re_mem_Ioo {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : (hirschmanDiskToStrip r z).re ∈ Ioo (0 : ℝ) 1 := by
  have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  have him := hirschmanDiskToHalfPlane_im_pos (Real.cos (π * r)) hs hz
  rw [hirschmanDiskToStrip_re]
  constructor
  · apply div_pos _ pi_pos
    exact lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) (by
      intro h
      exact him.ne' (arg_eq_zero_iff.mp h.symm).2)
  · apply (div_lt_one pi_pos).2
    exact arg_lt_pi_iff.mpr (Or.inr (ne_of_gt him))

/-- The disk center maps to precisely the prescribed interpolation parameter. -/
private theorem hirschmanDiskToStrip_zero {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    hirschmanDiskToStrip r 0 = (r : ℂ) := by
  have hcenter : hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) 0 =
      exp (((π * r : ℝ) : ℂ) * I) := by
    simp [hirschmanDiskToHalfPlane, exp_mul_I]
  unfold hirschmanDiskToStrip
  rw [hcenter, log_exp (by simp; nlinarith [pi_pos, hr.1]) (by simp; nlinarith [pi_pos, hr.2])]
  simp only [ofReal_mul]
  field_simp
  simp [I_sq]

/-- The disk-to-strip map is holomorphic throughout the open unit disk. -/
private theorem differentiableAt_hirschmanDiskToStrip {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : DifferentiableAt ℂ (hirschmanDiskToStrip r) z := by
  have hzn : ‖z‖ < 1 := by simpa using hz
  have hz1 : z ≠ 1 := by intro h; subst z; simp at hzn
  have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  have him := hirschmanDiskToHalfPlane_im_pos (Real.cos (π * r)) hs hz
  have hM : DifferentiableAt ℂ
      (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r))) z := by
    unfold hirschmanDiskToHalfPlane
    fun_prop (disch := exact sub_ne_zero.mpr hz1.symm)
  exact (((differentiableAt_log (Or.inr (ne_of_gt him))).comp z hM).mul_const (-I)).div_const _

private theorem analyticOnNhd_hirschmanDiskToStrip {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    AnalyticOnNhd ℂ (hirschmanDiskToStrip r) (ball (0 : ℂ) 1) := by
  apply (analyticOnNhd_iff_differentiableOn isOpen_ball).2
  exact fun z hz => (differentiableAt_hirschmanDiskToStrip hr hz).differentiableWithinAt

end Complex

end

section

open Real Set Metric MeasureTheory
open scoped NNReal

namespace Complex

/-- A bijective angle parametrization of the circle with the point `1` removed. -/
private noncomputable def hirschmanBoundaryAngle (q : ℝ) : ℝ := π + 2 * arctan q

private theorem hirschmanBoundaryAngle_mem (q : ℝ) :
    hirschmanBoundaryAngle q ∈ Ioo (0 : ℝ) (2 * π) := by
  dsimp [hirschmanBoundaryAngle]
  constructor <;> linarith [arctan_mem_Ioo q |>.1, arctan_mem_Ioo q |>.2]

private theorem strictMono_hirschmanBoundaryAngle : StrictMono hirschmanBoundaryAngle := by
  intro x y hxy
  dsimp [hirschmanBoundaryAngle]
  linarith [arctan_strictMono hxy]

private theorem range_hirschmanBoundaryAngle :
    Set.range hirschmanBoundaryAngle = Ioo (0 : ℝ) (2 * π) := by
  ext θ
  constructor
  · rintro ⟨q, rfl⟩
    exact hirschmanBoundaryAngle_mem q
  · intro hθ
    refine ⟨Real.tan ((θ - π) / 2), ?_⟩
    unfold hirschmanBoundaryAngle
    rw [Real.arctan_tan (by linarith [hθ.1]) (by linarith [hθ.2])]
    ring

private theorem hasDerivAt_hirschmanBoundaryAngle (q : ℝ) :
    HasDerivAt hirschmanBoundaryAngle (2 / (1 + q ^ 2)) q := by
  have h := ((Real.hasDerivAt_arctan q).const_mul 2).const_add π
  change HasDerivAt hirschmanBoundaryAngle (2 * (1 / (1 + q ^ 2))) q at h
  exact h.congr_deriv (by ring)

/-- The rational and trigonometric parametrizations are exactly equal. -/
private theorem circleMap_hirschmanBoundaryAngle (q : ℝ) :
    circleMap 0 1 (hirschmanBoundaryAngle q) = ((q : ℂ) - I) / ((q : ℂ) + I) := by
  have hcos : Real.cos (π + 2 * arctan q) = (q ^ 2 - 1) / (1 + q ^ 2) := by
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi, zero_mul, sub_zero, neg_one_mul,
      Real.cos_two_mul, Real.cos_sq_arctan]
    field_simp
    ring
  have hsin : Real.sin (π + 2 * arctan q) = -2 * q / (1 + q ^ 2) := by
    rw [Real.sin_add, Real.sin_pi, Real.cos_pi, zero_mul, zero_add, neg_one_mul,
      Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hs : sqrt (1 + q ^ 2) ≠ 0 := ne_of_gt (sqrt_pos.2 (by positivity))
    field_simp
    rw [sq_sqrt (by positivity)]
  apply Complex.ext
  · simp only [circleMap, zero_add, ofReal_one, one_mul, hirschmanBoundaryAngle,
      mul_I_re, mul_I_im, ofReal_im, ofReal_re, Complex.exp_re, neg_zero,
      zero_sub, Real.exp_zero, one_mul, div_re, sub_re, add_re, I_re, sub_zero,
      add_zero, sub_im, add_im, I_im, zero_sub, zero_add, normSq_apply]
    rw [hcos]
    ring
  · simp only [circleMap, zero_add, ofReal_one, one_mul, hirschmanBoundaryAngle,
      mul_I_re, mul_I_im, ofReal_im, ofReal_re, Complex.exp_im, neg_zero,
      zero_sub, Real.exp_zero, one_mul, div_im, sub_re, add_re, I_re, sub_zero,
      add_zero, sub_im, add_im, I_im, zero_sub, zero_add, normSq_apply]
    rw [hsin]
    ring

/-- In these boundary coordinates the prescribed half-plane map is simply affine. -/
private theorem hirschmanDiskToHalfPlane_circleMap_boundary (a b q : ℝ) :
    hirschmanDiskToHalfPlane a b (circleMap 0 1 (hirschmanBoundaryAngle q))
      = ((a + b * q : ℝ) : ℂ) := by
  rw [circleMap_hirschmanBoundaryAngle]
  have hden : (q : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have hne : ((q : ℂ) - I) / ((q : ℂ) + I) ≠ 1 := by
    intro h
    have he := (div_eq_one_iff_eq hden).mp h
    have := congrArg Complex.im he
    norm_num at this
  have hquot : (1 + ((q : ℂ) - I) / ((q : ℂ) + I)) /
      (1 - ((q : ℂ) - I) / ((q : ℂ) + I)) = -(q : ℂ) * I := by
    field_simp
    ring_nf
    simp [I_sq]
  unfold hirschmanDiskToHalfPlane
  rw [hquot]
  push_cast
  ring_nf
  simp [I_sq]

/-- The actual boundary circle average is exactly the arctangent parametrized
integral with the standard Cauchy density. -/
private theorem circleAverage_eq_integral_hirschmanBoundaryAngle (F : ℂ → ℝ) :
    Real.circleAverage F 0 1 =
      ∫ q : ℝ, (1 / (π * (1 + q ^ 2))) * F (circleMap 0 1 (hirschmanBoundaryAngle q)) := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun q _ => (hasDerivAt_hirschmanBoundaryAngle q).hasDerivWithinAt)
    strictMono_hirschmanBoundaryAngle.injective.injOn
    (fun θ => F (circleMap 0 1 θ))
  rw [image_univ, range_hirschmanBoundaryAngle] at hchange
  rw [Real.circleAverage, intervalIntegral.integral_of_le two_pi_pos.le,
    integral_Ioc_eq_integral_Ioo, hchange]
  simp only [Measure.restrict_univ, smul_eq_mul]
  have habs (q : ℝ) : |2 / (1 + q ^ 2)| = 2 / (1 + q ^ 2) := abs_of_pos (by positivity)
  simp_rw [habs]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun q => by
    field_simp

/-- The actual boundary circle average transports to the standard Cauchy
density and affine upper-half-plane boundary coordinates. -/
private theorem circleAverage_hirschmanDiskToHalfPlane (a b : ℝ) (F : ℂ → ℝ) :
    Real.circleAverage (fun z => F (hirschmanDiskToHalfPlane a b z)) 0 1 =
      ∫ q : ℝ, (1 / (π * (1 + q ^ 2))) * F ((a + b * q : ℝ) : ℂ) := by
  rw [circleAverage_eq_integral_hirschmanBoundaryAngle]
  simp_rw [hirschmanDiskToHalfPlane_circleMap_boundary]

/-- The affine Cayley map sends normalized angular measure on the unit circle to the real
Cauchy law with location $a$ and positive scale $b$. Its pole at $1$ has measure zero. -/
theorem circleAverage_eq_integral_cauchyPDFReal (a : ℝ) {b : ℝ≥0} (hb : 0 < b)
    (F : ℂ → ℝ) :
    Real.circleAverage (fun z => F ((a : ℂ) + ((b : ℝ) : ℂ) * I * ((1 + z) / (1 - z)))) 0 1 =
      ∫ w : ℝ, ProbabilityTheory.cauchyPDFReal a b w * F (w : ℂ) := by
  obtain ⟨b, hb₀⟩ := b
  change 0 < b at hb
  change Real.circleAverage (fun z => F (hirschmanDiskToHalfPlane a b z)) 0 1 = _
  have hRange : (fun q : ℝ => a + b * q) '' Set.univ = Set.univ := by
    ext w
    constructor
    · exact fun _ => Set.mem_univ _
    · intro _
      refine ⟨(w - a) / b, Set.mem_univ _, ?_⟩
      field_simp
      ring
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) MeasurableSet.univ
    (fun q _ => (((hasDerivAt_id q).const_mul b).const_add a).hasDerivWithinAt)
    (show Set.InjOn (fun q : ℝ => a + b * q) Set.univ from fun q _ w _ h => by
      have := (add_left_cancel h : b * q = b * w)
      exact mul_left_cancel₀ (ne_of_gt hb) this)
    (fun w : ℝ => ProbabilityTheory.cauchyPDFReal a (⟨b, hb.le⟩ : NNReal) w * F (w : ℂ))
  simp only [id_eq, mul_one] at hchange
  rw [hRange, Measure.restrict_univ] at hchange
  rw [circleAverage_hirschmanDiskToHalfPlane, hchange]
  apply integral_congr_ae
  exact ae_of_all _ fun q => by
    simp only [abs_of_pos hb, smul_eq_mul, ProbabilityTheory.cauchyPDFReal]
    change 1 / (π * (1 + q ^ 2)) * F ((a + b * q : ℝ) : ℂ) =
      b * (π⁻¹ * b * ((a + b * q - a) ^ 2 + b ^ 2)⁻¹ * F ((a + b * q : ℝ) : ℂ))
    have hd : b * (π⁻¹ * b * ((a + b * q - a) ^ 2 + b ^ 2)⁻¹) =
        1 / (π * (1 + q ^ 2)) := by
      field_simp
      ring
    rw [← mul_assoc, hd]

end Complex

end

section

open Real Set MeasureTheory

namespace MeasureTheory

/-- Exponential coordinates give an exact whole-line substitution for the
positive half-line, with their actual Jacobian. -/
private theorem integral_Ioi_zero_eq_exp_neg_pi (g : ℝ → ℝ) :
    (∫ w in Ioi (0 : ℝ), g w) =
      ∫ t : ℝ, (π * exp (-(π * t))) * g (exp (-(π * t))) := by
  have hRange : (fun t : ℝ => exp (-(π * t))) '' Set.univ = Ioi (0 : ℝ) := by
    ext w
    constructor
    · rintro ⟨t, _, rfl⟩
      exact exp_pos _
    · intro hw
      refine ⟨-(Real.log w) / π, Set.mem_univ _, ?_⟩
      change exp (-(π * (-(Real.log w) / π))) = w
      rw [show -(π * (-(Real.log w) / π)) = Real.log w by field_simp]
      exact exp_log hw
  have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => exp (-(π * t)))
      (-(π * exp (-(π * t)))) t := by
    have h := ((hasDerivAt_id t).const_mul π).neg.exp
    change HasDerivAt (fun t : ℝ => exp (-(π * t))) (exp (-(π * t)) * -(π * 1)) t at h
    exact h.congr_deriv (by ring)
  have hchange := integral_image_eq_integral_abs_deriv_smul (s := Set.univ) MeasurableSet.univ
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (show Set.InjOn (fun t : ℝ => exp (-(π * t))) Set.univ from fun t _ s _ h => by
      have he := exp_injective h
      nlinarith [pi_pos]) g
  rw [hRange, Measure.restrict_univ] at hchange
  simpa only [abs_neg, abs_of_pos (mul_pos pi_pos (exp_pos _)), smul_eq_mul] using hchange

/-- The negative half-line has the same positive Jacobian after reflection. -/
private theorem integral_Iio_zero_eq_neg_exp_neg_pi (g : ℝ → ℝ) :
    (∫ w in Iio (0 : ℝ), g w) =
      ∫ t : ℝ, (π * exp (-(π * t))) * g (-exp (-(π * t))) := by
  have hRange : (fun t : ℝ => -exp (-(π * t))) '' Set.univ = Iio (0 : ℝ) := by
    ext w
    constructor
    · rintro ⟨t, _, rfl⟩
      exact neg_neg_of_pos (exp_pos _)
    · intro hw
      refine ⟨-(Real.log (-w)) / π, Set.mem_univ _, ?_⟩
      change -exp (-(π * (-(Real.log (-w)) / π))) = w
      rw [show -(π * (-(Real.log (-w)) / π)) = Real.log (-w) by field_simp,
        exp_log (neg_pos.mpr hw), neg_neg]
  have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => -exp (-(π * t)))
      (π * exp (-(π * t))) t := by
    have h := (((hasDerivAt_id t).const_mul π).neg.exp).neg
    change HasDerivAt (fun t : ℝ => -exp (-(π * t))) (-(exp (-(π * t)) * -(π * 1))) t at h
    exact h.congr_deriv (by ring)
  have hchange := integral_image_eq_integral_abs_deriv_smul (s := Set.univ) MeasurableSet.univ
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (show Set.InjOn (fun t : ℝ => -exp (-(π * t))) Set.univ from fun t _ s _ h => by
      have he := exp_injective (neg_injective h)
      nlinarith [pi_pos]) g
  rw [hRange, Measure.restrict_univ] at hchange
  simpa only [abs_of_pos (mul_pos pi_pos (exp_pos _)), smul_eq_mul] using hchange

end MeasureTheory

namespace Complex

/-- The positive exponential coordinate lies on the left boundary of the strip. -/
private theorem hirschmanLog_positive_exp (t : ℝ) :
    log ((Real.exp (-(π * t)) : ℝ) : ℂ) * (-I) / (π : ℂ) = (t : ℂ) * I := by
  rw [← ofReal_log (Real.exp_pos _).le, Real.log_exp]
  push_cast
  field_simp

/-- The principal logarithm from the upper half-plane places the negative
exponential coordinate on the right boundary, with the same orientation. -/
private theorem hirschmanLog_negative_exp (t : ℝ) :
    log ((-Real.exp (-(π * t)) : ℝ) : ℂ) * (-I) / (π : ℂ) = 1 + (t : ℂ) * I := by
  have hneg : -Real.exp (-(π * t)) < 0 := neg_neg_of_pos (Real.exp_pos _)
  rw [Complex.log, norm_real, Real.norm_eq_abs, abs_of_neg hneg, neg_neg,
    Real.log_exp, arg_ofReal_of_neg hneg]
  push_cast
  field_simp
  ring_nf
  simp [I_sq]
  ring

end Complex

namespace Real

/-- The positive Cauchy boundary has exactly the left strip weight. -/
private theorem cauchyPDFReal_exp_neg_pi_mul_eq_hirschman_left {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (π * exp (-(π * t))) * ProbabilityTheory.cauchyPDFReal (cos (π * r))
      (Real.toNNReal (sin (π * r))) (exp (-(π * t))) =
      (1 - r) * stripPoissonDensity (1 - r) t := by
  have hs : 0 < sin (π * r) := sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  rw [one_sub_mul_stripPoissonDensity_one_sub hr]
  unfold ProbabilityTheory.cauchyPDFReal
  rw [Real.coe_toNNReal _ hs.le]
  have hden : (exp (-(π * t)) - cos (π * r)) ^ 2 + sin (π * r) ^ 2 =
      2 * exp (-(π * t)) * (cosh (π * t) - cos (π * r)) := by
    rw [cosh_eq, exp_neg]
    field_simp
    nlinarith [sin_sq_add_cos_sq (π * r)]
  rw [hden, mul_inv_rev, mul_inv_rev]
  field_simp

/-- The negative Cauchy boundary has exactly the right strip weight. -/
private theorem cauchyPDFReal_neg_exp_neg_pi_mul_eq_hirschman_right {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (π * exp (-(π * t))) * ProbabilityTheory.cauchyPDFReal (cos (π * r))
      (Real.toNNReal (sin (π * r))) (-exp (-(π * t))) = r * stripPoissonDensity r t := by
  have hs : 0 < sin (π * r) := sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  rw [mul_stripPoissonDensity (ne_of_gt hr.1)]
  unfold ProbabilityTheory.cauchyPDFReal
  rw [Real.coe_toNNReal _ hs.le]
  have hden : (-exp (-(π * t)) - cos (π * r)) ^ 2 + sin (π * r) ^ 2 =
      2 * exp (-(π * t)) * (cosh (π * t) + cos (π * r)) := by
    rw [cosh_eq, exp_neg]
    field_simp
    nlinarith [sin_sq_add_cos_sq (π * r)]
  rw [hden, mul_inv_rev, mul_inv_rev]
  field_simp

end Real

namespace Complex

/-- The logarithmic image of the Cauchy boundary measure splits into exactly
the two Stein–Hirschman boundary weights. -/
private theorem integral_cauchy_hirschmanLog_eq_boundary_integrals {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (G : ℂ → ℝ)
    (hG : Integrable (fun w : ℝ => ProbabilityTheory.cauchyPDFReal (Real.cos (π * r))
      (Real.toNNReal (Real.sin (π * r))) w * G (log (w : ℂ) * (-I) / (π : ℂ)))) :
    (∫ w : ℝ, ProbabilityTheory.cauchyPDFReal (Real.cos (π * r))
      (Real.toNNReal (Real.sin (π * r))) w * G (log (w : ℂ) * (-I) / (π : ℂ))) =
      (∫ t : ℝ, ((1 - r) * stripPoissonDensity (1 - r) t) * G ((t : ℂ) * I)) +
      ∫ t : ℝ, (r * stripPoissonDensity r t) * G (1 + (t : ℂ) * I) := by
  rw [← integral_add_compl measurableSet_Iic hG, compl_Iic, integral_Iic_eq_integral_Iio,
    integral_Iio_zero_eq_neg_exp_neg_pi, integral_Ioi_zero_eq_exp_neg_pi, add_comm]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      rw [hirschmanLog_positive_exp, ← mul_assoc,
        cauchyPDFReal_exp_neg_pi_mul_eq_hirschman_left hr]
  · apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      rw [hirschmanLog_negative_exp, ← mul_assoc,
        cauchyPDFReal_neg_exp_neg_pi_mul_eq_hirschman_right hr]

/-- The conformal disk boundary average equals the explicit weighted averages
on the two vertical strip boundaries. The hypothesis ensures the integrability
of the boundary function. -/
private theorem circleAverage_hirschmanDiskToStrip_eq_boundary_integrals {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (G : ℂ → ℝ)
    (hG : Integrable (fun w : ℝ => ProbabilityTheory.cauchyPDFReal (Real.cos (π * r))
      (Real.toNNReal (Real.sin (π * r))) w * G (log (w : ℂ) * (-I) / (π : ℂ)))) :
    Real.circleAverage (fun z => G (hirschmanDiskToStrip r z)) 0 1 =
      (∫ t : ℝ, ((1 - r) * stripPoissonDensity (1 - r) t) * G ((t : ℂ) * I)) +
      ∫ t : ℝ, (r * stripPoissonDensity r t) * G (1 + (t : ℂ) * I) := by
  have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  have h := circleAverage_eq_integral_cauchyPDFReal (Real.cos (π * r)) (Real.toNNReal_pos.mpr hs)
    (fun w => G (log w * (-I) / (π : ℂ)))
  simp only [Real.coe_toNNReal _ hs.le] at h
  exact h.trans (integral_cauchy_hirschmanLog_eq_boundary_integrals hr G hG)

end Complex

end

section

open Real Set Metric MeasureTheory Filter
open scoped Topology

namespace Complex

/-- The arctangent circle parametrization never takes the omitted point `1`. -/
private theorem circleMap_hirschmanBoundaryAngle_ne_one (q : ℝ) :
    circleMap 0 1 (hirschmanBoundaryAngle q) ≠ 1 := by
  rw [circleMap_hirschmanBoundaryAngle]
  have hden : (q : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  intro h
  have he := (div_eq_one_iff_eq hden).mp h
  have := congrArg Complex.im he
  norm_num at this

/-- Every real boundary coordinate maps into the closed vertical strip,
including the harmless convention at the single zero coordinate. -/
private theorem hirschmanLog_real_re_mem_Icc (w : ℝ) :
    (log (w : ℂ) * (-I) / (π : ℂ)).re ∈ Icc (0 : ℝ) 1 := by
  have heq : (log (w : ℂ) * (-I) / (π : ℂ)).re = arg (w : ℂ) / π := by
    simp [div_ofReal_re, mul_re, log_im]
  rw [heq]
  exact ⟨div_nonneg (arg_nonneg_iff.mpr (by simp)) pi_pos.le,
    (div_le_one pi_pos).mpr (arg_le_pi _)⟩

/-- Measurability of the real logarithmic boundary is available even though
the complex logarithm is not continuous across its branch cut. -/
private theorem measurable_hirschmanLog_real :
    Measurable (fun w : ℝ => log (w : ℂ) * (-I) / (π : ℂ)) := by
  fun_prop

/-- A continuous function on the closed strip gives a measurable boundary
observable; no measurability outside the strip is required. -/
private theorem _root_.ContinuousOn.measurable_comp_hirschmanLog_real {g : ℂ → ℂ}
    (hg : ContinuousOn g (HadamardThreeLines.verticalClosedStrip 0 1)) :
    Measurable (fun w : ℝ => g (log (w : ℂ) * (-I) / (π : ℂ))) := by
  let f : ℝ → HadamardThreeLines.verticalClosedStrip 0 1 := fun w =>
    ⟨log (w : ℂ) * (-I) / (π : ℂ), hirschmanLog_real_re_mem_Icc w⟩
  have hgc : Continuous (fun z : HadamardThreeLines.verticalClosedStrip 0 1 => g z) :=
    continuousOn_iff_continuous_domRestrict.mp hg
  exact hgc.measurable.comp (show Measurable f from measurable_hirschmanLog_real.subtype_mk)

/-- Limits from the open disk give the principal logarithmic boundary value
at every finite boundary coordinate except the one mapping to zero. -/
private theorem tendsto_hirschmanDiskToStrip_boundary {r q : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {u : ℕ → ℂ}
    (hu : ∀ n, u n ∈ ball (0 : ℂ) 1)
    (hlim : Tendsto u atTop (𝓝 (circleMap 0 1 (hirschmanBoundaryAngle q))))
    (hw : Real.cos (π * r) + Real.sin (π * r) * q ≠ 0) :
    Tendsto (fun n => hirschmanDiskToStrip r (u n)) atTop
      (𝓝 (log ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ) * (-I) / (π : ℂ))) := by
  have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
    (by nlinarith [pi_pos, hr.2])
  have hM : ContinuousAt (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)))
      (circleMap 0 1 (hirschmanBoundaryAngle q)) := by
    unfold hirschmanDiskToHalfPlane
    fun_prop (disch := exact sub_ne_zero.mpr (circleMap_hirschmanBoundaryAngle_ne_one q).symm)
  have hMl : Tendsto
      (fun n => hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) (u n))
      atTop (𝓝 ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ)) := by
    have ht := hM.tendsto.comp hlim
    rw [hirschmanDiskToHalfPlane_circleMap_boundary] at ht
    exact ht.congr' (Eventually.of_forall fun _ => rfl)
  have hlog : Tendsto
      (fun n => log (hirschmanDiskToHalfPlane (Real.cos (π * r)) (Real.sin (π * r)) (u n)))
      atTop (𝓝 (log ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ))) := by
    by_cases hp : 0 < Real.cos (π * r) + Real.sin (π * r) * q
    · exact (differentiableAt_log (Or.inl hp)).continuousAt.tendsto.comp hMl
    · have hn : Real.cos (π * r) + Real.sin (π * r) * q < 0 := lt_of_le_of_ne (le_of_not_gt hp) hw
      exact (continuousWithinAt_log_of_re_neg_of_im_zero
        (z := ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ)) hn rfl).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hMl, Eventually.of_forall fun n =>
          (hirschmanDiskToHalfPlane_im_pos (Real.cos (π * r)) hs (hu n)).le⟩)
  exact (hlog.mul_const (-I)).div_const (π : ℂ)

/-- Radial circles of radius strictly below one remain inside the conformal
domain and depend continuously on their real boundary parameter. -/
private theorem continuous_hirschmanDiskToStrip_radial {r ρ : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun q : ℝ => hirschmanDiskToStrip r
      ((ρ : ℂ) * circleMap 0 1 (hirschmanBoundaryAngle q))) := by
  apply (analyticOnNhd_hirschmanDiskToStrip hr).continuousOn.comp_continuous
  · unfold hirschmanBoundaryAngle
    fun_prop
  · intro q
    have hn : ‖(ρ : ℂ) * circleMap 0 1 (hirschmanBoundaryAngle q)‖ < 1 := by
      simpa [norm_mul, norm_circleMap_zero, abs_of_pos hρ.1] using hρ.2
    simpa using hn

/-- A strictly positive regularization of the logarithmic norm. -/
private noncomputable def regularizedLogNorm (ε : ℝ) (z : ℂ) : ℝ :=
  Real.log (sqrt (‖z‖ ^ 2 + ε ^ 2))

private theorem continuous_regularizedLogNorm {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedLogNorm ε) := by
  apply Continuous.log _ (fun z => ne_of_gt (sqrt_pos.mpr (by positivity)))
  exact ((continuous_norm.pow 2).add continuous_const).sqrt

/-- Both sides of the regularized logarithm have explicit uniform bounds. -/
private theorem regularizedLogNorm_bounds {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ B) :
    Real.log ε ≤ regularizedLogNorm ε z ∧
      regularizedLogNorm ε z ≤ Real.log (sqrt (B ^ 2 + ε ^ 2)) := by
  have hpos : 0 < sqrt (‖z‖ ^ 2 + ε ^ 2) := sqrt_pos.mpr (by positivity)
  constructor
  · apply Real.log_le_log hε
    calc
      ε = sqrt (ε ^ 2) := (sqrt_sq hε.le).symm
      _ ≤ _ := sqrt_le_sqrt (by nlinarith [sq_nonneg ‖z‖])
  · apply Real.log_le_log hpos
    apply sqrt_le_sqrt
    nlinarith [norm_nonneg z]

/-- A bounded strip function has a bounded regularized logarithmic boundary. -/
private theorem abs_regularizedLogNorm_le {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ B) :
    |regularizedLogNorm ε z| ≤ |Real.log ε| + |Real.log (sqrt (B ^ 2 + ε ^ 2))| := by
  have h := regularizedLogNorm_bounds hε hB hz
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log ε), abs_nonneg (Real.log (sqrt (B ^ 2 + ε ^ 2)))]
  · linarith [le_abs_self (Real.log (sqrt (B ^ 2 + ε ^ 2))), abs_nonneg (Real.log ε)]

/-- The regularized boundary observable is genuinely Bochner integrable
against every Cauchy density. -/
private theorem integrable_cauchy_mul_regularizedLog_boundary {g : ℂ → ℂ}
    (hg : ContinuousOn g (HadamardThreeLines.verticalClosedStrip 0 1))
    {B ε : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖g z‖ ≤ B)
    (hε : 0 < ε) (a : ℝ) (b : NNReal) :
    Integrable (fun w : ℝ => ProbabilityTheory.cauchyPDFReal a b w *
      regularizedLogNorm ε (g (log (w : ℂ) * (-I) / (π : ℂ)))) := by
  have hm := (continuous_regularizedLogNorm hε).measurable.comp
    hg.measurable_comp_hirschmanLog_real
  apply ((ProbabilityTheory.integrable_cauchyPDFReal a (γ := b)).const_mul
    (|Real.log ε| + |Real.log (sqrt (B ^ 2 + ε ^ 2))|)).mono'
    ((ProbabilityTheory.measurable_cauchyPDFReal a b).mul hm).aestronglyMeasurable
  exact ae_of_all _ fun w => by
    dsimp only [Pi.mul_apply, Function.comp_apply]
    have hp : 0 ≤ ProbabilityTheory.cauchyPDFReal a b w := by
      unfold ProbabilityTheory.cauchyPDFReal
      positivity
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hp, Real.norm_eq_abs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (abs_regularizedLogNorm_le hε hB (hbound _ (hirschmanLog_real_re_mem_Icc w))) hp

/-- The standard Cauchy density is exactly the arctangent angular Jacobian. -/
private theorem hirschmanBoundaryWeight_eq_cauchy (q : ℝ) :
    1 / (π * (1 + q ^ 2)) = ProbabilityTheory.cauchyPDFReal 0 1 q := by
  simp only [ProbabilityTheory.cauchyPDFReal, NNReal.coe_one, sub_zero, one_pow, mul_one]
  field_simp
  ring

/-- Scaling the circle radius can be moved into its integrand exactly. -/
private theorem circleAverage_zero_radius_eq_circleAverage_smul (F : ℂ → ℝ) (ρ : ℝ) :
    Real.circleAverage F 0 ρ = Real.circleAverage (fun z => F ((ρ : ℂ) * z)) 0 1 := by
  simp only [Real.circleAverage, circleMap, zero_add, ofReal_one, one_mul]

end Complex

end

section

open Real Set Metric MeasureTheory Filter
open scoped Topology

namespace Complex

/-- Regularized logarithmic disk averages converge to the boundary
average, for a bounded function continuous only on the closed strip. -/
private theorem tendsto_circleAverage_regularizedLogNorm_hirschman {r B ε : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {g : ℂ → ℂ}
    (hg : ContinuousOn g (HadamardThreeLines.verticalClosedStrip 0 1))
    (hB : 0 ≤ B)
    (hbound : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖g z‖ ≤ B)
    (hε : 0 < ε) {ρ : ℕ → ℝ} (hρ : ∀ n, ρ n ∈ Ioo (0 : ℝ) 1)
    (hρlim : Tendsto ρ atTop (𝓝 1)) :
    Tendsto (fun n => Real.circleAverage
      (fun z => regularizedLogNorm ε (g (hirschmanDiskToStrip r z))) 0 (ρ n)) atTop
      (𝓝 (Real.circleAverage (fun z => regularizedLogNorm ε
        (g (hirschmanDiskToStrip r z))) 0 1)) := by
  let C := |Real.log ε| + |Real.log (sqrt (B ^ 2 + ε ^ 2))|
  let P := ProbabilityTheory.cauchyPDFReal (0 : ℝ) (1 : NNReal)
  let U (n : ℕ) (q : ℝ) := (ρ n : ℂ) * circleMap 0 1 (hirschmanBoundaryAngle q)
  let W (q : ℝ) := log ((Real.cos (π * r) + Real.sin (π * r) * q : ℝ) : ℂ) * (-I) / (π : ℂ)
  have hU (n : ℕ) (q : ℝ) : U n q ∈ ball (0 : ℂ) 1 := by
    have hn : ‖U n q‖ < 1 := by
      simpa [U, norm_mul, norm_circleMap_zero, abs_of_pos (hρ n).1] using (hρ n).2
    simpa using hn
  have hstrip (n : ℕ) (q : ℝ) :
      hirschmanDiskToStrip r (U n q) ∈ HadamardThreeLines.verticalClosedStrip 0 1 :=
    Ioo_subset_Icc_self (hirschmanDiskToStrip_re_mem_Ioo hr (hU n q))
  have hcont (n : ℕ) : Continuous (fun q : ℝ => regularizedLogNorm ε
      (g (hirschmanDiskToStrip r (U n q)))) :=
    (continuous_regularizedLogNorm hε).comp
      (hg.comp_continuous (continuous_hirschmanDiskToStrip_radial hr (hρ n)) (hstrip n))
  have hlim : ∀ᵐ q : ℝ, Tendsto (fun n => P q * regularizedLogNorm ε
      (g (hirschmanDiskToStrip r (U n q)))) atTop (𝓝 (P q * regularizedLogNorm ε (g (W q)))) := by
    have hs : 0 < Real.sin (π * r) := Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hr.1)
      (by nlinarith [pi_pos, hr.2])
    filter_upwards [volume.ae_ne (-Real.cos (π * r) / Real.sin (π * r))] with q hq
    have hw : Real.cos (π * r) + Real.sin (π * r) * q ≠ 0 := by
      intro h
      apply hq
      apply (eq_div_iff (ne_of_gt hs)).mpr
      linarith
    have hUl : Tendsto (fun n => U n q) atTop
        (𝓝 (circleMap 0 1 (hirschmanBoundaryAngle q))) := by
      have ht := ((continuous_ofReal.tendsto _).comp hρlim).mul_const
        (circleMap 0 1 (hirschmanBoundaryAngle q))
      simp only [ofReal_one, one_mul] at ht
      exact ht.congr' (Eventually.of_forall fun _ => rfl)
    have hφ := tendsto_hirschmanDiskToStrip_boundary hr (fun n => hU n q) hUl hw
    have hgl : Tendsto (fun n => g (hirschmanDiskToStrip r (U n q))) atTop (𝓝 (g (W q))) :=
      (hg _ (hirschmanLog_real_re_mem_Icc _)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hφ, Eventually.of_forall fun n => hstrip n q⟩)
    exact ((continuous_regularizedLogNorm hε).continuousAt.tendsto.comp hgl).const_mul (P q)
  have hDCT := tendsto_integral_of_dominated_convergence (fun q : ℝ => C * P q)
    (fun n => ((ProbabilityTheory.measurable_cauchyPDFReal 0 1).mul
        (hcont n).measurable).aestronglyMeasurable)
    ((ProbabilityTheory.integrable_cauchyPDFReal 0 (γ := 1)).const_mul C)
    (fun n => ae_of_all _ fun q => by
      have hp : 0 ≤ P q := by dsimp [P, ProbabilityTheory.cauchyPDFReal]; positivity
      dsimp only [Pi.mul_apply, Function.comp_apply]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hp, Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (abs_regularizedLogNorm_le hε hB (hbound _ (hstrip n q))) hp)
    hlim
  have hEq (n : ℕ) : Real.circleAverage
      (fun z => regularizedLogNorm ε (g (hirschmanDiskToStrip r z))) 0 (ρ n) =
      ∫ q : ℝ, P q * regularizedLogNorm ε (g (hirschmanDiskToStrip r (U n q))) := by
    rw [circleAverage_zero_radius_eq_circleAverage_smul,
      circleAverage_eq_integral_hirschmanBoundaryAngle]
    simp_rw [hirschmanBoundaryWeight_eq_cauchy]
    rfl
  have hEqB : Real.circleAverage
      (fun z => regularizedLogNorm ε (g (hirschmanDiskToStrip r z))) 0 1 =
      ∫ q : ℝ, P q * regularizedLogNorm ε (g (W q)) := by
    rw [circleAverage_eq_integral_hirschmanBoundaryAngle]
    simp_rw [hirschmanBoundaryWeight_eq_cauchy]
    congr 1
    funext q
    simp only [hirschmanDiskToStrip, hirschmanDiskToHalfPlane_circleMap_boundary, W, P]
  simpa only [hEq, hEqB, Pi.mul_apply, P] using hDCT

/-- The actual bounded holomorphic strip function satisfies the logarithmic
boundary inequality after positive regularization. No nonvanishing hypothesis
on the function, on the center, or on either boundary is imposed. -/
private theorem regularizedLogNorm_le_hirschman_boundary_integrals {r B ε : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {g : ℂ → ℂ}
    (hg : ContinuousOn g (HadamardThreeLines.verticalClosedStrip 0 1))
    (ha : AnalyticOnNhd ℂ g (HadamardThreeLines.verticalStrip 0 1))
    (hB : 0 ≤ B)
    (hbound : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖g z‖ ≤ B)
    (hε : 0 < ε) :
    regularizedLogNorm ε (g (r : ℂ)) ≤
      (∫ t : ℝ, ((1 - r) * stripPoissonDensity (1 - r) t) *
        regularizedLogNorm ε (g ((t : ℂ) * I))) +
      ∫ t : ℝ, (r * stripPoissonDensity r t) *
        regularizedLogNorm ε (g (1 + (t : ℂ) * I)) := by
  obtain ⟨ρ, -, hρ, hρlim⟩ := exists_seq_strictMono_tendsto' (show (0 : ℝ) < 1 by norm_num)
  have hlim := tendsto_circleAverage_regularizedLogNorm_hirschman hr hg hB hbound hε hρ hρlim
  have hle : regularizedLogNorm ε (g (r : ℂ)) ≤
      Real.circleAverage (fun z => regularizedLogNorm ε (g (hirschmanDiskToStrip r z))) 0 1 := by
    apply ge_of_tendsto' hlim
    intro n
    have hf : AnalyticOnNhd ℂ (fun z => g (hirschmanDiskToStrip r z)) (closedBall 0 (ρ n)) := by
      intro z hz
      have hn : ‖z‖ ≤ ρ n := by simpa using hz
      have hb : z ∈ ball (0 : ℂ) 1 := by simpa using hn.trans_lt (hρ n).2
      exact (ha _ (hirschmanDiskToStrip_re_mem_Ioo hr hb)).comp
        (analyticOnNhd_hirschmanDiskToStrip hr _ hb)
    have hj := hf.log_sqrt_norm_sq_add_sq_le_circleAverage (hρ n).1 hε
    simpa only [hirschmanDiskToStrip_zero hr, regularizedLogNorm] using hj
  rw [circleAverage_hirschmanDiskToStrip_eq_boundary_integrals hr
    (fun z => regularizedLogNorm ε (g z))
    (integrable_cauchy_mul_regularizedLog_boundary hg hB hbound hε _ _)] at hle
  exact hle

end Complex

end

section

open Set Filter MeasureTheory Real
open scoped Topology

namespace Complex

/-- Exponential majorants retain a lower bound even as regularization tends
to zero, so negative logarithmic parts are controlled honestly. -/
private theorem regularizedLogNorm_exp_bounds {ε H x : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1)
    (hx : |x| ≤ H) :
    -H ≤ regularizedLogNorm ε ((Real.exp x : ℝ) : ℂ) ∧
      regularizedLogNorm ε ((Real.exp x : ℝ) : ℂ) ≤
        Real.log (sqrt ((Real.exp H) ^ 2 + 1)) := by
  have hn : ‖((Real.exp x : ℝ) : ℂ)‖ = Real.exp x := by
    simp only [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
  have hpos : 0 < sqrt ((Real.exp x) ^ 2 + ε ^ 2) := sqrt_pos.mpr (by positivity)
  have hxH := (abs_le.mp hx).2
  have he : Real.exp x ≤ Real.exp H := Real.exp_le_exp.mpr hxH
  unfold regularizedLogNorm
  rw [hn]
  constructor
  · calc
      -H ≤ x := (abs_le.mp hx).1
      _ = Real.log (Real.exp x) := (Real.log_exp x).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos x) (by
        calc
          Real.exp x = sqrt ((Real.exp x) ^ 2) := (sqrt_sq (Real.exp_pos x).le).symm
          _ ≤ _ := sqrt_le_sqrt (by nlinarith [sq_nonneg ε]))
  · apply Real.log_le_log hpos
    apply sqrt_le_sqrt
    nlinarith [Real.exp_pos x, Real.exp_pos H, hε.1, hε.2]

/-- A uniform absolute bound for all regularizations between zero and one. -/
private theorem abs_regularizedLogNorm_exp_le {ε H x : ℝ} (hε : ε ∈ Icc (0 : ℝ) 1)
    (hH : 0 ≤ H) (hx : |x| ≤ H) :
    |regularizedLogNorm ε ((Real.exp x : ℝ) : ℂ)| ≤
      H + |Real.log (sqrt ((Real.exp H) ^ 2 + 1))| := by
  have h := regularizedLogNorm_exp_bounds hε hx
  rw [abs_le]
  constructor
  · linarith [abs_nonneg (Real.log (sqrt ((Real.exp H) ^ 2 + 1)))]
  · linarith [le_abs_self (Real.log (sqrt ((Real.exp H) ^ 2 + 1)))]

/-- At every real majorant value the regularized logarithm converges to that
same value, since its unregularized exponential is strictly positive. -/
private theorem tendsto_regularizedLogNorm_exp {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n => regularizedLogNorm (ε n) ((Real.exp x : ℝ) : ℂ)) atTop (𝓝 x) := by
  have ht := ((tendsto_const_nhds (x := (Real.exp x) ^ 2)).add (hε.pow 2)).sqrt
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sqrt_sq (Real.exp_pos x).le] at ht
  have hl := (Real.continuousAt_log (Real.exp_ne_zero x)).tendsto.comp ht
  simpa only [Function.comp_def, regularizedLogNorm, norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos x),
    Real.log_exp] using hl

/-- Dominated convergence removes logarithmic regularization under the exact
Stein--Hirschman probability density. -/
private theorem tendsto_integral_hirschman_regularizedLogNorm_exp {r H : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {h : ℝ → ℝ} (hh : Measurable h)
    (hH : 0 ≤ H) (hbound : ∀ t, |h t| ≤ H)
    {ε : ℕ → ℝ} (hε : ∀ n, ε n ∈ Ioo (0 : ℝ) 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t : ℝ, stripPoissonDensity r t *
      regularizedLogNorm (ε n) ((Real.exp (h t) : ℝ) : ℂ)) atTop
      (𝓝 (∫ t : ℝ, stripPoissonDensity r t * h t)) := by
  let C := H + |Real.log (sqrt ((Real.exp H) ^ 2 + 1))|
  apply tendsto_integral_of_dominated_convergence (fun t => C * stripPoissonDensity r t)
  · intro n
    have hm := ((continuous_regularizedLogNorm (hε n).1).comp
      (continuous_ofReal.comp Real.continuous_exp)).measurable.comp hh
    exact ((continuous_stripPoissonDensity hr).measurable.mul hm).aestronglyMeasurable
  · exact (integrable_stripPoissonDensity hr).const_mul C
  · intro n
    exact ae_of_all _ fun t => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (stripPoissonDensity_pos hr t), Real.norm_eq_abs]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (abs_regularizedLogNorm_exp_le (Ioo_subset_Icc_self (hε n)) hH (hbound t))
        (stripPoissonDensity_pos hr t).le
  · exact ae_of_all _ fun t => (tendsto_regularizedLogNorm_exp hεlim (h t)).const_mul _

/-- An exponential bound on the norm gives the same bound after
positive logarithmic regularization. -/
private theorem regularizedLogNorm_le_exp_of_norm_le {ε x : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ ≤ Real.exp x) :
    regularizedLogNorm ε z ≤ regularizedLogNorm ε ((Real.exp x : ℝ) : ℂ) := by
  have h := (regularizedLogNorm_bounds hε (Real.exp_pos x).le hz).2
  simpa only [regularizedLogNorm, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using h

end Complex

end

section

open Real Set Filter MeasureTheory
open scoped Topology

namespace Complex

/-- The scalar Stein–Hirschman inequality bounds the interior modulus by the weighted
geometric mean of two measurable boundary majorants, including functions with zeros
[SutterBertaTomamichel2017, Theorem 3.1]. -/
theorem norm_le_exp_integral_stripHarmonicMeasure {r B H : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (HadamardThreeLines.verticalStrip 0 1))
    (hbound : ∀ z ∈ HadamardThreeLines.verticalClosedStrip 0 1, ‖g z‖ ≤ B)
    (h₀ h₁ : ℝ → ℝ) (hm₀ : Measurable h₀) (hm₁ : Measurable h₁)
    (hb₀ : ∀ t, |h₀ t| ≤ H) (hb₁ : ∀ t, |h₁ t| ≤ H)
    (hleft : ∀ t : ℝ, ‖g ((t : ℂ) * I)‖ ≤ Real.exp (h₀ t))
    (hright : ∀ t : ℝ, ‖g (1 + (t : ℂ) * I)‖ ≤ Real.exp (h₁ t)) :
    ‖g (r : ℂ)‖ ≤ Real.exp (
      (1 - r) * (∫ t, h₀ t ∂stripHarmonicMeasure (1 - r)) +
      r * (∫ t, h₁ t ∂stripHarmonicMeasure r)) := by
  have hcl : closure (HadamardThreeLines.verticalStrip 0 1) =
      HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp only [HadamardThreeLines.verticalStrip, HadamardThreeLines.verticalClosedStrip,
      closure_preimage_re, closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
  have hc := hg.continuousOn
  rw [hcl] at hc
  have ha : AnalyticOnNhd ℂ g (HadamardThreeLines.verticalStrip 0 1) :=
    (analyticOnNhd_iff_differentiableOn (isOpen_Ioo.preimage continuous_re)).mpr hg.differentiableOn
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hbound 0 (by
    simp [HadamardThreeLines.verticalClosedStrip]))
  have hH : 0 ≤ H := (abs_nonneg (h₀ 0)).trans (hb₀ 0)
  have hrr : 1 - r ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hmap₀ (t : ℝ) : (t : ℂ) * I ∈ HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [HadamardThreeLines.verticalClosedStrip]
  have hmap₁ (t : ℝ) : 1 + (t : ℂ) * I ∈ HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [HadamardThreeLines.verticalClosedStrip]
  have hcont₀ : Continuous (fun t : ℝ => g ((t : ℂ) * I)) := by
    simpa only [Function.comp_def] using hc.comp_continuous (by fun_prop) hmap₀
  have hcont₁ : Continuous (fun t : ℝ => g (1 + (t : ℂ) * I)) := by
    simpa only [Function.comp_def] using hc.comp_continuous (by fun_prop) hmap₁
  obtain ⟨ε, -, hε, hεlim⟩ := exists_seq_strictAnti_tendsto' (show (0 : ℝ) < 1 by norm_num)
  have hlim₀ := tendsto_integral_hirschman_regularizedLogNorm_exp hrr hm₀ hH hb₀ hε hεlim
  have hlim₁ := tendsto_integral_hirschman_regularizedLogNorm_exp hr hm₁ hH hb₁ hε hεlim
  have hrightlim := (hlim₀.const_mul (1 - r)).add (hlim₁.const_mul r)
  have hfinal (n : ℕ) : sqrt (‖g (r : ℂ)‖ ^ 2 + (ε n) ^ 2) ≤
      Real.exp ((1 - r) * (∫ t : ℝ, stripPoissonDensity (1 - r) t *
        regularizedLogNorm (ε n) ((Real.exp (h₀ t) : ℝ) : ℂ)) +
        r * (∫ t : ℝ, stripPoissonDensity r t *
          regularizedLogNorm (ε n) ((Real.exp (h₁ t) : ℝ) : ℂ))) := by
    have hgint₀ := integrable_stripPoissonDensity_mul_of_bounded hrr
      ((continuous_regularizedLogNorm (hε n).1).comp hcont₀).measurable
      (fun t => abs_regularizedLogNorm_le (hε n).1 hB (hbound _ (hmap₀ t)))
    have hgint₁ := integrable_stripPoissonDensity_mul_of_bounded hr
      ((continuous_regularizedLogNorm (hε n).1).comp hcont₁).measurable
      (fun t => abs_regularizedLogNorm_le (hε n).1 hB (hbound _ (hmap₁ t)))
    have hmeas₀ := ((continuous_regularizedLogNorm (hε n).1).comp
      (continuous_ofReal.comp Real.continuous_exp)).measurable.comp hm₀
    have hmeas₁ := ((continuous_regularizedLogNorm (hε n).1).comp
      (continuous_ofReal.comp Real.continuous_exp)).measurable.comp hm₁
    have hhint₀ := integrable_stripPoissonDensity_mul_of_bounded hrr hmeas₀
      (fun t => abs_regularizedLogNorm_exp_le (Ioo_subset_Icc_self (hε n)) hH (hb₀ t))
    have hhint₁ := integrable_stripPoissonDensity_mul_of_bounded hr hmeas₁
      (fun t => abs_regularizedLogNorm_exp_le (Ioo_subset_Icc_self (hε n)) hH (hb₁ t))
    have hmono₀ := integral_mono hgint₀ hhint₀ (fun t =>
      mul_le_mul_of_nonneg_left (regularizedLogNorm_le_exp_of_norm_le (hε n).1 (hleft t))
        (stripPoissonDensity_pos hrr t).le)
    have hmono₁ := integral_mono hgint₁ hhint₁ (fun t =>
      mul_le_mul_of_nonneg_left (regularizedLogNorm_le_exp_of_norm_le (hε n).1 (hright t))
        (stripPoissonDensity_pos hr t).le)
    have hbase := regularizedLogNorm_le_hirschman_boundary_integrals hr hc ha hB hbound (hε n).1
    simp only [mul_assoc, integral_const_mul] at hbase
    have hlog : regularizedLogNorm (ε n) (g (r : ℂ)) ≤
        (1 - r) * (∫ t : ℝ, stripPoissonDensity (1 - r) t *
          regularizedLogNorm (ε n) ((Real.exp (h₀ t) : ℝ) : ℂ)) +
        r * (∫ t : ℝ, stripPoissonDensity r t *
          regularizedLogNorm (ε n) ((Real.exp (h₁ t) : ℝ) : ℂ)) :=
      hbase.trans (add_le_add (mul_le_mul_of_nonneg_left hmono₀ (by linarith [hr.2]))
        (mul_le_mul_of_nonneg_left hmono₁ hr.1.le))
    exact (Real.log_le_iff_le_exp (sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (hε n).1)))).mp hlog
  have hleftlim := ((tendsto_const_nhds (x := ‖g (r : ℂ)‖ ^ 2)).add (hεlim.pow 2)).sqrt
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sqrt_sq (norm_nonneg _)] at hleftlim
  have h := le_of_tendsto_of_tendsto' hleftlim
    (Real.continuous_exp.continuousAt.tendsto.comp hrightlim) hfinal
  simpa only [Function.comp_def, integral_stripHarmonicMeasure hrr,
    integral_stripHarmonicMeasure hr, smul_eq_mul] using h

end Complex

end
