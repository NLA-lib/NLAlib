/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.InfinitePi
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.EntropyTensorization

/-!
# Gross's logarithmic Sobolev inequality on the line, for compactly supported functions

For the standard Gaussian `γ` on `ℝ` and a compactly supported `C¹` function `g`,
`Ent_γ (g²) ≤ 2 E_γ g'²`. This is Gross's original route: the two-point inequality
`Ent (G²) ≤ (G 1 - G (-1))² / 2` for a random sign, tensorized over `n` independent signs and
applied to `g ((s₁ + ⋯ + sₙ) / √n)`, gives the inequality for the law of the normalised sum up to
an error that vanishes with `n` (the derivative of `g` is uniformly continuous); the central
limit theorem passes to the limit.

## Main results

* `NLAlib.entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal_of_hasCompactSupport`.

## References

* [L. Gross, *Logarithmic Sobolev inequalities*][Gross1975].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology

namespace NLAlib

/-! ### The two-point inequality -/

private lemma two_point_aux {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a) :
    2⁻¹ * (a ^ 2 * Real.log (a ^ 2) + b ^ 2 * Real.log (b ^ 2)) -
      2⁻¹ * (a ^ 2 + b ^ 2) * Real.log (2⁻¹ * (a ^ 2 + b ^ 2)) ≤ (a - b) ^ 2 / 2 := by
  set m : ℝ → ℝ := fun b => 2⁻¹ * (a ^ 2 + b ^ 2) with hm
  have hm0 : ∀ b, 0 < m b := fun b => by simp only [hm]; positivity
  set φ : ℝ → ℝ := fun b => (a - b) ^ 2 / 2 -
    2⁻¹ * (a ^ 2 * Real.log (a ^ 2) + b ^ 2 * Real.log (b ^ 2)) +
    2⁻¹ * (a ^ 2 + b ^ 2) * Real.log (m b) with hφ
  set ψ : ℝ → ℝ := fun b => b - a - b * Real.log (b ^ 2) + b * Real.log (m b) with hψ
  have hmd : ∀ b, HasDerivAt m b b := fun b => by
    refine (((hasDerivAt_pow 2 b).const_add (a ^ 2)).const_mul 2⁻¹).congr_deriv ?_
    norm_num
    ring
  have hld : ∀ b : ℝ, b ≠ 0 → HasDerivAt (fun b : ℝ => Real.log (b ^ 2)) (2 / b) b := by
    intro b hb0
    refine ((hasDerivAt_pow 2 b).log (pow_ne_zero 2 hb0)).congr_deriv ?_
    field_simp
    ring
  have hφd : ∀ b, b ≠ 0 → HasDerivAt φ (ψ b) b := by
    intro b hb0
    have h1 := (hasDerivAt_pow 2 b).mul (hld b hb0)
    have h2 := (hasDerivAt_pow 2 b).mul ((hmd b).log (hm0 b).ne')
    have h3 := ((((hasDerivAt_id b).const_sub a).pow 2).div_const 2).sub
      ((h1.const_add (a ^ 2 * Real.log (a ^ 2))).const_mul 2⁻¹)
    have h4 := (h3.add ((((hasDerivAt_pow 2 b).const_add (a ^ 2)).const_mul 2⁻¹).mul
      ((hmd b).log (hm0 b).ne')))
    refine h4.congr_deriv ?_
    simp only [hψ, hm, id]
    field_simp
    ring
  have hψd : ∀ b, b ≠ 0 →
      HasDerivAt ψ (b ^ 2 / m b - 1 - Real.log (b ^ 2 / m b)) b := by
    intro b hb0
    have h := ((((hasDerivAt_id b).sub_const a).sub ((hasDerivAt_id b).mul (hld b hb0))).add
      ((hasDerivAt_id b).mul ((hmd b).log (hm0 b).ne')))
    refine h.congr_deriv ?_
    rw [Real.log_div (pow_ne_zero 2 hb0) (hm0 b).ne']
    simp only [id]
    field_simp
    ring
  -- `ψ ≤ 0` on `(0, a]`
  have hψmono : MonotoneOn ψ (Set.Ioc 0 a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 a) ?_ ?_ ?_
    · intro b hb
      exact (hψd b hb.1.ne').continuousAt.continuousWithinAt
    · intro b hb
      rw [interior_Ioc] at hb
      exact (hψd b hb.1.ne').differentiableAt.differentiableWithinAt
    · intro b hb
      rw [interior_Ioc] at hb
      rw [(hψd b hb.1.ne').deriv]
      have := Real.log_le_sub_one_of_pos (div_pos (pow_pos hb.1 2) (hm0 b))
      linarith
  have hψa : ψ a = 0 := by
    simp only [hψ, hm]
    rw [show 2⁻¹ * (a ^ 2 + a ^ 2) = a ^ 2 by ring]
    ring
  have hφanti : AntitoneOn φ (Set.Icc 0 a) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 a) ?_ ?_ ?_
    · refine Continuous.continuousOn ?_
      simp only [hφ]
      refine Continuous.add (Continuous.sub (by fun_prop) (continuous_const.mul
        (continuous_const.add ((Real.continuous_mul_log.comp (continuous_pow 2)))))) ?_
      exact (by fun_prop : Continuous fun b : ℝ => 2⁻¹ * (a ^ 2 + b ^ 2)).mul
        ((by fun_prop : Continuous m).log fun b => (hm0 b).ne')
    · intro b hb
      rw [interior_Icc] at hb
      exact (hφd b hb.1.ne').differentiableAt.differentiableWithinAt
    · intro b hb
      rw [interior_Icc] at hb
      rw [(hφd b hb.1.ne').deriv, ← hψa]
      exact hψmono ⟨hb.1, hb.2.le⟩ ⟨ha, le_rfl⟩ hb.2.le
  have hφa : φ a = 0 := by
    simp only [hφ, hm]
    rw [show 2⁻¹ * (a ^ 2 + a ^ 2) = a ^ 2 by ring]
    ring
  have := hφanti ⟨hb, hba⟩ ⟨ha.le, le_rfl⟩ hba
  simp only [hφ, hm] at this hφa
  linarith

private lemma two_point_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2⁻¹ * (a ^ 2 * Real.log (a ^ 2) + b ^ 2 * Real.log (b ^ 2)) -
      2⁻¹ * (a ^ 2 + b ^ 2) * Real.log (2⁻¹ * (a ^ 2 + b ^ 2)) ≤ (a - b) ^ 2 / 2 := by
  rcases le_total b a with hba | hab
  · rcases ha.eq_or_lt with rfl | ha'
    · obtain rfl : b = 0 := le_antisymm hba hb
      simp
    · exact two_point_aux ha' hb hba
  · rcases hb.eq_or_lt with rfl | hb'
    · obtain rfl : a = 0 := le_antisymm hab ha
      simp
    · calc _ = 2⁻¹ * (b ^ 2 * Real.log (b ^ 2) + a ^ 2 * Real.log (a ^ 2)) -
            2⁻¹ * (b ^ 2 + a ^ 2) * Real.log (2⁻¹ * (b ^ 2 + a ^ 2)) := by
            rw [add_comm (b ^ 2) (a ^ 2), add_comm (b ^ 2 * Real.log (b ^ 2))]
        _ ≤ (b - a) ^ 2 / 2 := two_point_aux hb' ha hab
        _ = (a - b) ^ 2 / 2 := by ring

/-- The two-point logarithmic Sobolev inequality for a random sign. -/
private lemma entropy_sq_rademacherMeasure_le (G : ℝ → ℝ) :
    entropy rademacherMeasure (fun y => G y ^ 2) ≤ (G 1 - G (-1)) ^ 2 / 2 := by
  rw [entropy, integral_rademacherMeasure, integral_rademacherMeasure, smul_eq_mul, smul_eq_mul]
  have h := two_point_nonneg (abs_nonneg (G 1)) (abs_nonneg (G (-1)))
  simp only [sq_abs] at h
  have : (|G 1| - |G (-1)|) ^ 2 ≤ (G 1 - G (-1)) ^ 2 :=
    sq_le_sq.2 (abs_abs_sub_abs_le_abs_sub _ _)
  linarith

/-! ### The central limit theorem for random signs -/

/-- The integral of a bounded continuous function of the normalised sum of `n` random signs
tends to its Gaussian integral. -/
private lemma tendsto_integral_rademacher {φ : ℝ → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) :
    Tendsto (fun n : ℕ => ∫ x, φ ((√n)⁻¹ * ∑ i, x i)
      ∂(Measure.pi fun _ : Finset.range n => rademacherMeasure)) atTop
      (𝓝 (∫ x, φ x ∂gaussianReal 0 1)) := by
  set P := Measure.infinitePi (fun _ : ℕ => rademacherMeasure) with hP
  have hX : ∀ k, HasLaw (fun ω : ℕ → ℝ => ω k) rademacherMeasure P := fun k =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => rademacherMeasure) k).hasLaw
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum (X := fun k (ω : ℕ → ℝ) => ω k) (P := P)
    (HasLaw.id (μ := gaussianReal 0 1)) (integral_of_hasLaw_rademacherMeasure (hX 0))
    (by simpa only [Pi.pow_apply] using integral_sq_of_hasLaw_rademacherMeasure (hX 0))
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
    (fun i => ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [(hX i).map_eq, (hX 0).map_eq]⟩)
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hclt.tendsto
    (BoundedContinuousFunction.ofNormedAddCommGroup φ hφ C fun x => by
      simpa only [Real.norm_eq_abs] using hC x)
  simp only [ProbabilityMeasure.coe_mk, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    Measure.map_id] at h
  refine h.congr fun n => ?_
  have hr : (Measure.pi fun _ : Finset.range n => rademacherMeasure) =
      P.map (Finset.range n).restrict :=
    (Measure.infinitePi_map_restrict (μ := fun _ : ℕ => rademacherMeasure)).symm
  rw [hr, integral_map (Finset.measurable_restrict _).aemeasurable
      (by fun_prop), integral_map (hclt.forall_aemeasurable n) hφ.aestronglyMeasurable]
  simp only [Finset.restrict, Finset.sum_coe_sort (Finset.range n) fun k => _]

/-! ### Tensorization over random signs -/

private lemma abs_mul_log_le_sq_add_one {s : ℝ} (hs : 0 ≤ s) : |s * Real.log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with rfl | hs'
  · simp
  rcases le_or_gt s 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt s hs' h1
    rw [mul_comm]
    nlinarith [sq_nonneg s]
  · have hl : 0 ≤ Real.log s := Real.log_nonneg h1.le
    have hl2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

/-- The first-order estimate `|g u - g v - (u - v) g' c| ≤ ε |u - v|` when `g'` varies by at
most `ε` on the `δ`-ball about `c`. -/
private lemma abs_sub_sub_mul_deriv_le {g : ℝ → ℝ} (hgd : Differentiable ℝ g) {ε δ c u v : ℝ}
    (hδ : ∀ w, |w - c| < δ → |deriv g w - deriv g c| ≤ ε) (hu : |u - c| < δ)
    (hv : |v - c| < δ) : |g u - g v - (u - v) * deriv g c| ≤ ε * |u - v| := by
  have h := (convex_ball c δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w => g w - w * deriv g c) (f' := fun w => deriv g w - deriv g c) (C := ε)
    (fun w _ => ((hgd w).hasDerivAt.sub (hasDerivAt_mul_const (deriv g c))).hasDerivWithinAt)
    (fun w hw => by
      rw [Real.norm_eq_abs]
      exact hδ w (by simpa only [Metric.mem_ball, Real.dist_eq] using hw))
    (by simpa only [Metric.mem_ball, Real.dist_eq] using hv)
    (by simpa only [Metric.mem_ball, Real.dist_eq] using hu)
  simp only [Real.norm_eq_abs] at h
  calc |g u - g v - (u - v) * deriv g c| = |g u - u * deriv g c - (g v - v * deriv g c)| := by
        ring_nf
    _ ≤ ε * |u - v| := h

/-- One coordinate of the tensorized bound: resampling the `i`-th sign moves the scaled sum by
`2 h`, so the two-point inequality and the first-order estimate bound the entropy. -/
private lemma entropy_update_le {ι : Type*} [Fintype ι] [DecidableEq ι] {g : ℝ → ℝ}
    (hgd : Differentiable ℝ g) {K ε δ h : ℝ} (hK : ∀ x, |deriv g x| ≤ K)
    (hδ : ∀ u v, |u - v| < δ → |deriv g u - deriv g v| ≤ ε) (h0 : 0 ≤ h)
    {x : ι → ℝ} (hx : ∀ i, x i ^ 2 = 1) (hh : 2 * h < δ) (i : ι) :
    entropy rademacherMeasure (fun y => g (h * ∑ j, Function.update x i y j) ^ 2) ≤
      2 * h ^ 2 * (deriv g (h * ∑ j, x j) ^ 2 + ε * (2 * K + ε)) := by
  have hsum : ∀ y : ℝ, h * ∑ j, Function.update x i y j = h * ∑ j, x j + h * (y - x i) := by
    intro y
    rw [Finset.sum_update_of_mem (Finset.mem_univ i),
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) x]
    ring
  refine (entropy_sq_rademacherMeasure_le _).trans ?_
  simp only [hsum]
  set T := h * ∑ j, x j
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hδ 0 0 (by simp only [sub_self, abs_zero]; linarith))
  have hxi : |x i| ≤ 1 := by
    have := hx i
    rw [← sq_abs] at this
    nlinarith [abs_nonneg (x i)]
  have hmv := abs_sub_sub_mul_deriv_le hgd (c := T) (u := T + h * (1 - x i))
    (v := T + h * (-1 - x i)) (fun w hw => hδ w T hw)
    (by
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg h0]
      nlinarith [abs_sub (1 : ℝ) (x i), abs_one (α := ℝ)])
    (by
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg h0]
      nlinarith [abs_sub (-1 : ℝ) (x i), abs_neg (1 : ℝ), abs_one (α := ℝ)])
  rw [show T + h * (1 - x i) - (T + h * (-1 - x i)) = 2 * h by ring,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * h)] at hmv
  set D := g (T + h * (1 - x i)) - g (T + h * (-1 - x i))
  have hDle : |D| ≤ 2 * h * (|deriv g T| + ε) := by
    have := abs_sub_abs_le_abs_sub D (2 * h * deriv g T)
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * h)] at this
    nlinarith
  have hD2 : D ^ 2 ≤ (2 * h * (|deriv g T| + ε)) ^ 2 := by
    rw [← sq_abs D]; exact pow_le_pow_left₀ (abs_nonneg _) hDle 2
  have hsq : (|deriv g T| + ε) ^ 2 ≤ deriv g T ^ 2 + ε * (2 * K + ε) := by
    have := hK T
    have h1 : |deriv g T| ^ 2 = deriv g T ^ 2 := sq_abs _
    nlinarith
  calc D ^ 2 / 2 ≤ (2 * h * (|deriv g T| + ε)) ^ 2 / 2 := by linarith
    _ = 2 * h ^ 2 * (|deriv g T| + ε) ^ 2 := by ring
    _ ≤ 2 * h ^ 2 * (deriv g T ^ 2 + ε * (2 * K + ε)) := by gcongr

/-- The tensorized two-point inequality for `g` of a scaled sum of random signs, with an error
controlled by the oscillation of `g'` at the scale of one step. -/
private lemma entropy_comp_sum_le {ι : Type*} [Fintype ι] {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) {B K ε δ h : ℝ} (hB : ∀ x, |g x| ≤ B) (hK : ∀ x, |deriv g x| ≤ K)
    (hδ : ∀ u v, |u - v| < δ → |deriv g u - deriv g v| ≤ ε) (h0 : 0 ≤ h) (hh : 2 * h < δ)
    (hn : (Fintype.card ι : ℝ) * h ^ 2 = 1) :
    entropy (Measure.pi fun _ : ι => rademacherMeasure) (fun x => g (h * ∑ i, x i) ^ 2) ≤
      2 * ∫ x, deriv g (h * ∑ i, x i) ^ 2 ∂(Measure.pi fun _ : ι => rademacherMeasure) +
        2 * (ε * (2 * K + ε)) := by
  classical
  set ν := Measure.pi fun _ : ι => rademacherMeasure with hν
  set T : (ι → ℝ) → ℝ := fun x => h * ∑ i, x i with hT
  have hgc : Continuous g := hg.continuous
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hTc : Continuous T := by fun_prop
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hδ 0 0 (by simp only [sub_self, abs_zero]; linarith))
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hB2 : ∀ x, g x ^ 2 ≤ B ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have hK2 : ∀ x, deriv g x ^ 2 ≤ K ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
  have hF : Integrable (fun x => g (T x) ^ 2) ν :=
    Integrable.of_bound ((hgc.comp hTc).pow 2).aestronglyMeasurable (B ^ 2)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hB2 _)
  have hFlog : Integrable (fun x => g (T x) ^ 2 * Real.log (g (T x) ^ 2)) ν := by
    refine Integrable.of_bound
      (Real.continuous_mul_log.comp ((hgc.comp hTc).pow 2)).aestronglyMeasurable
      ((B ^ 2) ^ 2 + 1) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_mul_log_le_sq_add_one (sq_nonneg _)).trans ?_
    have := pow_le_pow_left₀ (sq_nonneg _) (hB2 (T x)) 2
    linarith
  have hD : Integrable (fun x => deriv g (T x) ^ 2) ν :=
    Integrable.of_bound ((hdc.comp hTc).pow 2).aestronglyMeasurable (K ^ 2)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hK2 _)
  refine (entropy_pi_le_sum (fun _ : ι => rademacherMeasure) (f := fun x => g (T x) ^ 2)
    ((hgc.comp hTc).pow 2).measurable (fun x => sq_nonneg _) hF hFlog).trans ?_
  set e := ε * (2 * K + ε) with he
  have hae : ∀ᵐ x ∂ν, ∀ i, x i ^ 2 = 1 :=
    ae_sq_eq_one_of_hasLaw_rademacherVector (HasLaw.id (μ := rademacherVector ι))
  have he0 : 0 ≤ e := mul_nonneg hε (by linarith)
  have hG : Integrable (fun x => 2 * h ^ 2 * (deriv g (T x) ^ 2 + e)) ν :=
    (hD.add (integrable_const e)).const_mul _
  have hi : ∀ i, ∫ x, entropy rademacherMeasure (fun y => g (T (Function.update x i y)) ^ 2) ∂ν ≤
      ∫ x, 2 * h ^ 2 * (deriv g (T x) ^ 2 + e) ∂ν := by
    intro i
    by_cases hE : Integrable
      (fun x => entropy rademacherMeasure (fun y => g (T (Function.update x i y)) ^ 2)) ν
    · exact integral_mono_ae hE hG (hae.mono fun x hx =>
        entropy_update_le (hg.differentiable one_ne_zero) hK hδ h0 hx hh i)
    · rw [integral_undef hE]
      exact integral_nonneg fun x => mul_nonneg (by positivity) (add_nonneg (sq_nonneg _) he0)
  calc ∑ i, ∫ x, entropy rademacherMeasure (fun y => g (T (Function.update x i y)) ^ 2) ∂ν
      ≤ ∑ _i : ι, ∫ x, 2 * h ^ 2 * (deriv g (T x) ^ 2 + e) ∂ν := Finset.sum_le_sum fun i _ => hi i
    _ = (Fintype.card ι * h ^ 2) * 2 * (∫ x, deriv g (T x) ^ 2 ∂ν + e) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, integral_const_mul,
        integral_add hD (integrable_const e)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      ring
    _ = 2 * ∫ x, deriv g (T x) ^ 2 ∂ν + 2 * e := by rw [hn]; ring

/-! ### The limit -/

/-- **Gross's logarithmic Sobolev inequality** on `ℝ` for a compactly supported `C¹` function:
`Ent_γ (g²) ≤ 2 E_γ g'²` for the standard Gaussian `γ`. -/
theorem entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal_of_hasCompactSupport {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    entropy (gaussianReal 0 1) (fun x => g x ^ 2) ≤
      2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 := by
  have hgcont : Continuous g := hg.continuous
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, |g x| ≤ B := by
    obtain ⟨B, hB⟩ := hgcont.bounded_above_of_compact_support hgc
    exact ⟨B, fun x => by simpa only [Real.norm_eq_abs] using hB x⟩
  obtain ⟨K, hK⟩ : ∃ K, ∀ x, |deriv g x| ≤ K := by
    obtain ⟨K, hK⟩ := hdc.bounded_above_of_compact_support hgc.deriv
    exact ⟨K, fun x => by simpa only [Real.norm_eq_abs] using hK x⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hB2 : ∀ x, g x ^ 2 ≤ B ^ 2 := fun x => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have huc : UniformContinuous (deriv g) := hgc.deriv.uniformContinuous_of_continuous hdc
  -- the three integrals converge along the central limit theorem
  have hlimE := tendsto_integral_rademacher (φ := fun x => g x ^ 2 * Real.log (g x ^ 2))
    (Real.continuous_mul_log.comp (hgcont.pow 2)) (C := (B ^ 2) ^ 2 + 1) fun x => by
      refine (abs_mul_log_le_sq_add_one (sq_nonneg _)).trans ?_
      have := pow_le_pow_left₀ (sq_nonneg _) (hB2 x) 2
      linarith
  have hlimM := tendsto_integral_rademacher (φ := fun x => g x ^ 2) (hgcont.pow 2)
    (C := B ^ 2) fun x => by rw [abs_of_nonneg (sq_nonneg _)]; exact hB2 x
  have hlimD := tendsto_integral_rademacher (φ := fun x => deriv g x ^ 2) (hdc.pow 2)
    (C := K ^ 2) fun x => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
  have hlimEnt := hlimE.sub ((Real.continuous_mul_log.tendsto _).comp hlimM)
  have hsqrt : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  -- for each `ε > 0`, the inequality up to `2 ε (2 K + ε)`
  have hε : ∀ ε, 0 < ε → entropy (gaussianReal 0 1) (fun x => g x ^ 2) ≤
      2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 + 2 * (ε * (2 * K + ε)) := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 huc ε hε
    have hδ' : ∀ u v, |u - v| < δ → |deriv g u - deriv g v| ≤ ε := fun u v huv => by
      have := hδε (a := u) (b := v) (by rwa [Real.dist_eq])
      rw [Real.dist_eq] at this
      exact this.le
    refine le_of_tendsto_of_tendsto hlimEnt ((hlimD.const_mul 2).add_const _) ?_
    filter_upwards [hsqrt.eventually (gt_mem_nhds (half_pos hδ)), eventually_ge_atTop 1]
      with n hn hn1
    refine entropy_comp_sum_le hg hB hK hδ' (by positivity) (by linarith) ?_
    rw [Fintype.card_coe, Finset.card_range, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    exact mul_inv_cancel₀ (by positivity)
  have hlim0 : Tendsto (fun ε : ℝ => 2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 +
      2 * (ε * (2 * K + ε))) (𝓝[>] 0) (𝓝 (2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1)) := by
    have : Continuous (fun ε : ℝ => 2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1 +
        2 * (ε * (2 * K + ε))) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim0 (eventually_nhdsWithin_of_forall hε)

end NLAlib
