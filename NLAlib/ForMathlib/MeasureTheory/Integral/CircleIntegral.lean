/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Circle paths and parameter integrals

Circle and path parametrizations agree. A continuous integrand on compact parameter intervals
permits exchange of the two integrals. Upstream candidate for Mathlib.

The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `Complex.integral_circlePath_eq_circleIntegral`.
-/
@[expose] public section

section

open Set Metric MeasureTheory Complex

open scoped unitInterval

namespace Path

/-- A smooth parametrization agreeing with a path on the unit interval computes the
complex curve integral using the ordinary derivative. -/
theorem integral_eq_intervalIntegral_of_eqOn_extend {a b : ℂ} (p : Path a b)
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (heq : EqOn p.extend γ I) (f : ℂ → ℂ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) p =
      ∫ t in (0 : ℝ)..1, deriv γ t * f (γ t) := by
  rw [curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ I := by simpa only [uIcc_of_le zero_le_one] using ht
  rw [curveIntegralFun_def]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  change f (p.extend t) * derivWithin p.extend I t = deriv γ t * f (γ t)
  rw [heq ht', derivWithin_congr heq (heq ht'),
    (hγ.differentiable (by norm_num) t).derivWithin (uniqueDiffOn_Icc_zero_one t ht')]
  exact mul_comm _ _

end Path

namespace Complex

/-- The positively oriented circle, parametrized once on the unit interval.
For a negative signed radius the starting point is rotated by half a turn;
the traversal still has the same counterclockwise orientation. -/
noncomputable def circlePath (c : ℂ) (r : ℝ) : Path (c + (r : ℂ)) (c + (r : ℂ)) :=
  Path.ofLine (f := fun t : ℝ => circleMap c r (2 * Real.pi * t))
    (((continuous_circleMap c r).comp (continuous_const.mul continuous_id)).continuousOn)
    (by simp [circleMap])
    (by simp [circleMap])

/-- The native circle path agrees with the usual angular parametrization
through angle `2πt` on its entire closed parameter interval. -/
theorem circlePath_extend_apply {c : ℂ} {r t : ℝ} (ht : t ∈ I) :
    (circlePath c r).extend t = circleMap c r (2 * Real.pi * t) := by
  rw [Path.extend_apply _ ht]
  rfl

/-- The native circle path is continuously differentiable up to both
endpoints of the unit interval. -/
theorem contDiffOn_circlePath_extend (c : ℂ) (r : ℝ) :
    ContDiffOn ℝ 1 (circlePath c r).extend I := by
  have h : ContDiff ℝ 1 (fun t : ℝ => circleMap c r (2 * Real.pi * t)) :=
    (contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id)
  exact h.contDiffOn.congr (fun t ht => circlePath_extend_apply ht)

/-- The native circle path integral is exactly the existing circle integral,
including its normalization and orientation. -/
theorem integral_circlePath_eq_circleIntegral (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ) (circlePath c r) =
      ∮ z in C(c, r), f z := by
  have hγ : ContDiff ℝ 1 (fun t : ℝ => circleMap c r (2 * Real.pi * t)) :=
    (contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id)
  rw [Path.integral_eq_intervalIntegral_of_eqOn_extend _ hγ
    (fun _ ht => circlePath_extend_apply ht)]
  have hder (t : ℝ) : deriv (fun t : ℝ => circleMap c r (2 * Real.pi * t)) t =
      (2 * Real.pi) • deriv (circleMap c r) (2 * Real.pi * t) := by
    simpa only [Function.comp_def, mul_one, deriv_circleMap] using
      ((hasDerivAt_circleMap c r (2 * Real.pi * t)).scomp t
        ((hasDerivAt_id t).const_mul (2 * Real.pi))).deriv
  simp_rw [hder, smul_mul_assoc]
  rw [intervalIntegral.integral_smul]
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => deriv (circleMap c r) t * f (circleMap c r t)) (2 * Real.pi)
    (a := (0 : ℝ)) (b := 1)
  simpa only [mul_zero, mul_one, circleIntegral, smul_eq_mul] using hscale

/-- A holomorphic image of the circle path is continuously differentiable
up to both endpoints of its parameter interval. -/
theorem contDiffOn_circlePath_map_extend
    {g : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hc : sphere c |r| ⊆ U)
    (hgc : ContinuousOn g (range (circlePath c r))) :
    ContDiffOn ℝ 1 ((circlePath c r).map' hgc).extend I := by
  have hγ : ContDiff ℝ 1 (fun t : ℝ => g (circleMap c r (2 * Real.pi * t))) :=
    ((hg.contDiffOn hU).restrict_scalars ℝ).comp_contDiff
      ((contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id))
      (fun t => hc (circleMap_mem_sphere' c r _))
  apply hγ.contDiffOn.congr
  intro t ht
  rw [Path.extend_apply _ ht]
  rfl

/-- Integrating over a holomorphic image of a circle gives the circle
integral of the ordinary derivative pullback. This is an actual change of
parametrization, without an assumed contour-integral identity. -/
theorem integral_circlePath_map_eq_circleIntegral_mul_deriv
    (f : ℂ → ℂ) {g : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hc : sphere c |r| ⊆ U)
    (hgc : ContinuousOn g (range (circlePath c r))) :
    curveIntegral (fun z => f z • ContinuousLinearMap.id ℂ ℂ)
        ((circlePath c r).map' hgc) =
      ∮ z in C(c, r), f (g z) * deriv g z := by
  have hγ : ContDiff ℝ 1 (fun t : ℝ => g (circleMap c r (2 * Real.pi * t))) :=
    ((hg.contDiffOn hU).restrict_scalars ℝ).comp_contDiff
      ((contDiff_circleMap c r).comp (contDiff_const.mul contDiff_id))
      (fun t => hc (circleMap_mem_sphere' c r _))
  let p : Path (g (c + (r : ℂ))) (g (c + (r : ℂ))) :=
    Path.ofLine hγ.continuous.continuousOn
    (by simp [circleMap]) (by simp [circleMap])
  have hp : p = (circlePath c r).map' hgc := by
    ext t
    rfl
  have heq : Set.EqOn p.extend (fun t => g (circleMap c r (2 * Real.pi * t))) I := by
    intro t ht
    rw [p.extend_apply ht]
    rfl
  rw [← hp, Path.integral_eq_intervalIntegral_of_eqOn_extend p hγ heq]
  have hder (t : ℝ) : deriv (fun t : ℝ => g (circleMap c r (2 * Real.pi * t))) t =
      (2 * Real.pi) •
        (deriv (circleMap c r) (2 * Real.pi * t) * deriv g (circleMap c r (2 * Real.pi * t))) := by
    have hg' := (hg.differentiableAt
      (hU.mem_nhds (hc (circleMap_mem_sphere' c r (2 * Real.pi * t))))).hasDerivAt
    have hc' := (hasDerivAt_circleMap c r (2 * Real.pi * t)).scomp t
      ((hasDerivAt_id t).const_mul (2 * Real.pi))
    have hh := (hg'.scomp t hc').deriv
    simpa only [Function.comp_def, mul_one, deriv_circleMap, smul_eq_mul,
      Complex.real_smul, mul_assoc] using hh
  simp_rw [hder, smul_mul_assoc]
  rw [intervalIntegral.integral_smul]
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => deriv (circleMap c r) t *
      (f (g (circleMap c r t)) * deriv g (circleMap c r t))) (2 * Real.pi)
    (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one] at hscale
  simpa only [circleIntegral, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm] using hscale

end Complex

namespace circleIntegral

/-- Negating the signed radius rotates the circle's starting point by half a
turn and preserves its integral and counterclockwise orientation. -/
theorem neg_radius (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    (∮ z in C(c, -r), f z) = ∮ z in C(c, r), f z := by
  unfold circleIntegral
  let F : ℝ → ℂ := fun θ => deriv (circleMap c r) θ * f (circleMap c r θ)
  have hperiod : Function.Periodic F (2 * Real.pi) := by
    intro θ
    simp only [F, deriv_circleMap, (periodic_circleMap c r) θ,
      (periodic_circleMap 0 r) θ]
  calc
    (∫ θ in (0 : ℝ)..2 * Real.pi, deriv (circleMap c (-r)) θ • f (circleMap c (-r) θ)) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, F (θ + Real.pi) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [F, deriv_circleMap, circleMap_neg_radius, smul_eq_mul]
    _ = ∫ θ in Real.pi..2 * Real.pi + Real.pi, F θ := by
      simpa only [zero_add] using intervalIntegral.integral_comp_add_right F Real.pi
        (a := (0 : ℝ)) (b := 2 * Real.pi)
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi, F θ := by
      simpa only [zero_add, add_comm] using hperiod.intervalIntegral_add_eq Real.pi 0

end circleIntegral

end

section

open Set MeasureTheory Complex

namespace MeasureTheory

/-- A jointly continuous kernel has an integrable circle integral as a function
of the real parameter, and the two integrations commute. This supplies both
integrability and the Fubini identity for the contour density in [Stahl2013, Theorem 2]. -/
theorem intervalIntegrable_circleIntegral_and_integral_circleIntegral_eq
    {F : ℝ → ℂ → ℂ} {a b r : ℝ} {c : ℂ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Metric.sphere c r)) :
    IntervalIntegrable (fun x => ∮ z in C(c, r), F x z) volume a b ∧
    (∫ x in a..b, ∮ z in C(c, r), F x z) =
      ∮ z in C(c, r), ∫ x in a..b, F x z := by
  let H : ℝ × ℝ → ℂ := fun p => deriv (circleMap c r) p.2 * F p.1 (circleMap c r p.2)
  have hc : ContinuousOn H (Icc a b ×ˢ Icc 0 (2 * Real.pi)) := by
    have hmap : MapsTo (fun p : ℝ × ℝ => (p.1, circleMap c r p.2))
        (Icc a b ×ˢ Icc 0 (2 * Real.pi)) (Icc a b ×ˢ Metric.sphere c r) := by
      intro p hp
      exact ⟨hp.1, circleMap_mem_sphere c hr p.2⟩
    have hcomp : ContinuousOn (fun p : ℝ × ℝ => F p.1 (circleMap c r p.2))
        (Icc a b ×ˢ Icc 0 (2 * Real.pi)) :=
      hF.comp (by fun_prop) hmap
    have hd : Continuous (fun p : ℝ × ℝ => deriv (circleMap c r) p.2) := by
      simp only [deriv_circleMap]
      fun_prop
    exact hd.continuousOn.mul hcomp
  have hi : Integrable H
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have heq : (fun x => ∮ z in C(c, r), F x z) =
        fun x => ∫ y in Icc 0 (2 * Real.pi), H (x, y) := by
      funext x
      simp only [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
        ← integral_Icc_eq_integral_Ioc, H, smul_eq_mul]
    rw [heq]
    exact hi.integral_prod_left
  have hswap := integral_integral_swap (f := fun x θ => H (x, θ)) hi
  simp_rw [circleIntegral, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_Icc_eq_integral_Ioc]
  trans ∫ θ in Icc 0 (2 * Real.pi), ∫ x in Icc a b,
    deriv (circleMap c r) θ * F x (circleMap c r θ)
  · simpa only [H, smul_eq_mul] using hswap
  · apply integral_congr_ae
    filter_upwards with θ
    simp only [smul_eq_mul, integral_const_mul]

/-- Integrating a jointly continuous kernel over a finite real interval commutes
with its complex circle integral about any center. For $a\le b$ and $r\ge0$,
$\int_a^b\oint_{\lvert z-c\rvert=r} F(x,z)\,dz\,dx
=\oint_{\lvert z-c\rvert=r}\int_a^b F(x,z)\,dx\,dz$. -/
theorem integral_circleIntegral_eq_circleIntegral_integral
    {F : ℝ → ℂ → ℂ} {a b r : ℝ} {c : ℂ} (hab : a ≤ b) (hr : 0 ≤ r)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Metric.sphere c r)) :
    (∫ x in a..b, ∮ z in C(c, r), F x z) =
      ∮ z in C(c, r), ∫ x in a..b, F x z :=
  (intervalIntegrable_circleIntegral_and_integral_circleIntegral_eq hab hr hF).2

end MeasureTheory

end
