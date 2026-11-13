/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import NLAlib.ForMathlib.MeasureTheory.Integral.CurveIntegral.PrimitiveHomotopy
public import NLAlib.ForMathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Cauchy integrals on an exterior domain

Cauchy deformation and change of contour for holomorphic functions with prescribed behavior at
infinity. Upstream candidate for Mathlib.

The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `Complex.two_pi_i_inv_mul_circleIntegral_div_sub_eq_of_tendsto`.
-/
@[expose] public section

section

open Complex

open Set Metric Filter Bornology Complex

open scoped Topology

namespace Complex

/-- The integrals of a holomorphic function outside the closed disk $\lvert z-c\rvert\le R$ agree on
all counterclockwise circles centered at $c$ of positive radius greater than $R$. -/
theorem circleIntegral_eq_of_differentiableOn_compl_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} {R r s : ℝ}
    (hf : DifferentiableOn ℂ f (closedBall c R)ᶜ)
    (hr : 0 < r) (hs : 0 < s) (hRr : R < r) (hRs : R < s) :
    (∮ z in C(c, r), f z) = ∮ z in C(c, s), f z := by
  suffices haux : ∀ {u v : ℝ}, 0 < u → R < u → u ≤ v →
      (∮ z in C(c, v), f z) = ∮ z in C(c, u), f z by
    rcases le_total r s with hrs | hsr
    · exact (haux hr hRr hrs).symm
    · exact haux hs hRs hsr
  intro u v hu hRu huv
  have hsub : closedBall c v \ ball c u ⊆ (closedBall c R)ᶜ := by
    intro z hz hmem
    exact hz.2 (mem_ball.mpr ((mem_closedBall.mp hmem).trans_lt hRu))
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hu huv (s := (∅ : Set ℂ)) countable_empty (hf.continuousOn.mono hsub)
  intro z hz
  apply hf.differentiableAt (isClosed_closedBall.isOpen_compl.mem_nhds ?_)
  exact fun hmem => hz.1.2 (closedBall_subset_closedBall hRu.le hmem)

/-- Radius independence at the origin for the contour density in [Stahl2013, Theorem 2]. -/
theorem circleIntegral_eq_of_differentiableOn_exterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {R r s : ℝ} (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hr : 0 < r) (hs : 0 < s) (hRr : R < r) (hRs : R < s) :
    (∮ z in C(0, r), f z) = ∮ z in C(0, s), f z := by
  apply circleIntegral_eq_of_differentiableOn_compl_closedBall (R := R) _ hr hs hRr hRs
  exact hf.mono fun z hz => by simpa [mem_closedBall, dist_zero_right] using hz

/-- The exterior Cauchy kernel $f(z)/z$ has equal integrals on two counterclockwise circles
in its exterior holomorphy domain. -/
theorem circleIntegral_inv_mul_eq_of_differentiableOn_exterior
    {f : ℂ → ℂ} {R r s : ℝ} (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hr : 0 < r) (hRr : R < r) (hrs : r ≤ s) :
    (∮ z in C(0, s), z⁻¹ * f z) = ∮ z in C(0, r), z⁻¹ * f z := by
  have hm : max R 0 < r := max_lt hRr hr
  apply circleIntegral_eq_of_differentiableOn_exterior (R := max R 0) _ (hr.trans_le hrs) hr
    (hm.trans_le hrs) hm
  exact (differentiableOn_id.inv fun z hz => norm_pos_iff.mp ((le_max_right R 0).trans_lt hz)).mul
    (hf.mono fun z hz => (le_max_left R 0).trans_lt hz)

/-- A function holomorphic near infinity and vanishing there has zero exterior
circle integral against `1 / z`. This is proved by enlarging the circle and a
uniform norm estimate, rather than by assuming a residue at infinity. -/
theorem two_pi_i_inv_mul_circleIntegral_inv_mul_eq_zero_of_tendsto
    {f : ℂ → ℂ} {R r : ℝ} (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hr : 0 < r) (hRr : R < r) (hlim : Tendsto f (cobounded ℂ) (𝓝 0)) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), z⁻¹ * f z) = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ z in cobounded ℂ, ‖f z‖ < ε := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hlim ε hε)
  obtain ⟨K, _, hK⟩ := hasBasis_cobounded_norm.eventually_iff.mp hev
  let s := max r K
  have hrs : r ≤ s := le_max_left _ _
  have hKs : K ≤ s := le_max_right _ _
  have hs : 0 < s := hr.trans_le hrs
  rw [← circleIntegral_inv_mul_eq_of_differentiableOn_exterior hf hr hRr hrs]
  have hb : ∀ z ∈ sphere (0 : ℂ) s, ‖z⁻¹ * f z‖ ≤ ε / s := by
    intro z hz
    have hz' : ‖z‖ = s := by simpa only [mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_inv, hz']
    calc
      s⁻¹ * ‖f z‖ ≤ s⁻¹ * ε :=
        mul_le_mul_of_nonneg_left (hK (hKs.trans_eq hz'.symm)).le (inv_nonneg.mpr hs.le)
      _ = ε / s := by ring
  have hbound := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hs.le hb
  simpa only [smul_eq_mul, mul_div_cancel₀ _ hs.ne', zero_add] using hbound

/-- The counterclockwise exterior Cauchy integral of a function holomorphic near
infinity equals its finite limit at infinity. -/
theorem two_pi_i_inv_mul_circleIntegral_inv_mul_eq_of_tendsto
    {f : ℂ → ℂ} {a : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖}) (hr : 0 < r) (hRr : R < r)
    (hlim : Tendsto f (cobounded ℂ) (𝓝 a)) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), z⁻¹ * f z) = a := by
  have hsub : sphere (0 : ℂ) r ⊆ {z | R < ‖z‖} := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    exact hRr.trans_eq hz'.symm
  have hne (z : ℂ) (hz : z ∈ sphere (0 : ℂ) r) : z ≠ 0 := by
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    intro h
    exact hr.ne' (by simpa [h] using hz'.symm)
  have hci : CircleIntegrable (fun z => z⁻¹ * f z) 0 r :=
    ((continuousOn_id.inv₀ hne).mul (hf.continuousOn.mono hsub)).circleIntegrable hr.le
  have hca : CircleIntegrable (fun z : ℂ => z⁻¹ * a) 0 r :=
    ((continuousOn_id.inv₀ hne).mul continuousOn_const).circleIntegrable hr.le
  have hz := two_pi_i_inv_mul_circleIntegral_inv_mul_eq_zero_of_tendsto
    (hf.sub_const a) hr hRr (by simpa using hlim.sub_const a)
  have heq : (∮ z in C(0, r), z⁻¹ * (f z - a)) =
      (∮ z in C(0, r), z⁻¹ * f z) - (2 * Real.pi * I : ℂ) * a := by
    simp_rw [mul_sub]
    rw [circleIntegral.integral_sub hci hca]
    congr 1
    simp_rw [mul_comm _ a]
    rw [circleIntegral.integral_const_mul]
    have hk : (∮ z in C(0, r), z⁻¹) = (2 * Real.pi * I : ℂ) := by
      simpa only [sub_zero, smul_eq_mul] using
        circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
    rw [hk]
  rw [heq] at hz
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [mul_sub, inv_mul_cancel_left₀ hpi] at hz
  exact sub_eq_zero.mp hz

/-- For $\lvert t\rvert<r$, the exterior Cauchy formula gives
$(2\pi i)^{-1}\oint_{\lvert z\rvert=r} f(z)/(z-t)\,dz=\lim_{z\to\infty} f(z)$.
It requires holomorphy only outside a smaller closed disk.
This is the atomic Cauchy term in Stahl's representation [Stahl2013, Theorem 2]. -/
theorem two_pi_i_inv_mul_circleIntegral_div_sub_eq_of_tendsto
    {f : ℂ → ℂ} {a t : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖}) (hr : 0 < r) (hRr : R < r)
    (htr : ‖t‖ < r) (hlim : Tendsto f (cobounded ℂ) (𝓝 a)) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ z in C(0, r), f z / (z - t)) = a := by
  let g : ℂ → ℂ := fun z => (1 - t * z⁻¹)⁻¹ * f z
  have hzero (z : ℂ) (hz : max R ‖t‖ < ‖z‖) : z ≠ 0 := by
    intro h
    have h' := (le_max_right R ‖t‖).trans_lt hz
    simpa [h] using (norm_nonneg t).trans_lt h'
  have hsub (z : ℂ) (hz : max R ‖t‖ < ‖z‖) : z - t ≠ 0 := by
    intro h
    have h' := (le_max_right R ‖t‖).trans_lt hz
    simp [sub_eq_zero.mp h] at h'
  have hden (z : ℂ) (hz : max R ‖t‖ < ‖z‖) : 1 - t * z⁻¹ ≠ 0 := by
    intro h
    apply hsub z hz
    have hh := congrArg (fun w : ℂ => w * z) h
    simpa only [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ (hzero z hz), mul_one,
      zero_mul] using hh
  have hg : DifferentiableOn ℂ g {z | max R ‖t‖ < ‖z‖} := by
    have hf' : DifferentiableOn ℂ f {z | max R ‖t‖ < ‖z‖} :=
      hf.mono (fun _ hz => (le_max_left R ‖t‖).trans_lt hz)
    intro z hz
    have hi : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z :=
      differentiableAt_id.inv (hzero z hz)
    have hd : DifferentiableAt ℂ (fun w : ℂ => (1 - t * w⁻¹)⁻¹) z :=
      ((hi.const_mul t).const_sub 1).inv (hden z hz)
    exact hd.differentiableWithinAt.mul (hf' z hz)
  have hg_lim : Tendsto g (cobounded ℂ) (𝓝 a) := by
    have hinv : Tendsto (fun z : ℂ => (1 - t * z⁻¹)⁻¹) (cobounded ℂ) (𝓝 1) := by
      have hh : Tendsto (fun z : ℂ => 1 - t * z⁻¹) (cobounded ℂ) (𝓝 (1 : ℂ)) := by
        simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub
          (tendsto_inv₀_cobounded.const_mul t)
      simpa using hh.inv₀ one_ne_zero
    simpa [g] using hinv.mul hlim
  have hg_eq : (∮ z in C(0, r), z⁻¹ * g z) =
      ∮ z in C(0, r), f z / (z - t) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    have hzext : max R ‖t‖ < ‖z‖ := by rw [hz']; exact max_lt hRr htr
    dsimp [g]
    field_simp [hzero z hzext, hsub z hzext, hden z hzext]
  rw [← hg_eq]
  exact two_pi_i_inv_mul_circleIntegral_inv_mul_eq_of_tendsto hg hr
    (max_lt hRr htr) hg_lim

end Complex

end

section

open Complex

open Set Metric Complex

namespace circleIntegral

/-- Contour integration by parts on a circle follows from the product
primitive. Both functions need only be holomorphic on a neighborhood of the
circle; the disk interior need not belong to their domain. -/
theorem mul_deriv_eq_neg_deriv_mul
    {f g : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hU : IsOpen U) (hc : sphere c r ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) :
    (∮ z in C(c, r), f z * deriv g z) =
      -(∮ z in C(c, r), deriv f z * g z) := by
  have hfd : ContinuousOn (deriv f) U := (hf.deriv hU).continuousOn
  have hgd : ContinuousOn (deriv g) U := (hg.deriv hU).continuousOn
  have hleft : CircleIntegrable (fun z => deriv f z * g z) c r :=
    ((hfd.mul hg.continuousOn).mono hc).circleIntegrable hr
  have hright : CircleIntegrable (fun z => f z * deriv g z) c r :=
    ((hf.continuousOn.mul hgd).mono hc).circleIntegrable hr
  have hzero : (∮ z in C(c, r), deriv f z * g z + f z * deriv g z) = 0 := by
    apply integral_eq_zero_of_hasDerivWithinAt hr
    · intro z hz
      exact ((hf.differentiableAt (hU.mem_nhds (hc hz))).hasDerivAt.mul
        (hg.differentiableAt (hU.mem_nhds (hc hz))).hasDerivAt).hasDerivWithinAt
  rw [integral_add hleft hright] at hzero
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hzero)

/-- Moving the derivative from a holomorphic factor to the exponential
changes the sign of the circle integral. This applies on exterior domains
and therefore does not assume holomorphy inside the circle. -/
theorem exp_mul_deriv_eq_neg_exp_mul
    {h : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hU : IsOpen U) (hc : sphere c r ⊆ U)
    (hh : DifferentiableOn ℂ h U) :
    (∮ z in C(c, r), exp z * deriv h z) =
      -(∮ z in C(c, r), exp z * h z) := by
  simpa only [Complex.deriv_exp] using
    mul_deriv_eq_neg_deriv_mul hr hU hc
      Complex.differentiable_exp.differentiableOn hh

end circleIntegral

end

section

open Complex

open Set Metric Complex Filter

open scoped Topology unitInterval

namespace Complex

/-- A circle image sufficiently close to a real dilation can be replaced by
the dilated circle in an exterior holomorphy domain. Negative dilation still
preserves counterclockwise orientation. The strict closeness estimate keeps
the entire straight free homotopy outside the forbidden disk. -/
theorem circleIntegral_comp_mul_deriv_eq_of_close_to_real_mul
    {f g : ℂ → ℂ} {R S r a : ℝ}
    (hr : 0 < r)
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hg : DifferentiableOn ℂ g {z | S < ‖z‖}) (hSr : S < r)
    (hclose : ∀ u ∈ sphere (0 : ℂ) r, ‖g u - (a : ℂ) * u‖ < |a| * r - R) :
    (∮ u in C(0, r), f (g u) * deriv g u) =
      ∮ z in C(0, |a| * r), f z := by
  have hU : IsOpen {z : ℂ | S < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hV : IsOpen {z : ℂ | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hc : sphere (0 : ℂ) |r| ⊆ {z : ℂ | S < ‖z‖} := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa [mem_sphere_iff_norm, abs_of_pos hr] using hz
    simpa [hz'] using hSr
  have hgc : ContinuousOn g (range (circlePath 0 r)) :=
    hg.continuousOn.mono (by
      rintro z ⟨t, rfl⟩
      apply hc
      exact circleMap_mem_sphere' 0 r _)
  let γ₀ := (circlePath 0 r).map' hgc
  let γ₁ := circlePath 0 (a * r)
  let z : ℝ → ℂ := fun t => circleMap 0 r (2 * Real.pi * t)
  let ψ : ℝ × ℝ → ℂ := fun t =>
    ((1 - t.1 : ℝ) : ℂ) * (g (z t.2) - (a : ℂ) * z t.2) + (a : ℂ) * z t.2
  have hgz : Continuous (fun t => g (z t)) := by
    exact hg.continuousOn.comp_continuous
      ((continuous_circleMap 0 r).comp (continuous_const.mul continuous_id))
      (fun t => hc (circleMap_mem_sphere' 0 r _))
  have hz : Continuous z :=
    (continuous_circleMap 0 r).comp (continuous_const.mul continuous_id)
  have hψ : Continuous ψ := by
    exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).mul
      ((hgz.comp continuous_snd).sub (continuous_const.mul (hz.comp continuous_snd)))).add
      (continuous_const.mul (hz.comp continuous_snd))
  have hψV : ∀ t ∈ Icc (0 : ℝ × ℝ) 1, ψ t ∈ {z : ℂ | R < ‖z‖} := by
    intro t ht
    have hnormz : ‖z t.2‖ = r := by simp [z, abs_of_pos hr]
    have hnorma : ‖(a : ℂ) * z t.2‖ = |a| * r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hnormz]
    have herr := hclose (z t.2) (by simpa [mem_sphere_iff_norm] using hnormz)
    have htlo : 0 ≤ t.1 := ht.1.1
    have hthi : t.1 ≤ 1 := ht.2.1
    have hcoeff : ‖((1 - t.1 : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hsmall : ‖((1 - t.1 : ℝ) : ℂ) *
        (g (z t.2) - (a : ℂ) * z t.2)‖ ≤ ‖g (z t.2) - (a : ℂ) * z t.2‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcoeff
    have htriangle : ‖(a : ℂ) * z t.2‖ ≤ ‖ψ t‖ +
        ‖((1 - t.1 : ℝ) : ℂ) * (g (z t.2) - (a : ℂ) * z t.2)‖ := by
      have h := norm_sub_le (ψ t)
        (((1 - t.1 : ℝ) : ℂ) * (g (z t.2) - (a : ℂ) * z t.2))
      simpa only [ψ, add_sub_cancel_left] using h
    change R < ‖ψ t‖
    linarith
  have hleft : ∀ t ∈ Icc (0 : ℝ) 1, γ₀.extend t = ψ (0, t) := by
    intro t ht
    rw [Path.extend_apply _ ht]
    change g (z t) = ψ (0, t)
    simp [ψ]
  have hright : ∀ t ∈ Icc (0 : ℝ) 1, γ₁.extend t = ψ (1, t) := by
    intro t ht
    rw [circlePath_extend_apply ht]
    simp [ψ, z, circleMap, Complex.ofReal_mul, mul_assoc]
  have hloop : ∀ t ∈ Icc (0 : ℝ) 1, ψ (t, 0) = ψ (t, 1) := by
    intro t _
    simp [ψ, z, circleMap]
  have heq := integral_eq_of_differentiableOn_of_freeHomotopy γ₀ γ₁ hψ
    hV hf hψV hleft hright hloop
    (contDiffOn_circlePath_map_extend hU hg hc hgc)
    (contDiffOn_circlePath_extend 0 (a * r))
  rw [integral_circlePath_map_eq_circleIntegral_mul_deriv f hU hg hc hgc,
    integral_circlePath_eq_circleIntegral] at heq
  rw [heq]
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg (lt_of_not_ge ha), neg_mul]
    exact (circleIntegral.neg_radius f 0 (a * r)).symm

/-- An affine asymptote with nonzero real slope suffices to replace every
sufficiently large image circle by any fixed circle in an exterior
holomorphy domain. This derives the geometric homotopy bound from the limit
at infinity. -/
theorem eventually_circleIntegral_comp_mul_deriv_eq_of_tendsto_affine
    {f g : ℂ → ℂ} {R S ρ a : ℝ} {q : ℂ}
    (hf : DifferentiableOn ℂ f {z | R < ‖z‖})
    (hg : DifferentiableOn ℂ g {z | S < ‖z‖}) (ha : a ≠ 0)
    (hlim : Tendsto (fun u => g u - (a : ℂ) * u)
      (Bornology.cobounded ℂ) (𝓝 q)) (hρ : 0 < ρ) (hRρ : R < ρ) :
    ∀ᶠ r : ℝ in atTop,
      (∮ u in C(0, r), f (g u) * deriv g u) = ∮ z in C(0, ρ), f z := by
  have habs : 0 < |a| := abs_pos.mpr ha
  have hbound : ∀ᶠ u in Bornology.cobounded ℂ,
      ‖g u - (a : ℂ) * u‖ < ‖q‖ + 1 :=
    hlim.norm.eventually_lt_const (lt_add_one _)
  obtain ⟨T, _, hT⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hbound
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop S,
    eventually_ge_atTop T, eventually_gt_atTop ((R + ‖q‖ + 1) / |a|)]
    with r hr hSr hTr hlarge
  have hmul : R + ‖q‖ + 1 < r * |a| := (div_lt_iff₀ habs).mp hlarge
  have hclose : ∀ u ∈ sphere (0 : ℂ) r,
      ‖g u - (a : ℂ) * u‖ < |a| * r - R := by
    intro u hu
    have hnorm : ‖u‖ = r := by simpa [mem_sphere_iff_norm] using hu
    have hsmall := hT (x := u) (by change T ≤ ‖u‖; simpa only [hnorm] using hTr)
    nlinarith
  have hRr : R < |a| * r := by nlinarith [norm_nonneg q]
  exact (circleIntegral_comp_mul_deriv_eq_of_close_to_real_mul hr hf hg hSr hclose).trans
    (Complex.circleIntegral_eq_of_differentiableOn_exterior hf (mul_pos habs hr) hρ hRr hRρ)

/-- An exterior holomorphic inverse coordinate changes the exponential
circle moment into the negative exponential moment of the inverse. Both
the common-contour replacement and integration by parts are proved; the
only inverse premise is the pointwise identity near infinity. -/
theorem eventually_circleIntegral_exp_eq_neg_circleIntegral_exp_mul_of_inverse
    {F g : ℂ → ℂ} {R S ρ a : ℝ} {q : ℂ}
    (hF : DifferentiableOn ℂ F {z | R < ‖z‖})
    (hg : DifferentiableOn ℂ g {z | S < ‖z‖}) (ha : a ≠ 0)
    (hlim : Tendsto (fun u => g u - (a : ℂ) * u)
      (Bornology.cobounded ℂ) (𝓝 q))
    (hinverse : ∀ᶠ u in Bornology.cobounded ℂ, F (g u) = u)
    (hρ : 0 < ρ) (hRρ : R < ρ) :
    ∀ᶠ r : ℝ in atTop,
      (∮ z in C(0, ρ), exp (F z)) = -(∮ u in C(0, r), exp u * g u) := by
  have hmoment := eventually_circleIntegral_comp_mul_deriv_eq_of_tendsto_affine
    (Complex.differentiable_exp.comp_differentiableOn hF) hg ha hlim hρ hRρ
  obtain ⟨T, _, hT⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hinverse
  filter_upwards [hmoment, eventually_gt_atTop (0 : ℝ), eventually_gt_atTop S,
    eventually_ge_atTop T] with r hmoment hr hSr hTr
  simp only [Function.comp_def] at hmoment
  have hpoint : EqOn (fun u => exp (F (g u)) * deriv g u)
      (fun u => exp u * deriv g u) (sphere (0 : ℂ) r) := by
    intro u hu
    have hnorm : ‖u‖ = r := by simpa [mem_sphere_iff_norm] using hu
    change exp (F (g u)) * deriv g u = exp u * deriv g u
    rw [hT (x := u) (by change T ≤ ‖u‖; simpa only [hnorm] using hTr)]
  rw [circleIntegral.integral_congr hr.le hpoint] at hmoment
  have hU : IsOpen {z : ℂ | S < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hc : sphere (0 : ℂ) r ⊆ {z : ℂ | S < ‖z‖} := by
    intro u hu
    have hnorm : ‖u‖ = r := by simpa [mem_sphere_iff_norm] using hu
    change S < ‖u‖
    simpa only [hnorm] using hSr
  rw [circleIntegral.exp_mul_deriv_eq_neg_exp_mul hr.le hU hc hg]
    at hmoment
  exact hmoment.symm

end Complex

end
