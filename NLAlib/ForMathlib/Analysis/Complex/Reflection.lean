/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Reflection and half-plane control

Schwarz reflection and asymptotic affine behavior control the imaginary part on a half-plane.
Upstream candidate for Mathlib.

The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `Complex.differentiableOn_schwarzHalfPlaneExtension_union_exterior`.
-/
@[expose] public section

section

open Filter Metric Set

open scoped Topology

namespace Complex

private theorem norm_le_norm_add_mul_I {z : ℂ} (hz : 0 ≤ z.im) {t : ℝ} (ht : 0 ≤ t) :
    ‖z‖ ≤ ‖z + (t : ℂ) * I‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, sub_zero, mul_one, add_zero]
  nlinarith

private theorem im_pos_of_slope_pos {f : ℂ → ℂ} {R d : ℝ} {c z : ℂ}
    (hcont : ContinuousOn f {u | R < ‖u‖})
    (hreal : ∀ u, R < ‖u‖ → 0 < u.im → (f u).im ≠ 0)
    (hlim : Tendsto (fun u => f u - (d : ℂ) * u) (Bornology.cobounded ℂ) (𝓝 c))
    (hd : 0 < d) (hzR : R < ‖z‖) (hzim : 0 < z.im) : 0 < (f z).im := by
  let ray : ℝ → ℂ := fun t => z + (t : ℂ) * I
  have hnorm : ∀ t ∈ Ici (0 : ℝ), R < ‖ray t‖ := fun t ht =>
    hzR.trans_le (norm_le_norm_add_mul_I hzim.le ht)
  have him : ∀ t ∈ Ici (0 : ℝ), 0 < (ray t).im := by
    intro t ht
    simpa [ray] using add_pos_of_pos_of_nonneg hzim ht
  have hray : Continuous ray := by fun_prop
  have hg : ContinuousOn (fun t => (f (ray t)).im) (Ici (0 : ℝ)) :=
    continuous_im.continuousOn.comp
      (hcont.comp hray.continuousOn hnorm) (fun _ _ => mem_univ _)
  have ht : Tendsto (fun t : ℝ => z.im + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop z.im tendsto_id
  have hnormTop : Tendsto (fun t => ‖ray t‖) atTop atTop := by
    apply tendsto_atTop_mono _ ht
    intro t
    simpa [ray] using im_le_norm (ray t)
  have hcb : Tendsto ray atTop (Bornology.cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.mp hnormTop
  have herror : Tendsto (fun t => (f (ray t) - (d : ℂ) * ray t).im)
      atTop (𝓝 c.im) := continuous_im.tendsto c |>.comp (hlim.comp hcb)
  have hlinear : Tendsto (fun t : ℝ => d * (z.im + t)) atTop atTop :=
    ht.const_mul_atTop hd
  have hgTop : Tendsto (fun t => (f (ray t)).im) atTop atTop := by
    convert herror.add_atTop hlinear using 1
    ext t
    simp [ray]
  obtain ⟨T, hT, hgT⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hgTop.eventually_gt_atTop 0)).exists
  by_contra hnot
  have hzle : (f (ray 0)).im ≤ 0 := by simpa [ray] using le_of_not_gt hnot
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hT
    (hg.mono (fun _ ht => ht.1)) ⟨hzle, hgT.le⟩
  exact hreal (ray t) (hnorm t ht.1) (him t ht.1) hzero

/-- A continuous exterior branch avoiding the real axis in the upper half-plane
has positive imaginary part exactly when its nonzero real affine asymptotic slope
is positive. The conclusion holds on the whole exterior upper half-plane, including
points arbitrarily close to the real axis. -/
theorem im_pos_iff_slope_pos_of_tendsto_affine {f : ℂ → ℂ} {R d : ℝ} {c z : ℂ}
    (hcont : ContinuousOn f {u | R < ‖u‖})
    (hreal : ∀ u, R < ‖u‖ → 0 < u.im → (f u).im ≠ 0)
    (hlim : Tendsto (fun u => f u - (d : ℂ) * u) (Bornology.cobounded ℂ) (𝓝 c))
    (hd : d ≠ 0) (hzR : R < ‖z‖) (hzim : 0 < z.im) :
    0 < (f z).im ↔ 0 < d := by
  constructor
  · intro hf
    by_contra hdnot
    have hdneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hdnot) hd
    have hnegreal : ∀ u, R < ‖u‖ → 0 < u.im → (-f u).im ≠ 0 := by
      intro u hu him
      simpa using hreal u hu him
    have hneglim : Tendsto (fun u => -f u - ((-d : ℝ) : ℂ) * u)
        (Bornology.cobounded ℂ) (𝓝 (-c)) := by
      convert hlim.neg using 1
      ext u
      push_cast
      ring
    have hneg := im_pos_of_slope_pos hcont.neg hnegreal hneglim
      (neg_pos.mpr hdneg) hzR hzim
    simpa using (not_lt_of_ge hf.le) (neg_pos.mp hneg)
  · exact fun hdpos => im_pos_of_slope_pos hcont hreal hlim hdpos hzR hzim

end Complex

end

section

open Complex Filter

open scoped Topology ComplexConjugate

namespace Complex

private theorem tendsto_conj_cobounded :
    Tendsto (conj : ℂ → ℂ) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa only [norm_conj] using (tendsto_norm_cobounded_atTop (E := ℂ))

private theorem tendsto_affine_ratio {f : ℂ → ℂ} {d c : ℂ}
    (hf : Tendsto (fun u => f u - d * u) (Bornology.cobounded ℂ) (𝓝 c)) :
    Tendsto (fun u => f u * u⁻¹) (Bornology.cobounded ℂ) (𝓝 d) := by
  have hi : Tendsto (fun u : ℂ => u⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    tendsto_inv₀_cobounded
  have ht : Tendsto (fun u => (f u - d * u) * u⁻¹ + d)
      (Bornology.cobounded ℂ) (𝓝 d) := by
    simpa using (hf.mul hi).add_const d
  apply ht.congr'
  filter_upwards [eventually_cobounded_le_norm (1 : ℝ)] with u hu
  have hune : u ≠ 0 := by intro hzero; norm_num [hzero] at hu
  field_simp
  ring

/-- A finite exterior family preserved as an unlabelled family by conjugation
is eventually Schwarz-symmetric label by label when its affine slopes are real
and pairwise distinct. The constant terms may initially be arbitrary complex numbers. -/
theorem eventually_conj_eq_of_tendsto_affine_of_finite_matching
    {ι : Type*} [Finite ι] (f : ι → ℂ → ℂ) (d : ι → ℝ) (c : ι → ℂ)
    (hd : Function.Injective d)
    (hlim : ∀ i, Tendsto (fun u => f i u - (d i : ℂ) * u)
      (Bornology.cobounded ℂ) (𝓝 (c i)))
    (hmatch : ∀ᶠ u in Bornology.cobounded ℂ, ∀ i,
      ∃ j, conj (f i (conj u)) = f j u) :
    ∀ᶠ u in Bornology.cobounded ℂ, ∀ i, f i (conj u) = conj (f i u) := by
  have hratio (i : ι) : Tendsto (fun u => f i u * u⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (d i : ℂ)) := tendsto_affine_ratio (hlim i)
  have href (i : ι) : Tendsto (fun u => conj (f i (conj u)) * u⁻¹)
      (Bornology.cobounded ℂ) (𝓝 (d i : ℂ)) := by
    have h := continuous_conj.continuousAt.tendsto.comp
      ((hratio i).comp tendsto_conj_cobounded)
    simpa [Function.comp_def] using h
  have hneq : ∀ i j, ∀ᶠ u in Bornology.cobounded ℂ,
      i ≠ j → conj (f i (conj u)) ≠ f j u := by
    intro i j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    have hdiff : (d i : ℂ) - (d j : ℂ) ≠ 0 := by
      intro heq
      exact hij (hd (ofReal_injective (sub_eq_zero.mp heq)))
    filter_upwards [((href i).sub (hratio j)).eventually_ne hdiff] with u hu _ heq
    exact hu (by rw [heq]; ring)
  have hneq' : ∀ᶠ u in Bornology.cobounded ℂ, ∀ i j,
      i ≠ j → conj (f i (conj u)) ≠ f j u := by
    simpa only [Filter.eventually_all] using hneq
  filter_upwards [hmatch, hneq'] with u hm hn i
  obtain ⟨j, hj⟩ := hm i
  have hij : i = j := by
    by_contra hne
    exact hn i j hne hj
  subst j
  simpa using congrArg conj hj

end Complex

end

section

open Set Filter

open scoped Topology ComplexConjugate

namespace Complex

/-- Reflect an upper-half-plane function below the real axis, retaining the
specified values on the axis itself. No regularity across the axis is implicit. -/
noncomputable def schwarzHalfPlaneExtension (f axis : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 < z.im then f z else if z.im < 0 then conj (f (conj z)) else axis z

/-- The reflected extension has Schwarz symmetry away from the real axis. -/
theorem schwarzHalfPlaneExtension_conj (f axis : ℂ → ℂ) {z : ℂ}
    (hz : z.im ≠ 0) :
    schwarzHalfPlaneExtension f axis (conj z) =
      conj (schwarzHalfPlaneExtension f axis z) := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · simp [schwarzHalfPlaneExtension, hneg, not_lt_of_ge hneg.le]
  · simp [schwarzHalfPlaneExtension, hpos, not_lt_of_ge hpos.le]

/-- Schwarz-symmetric axis values make the reflected extension symmetric also
at real points. Regularity on the real axis is still a separate property. -/
theorem schwarzHalfPlaneExtension_conj_of_conj_eq_axis (f axis : ℂ → ℂ)
    (haxis : ∀ z : ℂ, axis (conj z) = conj (axis z)) (z : ℂ) :
    schwarzHalfPlaneExtension f axis (conj z) =
      conj (schwarzHalfPlaneExtension f axis z) := by
  by_cases hz : z.im = 0
  · simp [schwarzHalfPlaneExtension, hz, haxis]
  · exact schwarzHalfPlaneExtension_conj f axis hz

/-- Reflection preserves complex differentiability off the real axis. -/
theorem differentiableOn_schwarzHalfPlaneExtension (f axis : ℂ → ℂ)
    (hf : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ (schwarzHalfPlaneExtension f axis) {z | z.im ≠ 0} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hh : DifferentiableAt ℂ (conj ∘ f ∘ conj) z := by
      simpa only [conj_conj] using (hf (conj z) (by simpa using neg_pos.mpr hneg)).conj_conj
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_lt continuous_im continuous_const |>.mem_nhds hneg] with w hw
    simp only [Function.comp_apply]
    simp [schwarzHalfPlaneExtension, hw, not_lt_of_ge hw.le]
  · apply (hf z hpos).congr_of_eventuallyEq
    filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds hpos] with w hw
    simp [schwarzHalfPlaneExtension, hw]

/-- Exterior agreement above the real axis and Schwarz symmetry determine the
same extension below, while the supplied axis values handle the real points. -/
theorem schwarzHalfPlaneExtension_eq_of_conj_eq
    (f g : ℂ → ℂ) {R : ℝ}
    (hupper : ∀ z : ℂ, R < ‖z‖ → 0 < z.im → f z = g z)
    (href : ∀ z : ℂ, R < ‖z‖ → g (conj z) = conj (g z))
    {z : ℂ} (hz : R < ‖z‖) : schwarzHalfPlaneExtension f g z = g z := by
  by_cases hpos : 0 < z.im
  · simp [schwarzHalfPlaneExtension, hpos, hupper z hz hpos]
  · by_cases hneg : z.im < 0
    · have hzconj : R < ‖conj z‖ := by simpa using hz
      have hposconj : 0 < (conj z).im := by simpa using neg_pos.mpr hneg
      simp [schwarzHalfPlaneExtension, hpos, hneg, hupper (conj z) hzconj hposconj,
        href z hz]
    · simp [schwarzHalfPlaneExtension, hpos, hneg]

/-- The reflected function is holomorphic on the union of the two open
half-planes and any exterior domain on which the supplied analytic extension
agrees. This is an actual open domain across the exterior real rays. -/
theorem differentiableOn_schwarzHalfPlaneExtension_union_exterior
    (f g : ℂ → ℂ) {R : ℝ}
    (hf : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z)
    (hg : DifferentiableOn ℂ g {z | R < ‖z‖})
    (hupper : ∀ z : ℂ, R < ‖z‖ → 0 < z.im → f z = g z)
    (href : ∀ z : ℂ, R < ‖z‖ → g (conj z) = conj (g z)) :
    DifferentiableOn ℂ (schwarzHalfPlaneExtension f g)
      ({z | z.im ≠ 0} ∪ {z | R < ‖z‖}) := by
  have hext : DifferentiableOn ℂ (schwarzHalfPlaneExtension f g) {z | R < ‖z‖} := by
    apply hg.congr
    intro z hz
    exact schwarzHalfPlaneExtension_eq_of_conj_eq f g hupper href hz
  exact (differentiableOn_schwarzHalfPlaneExtension f g hf).union_of_isOpen hext
    (isOpen_ne_fun continuous_im continuous_const)
    (isOpen_lt continuous_const continuous_norm)

end Complex

end
