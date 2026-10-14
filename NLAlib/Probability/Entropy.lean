/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.Tilted

/-!
# The entropy functional and Herbst's argument

`NLAlib.entropy ν f = E f log f - E f log E f` is the entropy of a nonnegative function under a
measure. It is nonnegative under a probability measure (Jensen), it tensorizes over product
measures (`NLAlib/Probability/EntropyTensorization.lean`), and an entropy bound for `exp (s f)`
of the right order in `s` makes `f - E f` sub-Gaussian (Herbst's argument). These are the steps
from a logarithmic Sobolev inequality to concentration.

If `g` takes values in `[a, b]`, then `Ent(e^{s g}) ≤ s² (b - a)² / 8 · E e^{s g}`: the entropy
form of Hoeffding's lemma. With Herbst's argument it recovers Hoeffding's lemma; with the
tensorization of entropy (`NLAlib.entropy_pi_le_sum`) applied on the fibres of a function of
independent coordinates it gives the bounded differences inequality
(`NLAlib/Probability/BoundedDifferences.lean`).

`entropy ν f` is a junk value when `f log f` or `f` is not integrable (the Bochner integral is `0`
then), so every statement about it carries the integrability it needs.

## Main definitions

* `NLAlib.entropy ν f`.

## Main results

* `NLAlib.entropy_nonneg`.
* `NLAlib.hasSubgaussianMGF_sub_integral_of_entropy_le`: Herbst's argument.
* `NLAlib.entropy_exp_mul_le_of_mem_Icc`, `NLAlib.entropy_exp_mul_le_of_abs_sub_le`: the entropy
  of `e^{s g}` for `g` in `[a, b]`, respectively of oscillation at most `c`.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Proposition 6.1 and the proof of Theorem 6.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal ENNReal Topology

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}

/-- The entropy of a nonnegative function `f` under `ν`: `E f log f - E f log E f`. It is a junk
value when `f` or `f log f` is not integrable. -/
noncomputable def entropy (ν : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω * Real.log (f ω) ∂ν - (∫ ω, f ω ∂ν) * Real.log (∫ ω, f ω ∂ν)

/-- The entropy of a nonnegative function under a probability measure is nonnegative. -/
theorem entropy_nonneg [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[ν] f)
    (hf : Integrable f ν) (hflog : Integrable (fun ω => f ω * Real.log (f ω)) ν) :
    0 ≤ entropy ν f := by
  have h := Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici hf0 hf hflog
  rw [entropy, sub_nonneg]
  exact h

/-! ### Resampling one coordinate of a product measure -/


/-- Herbst's argument on the upper half-line: an entropy bound `c s² E e^{s f}` for `s > 0` gives
`E e^{s f} ≤ exp (s E f + c s²)` for `s ≥ 0`. -/
private theorem integral_exp_mul_le_exp_of_entropy_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (c : ℝ) (hint : ∀ s, Integrable (fun ω => rexp (s * f ω)) μ)
    (hent : ∀ s, 0 < s →
      entropy μ (fun ω => rexp (s * f ω)) ≤ c * s ^ 2 * ∫ ω, rexp (s * f ω) ∂μ)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫ ω, rexp (s * f ω) ∂μ ≤ rexp (s * ∫ ω, f ω ∂μ + c * s ^ 2) := by
  set M : ℝ → ℝ := mgf f μ with hMdef
  set E : ℝ := ∫ ω, f ω ∂μ with hEdef
  have hint' : ∀ u : ℝ, u ∈ interior (integrableExpSet f μ) := by
    intro u
    have : integrableExpSet f μ = Set.univ := Set.eq_univ_of_forall fun v => hint v
    simp [this]
  set M' : ℝ → ℝ := fun u => ∫ ω, f ω * rexp (u * f ω) ∂μ with hM'def
  have hM : ∀ u, HasDerivAt M (M' u) u := fun u => hasDerivAt_mgf (hint' u)
  have hMpos : ∀ u, 0 < M u := fun u => mgf_pos (hint u)
  have hMeq : ∀ u, ∫ ω, rexp (u * f ω) ∂μ = M u := fun u => rfl
  set G : ℝ → ℝ := fun u => Real.log (M u) - u * E - c * u ^ 2 with hGdef
  set G' : ℝ → ℝ := fun u => M' u / M u - E - c * (2 * u) with hG'def
  have hG : ∀ u, HasDerivAt G (G' u) u := by
    intro u
    have := (((hM u).log (hMpos u).ne').sub ((hasDerivAt_id u).mul_const E)).sub
      ((hasDerivAt_pow 2 u).const_mul c)
    refine HasDerivAt.congr_deriv (f := G) this ?_
    simp only [hG'def]
    ring
  have hG0 : G 0 = 0 := by simp [hGdef, hMdef]
  have hG'0 : G' 0 = 0 := by simp [hG'def, hM'def, hMdef, hEdef]
  set φ : ℝ → ℝ := fun u => G u / u with hφdef
  have hφ : ∀ u, 0 < u → HasDerivAt φ ((G' u * u - G u * 1) / u ^ 2) u :=
    fun u hu => (hG u).div (hasDerivAt_id u) hu.ne'
  have hnum : ∀ u, 0 < u → G' u * u - G u * 1 ≤ 0 := by
    intro u hu
    have he := hent u hu
    have hfe : ∫ ω, rexp (u * f ω) * Real.log (rexp (u * f ω)) ∂μ = u * M' u := by
      simp only [Real.log_exp, hM'def, ← integral_const_mul]
      congr 1; ext ω; ring
    rw [entropy, hfe, hMeq] at he
    have hMu := hMpos u
    have key : u * (M' u / M u) - Real.log (M u) ≤ c * u ^ 2 := by
      have : u * (M' u / M u) - Real.log (M u) = (u * M' u - M u * Real.log (M u)) / M u := by
        field_simp
      rw [this, div_le_iff₀ hMu]; linarith
    simp only [hG'def, hGdef]
    nlinarith [key]
  have hanti : AntitoneOn φ (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun u hu => (hφ u hu).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      exact fun u hu => (hφ u hu).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro u hu
      rw [(hφ u hu).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (hnum u hu) (sq_nonneg _)
  rcases hs.eq_or_lt with hs0 | hspos
  · subst hs0
    simp
  have hslope := (hG 0).tendsto_slope_zero_right
  rw [hG'0] at hslope
  have hφs : φ s ≤ 0 := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [Ioo_mem_nhdsGT hspos] with u hu
    simp only [zero_add, hG0, sub_zero, smul_eq_mul]
    rw [inv_mul_eq_div]
    exact hanti hu.1 hspos hu.2.le
  have hGs : G s ≤ 0 := by
    have : G s = φ s * s := by simp [hφdef, hspos.ne']
    rw [this]; exact mul_nonpos_of_nonpos_of_nonneg hφs hs
  rw [hMeq]
  have hlog : Real.log (M s) ≤ s * E + c * s ^ 2 := by simp only [hGdef] at hGs; linarith
  calc M s = rexp (Real.log (M s)) := (Real.exp_log (hMpos s)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- **Herbst's argument** ([BoucheronLugosiMassart2013], Proposition 6.1): if the entropy of
`exp (s f)` is at most `c s² / 2` times its mean for every `s`, then `f - E f` is sub-Gaussian with
proxy `c`. The hypothesis for `s > 0` gives the upper tail, for `s < 0` the lower one. -/
theorem hasSubgaussianMGF_sub_integral_of_entropy_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    {c : ℝ≥0} (hint : ∀ s, Integrable (fun ω => rexp (s * f ω)) μ)
    (hent : ∀ s, entropy μ (fun ω => rexp (s * f ω)) ≤ c * s ^ 2 / 2 * ∫ ω, rexp (s * f ω) ∂μ) :
    HasSubgaussianMGF (fun ω => f ω - ∫ ω', f ω' ∂μ) c μ := by
  set E := ∫ ω', f ω' ∂μ with hE
  have hexp (t : ℝ) : (fun ω => rexp (t * (f ω - E))) =
      fun ω => rexp (t * f ω) * rexp (-(t * E)) := by
    ext ω; rw [← Real.exp_add]; ring_nf
  have hent' : ∀ s, 0 < s → entropy μ (fun ω => rexp (s * f ω)) ≤
      (c / 2 : ℝ) * s ^ 2 * ∫ ω, rexp (s * f ω) ∂μ := fun s _ => by
    have := hent s; ring_nf at this ⊢; exact this
  have hnegf (s : ℝ) : (fun ω => rexp (s * -f ω)) = fun ω => rexp (-s * f ω) := by
    ext ω; ring_nf
  have hintn : ∀ s, Integrable (fun ω => rexp (s * -f ω)) μ := fun s => by
    rw [hnegf]; exact hint _
  have hentn : ∀ s, 0 < s → entropy μ (fun ω => rexp (s * -f ω)) ≤
      (c / 2 : ℝ) * s ^ 2 * ∫ ω, rexp (s * -f ω) ∂μ := fun s _ => by
    have := hent (-s); rw [hnegf]; ring_nf at this ⊢; exact this
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [hexp]; exact (hint t).mul_const _
  rw [mgf, hexp, integral_mul_const]
  rcases le_total 0 t with ht | ht
  · have h := integral_exp_mul_le_exp_of_entropy_le (c / 2 : ℝ) hint hent' ht
    calc (∫ ω, rexp (t * f ω) ∂μ) * rexp (-(t * E))
        ≤ rexp (t * E + c / 2 * t ^ 2) * rexp (-(t * E)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = rexp (c * t ^ 2 / 2) := by rw [← Real.exp_add]; ring_nf
  · have h := integral_exp_mul_le_exp_of_entropy_le (c / 2 : ℝ) hintn hentn (neg_nonneg.2 ht)
    rw [hnegf, neg_neg, integral_neg] at h
    calc (∫ ω, rexp (t * f ω) ∂μ) * rexp (-(t * E))
        ≤ rexp (-t * -E + c / 2 * (-t) ^ 2) * rexp (-(t * E)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = rexp (c * t ^ 2 / 2) := by rw [← Real.exp_add]; ring_nf

/-! ### The entropy of the exponential of a bounded function -/

/-- **The entropy of an exponential of a bounded function**: if `g` lies in `[a, b]` almost
surely, then `Ent(e^{s g}) ≤ s² (b - a)² / 8 · E e^{s g}` for every `s`. The entropy form of
Hoeffding's lemma, with the hypothesis of Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`.
[BoucheronLugosiMassart2013, proof of Theorem 6.2].
Proof: with `Λ = cgf g ν`, `Ent(e^{s g}) / E e^{s g} = s Λ'(s) - Λ(s) = ∫₀ˢ θ Λ''(θ) dθ`, and
`Λ''(θ)` is the variance of `g` under the tilted measure `ν.tilted (θ * g ·)`, at most
`(b - a)² / 4`. The variance step is that of Mathlib's
`ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero` (`variance_tilted_mul`,
`variance_le_sq_of_bounded`); in place of its Taylor step
(`exists_cgf_eq_iteratedDeriv_two_cgf_mul`), the mean value theorem for
`s Λ'(s) - Λ(s) - s² (b - a)² / 8`, which vanishes at `0` and has derivative
`s (Λ''(s) - (b - a)² / 4)`. -/
theorem entropy_exp_mul_le_of_mem_Icc [IsProbabilityMeasure ν] {g : Ω → ℝ}
    (hg : AEMeasurable g ν) {a b : ℝ} (hab : ∀ᵐ ω ∂ν, g ω ∈ Set.Icc a b) (s : ℝ) :
    entropy ν (fun ω => rexp (s * g ω)) ≤ s ^ 2 * (b - a) ^ 2 / 8 * ∫ ω, rexp (s * g ω) ∂ν := by
  have hi (u : ℝ) : Integrable (fun ω => rexp (u * g ω)) ν := integrable_exp_mul_of_mem_Icc hg hab
  have hint (u : ℝ) : u ∈ interior (integrableExpSet g ν) := by simp [hi, integrableExpSet]
  set Λ := cgf g ν with hΛdef
  have hvar (u : ℝ) : iteratedDeriv 2 Λ u ≤ (b - a) ^ 2 / 4 := by
    rw [← variance_tilted_mul (hint u)]
    have := isProbabilityMeasure_tilted (hi u)
    calc _ ≤ ((b - a) / 2) ^ 2 :=
          variance_le_sq_of_bounded ((tilted_absolutelyContinuous ν (u * g ·)) hab)
            (hg.mono_ac (tilted_absolutelyContinuous ν _))
      _ = _ := by ring
  have hΛ (u : ℝ) : HasDerivAt Λ (deriv Λ u) u :=
    (analyticAt_cgf (hint u)).differentiableAt.hasDerivAt
  have hΛ' (u : ℝ) : HasDerivAt (deriv Λ) (iteratedDeriv 2 Λ u) u := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (analyticAt_cgf (hint u)).deriv.differentiableAt.hasDerivAt
  set φ : ℝ → ℝ := fun u => u * deriv Λ u - Λ u - u ^ 2 * ((b - a) ^ 2 / 8) with hφdef
  have hφ (u : ℝ) : HasDerivAt φ (u * (iteratedDeriv 2 Λ u - (b - a) ^ 2 / 4)) u := by
    have h := (((hasDerivAt_id u).mul (hΛ' u)).sub (hΛ u)).sub
      ((hasDerivAt_pow 2 u).mul_const ((b - a) ^ 2 / 8))
    refine h.congr_deriv ?_
    simp only [id, Nat.cast_ofNat]
    ring
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun u => (hφ u).continuousAt
  have hφ0 : φ 0 = 0 := by simp [hφdef, hΛdef]
  have hφs : φ s ≤ 0 := by
    rcases lt_trichotomy s 0 with hs | hs | hs
    · obtain ⟨u, hu, hu'⟩ := exists_hasDerivAt_eq_slope φ _ hs hφc.continuousOn
        (fun x _ => hφ x)
      rw [hφ0] at hu'
      have he : φ s = s * (u * (iteratedDeriv 2 Λ u - (b - a) ^ 2 / 4)) := by
        rw [hu']; field_simp; ring
      rw [he]
      have := hvar u
      have hsu : 0 < s * u := mul_pos_of_neg_of_neg hs hu.2
      nlinarith
    · rw [hs, hφ0]
    · obtain ⟨u, hu, hu'⟩ := exists_hasDerivAt_eq_slope φ _ hs hφc.continuousOn
        (fun x _ => hφ x)
      rw [hφ0] at hu'
      have he : φ s = s * (u * (iteratedDeriv 2 Λ u - (b - a) ^ 2 / 4)) := by
        rw [hu', sub_zero, sub_zero]; field_simp
      rw [he]
      have := hvar u
      have hsu : 0 < s * u := mul_pos hs hu.1
      nlinarith
  have hM := mgf_pos (hi s)
  have h1 : ∫ ω, rexp (s * g ω) * Real.log (rexp (s * g ω)) ∂ν =
      s * ∫ ω, g ω * rexp (s * g ω) ∂ν := by
    simp only [Real.log_exp]
    rw [← integral_const_mul]
    congr 1
    ext ω
    ring
  have hent : entropy ν (fun ω => rexp (s * g ω)) = mgf g ν s * (s * deriv Λ s - Λ s) := by
    rw [entropy, h1, hΛdef, deriv_cgf (hint s)]
    change _ - mgf g ν s * Real.log (mgf g ν s) = _
    simp only [cgf]
    field_simp
  have hφs' : s * deriv Λ s - Λ s ≤ s ^ 2 * (b - a) ^ 2 / 8 := by
    simp only [hφdef] at hφs
    linarith
  rw [hent, show ∫ ω, rexp (s * g ω) ∂ν = mgf g ν s from rfl, mul_comm (mgf g ν s)]
  exact mul_le_mul_of_nonneg_right hφs' hM.le

/-- **The entropy of an exponential of a function of bounded oscillation**: if
`|g x - g y| ≤ c` for all `x`, `y`, then `Ent(e^{s g}) ≤ s² c² / 8 · E e^{s g}`. The pointwise
form used on the fibres of a function with bounded differences.
[BoucheronLugosiMassart2013, proof of Theorem 6.2].
Proof: `Ω` is nonempty (probability measure) and `g` is bounded, so with `a = sInf (Set.range g)`
and `b = a + c`, `g` takes values in `[a, b]`; `NLAlib.entropy_exp_mul_le_of_mem_Icc`. -/
theorem entropy_exp_mul_le_of_abs_sub_le [IsProbabilityMeasure ν] {g : Ω → ℝ}
    (hg : AEMeasurable g ν) {c : ℝ≥0} (hc : ∀ x y, |g x - g y| ≤ c) (s : ℝ) :
    entropy ν (fun ω => rexp (s * g ω)) ≤ s ^ 2 * c ^ 2 / 8 * ∫ ω, rexp (s * g ω) ∂ν := by
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure ν
  obtain ⟨ω₀⟩ := id hne
  have hlow : ∀ x y, g x - c ≤ g y := fun x y => by
    linarith [(le_abs_self (g x - g y)).trans (hc x y)]
  have hbdd : BddBelow (Set.range g) := ⟨g ω₀ - c, by rintro _ ⟨x, rfl⟩; exact hlow ω₀ x⟩
  set a := sInf (Set.range g)
  have hmem : ∀ x, g x ∈ Set.Icc a (a + c) := fun x =>
    ⟨csInf_le hbdd ⟨x, rfl⟩, by
      have : g x - c ≤ a := le_csInf (Set.range_nonempty g) (by rintro _ ⟨y, rfl⟩; exact hlow x y)
      linarith⟩
  have h := entropy_exp_mul_le_of_mem_Icc hg (ae_of_all _ hmem) s
  rwa [add_sub_cancel_left] at h

end NLAlib
