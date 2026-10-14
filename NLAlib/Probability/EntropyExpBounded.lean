/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.Tilted
public import NLAlib.Probability.Entropy

/-!
# The entropy of the exponential of a bounded function

If `g` takes values in `[a, b]`, then `Ent(e^{s g}) ≤ s² (b - a)² / 8 · E e^{s g}`: the entropy
form of Hoeffding's lemma. With Herbst's argument
(`NLAlib.hasSubgaussianMGF_sub_integral_of_entropy_le`) it recovers Hoeffding's lemma; with the
tensorization of entropy (`NLAlib.entropy_pi_le_sum`) applied on the fibres of a function of
independent coordinates it gives the bounded differences inequality
(`NLAlib/Probability/BoundedDifferences.lean`).

This file is a skeleton addition to `NLAlib/Probability/Entropy.lean`
(`docs/design/Probability-P7.md` §3.2, §8), to be merged into it at wrap-up.

## Main results

* `NLAlib.entropy_exp_mul_le_of_mem_Icc`: for `g` almost surely in `[a, b]`.
* `NLAlib.entropy_exp_mul_le_of_abs_sub_le`: for `g` with oscillation at most `c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ν : Measure Ω}

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
and `b = a + c`, `g` takes values in `[a, b]`; `NLAlib.entropy_exp_mul_le_of_mem_Icc`. Easy. -/
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
