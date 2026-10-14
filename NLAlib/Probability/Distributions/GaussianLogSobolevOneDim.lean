/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.CentralLimitTheorem
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

end NLAlib
