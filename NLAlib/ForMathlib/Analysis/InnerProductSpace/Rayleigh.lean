/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Cone majorants of the Rayleigh quotient

Upstream candidate for Mathlib. A symmetric operator whose Rayleigh quotients admit cone
majorants has an eigenvector in that cone at its norm.

## Main results

* `ContinuousLinearMap.exists_norm_eigenvector_of_rayleigh_majorants`.
-/

@[expose] public section

open Metric Set

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- A symmetric operator with same-norm cone majorants has a nonzero cone eigenvector at its
nonnegative operator norm. -/
theorem exists_norm_eigenvector_of_rayleigh_majorants
    (T : E →L[ℝ] E) (hT : T.IsSymmetric) (C : E → Prop)
    (hC : ∀ x, ∃ y, C y ∧ ‖y‖ = ‖x‖ ∧ |T.reApplyInnerSelf x| ≤ T.reApplyInnerSelf y) :
    ∃ y, y ≠ 0 ∧ C y ∧ T y = ‖T‖ • y := by
  classical
  let := FiniteDimensional.proper_rclike ℝ E
  let := FiniteDimensional.complete ℝ E
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_sphere (0 : E) ‖x‖).exists_isMaxOn
    (show (sphere (0 : E) ‖x‖).Nonempty from ⟨x, by simp⟩)
    T.reApplyInnerSelf_continuous.continuousOn
  have hnx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀
  obtain ⟨y, hyC, hyn, hyQ⟩ := hC x₀
  have hny : ‖y‖ = ‖x‖ := hyn.trans hnx₀
  have hy0 : y ≠ 0 := by
    intro h
    have hz : ‖x‖ = 0 := by simpa only [h, norm_zero] using hny.symm
    exact hxp.ne' hz
  have hymax : IsMaxOn T.reApplyInnerSelf (sphere (0 : E) ‖y‖) y := by
    intro z hz
    have hz' : z ∈ sphere (0 : E) ‖x‖ := by simpa only [hny] using hz
    exact (hmax hz').trans ((le_abs_self _).trans hyQ)
  have hqnonneg : 0 ≤ T.rayleighQuotient y :=
    div_nonneg ((abs_nonneg _).trans hyQ) (sq_nonneg _)
  have hbound (z : E) : |T.rayleighQuotient z| ≤ T.rayleighQuotient y := by
    by_cases hz0 : z = 0
    · simpa only [hz0, T.rayleighQuotient_apply_zero, abs_zero] using hqnonneg
    obtain ⟨k, hkC, hkn, hkQ⟩ := hC z
    have hk0 : k ≠ 0 := by
      intro h
      have : ‖z‖ = 0 := by simpa [h] using hkn.symm
      exact hz0 (norm_eq_zero.mp this)
    have hzK : |T.rayleighQuotient z| ≤ T.rayleighQuotient k := by
      simpa only [ContinuousLinearMap.rayleighQuotient, abs_div, abs_sq, hkn] using
        div_le_div_of_nonneg_right hkQ (sq_nonneg ‖z‖)
    have hm : T.rayleighQuotient k ∈ T.rayleighQuotient '' sphere (0 : E) ‖x‖ := by
      rw [← T.image_rayleigh_eq_image_rayleigh_sphere hxp]
      exact ⟨k, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hk0, rfl⟩
    obtain ⟨w, hw, heq⟩ := hm
    have hwn : ‖w‖ = ‖y‖ := by simpa only [mem_sphere, dist_zero_right, hny] using hw
    have hwmax : T.reApplyInnerSelf w ≤ T.reApplyInnerSelf y :=
      hymax (by simpa only [hny] using hw)
    apply hzK.trans
    rw [← heq]
    dsimp only [ContinuousLinearMap.rayleighQuotient]
    rw [hwn]
    exact div_le_div_of_nonneg_right hwmax (sq_nonneg _)
  have heq : ‖T‖ = T.rayleighQuotient y := by
    apply le_antisymm
    · rw [T.norm_eq_iSup_rayleighQuotient hT]
      exact ciSup_le hbound
    · exact (le_abs_self _).trans (T.rayleighQuotient_le_norm y)
  refine ⟨y, hy0, hyC, ?_⟩
  rw [heq]
  exact hT.isSelfAdjoint.eq_smul_self_of_isLocalExtrOn (Or.inr hymax.localize)

end ContinuousLinearMap
