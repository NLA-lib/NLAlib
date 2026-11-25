/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Rounding
public import NLAlib.ForMathlib.Analysis.Real.Sqrt

/-!
# Forward errors for rounded Cholesky columns

These scalar estimates concern the square root followed by division used by the actual
stored Cholesky column. A positive input spectral margin controls both denominators.

## Main results

* `NLAlib.abs_sub_div_sqrt_le_of_pivot_relErr`: the actual rounded normalized-column bound.
-/

@[expose] public section

namespace NLAlib

private theorem roundingFactor_two_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10) :
    Computation.roundingFactor 2 u ≤ 4 * u := by
  have hd : 0 < 1 - 2 * u := by linarith
  have h := Computation.roundingFactor_le (n := 2) hu (by norm_num; linarith)
  norm_num at h
  exact h.trans ((div_le_iff₀ hd).mpr (by nlinarith))

/-- The actual rounded square root and subsequent division perturb normalization by at
most $16uB/\sqrt{\mu}$ when the stored pivot is at least $\mu/2$. -/
theorem abs_sub_div_sqrt_le_of_relErr {u r a d v μ B : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10) (hμ : 0 < μ) (hB : 0 ≤ B)
    (ha : μ / 2 ≤ a) (hr : |r| ≤ 2 * B)
    (hroot : Computation.RelErr u (Real.sqrt a) d)
    (hdiv : Computation.RelErr u (r / d) v) :
    |v - r / Real.sqrt a| ≤ 16 * u * B / Real.sqrt μ := by
  obtain ⟨δ₁, hδ₁, hd⟩ := hroot
  obtain ⟨δ₂, hδ₂, hv⟩ := hdiv
  have ha0 : 0 < a := by linarith
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsa : Real.sqrt μ / 2 ≤ Real.sqrt a := by
    nlinarith [Real.sq_sqrt ha0.le, Real.sq_sqrt hμ.le, Real.sqrt_nonneg a]
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hδpos : 0 < 1 + δ₁ := by have hh := (abs_le.mp hδ₁).1; linarith
  have hθ : |(1 + δ₂) / (1 + δ₁) - 1| ≤ 4 * u := by
    have hh := ((Computation.isRoundingProduct_one_of_abs_le hδ₂).div
      (Computation.isRoundingProduct_one_of_abs_le hδ₁)).abs_le (by linarith : u < 1)
    exact hh.trans (roundingFactor_two_le hu hu1)
  have he : v - r / Real.sqrt a =
      (r / Real.sqrt a) * ((1 + δ₂) / (1 + δ₁) - 1) := by
    rw [hv, hd]
    field_simp [hsq.ne', hδpos.ne']
  have hai : |(Real.sqrt a)⁻¹| ≤ 2 / Real.sqrt μ := by
    rw [abs_of_pos (inv_pos.mpr hsq)]
    calc (Real.sqrt a)⁻¹ ≤ (Real.sqrt μ / 2)⁻¹ := inv_anti₀ (by positivity) hsa
         _ = 2 / Real.sqrt μ := by ring
  rw [he, abs_mul, div_eq_mul_inv, abs_mul]
  calc |r| * |(Real.sqrt a)⁻¹| * |(1 + δ₂) / (1 + δ₁) - 1|
      ≤ (2 * B) * (2 / Real.sqrt μ) * (4 * u) := by gcongr
    _ = 16 * u * B / Real.sqrt μ := by ring

/-- Combining the stored-pivot perturbation and the actual two local arithmetic errors
gives a forward bound relative to the exact normalized reference column. -/
theorem abs_sub_div_sqrt_le_of_pivot_relErr {u r e a d v root μ B η : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10) (hμ : 0 < μ) (hB : 0 ≤ B)
    (ha : μ / 2 ≤ a) (hd : μ ≤ d) (hr : |r| ≤ 2 * B) (he : |e| ≤ B)
    (hre : |r - e| ≤ η) (had : |a - d| ≤ η)
    (hroot : Computation.RelErr u (Real.sqrt a) root)
    (hdiv : Computation.RelErr u (r / root) v) :
    |v - e / Real.sqrt d| ≤
      (2 * (1 + B / μ) * η + 16 * u * B) / Real.sqrt μ := by
  calc |v - e / Real.sqrt d| ≤ |v - r / Real.sqrt a| +
      |r / Real.sqrt a - e / Real.sqrt d| := abs_sub_le _ _ _
    _ ≤ 16 * u * B / Real.sqrt μ + 2 * (1 + B / μ) * η / Real.sqrt μ :=
      add_le_add (abs_sub_div_sqrt_le_of_relErr hu hu1 hμ hB ha hr hroot hdiv)
        (Real.abs_div_sqrt_sub_div_sqrt_le hμ ha hd hre he had)
    _ = (2 * (1 + B / μ) * η + 16 * u * B) / Real.sqrt μ := by ring

/-- The rounded diagonal square root obeys the same uniform column error budget. -/
theorem abs_sub_sqrt_le_of_relErr {u a d v μ B η : ℝ}
    (hu : 0 ≤ u) (hμ : 0 < μ) (hμB : μ ≤ B) (hη : 0 ≤ η)
    (ha : 0 ≤ a) (haB : a ≤ 2 * B) (hd : μ ≤ d) (had : |a - d| ≤ η)
    (hroot : Computation.RelErr u (Real.sqrt a) v) :
    |v - Real.sqrt d| ≤
      (2 * (1 + B / μ) * η + 16 * u * B) / Real.sqrt μ := by
  have hB : 0 ≤ B := hμ.le.trans hμB
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsb : Real.sqrt a ≤ 2 * B / Real.sqrt μ := by
    apply (le_div_iff₀ hs).mpr
    have hm : 0 ≤ Real.sqrt a * Real.sqrt μ := by positivity
    have he : (Real.sqrt a * Real.sqrt μ) ^ 2 = a * μ := by
      rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hμ.le]
    nlinarith [mul_le_mul_of_nonneg_right haB hμ.le]
  obtain ⟨δ, hδ, hv⟩ := hroot
  have hv' : |v - Real.sqrt a| ≤ u * Real.sqrt a := by
    rw [hv, show Real.sqrt a * (1 + δ) - Real.sqrt a = Real.sqrt a * δ by ring,
      abs_mul, abs_of_nonneg (Real.sqrt_nonneg a)]
    exact (mul_le_mul_of_nonneg_left hδ (Real.sqrt_nonneg a)).trans_eq (mul_comm _ _)
  have hκ : 0 ≤ B / μ := div_nonneg hB hμ.le
  calc |v - Real.sqrt d| ≤ |v - Real.sqrt a| + |Real.sqrt a - Real.sqrt d| := abs_sub_le _ _ _
    _ ≤ u * (2 * B / Real.sqrt μ) + η / Real.sqrt μ :=
      add_le_add (hv'.trans (mul_le_mul_of_nonneg_left hsb hu))
        (Real.abs_sqrt_sub_sqrt_le_div ha hμ hd had)
    _ ≤ (2 * (1 + B / μ) * η + 16 * u * B) / Real.sqrt μ := by
      apply (le_div_iff₀ hs).mpr
      field_simp
      nlinarith [mul_nonneg hκ hη, mul_nonneg hu hB]

end NLAlib
