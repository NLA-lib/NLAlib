/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.CholeskyColumnError
public import NLAlib.Ops.ArithmeticError

/-!
# Forward Cholesky column errors with gradual underflow

A numerical lower bound for the actual rounded root controls division amplification of the
absolute rounding allowance. The reference column uses exact elimination.

## Main results

* `NLAlib.choleskyMixedColumnErrorBound_nonneg`: the uniform column budget is nonnegative.
-/

@[expose] public section

namespace NLAlib

open Computation

/-- The uniform factor-entry budget with relative allowance $u$, additive allowance $\tau$,
input scale $B$, positive lower margin $\mu$ and residual error $\eta$. Its value is
this explicit expression: <!-- value choleskyMixedColumnErrorBound u \tau B \mu \eta -->
$$m=\mu/2,\quad
H=2B,\quad
d=(1-u)\sqrt{m}-\tau,\quad
2(1+B/\mu)\eta/\sqrt{\mu}+(u\sqrt{H}+\tau)(1+H/(d\sqrt{m}))+u H/d+\tau$$
The denominator $d$ is the numerical lower bound for the actual rounded diagonal root. -/
noncomputable def choleskyMixedColumnErrorBound (u τ B μ η : ℝ) : ℝ :=
  let m := μ / 2
  let H := 2 * B
  let d := (1 - u) * Real.sqrt m - τ
  2 * (1 + B / μ) * η / Real.sqrt μ +
    (u * Real.sqrt H + τ) * (1 + H / (d * Real.sqrt m)) + u * H / d + τ

/-- Nonnegative allowances and residual scale give a nonnegative uniform factor-entry budget
when the lower margin and rounded-root margin are positive. -/
theorem choleskyMixedColumnErrorBound_nonneg {u τ B μ η : ℝ} (hu : 0 ≤ u) (hτ : 0 ≤ τ)
    (hB : 0 ≤ B) (hμ : 0 < μ) (hη : 0 ≤ η)
    (hd : 0 < (1 - u) * Real.sqrt (μ / 2) - τ) :
    0 ≤ choleskyMixedColumnErrorBound u τ B μ η := by
  dsimp only [choleskyMixedColumnErrorBound]
  positivity

private theorem abs_sub_div_sqrt_le_of_root_lower {u τ r a d m H D : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hm : 0 < m) (hD : 0 < D)
    (ha : m ≤ a) (haH : a ≤ H) (hr : |r| ≤ H) (hd : D ≤ d)
    {v : ℝ} (hroot : AbsRelErr u τ (Real.sqrt a) d) (hdiv : AbsRelErr u τ (r / d) v) :
    |v - r / Real.sqrt a| ≤
      (u * Real.sqrt H + τ) * H / (D * Real.sqrt m) + u * H / D + τ := by
  have ha0 : 0 ≤ a := hm.le.trans ha
  have hH : 0 ≤ H := ha0.trans haH
  have hd0 : 0 < d := hD.trans_le hd
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr (hm.trans_le ha)
  have hrange : |r / d| ≤ H / D := by
    rw [abs_div, abs_of_pos hd0]
    exact div_le_div₀ hH hr hD hd
  have hroot' : |Real.sqrt a - d| ≤ u * Real.sqrt H + τ := by
    have hh := hroot.abs_sub_le
    rw [abs_of_nonneg (Real.sqrt_nonneg a)] at hh
    exact hh.trans (by gcongr)
  have hden : 0 < D * Real.sqrt m := mul_pos hD (Real.sqrt_pos.mpr hm)
  have hid : |r / d - r / Real.sqrt a| =
      |r| * |Real.sqrt a - d| / (d * Real.sqrt a) := by
    rw [show r / d - r / Real.sqrt a = r * (Real.sqrt a - d) / (d * Real.sqrt a) by
      field_simp, abs_div, abs_mul, abs_of_pos (mul_pos hd0 hs)]
  have hdiff : |r / d - r / Real.sqrt a| ≤ H * (u * Real.sqrt H + τ) / (D * Real.sqrt m) := by
    rw [hid]
    apply div_le_div₀ (by positivity)
      (mul_le_mul hr hroot' (abs_nonneg _) hH) hden
    exact mul_le_mul hd (Real.sqrt_le_sqrt ha) (Real.sqrt_nonneg m) hd0.le
  have hv : |v - r / d| ≤ u * (H / D) + τ := by
    have he := hdiv.abs_sub_le
    rw [abs_sub_comm] at he
    exact he.trans (by gcongr)
  calc |v - r / Real.sqrt a| ≤ |v - r / d| + |r / d - r / Real.sqrt a| := abs_sub_le _ _ _
    _ ≤ (u * (H / D) + τ) + H * (u * Real.sqrt H + τ) / (D * Real.sqrt m) :=
      add_le_add hv hdiff
    _ = (u * Real.sqrt H + τ) * H / (D * Real.sqrt m) + u * H / D + τ := by ring

/-- Mixed root and division errors, together with a perturbed stored pivot, give a uniform
forward error relative to the exact normalized reference column. -/
theorem abs_sub_div_sqrt_le_choleskyMixedColumnErrorBound {u τ r e a d root v μ B η : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hμ : 0 < μ) (hμB : μ ≤ B)
    (ha : μ / 2 ≤ a) (haB : a ≤ 2 * B) (hd : μ ≤ d) (hr : |r| ≤ 2 * B) (he : |e| ≤ B)
    (hre : |r - e| ≤ η) (had : |a - d| ≤ η)
    (hD : 0 < (1 - u) * Real.sqrt (μ / 2) - τ)
    (hrootlower : (1 - u) * Real.sqrt (μ / 2) - τ ≤ root)
    (hroot : AbsRelErr u τ (Real.sqrt a) root) (hdiv : AbsRelErr u τ (r / root) v) :
    |v - e / Real.sqrt d| ≤ choleskyMixedColumnErrorBound u τ B μ η := by
  have hB : 0 ≤ B := hμ.le.trans hμB
  have hround := abs_sub_div_sqrt_le_of_root_lower hu hτ (by positivity : 0 < μ / 2)
    hD ha haB hr hrootlower hroot hdiv
  have hideal := Real.abs_div_sqrt_sub_div_sqrt_le hμ ha hd hre he had
  have hnoise : 0 ≤ u * Real.sqrt (2 * B) + τ := by positivity
  calc |v - e / Real.sqrt d| ≤ |v - r / Real.sqrt a| +
      |r / Real.sqrt a - e / Real.sqrt d| := abs_sub_le _ _ _
    _ ≤ ((u * Real.sqrt (2 * B) + τ) * (2 * B) /
        (((1 - u) * Real.sqrt (μ / 2) - τ) * Real.sqrt (μ / 2)) +
        u * (2 * B) / ((1 - u) * Real.sqrt (μ / 2) - τ) + τ) +
        2 * (1 + B / μ) * η / Real.sqrt μ := add_le_add hround hideal
    _ ≤ choleskyMixedColumnErrorBound u τ B μ η := by
      let R := (u * Real.sqrt (2 * B) + τ) * (2 * B) /
        (((1 - u) * Real.sqrt (μ / 2) - τ) * Real.sqrt (μ / 2)) +
        u * (2 * B) / ((1 - u) * Real.sqrt (μ / 2) - τ) + τ
      let I := 2 * (1 + B / μ) * η / Real.sqrt μ
      have hb : choleskyMixedColumnErrorBound u τ B μ η =
          R + I + (u * Real.sqrt (2 * B) + τ) := by
        dsimp only [choleskyMixedColumnErrorBound, R, I]
        ring
      change R + I ≤ choleskyMixedColumnErrorBound u τ B μ η
      rw [hb]
      exact le_add_of_nonneg_right hnoise

/-- The rounded diagonal obeys the same uniform mixed-error factor-entry budget. -/
theorem abs_sub_sqrt_le_choleskyMixedColumnErrorBound {u τ a d root μ B η : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hμ : 0 < μ) (hμB : μ ≤ B) (hη : 0 ≤ η)
    (ha : 0 ≤ a) (haB : a ≤ 2 * B) (hd : μ ≤ d) (had : |a - d| ≤ η)
    (hD : 0 < (1 - u) * Real.sqrt (μ / 2) - τ)
    (hroot : AbsRelErr u τ (Real.sqrt a) root) :
    |root - Real.sqrt d| ≤ choleskyMixedColumnErrorBound u τ B μ η := by
  have hB : 0 ≤ B := hμ.le.trans hμB
  have hroot' : |root - Real.sqrt a| ≤ u * Real.sqrt (2 * B) + τ := by
    have hh := hroot.abs_sub_le
    rw [abs_sub_comm, abs_of_nonneg (Real.sqrt_nonneg a)] at hh
    exact hh.trans (by gcongr)
  have hs : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hratio : 0 ≤ B / μ := div_nonneg hB hμ.le
  have hideal : η / Real.sqrt μ ≤ 2 * (1 + B / μ) * η / Real.sqrt μ := by
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith [mul_nonneg hratio hη]
  have hextra : 0 ≤ (u * Real.sqrt (2 * B) + τ) *
      (2 * B / (((1 - u) * Real.sqrt (μ / 2) - τ) * Real.sqrt (μ / 2))) := by positivity
  have hdiv : 0 ≤ u * (2 * B) / ((1 - u) * Real.sqrt (μ / 2) - τ) := by positivity
  calc |root - Real.sqrt d| ≤ |root - Real.sqrt a| + |Real.sqrt a - Real.sqrt d| := abs_sub_le _ _ _
    _ ≤ (u * Real.sqrt (2 * B) + τ) + η / Real.sqrt μ :=
      add_le_add hroot' (Real.abs_sqrt_sub_sqrt_le_div ha hμ hd had)
    _ ≤ (u * Real.sqrt (2 * B) + τ) + 2 * (1 + B / μ) * η / Real.sqrt μ :=
      add_le_add le_rfl hideal
    _ ≤ choleskyMixedColumnErrorBound u τ B μ η := by
      have hb : choleskyMixedColumnErrorBound u τ B μ η =
          (u * Real.sqrt (2 * B) + τ) + 2 * (1 + B / μ) * η / Real.sqrt μ +
          (u * Real.sqrt (2 * B) + τ) *
            (2 * B / (((1 - u) * Real.sqrt (μ / 2) - τ) * Real.sqrt (μ / 2))) +
          u * (2 * B) / ((1 - u) * Real.sqrt (μ / 2) - τ) + τ := by
        dsimp only [choleskyMixedColumnErrorBound]
        ring
      rw [hb]
      linarith

end NLAlib
