/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.ArithmeticError

/-!
# Mixed-error bounds for saved-pivot Schur updates

The literal minus one, reciprocal coefficient, row scaling, rank-one product and final add
are bounded in their actual instruction order. Additive underflow errors remain explicit.

## Main results

* `NLAlib.schurMixedErrorBound_nonneg`: the explicit local error budget is nonnegative.
-/

@[expose] public section

namespace NLAlib

open Computation

/-- The absolute local mixed-error Schur budget at matrix-entry scale $H$ and positive
pivot margin $m$. Its value follows the actual instruction order, including the literal:
this chain specifies it: <!-- value schurMixedErrorBound u \tau H m -->
$$\ell=1+u+\tau,\quad
C=(1+u)\ell/m+\tau,\quad
T=(1+u)C\cdot H+\tau,\quad
Q=(1+u)H\cdot T+\tau,\quad
E_c=(u+\tau)/m+u\ell/m+\tau,\quad
E_t=H\cdot E_c+u C\cdot H+\tau,\quad
E_q=H\cdot E_t+uH\cdot T+\tau,\quad
D=E_q+u(H+Q)+\tau$$
Here $C,T,Q$ bound the decoded coefficient, scaled row and rank-one product, while
$E_c,E_t,E_q$ bound their defects from the exact update. -/
noncomputable def schurMixedErrorBound (u τ H m : ℝ) : ℝ :=
  let ell := 1 + u + τ
  let c := (1 + u) * ell / m + τ
  let t := (1 + u) * c * H + τ
  let q := (1 + u) * H * t + τ
  let ec := (u + τ) / m + u * ell / m + τ
  let et := H * ec + u * c * H + τ
  let eq := H * et + u * H * t + τ
  eq + u * (H + q) + τ

/-- Nonnegative arithmetic allowances and entry scale with a positive pivot margin give a
nonnegative local mixed-error budget. -/
theorem schurMixedErrorBound_nonneg {u τ H m : ℝ} (hu : 0 ≤ u) (hτ : 0 ≤ τ)
    (hH : 0 ≤ H) (hm : 0 < m) : 0 ≤ schurMixedErrorBound u τ H m := by
  dsimp only [schurMixedErrorBound]
  positivity

private theorem abs_div_sub_neg_inv_le {u τ ell c p m : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hm : 0 < m) (hp : m ≤ p)
    (hell : AbsRelErr u τ (-1) ell) (hc : AbsRelErr u τ (ell / p) c) :
    |c - (-1) / p| ≤ (u + τ) / m + u * (1 + u + τ) / m + τ := by
  have hp0 : 0 < p := hm.trans_le hp
  have hellmag : |ell| ≤ 1 + u + τ := by simpa using hell.abs_le
  have hellerr : |ell - (-1)| ≤ u + τ := by simpa [abs_sub_comm] using hell.abs_sub_le
  have hcmag : |ell / p| ≤ (1 + u + τ) / m := by
    rw [abs_div, abs_of_pos hp0]
    exact div_le_div₀ (by positivity) hellmag hm hp
  have hlit : |ell / p - (-1) / p| ≤ (u + τ) / m := by
    rw [← sub_div, abs_div, abs_of_pos hp0]
    exact div_le_div₀ (add_nonneg hu hτ) hellerr hm hp
  calc |c - (-1) / p| ≤ |c - ell / p| + |ell / p - (-1) / p| := abs_sub_le _ _ _
    _ ≤ (u * |ell / p| + τ) + (u + τ) / m :=
      add_le_add (by simpa only [abs_sub_comm] using hc.abs_sub_le) hlit
    _ ≤ (u * ((1 + u + τ) / m) + τ) + (u + τ) / m := by gcongr
    _ = (u + τ) / m + u * (1 + u + τ) / m + τ := by ring

private theorem abs_sub_mul_le_of_absRelErr {u τ c c₀ y z C H E : ℝ}
    (hu : 0 ≤ u) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hc : |c| ≤ C) (hy : |y| ≤ H) (he : |c - c₀| ≤ E)
    (hz : AbsRelErr u τ (c * y) z) : |z - c₀ * y| ≤ H * E + u * C * H + τ := by
  have hprod : |c * y - c₀ * y| ≤ E * H := by
    rw [← sub_mul, abs_mul]
    exact mul_le_mul he hy (abs_nonneg _) hE
  have hmag : |c * y| ≤ C * H := by
    rw [abs_mul]
    exact mul_le_mul hc hy (abs_nonneg _) hC
  calc |z - c₀ * y| ≤ |z - c * y| + |c * y - c₀ * y| := abs_sub_le _ _ _
    _ ≤ (u * |c * y| + τ) + E * H :=
      add_le_add (by simpa only [abs_sub_comm] using hz.abs_sub_le) hprod
    _ ≤ (u * (C * H) + τ) + E * H := by gcongr
    _ = H * E + u * C * H + τ := by ring

private theorem abs_schur_scalars_le {u τ ell c t q p y x H m : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hH : 0 ≤ H) (hm : 0 < m) (hp : m ≤ p)
    (hx : |x| ≤ H) (hy : |y| ≤ H)
    (hell : AbsRelErr u τ (-1) ell) (hc : AbsRelErr u τ (ell / p) c)
    (ht : AbsRelErr u τ (c * y) t) (hq : AbsRelErr u τ (x * t) q) :
    let C := (1 + u) * (1 + u + τ) / m + τ
    let T := (1 + u) * C * H + τ
    let Q := (1 + u) * H * T + τ
    |c| ≤ C ∧ |t| ≤ T ∧ |q| ≤ Q := by
  dsimp only
  have hp0 : 0 < p := hm.trans_le hp
  have he : |ell| ≤ 1 + u + τ := by simpa using hell.abs_le
  have hc' : |c| ≤ (1 + u) * (1 + u + τ) / m + τ := by
    have hh := hc.abs_le
    rw [abs_div, abs_of_pos hp0] at hh
    calc |c| ≤ (1 + u) * (|ell| / p) + τ := hh
         _ ≤ (1 + u) * ((1 + u + τ) / m) + τ := by
           gcongr
         _ = (1 + u) * (1 + u + τ) / m + τ := by ring
  have ht' : |t| ≤ (1 + u) * ((1 + u) * (1 + u + τ) / m + τ) * H + τ := by
    have hh := ht.abs_le
    rw [abs_mul] at hh
    calc |t| ≤ (1 + u) * (|c| * |y|) + τ := hh
         _ ≤ (1 + u) * (((1 + u) * (1 + u + τ) / m + τ) * H) + τ := by gcongr
         _ = (1 + u) * ((1 + u) * (1 + u + τ) / m + τ) * H + τ := by ring
  refine ⟨hc', ht', ?_⟩
  have hh := hq.abs_le
  rw [abs_mul] at hh
  calc |q| ≤ (1 + u) * (|x| * |t|) + τ := hh
       _ ≤ (1 + u) * (H * ((1 + u) * ((1 + u) * (1 + u + τ) / m + τ) * H + τ)) + τ := by
         gcongr
       _ = _ := by ring

/-- The actual five-stage saved-pivot update has absolute local error bounded by its explicit
mixed-error budget. The lower pivot margin and matrix-entry scale are numerical assumptions;
all five scalar accuracy hypotheses follow the actual instruction order. -/
theorem abs_sub_schurUpdate_le_schurMixedErrorBound {u τ a x y p ell c t q z H m : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hH : 0 ≤ H) (hm : 0 < m) (hp : m ≤ p)
    (ha : |a| ≤ H) (hx : |x| ≤ H) (hy : |y| ≤ H)
    (hell : AbsRelErr u τ (-1) ell) (hc : AbsRelErr u τ (ell / p) c)
    (ht : AbsRelErr u τ (c * y) t) (hq : AbsRelErr u τ (x * t) q)
    (hz : AbsRelErr u τ (a + q) z) :
    |z - (a - x * y / p)| ≤ schurMixedErrorBound u τ H m := by
  let C := (1 + u) * (1 + u + τ) / m + τ
  let T := (1 + u) * C * H + τ
  let Q := (1 + u) * H * T + τ
  let Ec := (u + τ) / m + u * (1 + u + τ) / m + τ
  let Et := H * Ec + u * C * H + τ
  let Eq := H * Et + u * H * T + τ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hEc : 0 ≤ Ec := by dsimp [Ec]; positivity
  have hEt : 0 ≤ Et := by dsimp [Et]; positivity
  obtain ⟨hcmag, htmag, hqmag⟩ := abs_schur_scalars_le hu hτ hH hm hp hx hy hell hc ht hq
  have hec : |c - (-1) / p| ≤ Ec := abs_div_sub_neg_inv_le hu hτ hm hp hell hc
  have het : |t - ((-1) / p) * y| ≤ Et :=
    abs_sub_mul_le_of_absRelErr hu hC hEc hcmag hy hec ht
  have heq : |q - (((-1) / p) * y) * x| ≤ Eq := by
    have hh := abs_sub_mul_le_of_absRelErr hu hT hEt htmag hx het
      (by simpa only [mul_comm] using hq)
    dsimp only [Eq]
    convert hh using 1
    ring
  have hid : a - x * y / p = a + (((-1) / p) * y) * x := by ring
  rw [hid]
  calc |z - (a + (((-1) / p) * y) * x)|
      ≤ |z - (a + q)| + |(a + q) - (a + (((-1) / p) * y) * x)| := abs_sub_le _ _ _
    _ = |z - (a + q)| + |q - (((-1) / p) * y) * x| := by congr 2; ring
    _ ≤ (u * |a + q| + τ) + Eq :=
      add_le_add (by simpa only [abs_sub_comm] using hz.abs_sub_le) heq
    _ ≤ (u * (H + Q) + τ) + Eq := by
      gcongr
      exact (abs_add_le _ _).trans (add_le_add ha hqmag)
    _ = schurMixedErrorBound u τ H m := by dsimp [schurMixedErrorBound, C, T, Q, Ec, Et, Eq]; ring

end NLAlib
