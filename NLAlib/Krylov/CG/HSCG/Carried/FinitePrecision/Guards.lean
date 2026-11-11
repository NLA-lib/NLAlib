/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Bounds
public import NLAlib.Krylov.FinitePrecision.CGRunSpectrum

/-!
# Input-based curvature guards for rounded CG

A spectral interval and a scalar precision inequality imply the componentwise curvature
margin of the new rounded operation contract for every nonzero direction. Thus the margin
can be derived from mathematical inputs rather than assumed along a successful trajectory.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.curvature_margin` supplies the computed-dot margin.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open scoped Matrix

/-- A symmetric positive spectral interval and the input precision inequality imply the curvature
margin whenever the direction is nonzero. [StrakosTichy2002, (7.14)]. -/
theorem curvature_margin {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {a a' e ed : ℝ}
    (hA : Aᵀ = A) (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (he : 0 ≤ e) (hprec : 3 * e * a' ≤ a) (hd : 0 ≤ ed) (hde : ed ≤ e)
    {p : Fin n → ℝ} (hp : p ≠ 0) :
    ed * ∑ i, |p i * (A *ᵥ p) i| < p ⬝ᵥ (A *ᵥ p) := by
  have hsum := sum_abs_mul_le p (A *ᵥ p)
  have herr : |-ed * (∑ i, |p i * (A *ᵥ p) i|)| ≤
      e * ‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 (A *ᵥ p + 0)‖ := by
    rw [abs_mul, abs_neg, abs_of_nonneg hd,
      abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _), add_zero]
    calc
      _ ≤ ed * (‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 (A *ᵥ p)‖) :=
        mul_le_mul_of_nonneg_left hsum hd
      _ ≤ e * (‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 (A *ᵥ p)‖) :=
        mul_le_mul_of_nonneg_right hde (by positivity)
      _ = _ := (mul_assoc ..).symm
  have hpos := dotProduct_add_pos_of_spectrum_subset_Icc hA ha hs he hprec hp
    (e := 0) (e' := -ed * ∑ i, |p i * (A *ᵥ p) i|) (by
      simp only [WithLp.toLp_zero, norm_zero]
      exact mul_nonneg (mul_nonneg he (specNorm_nonneg _)) (norm_nonneg _)) herr
  simp only [add_zero] at hpos
  linarith

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
