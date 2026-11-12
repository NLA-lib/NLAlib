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
theorem curvature_margin {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {a a' e ed em : ℝ}
    (hA : Aᵀ = A) (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (he : 0 ≤ e) (hprec : 3 * e * a' ≤ a) (hd : 0 ≤ ed) (hde : ed ≤ e)
    (hem : em ≤ e) {p : Fin n → ℝ} (hp : p ≠ 0) (q : Fin n → ℝ)
    (hq : ‖WithLp.toLp 2 (A *ᵥ p - q)‖ ≤ em * specNorm A * ‖WithLp.toLp 2 p‖) :
    ed * ∑ i, |p i * q i| < p ⬝ᵥ q := by
  have hsum := sum_abs_mul_le p q
  have hqeq : A *ᵥ p + (q - A *ᵥ p) = q := by abel
  have hmv : ‖WithLp.toLp 2 (q - A *ᵥ p)‖ ≤ e * specNorm A * ‖WithLp.toLp 2 p‖ := by
    rw [show q - A *ᵥ p = -(A *ᵥ p - q) by abel, WithLp.toLp_neg, norm_neg]
    exact hq.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hem (specNorm_nonneg _)) (norm_nonneg _))
  have herr : |-ed * (∑ i, |p i * q i|)| ≤
      e * ‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 (A *ᵥ p + (q - A *ᵥ p))‖ := by
    rw [hqeq, abs_mul, abs_neg, abs_of_nonneg hd,
      abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
    calc
      _ ≤ ed * (‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 q‖) :=
        mul_le_mul_of_nonneg_left hsum hd
      _ ≤ e * (‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 q‖) :=
        mul_le_mul_of_nonneg_right hde (by positivity)
      _ = _ := (mul_assoc ..).symm
  have hpos := dotProduct_add_pos_of_spectrum_subset_Icc hA ha hs he hprec hp hmv herr
  rw [hqeq] at hpos
  linarith

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
