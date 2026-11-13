/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.AbsoluteValue
public import NLAlib.Matrix.Functions.OrderedExponential
public import NLAlib.Matrix.Norms.SchattenInterpolation
public import NLAlib.Matrix.Perturbation.Continuity

/-!
# Schatten interpolation for ordered exponential products

On the right boundary of the interpolation strip, the product and its inverse bound both
sides of the logarithm of the Schatten norm. This permits the exact strip interpolation
estimate for products of Hermitian exponentials [SutterBertaTomamichel2017, Theorem 3.2].

## Main results

* `NLAlib.schattenNorm_rpow_abs_orderedMatrixExp_le_exp_integral`: the finite-parameter
  Schatten bound with the normalized strip density.
-/

@[expose] public section

open Complex Set MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem schattenNorm_orderedMatrixExp_le (H : List (Matrix n n ℂ))
    (hH : ∀ A ∈ H, A.IsHermitian) {p : ℝ} (hp : 0 < p) (t : ℝ) :
    schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I)) ≤
      (Fintype.card n : ℝ) ^ (1 / p) * Real.exp ((H.map (fun A => specNorm A)).sum) := by
  apply (schattenNorm_le_card_rpow_mul_specNorm (ENNReal.ofReal_pos.mpr hp).ne' _).trans
  rw [ENNReal.toReal_ofReal hp.le, ← one_div]
  exact mul_le_mul_of_nonneg_left (specNorm_orderedMatrixExp_le_exp_sum H hH (by simp))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem exp_neg_sum_le_schattenNorm_orderedMatrixExp [Nonempty n]
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian) {p : ℝ} (hp : 0 < p) (t : ℝ) :
    Real.exp (-(H.map (fun A => specNorm A)).sum) ≤
      schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I)) :=
  (exp_neg_sum_specNorm_le_specNorm_orderedMatrixExp H hH t).trans
    (specNorm_le_schattenNorm (ENNReal.ofReal_pos.mpr hp).ne' _)

/-- The right-boundary logarithm is uniformly bounded for every positive Schatten index.
The inverse product controls its negative part. -/
theorem abs_log_schattenNorm_orderedMatrixExp_le [Nonempty n]
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian) {p : ℝ} (hp : 0 < p) (t : ℝ) :
    |Real.log (schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I)))| ≤
      (H.map (fun A => specNorm A)).sum + |Real.log ((Fintype.card n : ℝ) ^ (1 / p))| := by
  have hl := exp_neg_sum_le_schattenNorm_orderedMatrixExp H hH hp t
  have hu := schattenNorm_orderedMatrixExp_le H hH hp t
  have hdim : 0 < (Fintype.card n : ℝ) ^ (1 / p) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Fintype.card_pos) _
  have hlogl := Real.log_le_log (Real.exp_pos _) hl
  have hlogu := Real.log_le_log ((Real.exp_pos _).trans_le hl) hu
  rw [Real.log_exp] at hlogl
  rw [Real.log_mul hdim.ne' (Real.exp_ne_zero _), Real.log_exp] at hlogu
  exact abs_le.mpr ⟨by linarith [abs_nonneg (Real.log ((Fintype.card n : ℝ) ^ (1 / p)))],
    by linarith [le_abs_self (Real.log ((Fintype.card n : ℝ) ^ (1 / p)))]⟩

/-- The right-boundary logarithm of the Schatten quantity is continuous. -/
theorem continuous_log_schattenNorm_orderedMatrixExp [Nonempty n]
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian) {p : ℝ} (hp : 0 < p) :
    Continuous fun t : ℝ =>
      Real.log (schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I))) := by
  have hc : Continuous (orderedMatrixExp H) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_orderedMatrixExp H z).continuousAt
  apply ((continuous_schattenNorm_ofReal hp).comp (hc.comp (by fun_prop))).log
  intro t
  exact ((Real.exp_pos _).trans_le (exp_neg_sum_le_schattenNorm_orderedMatrixExp H hH hp t)).ne'

/-- For a list of Hermitian matrices the Schatten norm of the powered absolute value of the
ordered exponential product is bounded by its geometric mean on the other boundary of the
strip [SutterBertaTomamichel2017, Theorem 3.2]. -/
theorem schattenNorm_rpow_abs_orderedMatrixExp_le_exp_integral
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian) {p r : ℝ}
    (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    schattenNorm (ENNReal.ofReal p) ((CFC.abs (orderedMatrixExp H (r : ℂ))) ^ (1 / r)) ≤
      Real.exp (∫ t : ℝ, Real.log (schattenNorm (ENNReal.ofReal p)
        (orderedMatrixExp H (1 + (t : ℂ) * I))) ∂Real.stripHarmonicMeasure r) := by
  have hp0 := zero_lt_one.trans_le hp
  rw [schattenNorm_rpow_abs _ hp0 (one_div_pos.mpr hr.1), one_div_mul_eq_div]
  by_cases hn : Nonempty n
  · let := hn
    have hc : Continuous (orderedMatrixExp H) :=
      continuous_iff_continuousAt.mpr fun z => (analyticAt_orderedMatrixExp H z).continuousAt
    have hdiff : DiffContOnCl ℂ (orderedMatrixExp H)
        (Complex.HadamardThreeLines.verticalStrip 0 1) :=
      ⟨fun z _ => (analyticAt_orderedMatrixExp H z).differentiableAt.differentiableWithinAt,
        hc.continuousOn⟩
    have hb (z : ℂ) (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :=
      specNorm_orderedMatrixExp_le_exp_sum H hH (z := z) (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩)
    have h := schattenNorm_le_exp_integral_stripHarmonicMeasure_of_specNorm_le_one hr hp hdiff hb
      _ (continuous_log_schattenNorm_orderedMatrixExp H hH hp0).measurable
      (abs_log_schattenNorm_orderedMatrixExp_le H hH hp0)
      (specNorm_orderedMatrixExp_imaginary_le_one H hH)
      (fun t => (Real.exp_log ((Real.exp_pos _).trans_le
        (exp_neg_sum_le_schattenNorm_orderedMatrixExp H hH hp0 t))).symm.le)
    apply (Real.rpow_le_rpow (schattenNorm_nonneg _ _) h (one_div_nonneg.mpr hr.1.le)).trans_eq
    rw [← Real.exp_mul]
    congr 1
    rw [mul_comm r _, mul_assoc, one_div, mul_inv_cancel₀ hr.1.ne', mul_one]
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz : orderedMatrixExp H (r : ℂ) = 0 := Subsingleton.elim _ _
    rw [hz, schattenNorm_zero, Real.zero_rpow (one_div_pos.mpr hr.1).ne']
    exact (Real.exp_pos _).le

end NLAlib
