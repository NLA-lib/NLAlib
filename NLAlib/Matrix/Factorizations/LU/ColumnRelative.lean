/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Column
public import NLAlib.Ops.ArithmeticError

/-!
# Relative rounding of materialized LU columns

The actual lower-column update retains literal structural zeros and a unit diagonal, and
uses rounded quotients below the pivot. Its zero branch performs no division. The word
formula and the relative error facts are independent of any completed factorization or run.

## Main results

* `NLAlib.LU.dec_columnLowerValues_eq`: decoded materialization as a column update.
* `NLAlib.LU.relativeLowerColumn_error`: quotient errors, including a zero pivot.
-/

@[expose] public section

namespace NLAlib.LU

open Ops Computation

variable {K : Type}

/-- Decoded lower-column values, retaining the actual guarded quotient below the diagonal. -/
noncomputable def relativeLowerColumn (M : Machine K) (dec : K → ℝ)
    (R : ℕ → ℕ → K) (k i : ℕ) : ℝ :=
  if i < k then 0 else if i = k then 1 else
    if dec (R k k) = 0 then 0 else dec (M.div (R i k) (R k k))

/-- The actual word column decodes to the relative column formula, with the other columns
retained. The required structural zeros belong to the uncommitted current column. -/
theorem dec_columnLowerValues_eq {M : Machine K} {dec : K → ℝ}
    (hzero : dec (M.lit 0) = 0) (hone : dec (M.lit 1) = 1)
    (zeroPivot : Bool) (R L : ℕ → ℕ → K) (k i j : ℕ)
    (hz : zeroPivot = true ↔ dec (R k k) = 0) (hL : ∀ i < k, dec (L i k) = 0) :
    dec (columnLowerValues M zeroPivot R L k i j) =
      if j = k then relativeLowerColumn M dec R k i else dec (L i j) := by
  classical
  by_cases hj : j = k
  · subst j
    by_cases hi : i < k
    · have hcond : ¬(k = k ∧ k ≤ i) := by omega
      rw [columnLowerValues, if_neg hcond, if_pos rfl, relativeLowerColumn, if_pos hi, hL i hi]
    · have hki : k ≤ i := by omega
      by_cases he : i = k
      · subst i
        simp only [columnLowerValues, relativeLowerColumn, le_refl, and_self, if_true,
          lt_irrefl, if_false, hone]
      · by_cases hp : dec (R k k) = 0
        · have hb : zeroPivot = true := hz.mpr hp
          simp only [columnLowerValues, relativeLowerColumn, hki, and_true, if_true,
            if_neg hi, if_neg he, hb, if_pos hp, hzero]
        · have hb : zeroPivot = false := Bool.eq_false_iff.mpr (fun h => hp (hz.mp h))
          simp only [columnLowerValues, relativeLowerColumn, hki, and_true, if_true,
            if_neg hi, if_neg he, hb, Bool.false_eq_true, if_false, if_neg hp]
  · have hcond : ¬(j = k ∧ k ≤ i) := fun h => hj h.1
    simp only [columnLowerValues, if_neg hcond, if_neg hj]

/-- The pivot-row materialization is an actual row update when the uncommitted row has its
initialized zeros to the left. No numerical accuracy law is needed. -/
theorem dec_columnUpperValues_eq {dec : K → ℝ} (R U : ℕ → ℕ → K) (k i j : ℕ)
    (hU : ∀ j < k, dec (U k j) = 0) :
    dec (columnUpperValues R U k i j) =
      if i = k then (if j < k then 0 else dec (R k j)) else dec (U i j) := by
  by_cases hi : i = k
  · subst i
    by_cases hj : j < k
    · have hcond : ¬(k = k ∧ k ≤ j) := by omega
      rw [columnUpperValues, if_neg hcond, if_pos rfl, if_pos hj, hU j hj]
    · simp only [columnUpperValues, show k ≤ j from by omega, and_self, if_true, if_neg hj]
  · have hcond : ¬(i = k ∧ k ≤ j) := fun h => hi h.1
    simp only [columnUpperValues, if_neg hcond, if_neg hi]

/-- The guarded lower column is zero above the diagonal, one on it, and satisfies the
standard relative quotient relation below it, including a zero decoded pivot. -/
theorem relativeLowerColumn_error {M : Machine K} {dec : K → ℝ} {u : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (R : ℕ → ℕ → K) (k : ℕ) :
    (∀ i < k, relativeLowerColumn M dec R k i = 0) ∧
      relativeLowerColumn M dec R k k = 1 ∧
      ∀ i, k < i → RelErr u (dec (R i k) / dec (R k k)) (relativeLowerColumn M dec R k i) := by
  refine ⟨fun i hi => by simp only [relativeLowerColumn, if_pos hi], ?_, ?_⟩
  · simp only [relativeLowerColumn, lt_irrefl, if_false, if_true]
  · intro i hi
    rw [relativeLowerColumn, if_neg (by omega : ¬i < k), if_neg (by omega : i ≠ k)]
    by_cases hp : dec (R k k) = 0
    · rw [if_pos hp, hp, div_zero]
      exact ⟨0, by simpa only [abs_zero] using hu, by ring⟩
    · rw [if_neg hp]
      apply AbsRelErr.relErr (u := u) _ hu
      simpa only [AbsRelErr, add_zero, abs_sub_comm] using hM.div (R i k) (R k k) hp

/-- A positive pivot-quality fraction bounds every actual lower-column multiplier under
standard relative rounding. The literal unit diagonal also satisfies this budget. -/
theorem abs_relativeLowerColumn_le {M : Machine K} {dec : K → ℝ} {u quality : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hquality : 0 < quality) (hquality₁ : quality ≤ 1)
    (R : ℕ → ℕ → K) (k i : ℕ)
    (hchoice : k ≤ i → quality * |dec (R i k)| ≤ |dec (R k k)|) :
    |relativeLowerColumn M dec R k i| ≤ (1 + u) / quality := by
  have hbudget : 0 ≤ (1 + u) / quality := div_nonneg (by linarith) hquality.le
  by_cases hi : i < k
  · simpa only [relativeLowerColumn, if_pos hi, abs_zero] using hbudget
  by_cases hik : i = k
  · rw [relativeLowerColumn, if_neg hi, if_pos hik, abs_one]
    exact (le_div_iff₀ hquality).mpr (by nlinarith)
  by_cases hp : dec (R k k) = 0
  · simpa only [relativeLowerColumn, if_neg hi, if_neg hik, if_pos hp, abs_zero] using hbudget
  have hden : 0 < |dec (R k k)| := abs_pos.mpr hp
  have hratio : |dec (R i k) / dec (R k k)| ≤ 1 / quality := by
    rw [abs_div]
    apply (div_le_div_iff₀ hden hquality).mpr
    simpa only [one_mul, mul_comm quality] using hchoice (by omega)
  have he := (relativeLowerColumn_error hM hu R k).2.2 i (by omega)
  calc |relativeLowerColumn M dec R k i|
      ≤ (1 + u) * |dec (R i k) / dec (R k k)| := by
        simpa only [add_zero] using (he.absRelErr (le_refl 0)).abs_le
    _ ≤ (1 + u) * (1 / quality) := mul_le_mul_of_nonneg_left hratio (by linarith)
    _ = (1 + u) / quality := by ring

end NLAlib.LU
