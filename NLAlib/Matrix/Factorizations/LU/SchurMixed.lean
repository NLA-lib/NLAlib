/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.SchurValues
public import NLAlib.Matrix.Perturbation.CholeskyRangeConditions

/-!
# Range and mixed errors of the saved-pivot scalar update

The literal, reciprocal, scaled row, rank-one product, and final addition are checked in
their actual instruction order. Input scale and positive pivot-margin bounds imply safety
of all these exact targets, and the existing mixed-error budget controls the resulting word.
This local statement is independent of a store or successful execution.

## Main results

* `NLAlib.LU.IsSchurSafe`: the actual primitive targets are in range.
* `NLAlib.LU.schurValues_mixed`: range safety and a local error bound from numerical bounds.
-/

@[expose] public section

namespace NLAlib.LU

open Ops Computation

variable {K : Type}

/-- The exact targets of the actual saved-pivot scalar operations are accepted. These are
local primitive conditions, not a successful-execution or factorization predicate. -/
structure IsSchurSafe (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop)
    (A : ℕ → ℕ → K) (n k : ℕ) : Prop where
  /-- The rounded minus-one literal can be evaluated. -/
  literal : safe (-1)
  /-- The decoded pivot is nonzero. -/
  pivot_ne : dec (A k k) ≠ 0
  /-- The exact quotient defining the reciprocal coefficient is accepted. -/
  coefficient : safe (dec (M.lit (-1)) / dec (A k k))
  /-- Each exact coefficient-times-row product is accepted. -/
  row : ∀ j < n, safe (dec (M.div (M.lit (-1)) (A k k)) * dec (A k j))
  /-- Each exact scaled-row-times-column product is accepted. -/
  product : ∀ i < n, ∀ j < n, safe
    (dec (M.mul (M.div (M.lit (-1)) (A k k)) (A k j)) * dec (A i k))
  /-- Each exact final sum is accepted. -/
  add : ∀ i < n, ∀ j < n, safe
    (dec (A i j) + dec (M.mul (M.mul (M.div (M.lit (-1)) (A k k)) (A k j)) (A i k)))

private theorem coefficient_mixed {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {N : ℕ} {u η B μ Ω : ℝ} (hM : MixedModel u η dec M safe)
    (hc : CholeskyRangeConditions N u η B μ Ω) (hrange : ∀ x, |x| ≤ Ω → safe x)
    (p : K) (hp : μ / 2 ≤ dec p) :
    safe (-1) ∧ safe (dec (M.lit (-1)) / dec p) ∧
      AbsRelErr u η (-1) (dec (M.lit (-1))) ∧
      AbsRelErr u η (dec (M.lit (-1)) / dec p) (dec (M.div (M.lit (-1)) p)) ∧
      |dec (M.div (M.lit (-1)) p)| ≤ (1 + u) * (1 + u + η) / (μ / 2) + η := by
  have hμ : 0 < μ / 2 := by linarith [hc.margin_pos]
  have hp0 := hμ.trans_le hp
  have hs : safe (-1) := hrange _ (by simpa only [abs_neg, abs_one] using hc.literal_le)
  have hsQ : safe ((-1 : ℚ) : ℝ) := by simpa only [Rat.cast_neg, Rat.cast_one] using hs
  have he : AbsRelErr u η (-1) (dec (M.lit (-1))) := by
    simpa only [AbsRelErr, abs_sub_comm, Rat.cast_neg, Rat.cast_one] using hM.lit (-1) hsQ
  have heabs : |dec (M.lit (-1))| ≤ 1 + u + η := by
    simpa only [abs_neg, abs_one, mul_one] using he.abs_le
  have hq : |dec (M.lit (-1)) / dec p| ≤ (1 + u + η) / (μ / 2) := by
    rw [abs_div, abs_of_pos hp0]
    exact div_le_div₀ (by linarith [hc.roundoff_nonneg, hc.underflow_nonneg]) heabs hμ hp
  have hsafe := hrange _ (hq.trans hc.coefficient_le)
  have hce : AbsRelErr u η (dec (M.lit (-1)) / dec p) (dec (M.div (M.lit (-1)) p)) := by
    simpa only [AbsRelErr, abs_sub_comm] using hM.div (M.lit (-1)) p hp0.ne' hsafe
  refine ⟨hs, hsafe, he, hce, ?_⟩
  calc |dec (M.div (M.lit (-1)) p)| ≤ (1 + u) * |dec (M.lit (-1)) / dec p| + η := hce.abs_le
    _ ≤ (1 + u) * ((1 + u + η) / (μ / 2)) + η := by
      gcongr
      · linarith [hc.roundoff_nonneg]
    _ = _ := by ring

private theorem row_mixed {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {N : ℕ} {u η B μ Ω : ℝ} (hM : MixedModel u η dec M safe)
    (hc : CholeskyRangeConditions N u η B μ Ω) (hrange : ∀ x, |x| ≤ Ω → safe x)
    (c y : K) (hcabs : |dec c| ≤ (1 + u) * (1 + u + η) / (μ / 2) + η)
    (hy : |dec y| ≤ 2 * B) :
    safe (dec c * dec y) ∧ AbsRelErr u η (dec c * dec y) (dec (M.mul c y)) ∧
      |dec (M.mul c y)| ≤
        (1 + u) * ((1 + u) * (1 + u + η) / (μ / 2) + η) * (2 * B) + η := by
  have hC : 0 ≤ (1 + u) * (1 + u + η) / (μ / 2) + η :=
    (abs_nonneg _).trans hcabs
  have hcy : |dec c * dec y| ≤ ((1 + u) * (1 + u + η) / (μ / 2) + η) * (2 * B) := by
    rw [abs_mul]
    exact mul_le_mul hcabs hy (abs_nonneg _) hC
  have hs := hrange _ (hcy.trans hc.row_product_le)
  have he : AbsRelErr u η (dec c * dec y) (dec (M.mul c y)) := by
    simpa only [AbsRelErr, abs_sub_comm] using hM.mul c y hs
  refine ⟨hs, he, ?_⟩
  calc |dec (M.mul c y)| ≤ (1 + u) * |dec c * dec y| + η := he.abs_le
    _ ≤ (1 + u) * (((1 + u) * (1 + u + η) / (μ / 2) + η) * (2 * B)) + η := by
      gcongr
      · linarith [hc.roundoff_nonneg]
    _ = _ := by ring

/-- Numerical residual-entry and pivot bounds imply every actual scalar target is in range
and its local mixed Schur defect satisfies the explicit error budget. -/
theorem schurValues_mixed {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {N : ℕ} {u η B μ Ω : ℝ} (hM : MixedModel u η dec M safe)
    (hc : CholeskyRangeConditions N u η B μ Ω) (hrange : ∀ x, |x| ≤ Ω → safe x)
    (A : ℕ → ℕ → K) {k : ℕ} (hk : k < N) (hp : μ / 2 ≤ dec (A k k))
    (hA : ∀ i < N, ∀ j < N, |dec (A i j)| ≤ 2 * B) :
    IsSchurSafe M dec safe A N k ∧
      ∀ i < N, ∀ j < N,
        |dec (schurValues M A k i j) -
          (dec (A i j) - dec (A i k) * dec (A k j) / dec (A k k))| ≤
            schurMixedErrorBound u η (2 * B) (μ / 2) := by
  obtain ⟨hs, hcq, hell, hce, hcabs⟩ := coefficient_mixed hM hc hrange (A k k) hp
  have hrows := fun j hj => row_mixed hM hc hrange
    (M.div (M.lit (-1)) (A k k)) (A k j) hcabs (hA k hk j hj)
  have hμ : 0 < μ / 2 := by linarith [hc.margin_pos]
  have hB : 0 ≤ 2 * B := by linarith [hc.margin_pos, hc.margin_le_scale]
  have entry (i j : ℕ) (hi : i < N) (hj : j < N) :
      safe (dec (M.mul (M.div (M.lit (-1)) (A k k)) (A k j)) * dec (A i k)) ∧
      safe (dec (A i j) + dec (M.mul
        (M.mul (M.div (M.lit (-1)) (A k k)) (A k j)) (A i k))) ∧
      |dec (schurValues M A k i j) -
        (dec (A i j) - dec (A i k) * dec (A k j) / dec (A k k))| ≤
          schurMixedErrorBound u η (2 * B) (μ / 2) := by
    obtain ⟨hr, hre, hrabs⟩ := hrows j hj
    let t := M.mul (M.div (M.lit (-1)) (A k k)) (A k j)
    let T := (1 + u) * ((1 + u) * (1 + u + η) / (μ / 2) + η) * (2 * B) + η
    have hT : 0 ≤ T := (abs_nonneg _).trans hrabs
    have hpabs : |dec t * dec (A i k)| ≤ (2 * B) * T := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul (hA i hi k hk) hrabs (abs_nonneg _) hB
    have hps := hrange _ (hpabs.trans hc.cell_product_le)
    have hpe : AbsRelErr u η (dec t * dec (A i k)) (dec (M.mul t (A i k))) := by
      simpa only [AbsRelErr, abs_sub_comm] using hM.mul t (A i k) hps
    have hpmag : |dec (M.mul t (A i k))| ≤ (1 + u) * (2 * B) * T + η := by
      have h := hpe.abs_le
      calc |dec (M.mul t (A i k))| ≤ (1 + u) * |dec t * dec (A i k)| + η := h
        _ ≤ (1 + u) * ((2 * B) * T) + η := by
          gcongr
          · linarith [hc.roundoff_nonneg]
        _ = _ := by ring
    have hasum : |dec (A i j) + dec (M.mul t (A i k))| ≤ Ω := by
      exact ((abs_add_le _ _).trans (add_le_add (hA i hi j hj) hpmag)).trans hc.sum_le
    have hsum := hrange _ hasum
    have hae : AbsRelErr u η (dec (A i j) + dec (M.mul t (A i k)))
        (dec (M.add (A i j) (M.mul t (A i k)))) := by
      simpa only [AbsRelErr, abs_sub_comm] using hM.add (A i j) (M.mul t (A i k)) hsum
    refine ⟨hps, hsum, ?_⟩
    exact abs_sub_schurUpdate_le_schurMixedErrorBound hc.roundoff_nonneg hc.underflow_nonneg
      hB hμ hp (hA i hi j hj) (hA i hi k hk) (hA k hk j hj) hell hce hre
      (by simpa only [mul_comm] using hpe) hae
  refine ⟨⟨hs, (hμ.trans_le hp).ne', hcq, fun j hj => (hrows j hj).1,
    fun i hi j hj => (entry i j hi hj).1, fun i hi j hj => (entry i j hi hj).2.1⟩,
    fun i hi j hj => (entry i j hi hj).2.2⟩

end NLAlib.LU
