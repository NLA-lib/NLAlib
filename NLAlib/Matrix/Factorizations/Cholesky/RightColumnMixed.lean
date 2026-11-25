/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightColumnGuarded
public import NLAlib.Matrix.Perturbation.CholeskyRangeConditions
public import NLAlib.Ops.Blas.Dot

/-!
# Mixed arithmetic of the actual Cholesky column words

A positive residual pivot and an entry scale bound put the square root and every suffix
normalization target in the accepted range. The rounded root stays above the explicit
positive input-margin expression. The conclusions refer to the column routine's actual
machine words and retain the absolute underflow allowance.

## Main results

* `NLAlib.Cholesky.rightColumnSpec_mixed`: positive root and guarded mixed-error quotients.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops Computation

variable {K : Type} [Inhabited K]

/-- The actual rounded column has a positive diagonal and mixed-error normalizations under
the input range inequalities and current residual bounds. These are local numerical bounds;
the whole factorization must derive them from the original matrix's spectral band. -/
theorem rightColumnSpec_mixed {M : Machine K} {dec : K → ℝ} {u η B μ Ω : ℝ}
    {safe : ℝ → Prop} (hM : MixedModel u η dec M safe) {N n : ℕ}
    (hc : CholeskyRangeConditions N u η B μ Ω)
    (hrange : ∀ x, |x| ≤ Ω → safe x) {p : K} {xs ys : List K} {τ : Tape K}
    (hpost : (rightColumnSpec M).post [n] τ [[p], xs] [ys])
    (hp : μ / 2 ≤ dec p) (hpB : dec p ≤ 2 * B)
    (hx : ∀ i < n, |dec (vec xs i)| ≤ 2 * B) :
    0 < dec (vec ys 0) ∧
      (1 - u) * Real.sqrt (μ / 2) - η ≤ dec (vec ys 0) ∧
      AbsRelErr u η (Real.sqrt (dec p)) (dec (vec ys 0)) ∧
      ∀ i < n, AbsRelErr u η (dec (vec xs i) / dec (vec ys 0))
        (dec (vec ys (i + 1))) := by
  have hp0 : 0 < dec p := (by linarith [hc.margin_pos] : 0 < μ / 2).trans_le hp
  have hrootSafe : safe (Real.sqrt (dec p)) := by
    apply hrange
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_sqrt hpB).trans hc.root_le
  have hroot : AbsRelErr u η (Real.sqrt (dec p)) (dec (M.sqrt p)) := by
    simpa only [AbsRelErr, abs_sub_comm, abs_of_nonneg (Real.sqrt_nonneg _)] using
      hM.sqrt p hp0.le hrootSafe
  have hlo : (1 - u) * Real.sqrt (μ / 2) - η ≤ dec (M.sqrt p) := by
    have he := (abs_le.mp hroot.abs_sub_le).2
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at he
    have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp)
      (by linarith [hc.roundoff_lt_one] : 0 ≤ 1 - u)
    linarith
  have hpos : 0 < dec (M.sqrt p) := hc.root_margin_pos.trans_le hlo
  have hy : ys = M.sqrt p :: scalF M (M.sqrt p) (vec xs) n := hpost
  have hhead : vec ys 0 = M.sqrt p := by rw [hy]; rfl
  refine ⟨by simpa only [hhead] using hpos, by simpa only [hhead] using hlo,
    by simpa only [hhead] using hroot, ?_⟩
  intro i hi
  have hquot : |dec (vec xs i) / dec (M.sqrt p)| ≤ Ω := by
    rw [abs_div, abs_of_pos hpos]
    calc |dec (vec xs i)| / dec (M.sqrt p)
        ≤ (2 * B) / ((1 - u) * Real.sqrt (μ / 2) - η) := by
          exact div_le_div₀ (by linarith [hc.margin_pos, hc.margin_le_scale])
            (hx i hi) hc.root_margin_pos hlo
      _ ≤ Ω := hc.quotient_le
  have hv : vec ys (i + 1) = M.div (vec xs i) (M.sqrt p) := by
    rw [hy]
    change vec (scalF M (M.sqrt p) (vec xs) n) i = _
    simp only [scalF, vec_map_range _ hi]
  rw [hv, hhead]
  simpa only [AbsRelErr, abs_sub_comm] using
    hM.div (vec xs i) (M.sqrt p) hpos.ne' (hrange _ hquot)

/-- The numerical input inequalities accept every exact primitive target of the column.
This proves its rejecting-arithmetic precondition before any column execution. -/
theorem rightColumnGuardedSpec_pre {M : Machine K} {dec : K → ℝ} {u η B μ Ω : ℝ}
    {safe : ℝ → Prop} (hM : MixedModel u η dec M safe) {N n : ℕ}
    (hc : CholeskyRangeConditions N u η B μ Ω)
    (hrange : ∀ x, |x| ≤ Ω → safe x) {p : K} {xs : List K} {τ : Tape K}
    (hp : μ / 2 ≤ dec p) (hpB : dec p ≤ 2 * B)
    (hx : ∀ i < n, |dec (vec xs i)| ≤ 2 * B) :
    (rightColumnGuardedSpec M dec safe).pre [n] τ [[p], xs] := by
  let ys := M.sqrt p :: scalF M (M.sqrt p) (vec xs) n
  have hp0 : 0 < dec p := (by linarith [hc.margin_pos] : 0 < μ / 2).trans_le hp
  obtain ⟨hpos, hlo, -, -⟩ := rightColumnSpec_mixed hM hc hrange
    (ys := ys) (τ := τ) rfl hp hpB hx
  have hhead : vec ys 0 = M.sqrt p := rfl
  rw [hhead] at hpos hlo
  refine ⟨hp0.le, ?_, hpos.ne', fun i hi => ?_⟩
  · apply hrange
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_sqrt hpB).trans hc.root_le
  · apply hrange
    rw [abs_div, abs_of_pos hpos]
    exact (div_le_div₀ (by linarith [hc.margin_pos, hc.margin_le_scale])
      (hx i hi) hc.root_margin_pos hlo).trans hc.quotient_le

end NLAlib.Cholesky
