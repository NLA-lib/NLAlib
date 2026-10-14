/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bounds on `s log s`

`|s log s| ≤ s² + 1` for `s ≥ 0`: the domination that makes `g² log g²` integrable once `g⁴` is,
used for entropies of squares. `|G s log (G s)| ≤ |G log G| + G` for `G ≥ 0` and `s ∈ [0, 1]`:
the domination of `x log x` along a shrinking of `x`, used to pass to the limit in an entropy
under a truncation or a cutoff. Upstream candidates for
`Mathlib.Analysis.SpecialFunctions.Log.Basic`.

## Main results

* `Real.abs_mul_log_le_sq_add_one`.
* `Real.abs_mul_mul_log_mul_le`.
-/

@[expose] public section

namespace Real

/-- `|s log s| ≤ s² + 1` for `s ≥ 0`. -/
theorem abs_mul_log_le_sq_add_one {s : ℝ} (hs : 0 ≤ s) : |s * log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with rfl | hs'
  · simp
  rcases le_or_gt s 1 with h1 | h1
  · have := abs_log_mul_self_lt s hs' h1
    rw [mul_comm]
    nlinarith [sq_nonneg s]
  · have hl : 0 ≤ log s := log_nonneg h1.le
    have hl2 : log s ≤ s - 1 := log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

/-- `|(G s) log (G s)| ≤ |G log G| + G` for `G ≥ 0` and `s ∈ [0, 1]`: shrinking `x ≥ 0` by a
factor in `[0, 1]` changes `|x log x|` by at most `x`. -/
theorem abs_mul_mul_log_mul_le {G s : ℝ} (hG : 0 ≤ G) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |G * s * log (G * s)| ≤ |G * log G| + G := by
  rcases hG.eq_or_lt with rfl | hG'
  · simp
  rcases hs0.eq_or_lt with rfl | hs'
  · simp only [mul_zero, zero_mul, abs_zero]; positivity
  rw [log_mul hG'.ne' hs'.ne']
  have e : G * s * (log G + log s) = s * (G * log G) + G * (log s * s) := by
    ring
  rw [e]
  have h1 := abs_log_mul_self_lt s hs' hs1
  calc |s * (G * log G) + G * (log s * s)|
      ≤ |s * (G * log G)| + |G * (log s * s)| := abs_add_le _ _
    _ = s * |G * log G| + G * |log s * s| := by
        rw [abs_mul s (G * log G), abs_mul G (log s * s), abs_of_nonneg hs0, abs_of_nonneg hG]
    _ ≤ 1 * |G * log G| + G * 1 := by gcongr
    _ = |G * log G| + G := by ring

end Real
