/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A quadratic bound on `s log s`

`|s log s| ≤ s² + 1` for `s ≥ 0`: the domination that makes `g² log g²` integrable once `g⁴` is,
used for entropies of squares. Upstream candidate for
`Mathlib.Analysis.SpecialFunctions.Log.Basic`.

## Main results

* `Real.abs_mul_log_le_sq_add_one`.
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

end Real
