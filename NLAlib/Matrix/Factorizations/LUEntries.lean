/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU

/-!
# Canonical LU entries in materialization order

Stored factor materialization tests the structural zero region first, then the lower unit
diagonal. These entry identities connect that control order with the existing canonical
factor functions. Both scalar and blocked LU verification use the same forms.

## Main results

* `NLAlib.luLower_apply_eq_ite`: structural zero, unit diagonal, or total pivot quotient.
* `NLAlib.luUpper_apply_eq_ite`: structural zero or the current Gaussian pivot row.
-/

@[expose] public section

namespace NLAlib

variable {K : Type*} [Field K] {N : ℕ}

/-- The canonical lower entry in the order used by stored column materialization. Total
division permits zero pivots; no triangular or nonsingularity premise is required. -/
theorem luLower_apply_eq_ite (A : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    luLower A i j = if i < j then 0 else if i = j then 1 else
      gaussState A j.val i j / gaussState A j.val j j := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [luLower, Matrix.of_apply, h, h.not_gt, h.ne, if_true, if_false]
  · simp only [luLower, Matrix.of_apply, lt_self_iff_false, if_false, if_true]
  · simp only [luLower, Matrix.of_apply, h, h.not_gt, h.ne', if_true, if_false]

/-- The canonical upper entry with its structural zero test first, as in stored pivot-row
materialization. The pivot row is copied exactly and may contain zeros. -/
theorem luUpper_apply_eq_ite (A : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    luUpper A i j = if j < i then 0 else gaussState A i.val i j := by
  by_cases h : j < i
  · simp only [luUpper, Matrix.of_apply, h, h.not_ge, if_true, if_false]
  · simp only [luUpper, Matrix.of_apply, h, not_lt.mp h, if_true, if_false]

end NLAlib
