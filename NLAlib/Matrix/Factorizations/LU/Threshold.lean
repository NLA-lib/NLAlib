/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RowPivoted
public import NLAlib.Matrix.Factorizations.LU.ThresholdChoice

/-!
# Scalar threshold-pivot LU

The concrete driver uses the rational fixed-column threshold selector. Equality accepts the
diagonal, and rejection chooses the first active column maximum. The shared row-policy
wrapper reports actual row history and uses one scoped column-history word.

## Main results

* `NLAlib.LU.factorThreshold_meets`: all-input threshold PLU with reciprocal threshold bound.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Factor with the actual scalar threshold selector, retaining the diagonal at equality and
otherwise using the first column maximum. The threshold is a counted rational literal. -/
def factorThreshold (threshold : ℚ) : Routine Op Tst :=
  factorRowPivoted (thresholdChoice (Op := Op) (Tst := Tst) threshold).body

variable [Inhabited K]

/-- Canonical factors of the input row-permuted by the actual reported history, with lower
multipliers bounded by the reciprocal threshold. Source and shape preservation belong to
the routine's framed judgment. -/
def factorThresholdSpec (dec : K → ℝ) (threshold : ℚ) : Routine.Spec K :=
  factorRowPivotedSpec dec (threshold : ℝ)

/-- A rational threshold in `(0, 1]` gives a total factorization on every matrix, including
singular and empty matrices. The concrete selector judgment is proved from actual scalar
instructions and exact rational literal decoding, rather than assumed by this theorem. -/
theorem factorThreshold_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (threshold : ℚ) (hτ : 0 < threshold) (hτ₁ : threshold ≤ 1)
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (factorThreshold (Op := Op) (Tst := Tst) threshold).Meets I
      (factorThresholdSpec dec threshold) := by
  have hτR : 0 < (threshold : ℝ) := by exact_mod_cast hτ
  have hτR₁ : (threshold : ℝ) ≤ 1 := by exact_mod_cast hτ₁
  exact factorRowPivoted_meets hI hcmp hlit hQ hM hτR hτR₁
    (fun _ => thresholdChoice_meets_choice threshold hτ hτ₁ hI hcmp hlit hQ hM)

end NLAlib.LU
