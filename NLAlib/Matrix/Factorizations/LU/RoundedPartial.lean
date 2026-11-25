/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Partial
public import NLAlib.Matrix.Factorizations.LU.RoundedRow

/-!
# Full rounded partial-pivot LU

The actual stable maximum-column selector instantiates the rounded row-policy theorem.
Every original matrix is admitted in the bounded exact index range, including singular and
empty inputs. The reported actual row log determines the permuted matrix in the preserved
componentwise backward-error bound; lower multipliers are bounded by one plus roundoff.

## Main results

* `NLAlib.LU.Rounded.factorPartial_meets`: the actual partial-pivot factorization under rounding.
-/

@[expose] public section

namespace NLAlib.LU.Rounded

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Full rounded partial-pivot LU from original matrix words and primitive scalar/index
laws, with actual history, triangular shapes, multiplier bounds and conditional numerical
backward error. No nonsingularity, computed-pivot or execution hypothesis is used. -/
theorem factorPartial_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {literalBound : ℕ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hNat : IsExactNatLit dec M literalBound) :
    (LU.factorPartial (Op := Op) (Tst := Tst)).Meets I
      (factorRowPivotedSpec dec u 1 literalBound) := by
  exact factorRowPivoted_meets hI hcmp hlit hQ hM hu hNat (by norm_num) (by norm_num)
    (partialChoice_meets_choice hI hcmp hlit hQ hM hNat)

end NLAlib.LU.Rounded
