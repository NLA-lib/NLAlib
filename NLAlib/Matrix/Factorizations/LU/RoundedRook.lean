/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Rook
public import NLAlib.Matrix.Factorizations.LU.RoundedRoutine

/-!
# Full rounded rook-pivot LU

The actual bounded alternating row/column selector instantiates the rounded two-log policy
engine. Every matrix within the bounded exact index range is admitted, including singular
and empty inputs. Actual row and column histories identify the independently permuted
original input in the preserved componentwise backward-error bound.

## Main results

* `NLAlib.LU.Rounded.factorRook_meets`: actual rounded rook-pivot factorization.
-/

@[expose] public section

namespace NLAlib.LU.Rounded

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Rook pivoting succeeds on every original matrix under standard relative rounding,
with both actual logs, triangular factors and multiplier bound one plus roundoff. Roundoff
below one gives the original componentwise backward-error budget; no run is assumed. -/
theorem factorRook_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {literalBound : ℕ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hNat : IsExactNatLit dec M literalBound) :
    (LU.factorRook (Op := Op) (Tst := Tst)).Meets I
      (factorPivotedSpec dec u 1 false literalBound) := by
  routine_intro [n] (A, L, U, H, Q) reads (as)
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    call (factorPivoted_meets (quality := 1) (fixedColumns := false)
      hI hcmp hlit hQ hM hu hNat (by norm_num) le_rfl
      (rookChoice_meets_choice hI hcmp hlit hQ hM hNat)) [n] (A, L, U, H, Q)
      (pre := hpre) as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hout
    routine_exit
    exact hout
  · rw [if_neg hn]
    have he : n = 0 := by omega
    subst n
    have heas : as = [] := List.eq_nil_of_length_eq_zero (Store.length_of_readBlock has)
    subst as
    exact ⟨rfl, [[], [], [], []], by simp [Mem.readBlocks, Store.readBlock_zero],
      factorPivotedSpec_zero dec u 1 false literalBound (τ.shift m.pos)⟩

end NLAlib.LU.Rounded
