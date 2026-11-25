/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Complete
public import NLAlib.Matrix.Factorizations.LU.RoundedRoutine

/-!
# Full rounded complete-pivot LU

The actual stable active-square maximum selector instantiates the rounded two-log policy
engine. Every matrix within the bounded exact index range is admitted, including singular
and empty inputs. Actual row and column histories identify the independently permuted
original input in the preserved componentwise backward-error bound.

## Main results

* `NLAlib.LU.Rounded.factorComplete_meets`: actual rounded complete-pivot factorization.
-/

@[expose] public section

namespace NLAlib.LU.Rounded

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Complete pivoting succeeds on every original matrix under standard relative rounding,
with both actual logs, triangular factors and multiplier bound one plus roundoff. Roundoff
below one gives the original componentwise backward-error budget; no run is assumed. -/
theorem factorComplete_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {literalBound : ℕ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hNat : IsExactNatLit dec M literalBound) :
    (LU.factorComplete (Op := Op) (Tst := Tst)).Meets I
      (factorPivotedSpec dec u 1 false literalBound) := by
  routine_intro [n] (A, L, U, H, Q) reads (as)
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    call (factorPivoted_meets (quality := 1) (fixedColumns := false)
      hI hcmp hlit hQ hM hu hNat (by norm_num) le_rfl
      (completeChoice_meets_choice hI hcmp hlit hQ hM hNat)) [n] (A, L, U, H, Q)
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
