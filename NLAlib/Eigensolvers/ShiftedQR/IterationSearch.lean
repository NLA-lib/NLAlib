/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.IterationAlg
public import NLAlib.Eigensolvers.ShiftedQR.FindRitz

/-!
# The concrete promising search in the strategy composition

The checked scalar binary search meets the local implementation-substitution interface used
by the strategy iteration. The matrix and list premises are actual stored words. Shifted
invertibility is supplied by the mathematical rejection theorem at the call site.

## Main results

* `NLAlib.ShiftedQR.ritzSearchContract_findRitzSearch`: the concrete scalar implementation law.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The actual scalar promising-Ritz search satisfies the composed strategy's local word
interface. No operation of the access model represents the whole binary search. -/
theorem ritzSearchContract_findRitzSearch {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hC : IsCmp id I)
    (hL : IsIndexLit M I) (hQ : IsToNat id I) : RitzSearchContract findRitzSearch I := by
  intro n levels h ss r tape μ H shifts hHess hlen hdet hH hSS _ hcap hsep
  have hShifts : HoldsShifts (k := 2 ^ levels) ss shifts μ.store := by
    change HoldsMatrix ss (listColumn shifts (2 ^ levels)) μ.store
    rw [← hlen, listColumn_length]
    exact hSS
  exact findRitzSearch_writes (τ := tape) (m := μ) hS hE hC hL hQ hHess hH hShifts
    hlen rfl hdet (by simpa only [hlen] using hsep.symm.mono le_sup_right le_rfl) hcap

end NLAlib.ShiftedQR
