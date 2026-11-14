/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FindRitzRegisters
public import NLAlib.Ops.Blas.HermitianEntry

/-!
# Copying the selected stored Ritz candidate

The actual bounded natural-index query reads the selected candidate index from its search
word. Two scalar copy calls return that candidate's stored real and imaginary components.
The index-range premise concerns the actual search value, with no execution premise.

## Main results

* `NLAlib.ShiftedQR.findRitzCopy_writes`: total final copy of the selected actual shift pair.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IdxTst Tst]

/-- The actual bounded index query followed by two scalar copies returns the selected stored
candidate. Its whole source shift block is spatially disjoint from the output pair. -/
theorem findRitzCopy_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hQ : IsToNat id I) {τ : Tape ℝ} {m : Mem ℝ}
    {k a : ℕ} {ss r center : ℕ × ℕ} {shifts : List ℂ}
    (hSS : HoldsShifts (k := k) ss shifts m.store)
    (hA : m.store.get r.1 r.2 = some (a : ℝ)) (ha : a < k)
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k))
      (Store.inBlock center.1 center.2 2))
    (hCenter : center.2 + 2 ≤ m.store.len center.1) :
    Writes .total I τ findRitzCopy.body (Env.frame [k] [ss, r, center])
      (Store.inBlock center.1 center.2 2)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock center.1 center.2 2 =
        some [(shifts.getD a 0).re, (shifts.getD a 0).im]) m := by
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hA rfl (by omega) ?_
  have hre : m.store.get ss.1 (ss.2 + 2 * a) = some (shifts.getD a 0).re :=
    HoldsVector.get_re hSS ⟨a, ha⟩
  have him : m.store.get ss.1 (ss.2 + 2 * a + 1) = some (shifts.getD a 0).im :=
    HoldsVector.get_im hSS ⟨a, ha⟩
  have hlocal : Fp.Disj (Store.inBlock ss.1 (ss.2 + 2 * a) 2)
      (Store.inBlock center.1 center.2 2) :=
    hsep.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl
  have hsLive := Store.lt_length_of_get hre
  have hcLive := Store.lt_length_of_lt_len
    (show center.2 < m.store.len center.1 by omega)
  have hcopy := Writes.of_wp_eq_updBlock
    (Hermitian.wp_copyPair_of_disj (md := .total) (τ := τ)
      (x := (ss.1, ss.2 + 2 * a)) (z := center) hS hlocal hre him hCenter rfl)
  refine (hcopy.in_frame rfl rfl (by simp [Mem.Live]; omega)).mono le_rfl ?_
  rintro μ _ rfl
  exact ⟨rfl, Store.readBlock_updBlock_self (by simpa using hCenter)⟩

end NLAlib.ShiftedQR
