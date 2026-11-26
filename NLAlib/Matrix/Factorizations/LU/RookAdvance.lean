/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RookPrefix

/-!
# One actual alternating rook-search continuation

The current row scan has stored a strictly improving candidate column. This routine copies
that actual word to the reported column, reads it through a bounded query, rescans its column,
then reads the selected row and scans that row. No visited array or host-selected index is
used. The finite progress proof is a separate consumer of these actual word results.

## Main results

* `NLAlib.LU.rookAdvance_meets`: the actual two alternating scans and stored incumbent pair.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Adopt the actual candidate column, then compute its first maximum row and that row's
first maximum column. All index queries consume previously stored bounded index words. -/
def rookAdvance : Routine Op Tst :=
  routine% [n, k] (R : n * n, candidate : 1) →
      (candidate, best : 1, rowMaximum : 1, p : 2) {
    call (Has.inj ScalarOp.copy) [] (candidate) → (p[1]);
    let col ← index (Has.inj IdxTst.toNat) (p[1]) ≤ n - 1;
    run completeColumn [n, k, col] (R, p, best);
    let row ← index (Has.inj IdxTst.toNat) (p) ≤ n - 1;
    run rookRow [n, k, row] (R, candidate, rowMaximum)
  }

variable [Inhabited K]

/-- Both scans concern the same original source words. The reported column is the original
candidate word, while the reported row, incumbent score and next row-scan candidate have the
actual shared scan postconditions. No strict-growth or execution assumption is needed here. -/
def rookAdvanceSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] tape t (rs, [d]) → ([d'], [b], [a], [r, c]) requires
    k < n ∧ n ≤ bound ∧ (∃ col : Fin n, k ≤ col.val ∧ dec d = col.val) ensures
    c = d ∧ ∃ col row : Fin n, k ≤ col.val ∧ dec d = col.val ∧
      (completeColumnSpec dec bound).post [n, k, col.val] t [rs] [[r], [b]] ∧
      dec r = row.val ∧
      (rookRowSpec dec bound).post [n, k, row.val] t [rs] [[d'], [a]]

/-- The continuation succeeds from actual bounded candidate words and the primitive
contracts. It computes both scans and restores the tape position, without assuming a run. -/
theorem rookAdvance_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (rookAdvance (Op := Op) (Tst := Tst)).Meets I (rookAdvanceSpec dec bound) := by
  routine_intro [n, k] (R, candidate, best, rowMaximum, p) reads (rs, ds)
  obtain ⟨d, hd, rfl⟩ := Store.readBlock_one_eq_some.mp hds
  obtain ⟨hkn, hnb, col, hkc, hdc⟩ := hpre
  step (hI .copy) as m₁ hfr₁ ⟨hpos₁, w, hw, rfl⟩
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hw hdc (by have := col.isLt; omega) ?_
  have hR₁ : m₁.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  call (completeColumn_meets hI hcmp hlit hQ hM hNat) [n, k, col.val] (R, p, best)
    (pre := ⟨hkn, col.isLt, hnb⟩) as m₂ hfr₂ hpos₂ (rows, bs) hcolumn
  obtain ⟨r, hr, rfl⟩ := Store.readBlock_one_eq_some.mp hrows
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨row, hkr, hdr, hbd, hmax, hfirst⟩ := hcolumn
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hr hdr (by have := row.isLt; omega) ?_
  have hR₂ : m₂.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  call (rookRow_meets hI hcmp hlit hQ hM hNat) [n, k, row.val] (R, candidate, rowMaximum)
    (pre := ⟨hkn, row.isLt, hnb⟩) as m₃ hfr₃ hpos₃ (ds', ass) hrow
  obtain ⟨d', hd', rfl⟩ := Store.readBlock_one_eq_some.mp hds'
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hass
  have hc₃ : m₃.store.get p.1 (p.2 + 1) = some d := by keep
  have hr₃ : m₃.store.get p.1 p.2 = some r := by keep
  refine ⟨hpos₃.trans (hpos₂.trans hpos₁), [[d'], [b], [a], [r, d]],
    Mem.readBlocks_of_cons hds' (Mem.readBlocks_of_cons (by keep)
      (Mem.readBlocks_of_cons hass (Mem.readBlocks_of_cons
        (Store.readBlock_succ_of (Store.readBlock_one_of_get hr₃) hc₃) rfl))),
    rfl, col, row, hkc, hdc, ?_, hdr, hrow⟩
  exact ⟨row, hkr, hdr, hbd, hmax, hfirst⟩

end NLAlib.LU
