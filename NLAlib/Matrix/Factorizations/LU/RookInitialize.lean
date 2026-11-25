/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RookAdvanceCorrect

/-!
# Actual rook-search initialization

The active pivot column supplies the first maximum row. Its actual stored row word is read
through a bounded query before scanning that row. The incumbent column is recorded by an
index literal. All five state words are initialized before the finite alternating search.

## Main results

* `NLAlib.LU.rookInitialize_meets`: initialization from actual source words and dimensions.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Initialize the incumbent pair and scores using one column scan and one row scan. The row
scan consumes the actual selected row word, and the pivot-column word is an index literal. -/
def rookInitialize : Routine Op Tst :=
  routine% [n, k] (R : n * n) → (p : 2, best : 1, rowMaximum : 1, candidate : 1) {
    run completeColumn [n, k, k] (R, p, best);
    call (Has.inj IndexOp.lit) [k] () → (p[1]);
    let row ← index (Has.inj IdxTst.toNat) (p) ≤ n - 1;
    run rookRow [n, k, row] (R, candidate, rowMaximum)
  }

variable [Inhabited K]

/-- The incumbent column decodes to the pivot position. Its row and score satisfy the actual
column scan, and the next candidate and score satisfy the actual selected-row scan. -/
def rookInitializeSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] tape t (rs) → ([r, c], [b], [a], [d]) requires k < n ∧ n ≤ bound ensures
    dec c = k ∧ ∃ row : Fin n,
      (completeColumnSpec dec bound).post [n, k, k] t [rs] [[r], [b]] ∧
      dec r = row.val ∧ (rookRowSpec dec bound).post [n, k, row.val] t [rs] [[d], [a]]

/-- Actual scans, index literal and bounded stored-row read initialize every state word under
the local primitive laws. Only dimensions bound the literal and query values. -/
theorem rookInitialize_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (rookInitialize (Op := Op) (Tst := Tst)).Meets I (rookInitializeSpec dec bound) := by
  routine_intro [n, k] (R, p, best, rowMaximum, candidate) reads (rs)
  obtain ⟨hkn, hnb⟩ := hpre
  call (completeColumn_meets hI hcmp hlit hQ hM hNat) [n, k, k] (R, p, best)
    (pre := ⟨hkn, hkn, hnb⟩) as m₁ hfr₁ hpos₁ (rows, bs) hcolumn
  obtain ⟨r, hr, rfl⟩ := Store.readBlock_one_eq_some.mp hrows
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨row, hkr, hdr, hbd, hmax, hfirst⟩ := hcolumn
  step hlit as m₂ hfr₂ ⟨hpos₂, c, hc, hword⟩
  have he : M.lit (k : ℕ) = c := by simpa [Machine.indexFn] using hword
  subst c
  simp only [Machine.indexFn, Nat.add_zero] at hpos₂
  have hr₂ : m₂.store.get p.1 p.2 = some r := by keep
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hr₂ hdr (by have := row.isLt; omega) ?_
  have hrs₂ : m₂.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  call (rookRow_meets hI hcmp hlit hQ hM hNat) [n, k, row.val] (R, candidate, rowMaximum)
    (pre := ⟨hkn, row.isLt, hnb⟩) as m₃ hfr₃ hpos₃ (ds, ass) hrow
  obtain ⟨d, hd, rfl⟩ := Store.readBlock_one_eq_some.mp hds
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hass
  refine ⟨hpos₃.trans (hpos₂.trans hpos₁), [[r, M.lit (k : ℕ)], [b], [a], [d]],
    Mem.readBlocks_of_cons
      (Store.readBlock_succ_of (Store.readBlock_one_of_get (by keep)) (by keep))
      (Mem.readBlocks_of_cons (by keep) (Mem.readBlocks_of_cons hass
        (Mem.readBlocks_of_cons hds rfl))), hNat k (by omega), row,
      ⟨row, hkr, hdr, hbd, hmax, hfirst⟩, hdr, hrow⟩

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] [Has IdxTst Tst] in
/-- The actual initialization word postcondition establishes the finite-progress search
invariant with its singleton initial visited-column witness. -/
theorem IsRookPrefix.of_initialize_post {N bound : ℕ} (dec : K → ℝ) (xs : List K) (k : Fin N)
    {best rowMaximum candidate pair : ℕ × ℕ} {s : Store K} {τ : Tape K} {b a r c d : K}
    (hpost : (rookInitializeSpec dec bound).post [N, k.val] τ [xs] [[r, c], [b], [a], [d]])
    (hb : s.get best.1 best.2 = some b) (ha : s.get rowMaximum.1 rowMaximum.2 = some a)
    (hd : s.get candidate.1 candidate.2 = some d) (hr : s.get pair.1 pair.2 = some r)
    (hc : s.get pair.1 (pair.2 + 1) = some c) :
    IsRookPrefix dec xs k 0 best rowMaximum candidate pair s := by
  obtain ⟨hcd, row, hcolumn, hrd, hrow⟩ := hpost
  exact IsRookPrefix.initial_of_scans dec xs k row hcolumn hrd hrow hb ha hd hr hc hcd

end NLAlib.LU
