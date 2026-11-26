/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RookSearch

/-!
# Actual rook pivot selection

Three scoped score/candidate words support alternating actual column and row scans. Only a
strict magnitude improvement continues, and finite active-column progress proves the cap is
enough. The reported current-position pair is maximal in its active row and column. Ties in
the row comparison retain the incumbent column, preventing tied-column cycles.

## Main results

* `NLAlib.LU.rookChoice_meets`: actual total rook selection from bounded dimensions alone.
* `NLAlib.LU.rookChoiceSpec_choiceSpec`: unit column quality for the shared pivoted driver.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Actual rook search with three scoped state words and an active-column fuel bound. Every
selected index is read from a stored scan result; no visited-column array is allocated. -/
def rookChoice : Routine Op Tst := routine% [n, k] (R : n * n) → (p : 2) {
  let best ← alloc 1;
  let rowMaximum ← alloc 1;
  let candidate ← alloc 1;
  run rookInitialize [n, k] (R, p, best, rowMaximum, candidate);
  run rookSearch [n, k] (R, best, rowMaximum, candidate, p)
}

variable [Inhabited K]

/-- Actual initialization and finite strict-growth search return the stored rook pair.
Only bounded dimensions and local primitive laws are required, including all-zero squares. -/
theorem rookChoice_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (rookChoice (Op := Op) (Tst := Tst)).Meets I (rookChoiceSpec dec bound) := by
  routine_intro [n, k] (R, p) reads (rs)
  obtain ⟨hkn, hnb⟩ := hpre
  change Writes .total I τ _ (Env.frame [n, k] [R, p]) (Fp.blocks [p] [2]) _ m
  alloc as best rowMaximum candidate
  have hRb : R.1 ≠ best := by change R.1 ≠ m.store.length + 0; omega
  have hRa : R.1 ≠ rowMaximum := by change R.1 ≠ m.store.length + 1; omega
  have hRd : R.1 ≠ candidate := by change R.1 ≠ m.store.length + 2; omega
  have hpb : p.1 ≠ best := by change p.1 ≠ m.store.length + 0; omega
  have hpa : p.1 ≠ rowMaximum := by change p.1 ≠ m.store.length + 1; omega
  have hpd : p.1 ≠ candidate := by change p.1 ≠ m.store.length + 2; omega
  have hba : best ≠ rowMaximum := by change m.store.length + 0 ≠ m.store.length + 1; omega
  have hbd : best ≠ candidate := by change m.store.length + 0 ≠ m.store.length + 2; omega
  have had : rowMaximum ≠ candidate := by
    change m.store.length + 1 ≠ m.store.length + 2; omega
  call (rookInitialize_meets hI hcmp hlit hQ hM hNat) [n, k]
    (R, p, (best, 0), (rowMaximum, 0), (candidate, 0)) (pre := ⟨hkn, hnb⟩)
    as m₁ hfr₁ hpos₁ (ps, bs, ass, ds) hinit
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change R.1 < s_best.length ∧ p.1 < s_best.length ∧ m.store.length < s_best.length ∧
      m.store.length + 1 < s_best.length ∧ m.store.length + 2 < s_best.length
    simp only [List.length_cons, List.length_nil] at hlen_best
    omega
  case' hroom =>
    change (p.2 + 2 ≤ s_best.len p.1 ∧ 0 + 1 ≤ s_best.len best ∧
      0 + 1 ≤ s_best.len rowMaximum ∧ 0 + 1 ≤ s_best.len candidate ∧ True)
    rw [(hbelow_best p.1 hl.2).1, hbest, hrowMaximum, hcandidate]
    exact ⟨hroom, by omega, by omega, by omega, trivial⟩
  obtain ⟨r, c, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hps)
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hass
  obtain ⟨d, hd, rfl⟩ := Store.readBlock_one_eq_some.mp hds
  have hrs₁ : m₁.store.readBlock R.1 R.2 (n * n) = some rs := by keep
  call (rookSearch_meets hI hcmp hlit hQ hM hNat) [n, k]
    (R, (best, 0), (rowMaximum, 0), (candidate, 0), p) (pre := ⟨hkn, hnb, hinit⟩)
    as m₂ hfr₂ hpos₂ (ps') hpost
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨Store.lt_length_of_get (Store.get_of_readBlock hrs₁
      (j := 0) (by nlinarith : 0 < n * n) default), Store.lt_length_of_get hb,
      Store.lt_length_of_get ha, Store.lt_length_of_get hd,
      Store.lt_length_of_get (Store.get_of_readBlock hps (by omega : 0 < 2) default)⟩
  case' hroom =>
    change (0 + 1 ≤ m₁.store.len best ∧ 0 + 1 ≤ m₁.store.len rowMaximum ∧
      0 + 1 ≤ m₁.store.len candidate ∧ p.2 + 2 ≤ m₁.store.len p.1 ∧ True)
    exact ⟨by simpa using Nat.succ_le_of_lt (Store.lt_len_of_get hb),
      by simpa using Nat.succ_le_of_lt (Store.lt_len_of_get ha),
      by simpa using Nat.succ_le_of_lt (Store.lt_len_of_get hd),
      by rw [hfr₁.len_eq, (hbelow_best p.1 hl.2).1]; exact hroom, trivial⟩
  intro s₂ hs₂ hbelow
  exact ⟨hpos₂.trans hpos₁, [ps'], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hl.2 hps') rfl, hpost⟩

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] [Has IdxTst Tst] in
/-- Rook column maximality supplies unit quality to the common all-input pivoted driver.
The policy retains its stronger row maximum and first maximum row guarantee separately. -/
theorem rookChoiceSpec_choiceSpec {dec : K → ℝ} {bound n k : ℕ} {rs : List K}
    {r c : K} {τ : Tape K}
    (h : (rookChoiceSpec dec bound).post [n, k] τ [rs] [[r, c]]) :
    (choiceSpec dec 1 bound false).post [n, k] τ [rs] [[r, c]] := by
  obtain ⟨row, col, hkr, hkc, hdr, hdc, hcol, hrow, hfirst⟩ := h
  exact ⟨row, col, hkr, hkc, hdr, hdc, by simp,
    fun i hi => by simpa only [one_mul] using hcol i hi⟩

end NLAlib.LU
