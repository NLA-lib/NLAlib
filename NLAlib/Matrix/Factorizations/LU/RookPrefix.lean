/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.CompleteColumn
public import NLAlib.Matrix.Factorizations.LU.RookRow
public import NLAlib.Matrix.Factorizations.RookPivotingProgress

/-!
# Stored rook-search state and its finite progress witness

The incumbent pair, column score, row score and next candidate column all have actual stored
words. The mathematical visited set records strict improvements and is never allocated by the
algorithm. Its finite cardinality proves that the capped search cannot stop while an improving
column remains. Equal row scores retain the incumbent column.

## Main results

* `NLAlib.LU.IsRookPrefix.dec_le_of_cap`: exhausted fuel rules out further improvement.
* `NLAlib.LU.IsRookPrefix.return_of_stop`: actual pair readback and both rook maxima.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} [Inhabited K]

/-- Both actual selected indices are active, and their original stored entry is maximal in
its active row and column. The selected row is the first maximum in its column. Tied row
maxima retain the current column, so no global lexicographic rook tie rule is asserted. -/
def rookChoiceSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n, k] (rs) → ([r, c]) requires k < n ∧ n ≤ bound ensures
    ∃ row col : Fin n, k ≤ row.val ∧ k ≤ col.val ∧ dec r = row.val ∧ dec c = col.val ∧
      (∀ i : Fin n, k ≤ i.val →
        |dec (vec rs (col.val * n + i.val))| ≤ |dec (vec rs (col.val * n + row.val))|) ∧
      (∀ j : Fin n, k ≤ j.val →
        |dec (vec rs (j.val * n + row.val))| ≤ |dec (vec rs (col.val * n + row.val))|) ∧
      (∀ i : Fin n, k ≤ i.val → i < row →
        |dec (vec rs (col.val * n + i.val))| < |dec (vec rs (col.val * n + row.val))|)

/-- The five actual search words represent a column maximum and a row-scan candidate. The
visited-column witness tracks only numerical strict growth; it occupies no runtime storage. -/
def IsRookPrefix {N : ℕ} (dec : K → ℝ) (xs : List K) (k : Fin N) (rounds : ℕ)
    (best rowMaximum candidate pair : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ row col next : Fin N, ∃ b a r c d : K, ∃ visited : Finset (Fin N),
    s.get best.1 best.2 = some b ∧ s.get rowMaximum.1 rowMaximum.2 = some a ∧
    s.get candidate.1 candidate.2 = some d ∧ s.get pair.1 pair.2 = some r ∧
    s.get pair.1 (pair.2 + 1) = some c ∧
    dec r = row.val ∧ dec c = col.val ∧ dec d = next.val ∧
    dec b = |dec (vec xs (col.val * N + row.val))| ∧
    dec a = |dec (vec xs (next.val * N + row.val))| ∧
    k ≤ row ∧ k ≤ col ∧ k ≤ next ∧
    (∀ i : Fin N, k ≤ i →
      |dec (vec xs (col.val * N + i.val))| ≤ |dec (vec xs (col.val * N + row.val))|) ∧
    (∀ i : Fin N, k ≤ i → i < row →
      |dec (vec xs (col.val * N + i.val))| < |dec (vec xs (col.val * N + row.val))|) ∧
    (∀ j : Fin N, k ≤ j →
      |dec (vec xs (j.val * N + row.val))| ≤ |dec (vec xs (next.val * N + row.val))|) ∧
    (∀ j : Fin N, k ≤ j → j < next →
      |dec (vec xs (j.val * N + row.val))| < |dec (vec xs (next.val * N + row.val))|) ∧
    HasRookVisitedColumns (decodeMatrix dec N N xs) k rounds col visited

namespace IsRookPrefix

/-- Read the two actual score words of a represented rook search. -/
theorem exists_score_words {N rounds : ℕ} {dec : K → ℝ} {xs : List K} {k : Fin N}
    {best rowMaximum candidate pair : ℕ × ℕ} {s : Store K}
    (h : IsRookPrefix dec xs k rounds best rowMaximum candidate pair s) :
    ∃ b a : K, s.get best.1 best.2 = some b ∧ s.get rowMaximum.1 rowMaximum.2 = some a := by
  obtain ⟨row, col, next, b, a, r, c, d, visited, hb, ha, rest⟩ := h
  exact ⟨b, a, hb, ha⟩

/-- Read the actual bounded next-column word of a represented rook search. -/
theorem exists_candidate_word {N rounds : ℕ} {dec : K → ℝ} {xs : List K} {k : Fin N}
    {best rowMaximum candidate pair : ℕ × ℕ} {s : Store K}
    (h : IsRookPrefix dec xs k rounds best rowMaximum candidate pair s) :
    ∃ d : K, ∃ next : Fin N,
      s.get candidate.1 candidate.2 = some d ∧ dec d = next.val ∧ k ≤ next := by
  obtain ⟨row, col, next, b, a, r, c, d, visited, hb, ha, hd, hr, hc,
    hrd, hcd, hdd, hbd, had, hkr, hkc, hkd, rest⟩ := h
  exact ⟨d, next, hd, hdd, hkd⟩

/-- The first actual column scan and its row scan initialize the stored search state. The
only initially visited column is the pivot column itself. -/
theorem initial_of_scans {N bound : ℕ} (dec : K → ℝ) (xs : List K) (k row : Fin N)
    {best rowMaximum candidate pair : ℕ × ℕ} {s : Store K} {τ : Tape K}
    {b a r c d : K}
    (hcolumn : (completeColumnSpec dec bound).post [N, k.val, k.val] τ [xs] [[r], [b]])
    (hrd : dec r = row.val)
    (hrow : (rookRowSpec dec bound).post [N, k.val, row.val] τ [xs] [[d], [a]])
    (hb : s.get best.1 best.2 = some b) (ha : s.get rowMaximum.1 rowMaximum.2 = some a)
    (hd : s.get candidate.1 candidate.2 = some d) (hr : s.get pair.1 pair.2 = some r)
    (hc : s.get pair.1 (pair.2 + 1) = some c) (hcd : dec c = k.val) :
    IsRookPrefix dec xs k 0 best rowMaximum candidate pair s := by
  obtain ⟨row', hkr, hdr, hbd, hmax, hfirst⟩ := hcolumn
  have he : row' = row := Fin.ext (Nat.cast_injective (hdr.symm.trans hrd))
  subst row'
  obtain ⟨next, hkn, hdd, had, hrowMax, hrowFirst⟩ := hrow
  exact ⟨row, k, next, b, a, r, c, d, {k}, hb, ha, hd, hr, hc,
    hrd, hcd, hdd, hbd, had, hkr, le_rfl, hkn, hmax, hfirst, hrowMax, hrowFirst,
    HasRookVisitedColumns.initial (decodeMatrix dec N N xs) k⟩

/-- A decoded stored-column maximum realizes the pure column-magnitude quantity used in the
finite progress argument. This bridges actual word scores to the shared rook mathematics. -/
theorem rookColumnMagnitude_decodeMatrix {N : ℕ} (dec : K → ℝ) (xs : List K) (k col row : Fin N)
    (hr : k ≤ row)
    (hm : ∀ i : Fin N, k ≤ i →
      |dec (vec xs (col.val * N + i.val))| ≤ |dec (vec xs (col.val * N + row.val))|) :
    rookColumnMagnitude (decodeMatrix dec N N xs) k col =
      |dec (vec xs (col.val * N + row.val))| := by
  have h := rookColumnMagnitude_eq (decodeMatrix dec N N xs) k col row hr (by
    intro i hi
    simpa only [Real.norm_eq_abs, decodeMatrix_apply] using hm i hi)
  simpa only [Real.norm_eq_abs, decodeMatrix_apply] using h

/-- At the finite cap the stored row maximum is no larger than the incumbent column score.
The proof uses the visited-column cardinality and source matrix, without an execution premise. -/
theorem dec_le_of_cap {N rounds : ℕ} {dec : K → ℝ} {xs : List K} {k : Fin N}
    {best rowMaximum candidate pair : ℕ × ℕ} {s : Store K}
    (h : IsRookPrefix dec xs k rounds best rowMaximum candidate pair s)
    (hcap : N - k.val ≤ rounds + 1) {b a : K}
    (hb : s.get best.1 best.2 = some b) (ha : s.get rowMaximum.1 rowMaximum.2 = some a) :
    dec a ≤ dec b := by
  obtain ⟨row, col, next, b', a', r, c, d, visited, hb', ha', hd, hr, hc,
    hrd, hcd, hdd, hbd, had, hkr, hkc, hkd, hmax, hfirst, hrow, hrowFirst, hv⟩ := h
  have heb : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hea : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst b'
  subst a'
  rw [had, hbd]
  have he := rookColumnMagnitude_decodeMatrix dec xs k col row hkr hmax
  have hcell := norm_le_rookColumnMagnitude (decodeMatrix dec N N xs) k next row hkr
  have hcol := hv.rookColumnMagnitude_le_of_card hcap next hkd
  simpa only [Real.norm_eq_abs, decodeMatrix_apply, he] using hcell.trans hcol

/-- When the comparison does not strictly improve, read back the actual stored pair and
obtain both rook maxima and the first maximum row of the current column. Scoped scratch can
be popped because only the caller's pair is read in the result. -/
theorem return_of_stop {N rounds bound : ℕ} {dec : K → ℝ} {xs : List K} {k : Fin N}
    {best rowMaximum candidate pair : ℕ × ℕ} {s s' : Store K}
    {length pos initialPos : ℕ} (h : IsRookPrefix dec xs k rounds best rowMaximum candidate pair s)
    {b a : K} (hb : s.get best.1 best.2 = some b)
    (ha : s.get rowMaximum.1 rowMaximum.2 = some a) (hstop : dec a ≤ dec b)
    (hbelow : Store.Below length s s') (hpair : pair.1 < length)
    (hpos : pos = initialPos) (τ : Tape K) :
    ({ store := s', pos := pos } : Mem K).pos = initialPos ∧
      ∃ ys, ({ store := s', pos := pos } : Mem K).readBlocks [pair] [2] = some ys ∧
        (rookChoiceSpec dec bound).post [N, k.val] τ [xs] ys := by
  obtain ⟨row, col, next, b', a', r, c, d, visited, hb', ha', hd, hr, hc,
    hrd, hcd, hdd, hbd, had, hkr, hkc, hkd, hmax, hfirst, hrow, hrowFirst, hv⟩ := h
  have heb : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hea : a' = a := Option.some.inj (ha'.symm.trans ha)
  subst b'
  subst a'
  have hread := Store.readBlock_succ_of (Store.readBlock_one_of_get hr) hc
  refine ⟨hpos, [[r, c]], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hpair hread) rfl,
    row, col, hkr, hkc, hrd, hcd, hmax, ?_, hfirst⟩
  intro j hj
  exact (hrow j hj).trans (by simpa only [had, hbd] using hstop)

end IsRookPrefix

end NLAlib.LU
