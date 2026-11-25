/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RookAdvance

/-!
# Strict progress from an actual rook continuation

The actual comparison, copied candidate column and two scan postconditions advance the word
invariant. The existing pure column-magnitude growth theorem inserts a fresh active column
in the mathematical witness. No visited array or execution assumption is introduced.

## Main results

* `NLAlib.LU.IsRookPrefix.advance_of_post`: actual continuation results advance finite progress.
-/

@[expose] public section

namespace NLAlib.LU.IsRookPrefix

open Ops

variable {K : Type} [Inhabited K]

/-- A strict actual score comparison and the continuation's word postcondition advance the
stored rook state and its finite progress witness. The new reported column is the original
candidate word; all new scores and selected words come from the executed scans. -/
theorem advance_of_post {N rounds bound : ℕ} {dec : K → ℝ} {xs : List K} {k : Fin N}
    {best rowMaximum candidate pair : ℕ × ℕ} {s s' : Store K} {τ : Tape K}
    (h : IsRookPrefix dec xs k rounds best rowMaximum candidate pair s)
    {b a d b' a' d' r' c' : K}
    (hb : s.get best.1 best.2 = some b) (ha : s.get rowMaximum.1 rowMaximum.2 = some a)
    (hd : s.get candidate.1 candidate.2 = some d) (hbetter : dec b < dec a)
    (hpost : (rookAdvanceSpec dec bound).post [N, k.val] τ [xs, [d]]
      [[d'], [b'], [a'], [r', c']])
    (hb' : s'.get best.1 best.2 = some b') (ha' : s'.get rowMaximum.1 rowMaximum.2 = some a')
    (hd' : s'.get candidate.1 candidate.2 = some d') (hr' : s'.get pair.1 pair.2 = some r')
    (hc' : s'.get pair.1 (pair.2 + 1) = some c') :
    IsRookPrefix dec xs k (rounds + 1) best rowMaximum candidate pair s' := by
  obtain ⟨row, col, next, b₀, a₀, r, c, d₀, visited, hb₀, ha₀, hd₀, hr, hc,
    hrd, hcd, hdd, hbd, had, hkr, hkc, hkd, hmax, hfirst, hrow, hrowFirst, hv⟩ := h
  have heb : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
  have hea : a₀ = a := Option.some.inj (ha₀.symm.trans ha)
  have hed : d₀ = d := Option.some.inj (hd₀.symm.trans hd)
  subst b₀
  subst a₀
  subst d₀
  rw [hbd, had] at hbetter
  have hgrowth := rookColumnMagnitude_lt_of_lt (decodeMatrix dec N N xs) k col row next hkr
    (by intro i hi; simpa only [Real.norm_eq_abs, decodeMatrix_apply] using hmax i hi)
    (by simpa only [Real.norm_eq_abs, decodeMatrix_apply] using hbetter)
  obtain ⟨hec, col', row', hkc', hdc', hcolumn, hdr', hrow'⟩ := hpost
  rw [hec] at hc'
  have hecol : col' = next := Fin.ext (Nat.cast_injective (hdc'.symm.trans hdd))
  subst col'
  obtain ⟨row'', hkr', hdr'', hbd', hmax', hfirst'⟩ := hcolumn
  have herow : row'' = row' := Fin.ext (Nat.cast_injective (hdr''.symm.trans hdr'))
  subst row''
  obtain ⟨next', hkn', hdd', had', hrowMax', hrowFirst'⟩ := hrow'
  exact ⟨row', next, next', b', a', r', d, d', insert next visited,
    hb', ha', hd', hr', hc', hdr', hdd, hdd', hbd', had', hkr', hkd, hkn',
    hmax', hfirst', hrowMax', hrowFirst', hv.insert hkd hgrowth⟩

end NLAlib.LU.IsRookPrefix
