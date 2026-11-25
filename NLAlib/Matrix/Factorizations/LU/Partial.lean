/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PartialPivot
public import NLAlib.Matrix.Factorizations.LU.RowPivoted

/-!
# Scalar partial-pivot LU

The concrete routine instantiates the policy engine with the actual first-maximum active
column scan. Only the row history is reported; a single scoped word holds the fixed column
choice. Every matrix is admitted, including singular matrices and empty orders.

## Main results

* `NLAlib.LU.factorPartial_meets`: exact canonical PLU from actual partial pivot selection.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- The actual first-maximum column selector supplies unit column quality to the common
engine. The stronger stable-tie result remains in `partialChoiceSpec`. -/
theorem partialChoice_meets_choice {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (partialChoice (Op := Op) (Tst := Tst)).Meets I
      (choiceSpec dec 1 bound true) := by
  routine_intro [n, k] (R, p) reads (rs)
  have hraw := (partialChoice_meets hI hcmp hlit hQ hM hNat)
    [n, k] [R, p] τ m [rs] rfl rfl hlive hsep hr hpre hrooms
  refine hraw.mono le_rfl ?_
  rintro m' hfr ⟨hpos, ys, hys, hpost⟩
  change m'.readBlocks [p] [2] = some ys at hys
  obtain ⟨ws, rest, hws, hrest, rfl⟩ := Mem.readBlocks_cons_eq_some.mp hys
  simp only [Mem.readBlocks_nil, Option.some.injEq] at hrest
  subst rest
  obtain ⟨r, c, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hws)
  obtain ⟨row, hkr, hdr, hdc, hmax, _⟩ := hpost
  refine ⟨hpos, [[r, c]], Mem.readBlocks_of_cons hws rfl,
    row, ⟨k, hpre.1⟩, hkr, le_rfl, hdr, hdc, fun _ => rfl, ?_⟩
  intro i hi
  simpa only [one_mul] using hmax i hi

/-- Stored partial-pivot LU with one reported current-position row log. The full shared
policy engine reuses one scoped column word; it never allocates a hidden length-`n` log. -/
def factorPartial : Routine Op Tst :=
  factorRowPivoted (partialChoice (Op := Op) (Tst := Tst)).body

/-- The actual row history determines the row permutation, and the reported factors are its
canonical LU factors. Unit column quality gives lower multipliers of absolute value at most
one, without nonsingularity or a nonzero-pivot premise. -/
def factorPartialSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls, us, hs) ensures
    ∃ p : Fin n → Fin n,
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) ∧ (∀ i : Fin n, i ≤ p i) ∧
      let B := (decodeMatrix dec n n as).submatrix (luPivotPermutation p n) id
      decodeMatrix dec n n ls = luLower B ∧ decodeMatrix dec n n us = luUpper B ∧
        IsLU B (decodeMatrix dec n n ls) (decodeMatrix dec n n us) ∧
        ∀ i j : Fin n, |decodeMatrix dec n n ls i j| ≤ 1

/-- Identity column choices in the common output specification give the row-only PLU
specification. The permutation is decoded from the reported row words. -/
theorem factorPartialSpec_of_pivoted {dec : K → ℝ} {n : ℕ} {τ : Tape K}
    {as ls us hs qs : List K}
    (h : (factorPivotedSpec dec 1 true).post [n] τ [as] [ls, us, hs, qs]) :
    (factorPartialSpec dec).post [n] τ [as] [ls, us, hs] := by
  have hrow := factorRowPivotedSpec_of_pivoted h
  simpa only [factorRowPivotedSpec, factorPartialSpec, inv_one] using hrow

/-- The concrete first-maximum partial-pivot routine executes on every input matrix and
returns exact canonical PLU factors and its actual stored row log. Singular pivots skip
unsafe division through the common guarded step. -/
theorem factorPartial_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (factorPartial (Op := Op) (Tst := Tst)).Meets I (factorPartialSpec dec) := by
  have hrow := factorRowPivoted_meets (quality := 1) hI hcmp hlit hQ hM
    (by norm_num) le_rfl (fun bound => partialChoice_meets_choice hI hcmp hlit hQ
      hM.toStdModel_zero (hM.isExactNatLit bound))
  routine_intro [n] (A, L, U, H) reads (as)
  have hraw := hrow [n] [A, L, U, H] τ m [as] rfl rfl hlive hsep hr hpre hrooms
  refine hraw.mono le_rfl ?_
  rintro m' hfr ⟨hp, ys, hys, hpost⟩
  change m'.readBlocks [L, U, H] [n * n, n * n, n] = some ys at hys
  obtain ⟨ls, tailL, _, hreadU, houtL⟩ := Mem.readBlocks_cons_eq_some.mp hys
  obtain ⟨us, tailU, _, hreadH, houtU⟩ := Mem.readBlocks_cons_eq_some.mp hreadU
  obtain ⟨hs, tailH, _, hreadNil, houtH⟩ := Mem.readBlocks_cons_eq_some.mp hreadH
  have heNil : tailH = [] := by
    simpa only [Mem.readBlocks_nil, Option.some.injEq] using hreadNil.symm
  have heys : ys = [ls, us, hs] := by rw [houtL, houtU, houtH, heNil]
  rw [heys] at hpost hys
  refine ⟨hp, [ls, us, hs], hys, ?_⟩
  simpa only [factorRowPivotedSpec, factorPartialSpec, inv_one] using hpost

end NLAlib.LU
