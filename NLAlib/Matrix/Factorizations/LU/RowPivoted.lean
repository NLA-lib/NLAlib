/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedRoutine

/-!
# Row-policy LU with one column-history word

Partial and threshold pivoting share this actual wrapper around the common policy engine.
Only the row history is reported. A single scoped word receives the fixed column choice,
which is checked at each step; no hidden full column history is allocated.

## Main results

* `NLAlib.LU.factorRowPivoted_meets`: canonical row-permuted factors and actual row history.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Stored LU for a fixed-column row policy, with one current-position row log. The shared
policy engine reuses one scoped column word; it never allocates a hidden length-`n` log. -/
def factorRowPivoted (choose : Stmt Op Tst) : Routine Op Tst :=
  routine% [n] (A : n * n) → (L : n * n, U : n * n, H : n) {
    ifPos n {
      let Q ← alloc 1;
      run (factorPivoted choose true) [n] (A, L, U, H, Q)
    }
  }

/-- The actual row history determines the row permutation, and the reported factors are its
canonical LU factors. Positive column quality bounds the lower multipliers by its reciprocal,
without nonsingularity or a nonzero-pivot premise. -/
def factorRowPivotedSpec (dec : K → ℝ) (quality : ℝ) : Routine.Spec K :=
  spec% [n] (as) → (ls, us, hs) ensures
    ∃ p : Fin n → Fin n,
      (∀ i : Fin n, dec (vec hs i.val) = (p i).val) ∧ (∀ i : Fin n, i ≤ p i) ∧
      let B := (decodeMatrix dec n n as).submatrix (luPivotPermutation p n) id
      decodeMatrix dec n n ls = luLower B ∧ decodeMatrix dec n n us = luUpper B ∧
        IsLU B (decodeMatrix dec n n ls) (decodeMatrix dec n n us) ∧
        ∀ i j : Fin n, |decodeMatrix dec n n ls i j| ≤ quality⁻¹

/-- Identity column choices in the common output specification give the row-only PLU
specification. The permutation is decoded from the reported row words. -/
theorem factorRowPivotedSpec_of_pivoted {dec : K → ℝ} {quality : ℝ} {n : ℕ} {τ : Tape K}
    {as ls us hs qs : List K}
    (h : (factorPivotedSpec dec quality true).post [n] τ [as] [ls, us, hs, qs]) :
    (factorRowPivotedSpec dec quality).post [n] τ [as] [ls, us, hs] := by
  obtain ⟨p, q, hH, _, _, hp, _, hq, hlo, hup, hLU, hbound⟩ := h
  have he : q = id := funext (hq rfl)
  subst q
  refine ⟨p, hH, hp, ?_⟩
  simpa only [luPivotPermutation_id, Equiv.coe_refl] using
    And.intro hlo (And.intro hup (And.intro hLU hbound))

/-- A proved fixed-column selector gives the actual row-policy factorization for every
matrix. The only hidden history storage is one word; order zero enters no allocation or
framed call. Concrete policy theorems instantiate the selector with their actual scalar tree. -/
theorem factorRowPivoted_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {choose : Stmt Op Tst} {quality : ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) (hα : 0 < quality) (hα₁ : quality ≤ 1)
    (hchoice : ∀ bound : ℕ,
      (choiceRoutine choose).Meets I (choiceSpec dec quality bound true)) :
    (factorRowPivoted choose).Meets I (factorRowPivotedSpec dec quality) := by
  routine_intro [n] (A, L, U, H) reads (as)
  refine writes_ifPos rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    alloc as column
    have hAc : A.1 ≠ column := by change A.1 ≠ m.store.length + 0; omega
    have hLc : L.1 ≠ column := by change L.1 ≠ m.store.length + 0; omega
    have hUc : U.1 ≠ column := by change U.1 ≠ m.store.length + 0; omega
    have hHc : H.1 ≠ column := by change H.1 ≠ m.store.length + 0; omega
    call (factorPivoted_meets (quality := quality) (fixedColumns := true)
      hI hcmp hlit hQ hM hα hα₁ hchoice) [n] (A, L, U, H, (column, 0))
      as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hout
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change A.1 < s_column.length ∧ L.1 < s_column.length ∧ U.1 < s_column.length ∧
        H.1 < s_column.length ∧ m.store.length < s_column.length
      simp only [List.length_singleton] at hlen_column
      omega
    case' hroom =>
      change (L.2 + n * n ≤ s_column.len L.1) ∧ (U.2 + n * n ≤ s_column.len U.1) ∧
        (H.2 + n ≤ s_column.len H.1) ∧ (0 + (n - (n - 1)) ≤ s_column.len column) ∧ True
      have hlen : n - (n - 1) = 1 := by omega
      exact ⟨by rw [(hbelow_column L.1 hl.2.1).1]; exact hroom.1,
        by rw [(hbelow_column U.1 hl.2.2.1).1]; exact hroom.2.1,
        by rw [(hbelow_column H.1 hl.2.2.2).1]; exact hroom.2.2,
        by simpa only [Nat.zero_add, hlen] using hcolumn.ge, trivial⟩
    intro s₂ hs₂ hbelow
    refine ⟨hpos₁, [ls, us, hs], Mem.readBlocks_of_cons ?_
      (Mem.readBlocks_of_cons ?_ (Mem.readBlocks_of_cons ?_ rfl)),
      factorRowPivotedSpec_of_pivoted hout⟩
    · exact Store.Below.readBlock_of hbelow hl.2.1 hls
    · exact Store.Below.readBlock_of hbelow hl.2.2.1 hus
    · exact Store.Below.readBlock_of hbelow hl.2.2.2 hhs
  · rw [if_neg hn]
    have he : n = 0 := by omega
    subst n
    have has : as = [] := List.eq_nil_of_length_eq_zero (Store.length_of_readBlock has)
    subst as
    exact ⟨rfl, [[], [], []], by simp [Mem.readBlocks, Store.readBlock_zero],
      factorRowPivotedSpec_of_pivoted (factorPivotedSpec_zero dec quality true (τ.shift m.pos))⟩

end NLAlib.LU
