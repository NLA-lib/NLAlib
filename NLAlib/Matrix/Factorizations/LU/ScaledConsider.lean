/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PartialPivot

/-!
# Division-free scaled candidate comparisons

The incumbent contains an absolute value, its row scale and its actual stored index. A zero
incumbent scale is treated separately; compatible zero scales have zero numerator. Otherwise
two actual cross products decide strict improvement. Equal ratios preserve the incumbent.
No division is executed by either routine.

## Main definitions

* `NLAlib.LU.acceptScaled`: copy an accepted candidate and write its actual index.
* `NLAlib.LU.considerScaled`: compare a candidate against the stored incumbent.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Commit a candidate's magnitude, scale and dimension index. Both comparison branches use
this identical scalar-copy and index-literal routine. -/
def acceptScaled : Routine Op Tst := routine% [i] (a : 1, t : 1) → (b : 1, s : 1, j : 1) by blocks {
  call (Has.inj ScalarOp.copy) [] (a) → (b);
  call (Has.inj ScalarOp.copy) [] (t) → (s);
  call (Has.inj IndexOp.lit) [i] () → (j)
}

/-- Improve only at a strictly larger scaled magnitude. The zero-incumbent branch avoids
cross products, including for an all-zero active column and zero scales. -/
def considerScaled : Routine Op Tst :=
  routine% [i] (a : 1, t : 1, b : 1, s : 1, j : 1) → (b, s, j) by blocks {
    if (Has.inj CmpTst.isZero) [] (s) {
      if (Has.inj CmpTst.isPos) [] (a) {
        run acceptScaled [i] (a, t, b, s, j)
      } else { skip }
    } else {
      let left ← alloc 1;
      let right ← alloc 1;
      call (Has.inj ScalarOp.mul) [] (a, s) → (left);
      call (Has.inj ScalarOp.mul) [] (b, t) → (right);
      if (Has.inj CmpTst.lt) [] (right, left) {
        run acceptScaled [i] (a, t, b, s, j)
      } else { skip }
    }
  }

/-- The committed words are exactly the candidate words and machine index literal. -/
def acceptScaledSpec (M : Machine K) : Routine.Spec K :=
  spec% [i] ([a], [t]) → ([b], [s], [j]) ensures
    b = a ∧ s = t ∧ j = M.lit (i : ℕ)

omit [Has CmpTst Tst] in
/-- The actual copy/index instructions commit the candidate without numerical assumptions. -/
theorem acceptScaled_meets {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) (hlit : IsIndexLit M I) :
    (acceptScaled (Op := Op) (Tst := Tst)).Meets I (acceptScaledSpec M) := by
  routine_intro [i] (a, t, b, s, j) reads (ass, ts)
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq,
    Fp.disj_sup_left, Fp.disj_sup_right, Fp.disj_bot_left, Fp.disj_bot_right,
    and_true] at hblocks
  have hbs : Fp.Disj (Store.inBlock b.1 b.2 1) (Store.inBlock s.1 s.2 1) := by tauto
  have hbj : Fp.Disj (Store.inBlock b.1 b.2 1) (Store.inBlock j.1 j.2 1) := by tauto
  have hsj : Fp.Disj (Store.inBlock s.1 s.2 1) (Store.inBlock j.1 j.2 1) := by tauto
  have hbt : Fp.Disj (Store.inBlock b.1 b.2 1) (Store.inBlock t.1 t.2 1) := by tauto
  obtain ⟨a₀, ha₀, rfl⟩ := Store.readBlock_one_eq_some.mp hass
  obtain ⟨t₀, ht₀, rfl⟩ := Store.readBlock_one_eq_some.mp hts
  step (hI .copy) as m₁ hfr₁ ⟨hpos₁, v, hv, rfl⟩
  have ht₁ := hfr₁.keep (Store.readsOnly_get _ _ _) hbt ht₀
  step (hI .copy) as m₂ hfr₂ ⟨hpos₂, w, hw, rfl⟩
  step hlit as m₃ hfr₃ ⟨hpos₃, z, hz, hword⟩
  have he : M.lit (i : ℕ) = z := by simpa [Machine.indexFn] using hword
  subst z
  simp only [Machine.indexFn, Nat.add_zero] at hpos₃
  have hb₂ := hfr₂.keep (Store.readsOnly_get _ _ _) hbs.symm hv
  have hb₃ := hfr₃.keep (Store.readsOnly_get _ _ _) hbj.symm hb₂
  have hs₃ := hfr₃.keep (Store.readsOnly_get _ _ _) hsj.symm hw
  refine ⟨hpos₃.trans (hpos₂.trans hpos₁), [[a₀], [t₀], [M.lit (i : ℕ)]],
    Mem.readBlocks_of_cons (Store.readBlock_one_of_get hb₃)
      (Mem.readBlocks_of_cons (Store.readBlock_one_of_get hs₃)
        (Mem.readBlocks_of_cons (Store.readBlock_one_of_get hz) rfl)), rfl, rfl, rfl⟩

/-- The exact machine words selected by the zero-scale or cross-product branch. This word
specification makes no claim that rounded products preserve ratio ordering. -/
def considerScaledSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [i] ([a], [t], [b], [s], [j]) → ([b'], [s'], [j']) ensures
    if (if dec s = 0 then 0 < dec a else dec (M.mul b t) < dec (M.mul a s)) then
      b' = a ∧ s' = t ∧ j' = M.lit (i : ℕ)
    else b' = b ∧ s' = s ∧ j' = j

private theorem considerScaled_return {M : Machine K} {dec : K → ℝ}
    {i : ℕ} {a t b s j b' s' j' : K} {τ : Tape K}
    {st st' : Store K} {bp sp jp : ℕ × ℕ} {length pos initialPos : ℕ}
    (hbelow : Store.Below length st st')
    (hb : bp.1 < length) (hs : sp.1 < length) (hj : jp.1 < length)
    (hp : pos = initialPos) (hbg : st.get bp.1 bp.2 = some b')
    (hsg : st.get sp.1 sp.2 = some s') (hjg : st.get jp.1 jp.2 = some j')
    (hpost : if (if dec s = 0 then 0 < dec a else
        dec (M.mul b t) < dec (M.mul a s)) then
      b' = a ∧ s' = t ∧ j' = M.lit (i : ℕ) else b' = b ∧ s' = s ∧ j' = j) :
    ({store := st', pos := pos} : Mem K).pos = initialPos ∧ ∃ ys,
      ({store := st', pos := pos} : Mem K).readBlocks [bp, sp, jp] [1, 1, 1] = some ys ∧
        (considerScaledSpec M dec).post [i] τ [[a], [t], [b], [s], [j]] ys := by
  exact ⟨hp, [[b'], [s'], [j']], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hb (Store.readBlock_one_of_get hbg))
    (Mem.readBlocks_of_cons
      (Store.Below.readBlock_of hbelow hs (Store.readBlock_one_of_get hsg))
      (Mem.readBlocks_of_cons
        (Store.Below.readBlock_of hbelow hj (Store.readBlock_one_of_get hjg)) rfl)), hpost⟩

/-- The actual cross products, comparisons and copies satisfy the word-level branch
contract. No rounding bound or ratio-order assumption is used in this execution theorem. -/
theorem considerScaled_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I) :
    (considerScaled (Op := Op) (Tst := Tst)).Meets I (considerScaledSpec M dec) := by
  routine_intro [i] (a, t, b, s, j) reads (ass, ts, bs, ss, js)
  have hacc : (acceptScaled (Op := Op) (Tst := Tst)).SeparatedAt [i] [a, t, b, s, j] := by
    apply Routine.separatedAt_of_blocks rfl
    exact hblocks
  obtain ⟨a₀, ha₀, rfl⟩ := Store.readBlock_one_eq_some.mp hass
  obtain ⟨t₀, ht₀, rfl⟩ := Store.readBlock_one_eq_some.mp hts
  obtain ⟨b₀, hb₀, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨s₀, hs₀, rfl⟩ := Store.readBlock_one_eq_some.mp hss
  obtain ⟨j₀, hj₀, rfl⟩ := Store.readBlock_one_eq_some.mp hjs
  refine writes_ite rfl rfl (hcmp.test_isZero hs₀) ?_
  by_cases hz : dec s₀ = 0
  · simp only [hz, decide_true, ite_true]
    refine writes_ite rfl rfl (hcmp.test_isPos ha₀) ?_
    by_cases hp : 0 < dec a₀
    · simp only [hp, decide_true, ite_true]
      call (acceptScaled_meets hI hlit) [i] (a, t, b, s, j)
        as m₁ hfr₁ hpos₁ (bs', ss', js') hpost
      case' hsep => exact hacc
      obtain ⟨b', hb', rfl⟩ := Store.readBlock_one_eq_some.mp hbs'
      obtain ⟨s', hs', rfl⟩ := Store.readBlock_one_eq_some.mp hss'
      obtain ⟨j', hj', rfl⟩ := Store.readBlock_one_eq_some.mp hjs'
      routine_exit
      change b' = a₀ ∧ s' = t₀ ∧ j' = M.lit (i : ℕ) at hpost
      change if (if dec s₀ = 0 then _ else _) then _ else _
      simpa only [hz, if_true, hp] using hpost
    · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
      apply wp_skip
      refine ⟨Store.EqOff.refl _ _, rfl, [[b₀], [s₀], [j₀]],
        Mem.readBlocks_of_cons hbs (Mem.readBlocks_of_cons hss
          (Mem.readBlocks_of_cons hjs rfl)), ?_⟩
      change if (if dec s₀ = 0 then _ else _) then _ else _
      simp only [hz, if_true, hp, if_false]
      exact ⟨trivial, trivial, trivial⟩
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
    change Writes .total I τ _ (Env.frame [i] [a, t, b, s, j, b, s, j])
      (Fp.blocks [b, s, j] [1, 1, 1]) _ m
    alloc as left right
    have hal : a.1 ≠ left := by change a.1 ≠ m.store.length + 0; omega
    have har : a.1 ≠ right := by change a.1 ≠ m.store.length + 1; omega
    have htl : t.1 ≠ left := by change t.1 ≠ m.store.length + 0; omega
    have htr : t.1 ≠ right := by change t.1 ≠ m.store.length + 1; omega
    have hbl : b.1 ≠ left := by change b.1 ≠ m.store.length + 0; omega
    have hbr : b.1 ≠ right := by change b.1 ≠ m.store.length + 1; omega
    have hsl : s.1 ≠ left := by change s.1 ≠ m.store.length + 0; omega
    have hsr : s.1 ≠ right := by change s.1 ≠ m.store.length + 1; omega
    have hjl : j.1 ≠ left := by change j.1 ≠ m.store.length + 0; omega
    have hjr : j.1 ≠ right := by change j.1 ≠ m.store.length + 1; omega
    have hlr : left ≠ right := by change m.store.length + 0 ≠ m.store.length + 1; omega
    step (hI .mul) as m₁ hfr₁ ⟨hpos₁, v, hv, rfl⟩
    step (hI .mul) as m₂ hfr₂ ⟨hpos₂, w, hw, rfl⟩
    have hv₂ : m₂.store.get left 0 = some (M.mul a₀ s₀) := by keep
    refine writes_ite rfl rfl (hcmp.test_lt hw hv₂) ?_
    by_cases hp : dec (M.mul b₀ t₀) < dec (M.mul a₀ s₀)
    · simp only [hp, decide_true, ite_true]
      call (acceptScaled_meets hI hlit) [i] (a, t, b, s, j)
        as m₃ hfr₃ hpos₃ (bs', ss', js') hpost
      case' hsep => exact hacc
      obtain ⟨b', hb', rfl⟩ := Store.readBlock_one_eq_some.mp hbs'
      obtain ⟨s', hs', rfl⟩ := Store.readBlock_one_eq_some.mp hss'
      obtain ⟨j', hj', rfl⟩ := Store.readBlock_one_eq_some.mp hjs'
      intro st₃ hst₃ hbelow
      apply considerScaled_return (τ := τ.shift m.pos) (pos := m₃.pos)
        (initialPos := m.pos) hbelow hl.2.2.1 hl.2.2.2.1
        hl.2.2.2.2 (by omega) hb' hs' hj'
      change b' = a₀ ∧ s' = t₀ ∧ j' = M.lit (i : ℕ) at hpost
      simpa only [hz, if_false, hp, if_true] using hpost
    · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
      apply wp_skip
      refine ⟨Store.EqOff.refl _ _, ?_⟩
      intro st₂ hst₂ hbelow
      apply considerScaled_return (τ := τ.shift m.pos) (pos := m₂.pos)
        (initialPos := m.pos) hbelow hl.2.2.1 hl.2.2.2.1
        hl.2.2.2.2 (by omega) (by keep) (by keep) (by keep)
      simp only [hz, if_false, hp]
      exact ⟨trivial, trivial, trivial⟩

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] in
/-- Under exact multiplication, nonnegative compatible zero scales make the actual branch
exactly strict ratio improvement. This justifies the selector's guarded division-free test. -/
theorem considerScaled_comparison {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) (a t b s : K)
    (_ha : 0 ≤ dec a) (ht : 0 ≤ dec t) (hb : 0 ≤ dec b) (hs : 0 ≤ dec s)
    (haz : dec t = 0 → dec a = 0) (hbz : dec s = 0 → dec b = 0) :
    (if dec s = 0 then 0 < dec a else dec (M.mul b t) < dec (M.mul a s)) ↔
      dec b / dec s < dec a / dec t := by
  rw [hM.mul, hM.mul]
  by_cases hz : dec s = 0
  · rw [if_pos hz, hbz hz, zero_div]
    by_cases htz : dec t = 0
    · rw [haz htz, htz, zero_div]
    · exact (div_pos_iff_of_pos_right (lt_of_le_of_ne ht (Ne.symm htz))).symm
  · rw [if_neg hz]
    by_cases htz : dec t = 0
    · rw [haz htz, htz, mul_zero, zero_mul, zero_div]
      have hd : 0 ≤ dec b / dec s := div_nonneg hb hs
      exact ⟨fun h => (lt_irrefl 0 h).elim, fun h => (not_lt_of_ge hd h).elim⟩
    · exact (div_lt_div_iff₀ (lt_of_le_of_ne hs (Ne.symm hz))
        (lt_of_le_of_ne ht (Ne.symm htz))).symm

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] in
/-- The actual committed words select the strict ratio winner, retaining all old words at a
tie. No operation in the routine evaluates either division appearing in this conclusion. -/
theorem considerScaledSpec_ratio {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {i : ℕ} {a t b s j b' s' j' : K} {τ : Tape K}
    (ha : 0 ≤ dec a) (ht : 0 ≤ dec t) (hb : 0 ≤ dec b) (hs : 0 ≤ dec s)
    (haz : dec t = 0 → dec a = 0) (hbz : dec s = 0 → dec b = 0)
    (hpost : (considerScaledSpec M dec).post [i] τ
      [[a], [t], [b], [s], [j]] [[b'], [s'], [j']]) :
    if dec b / dec s < dec a / dec t then
      b' = a ∧ s' = t ∧ j' = M.lit (i : ℕ) else b' = b ∧ s' = s ∧ j' = j := by
  change (if (if dec s = 0 then 0 < dec a else
    dec (M.mul b t) < dec (M.mul a s)) then _ else _) at hpost
  simpa only [considerScaled_comparison hM a t b s ha ht hb hs haz hbz] using hpost

end NLAlib.LU
