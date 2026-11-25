/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledAdvance

/-!
# Stable scaled absolute-value selection

The scan caches a numerator and its fixed row scale, then uses the actual division-free
candidate comparison. Equal ratios retain the first index. Compatible zero scales are
allowed. Divisions below occur only in mathematical specifications, never in the program.

## Main results

* `NLAlib.LU.argmaxScaledAbs_meets`: the actual scan returns a first ratio maximum.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Scan nonempty numerator and scale vectors by actual cross products and comparisons.
Two persistent scratch words cache the incumbent magnitude and scale. Candidate magnitudes
and cross products are scoped inside the single-candidate advance routine. -/
def argmaxScaledAbs : Routine Op Tst :=
  routine% [n] (x : n, scales : n) → (j : 1) {
    let best ← alloc 1;
    let scale ← alloc 1;
    run absolute [] (x, best);
    call (Has.inj ScalarOp.copy) [] (scales) → (scale);
    call (Has.inj IndexOp.lit) [0] () → (j);
    for i < n - 1 {
      run advanceScaled [n, i + 1] (x, scales, best, scale, j)
    }
  }

variable [Inhabited K]

/-- The input scales are nonnegative and zero scales have zero numerators. The actual index
selects a first maximum of absolute-value/scale ratios, with the field convention `0/0=0`. -/
def argmaxScaledAbsSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K :=
  spec% [n] (xs, ss) → ([j]) requires
    (0 < n ∧ n ≤ bound) ∧ ∀ i : Fin n,
      0 ≤ dec (vec ss i.val) ∧ (dec (vec ss i.val) = 0 → dec (vec xs i.val) = 0)
  ensures ∃ i : Fin n, dec j = i.val ∧
    (∀ t : Fin n, |dec (vec xs t.val)| / dec (vec ss t.val) ≤
      |dec (vec xs i.val)| / dec (vec ss i.val)) ∧
    (∀ t : Fin n, t < i → |dec (vec xs t.val)| / dec (vec ss t.val) <
      |dec (vec xs i.val)| / dec (vec ss i.val))

private def IsScaledPrefix (dec : K → ℝ) (xs ss : List K) (N covered : ℕ)
    (best scale index : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ q : Fin N, ∃ b t w : K,
    s.get best.1 best.2 = some b ∧ s.get scale.1 scale.2 = some t ∧
    s.get index.1 index.2 = some w ∧
    dec b = |dec (vec xs q.val)| ∧ dec t = dec (vec ss q.val) ∧ dec w = q.val ∧
    q.val < covered ∧
    (∀ a : Fin N, a.val < covered → |dec (vec xs a.val)| / dec (vec ss a.val) ≤
      |dec (vec xs q.val)| / dec (vec ss q.val)) ∧
    (∀ a : Fin N, a < q → |dec (vec xs a.val)| / dec (vec ss a.val) <
      |dec (vec xs q.val)| / dec (vec ss q.val))

private theorem scaledPrefix_initial {dec : K → ℝ} {xs ss : List K} {N : ℕ}
    (hN : 0 < N) {best scale index : ℕ × ℕ} {s : Store K} {b t w : K}
    (hb : s.get best.1 best.2 = some b) (ht : s.get scale.1 scale.2 = some t)
    (hw : s.get index.1 index.2 = some w)
    (hbd : dec b = |dec (vec xs 0)|) (htd : dec t = dec (vec ss 0)) (hwd : dec w = 0) :
    IsScaledPrefix dec xs ss N 1 best scale index s := by
  refine ⟨⟨0, hN⟩, b, t, w, hb, ht, hw, hbd, htd, by simpa using hwd,
    Nat.zero_lt_one, ?_, ?_⟩
  · intro a ha
    have he : a.val = 0 := by omega
    simp only [he, le_refl]
  · intro a ha
    exact (Nat.not_lt_zero a.val ha).elim

private theorem scaledPrefix_choose {dec : K → ℝ} {xs ss : List K} {N covered : ℕ}
    (q a : Fin N) (ha : a.val = covered) (hq : q.val < covered)
    (hdom : ∀ t : Fin N, t.val < covered → |dec (vec xs t.val)| / dec (vec ss t.val) ≤
      |dec (vec xs q.val)| / dec (vec ss q.val))
    (hfirst : ∀ t : Fin N, t < q → |dec (vec xs t.val)| / dec (vec ss t.val) <
      |dec (vec xs q.val)| / dec (vec ss q.val))
    {best scale index : ℕ × ℕ} {s : Store K} {b t w : K}
    (hb : s.get best.1 best.2 = some b) (ht : s.get scale.1 scale.2 = some t)
    (hw : s.get index.1 index.2 = some w)
    (hbd : dec b = |dec (vec xs
      (if |dec (vec xs q.val)| / dec (vec ss q.val) <
        |dec (vec xs a.val)| / dec (vec ss a.val) then a else q).val)|)
    (htd : dec t = dec (vec ss
      (if |dec (vec xs q.val)| / dec (vec ss q.val) <
        |dec (vec xs a.val)| / dec (vec ss a.val) then a else q).val))
    (hwd : dec w = (if |dec (vec xs q.val)| / dec (vec ss q.val) <
      |dec (vec xs a.val)| / dec (vec ss a.val) then a else q).val) :
    IsScaledPrefix dec xs ss N (covered + 1) best scale index s := by
  have hh := Fin.max_eq_score_choose_of_prefix
    (fun a : Fin N => |dec (vec xs a.val)| / dec (vec ss a.val)) q a ha hdom hfirst
  refine ⟨_, b, t, w, hb, ht, hw, hbd, htd, hwd, ?_, hh.2.1, hh.2.2⟩
  split_ifs <;> omega

private theorem scaledPrefix_next {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {N i : ℕ} {xs ss : List K}
    (q : Fin N) (hi : i < N) (hq : q.val < i)
    (hcompat : ∀ t : Fin N, 0 ≤ dec (vec ss t.val) ∧
      (dec (vec ss t.val) = 0 → dec (vec xs t.val) = 0))
    (hdom : ∀ t : Fin N, t.val < i → |dec (vec xs t.val)| / dec (vec ss t.val) ≤
      |dec (vec xs q.val)| / dec (vec ss q.val))
    (hfirst : ∀ t : Fin N, t < q → |dec (vec xs t.val)| / dec (vec ss t.val) <
      |dec (vec xs q.val)| / dec (vec ss q.val))
    {best scale index : ℕ × ℕ} {s : Store K} {a t b z w b' z' w' : K} {τ : Tape K}
    (hbd : dec b = |dec (vec xs q.val)|) (hzd : dec z = dec (vec ss q.val))
    (hwd : dec w = q.val) (had : dec a = |dec (vec xs i)|)
    (htd : dec t = dec (vec ss i))
    (hb : s.get best.1 best.2 = some b') (hz : s.get scale.1 scale.2 = some z')
    (hw : s.get index.1 index.2 = some w')
    (hpost : (considerScaledSpec M dec).post [i] τ
      [[a], [t], [b], [z], [w]] [[b'], [z'], [w']]) :
    IsScaledPrefix dec xs ss N (i + 1) best scale index s := by
  have hc := hcompat ⟨i, hi⟩
  have hqcompat := hcompat q
  have hp := considerScaledSpec_ratio hM
    (by rw [had]; exact abs_nonneg _) (by simpa only [htd] using hc.1)
    (by rw [hbd]; exact abs_nonneg _) (by simpa only [hzd] using hqcompat.1)
    (fun h => by rw [had, hc.2 (htd.symm.trans h), abs_zero])
    (fun h => by rw [hbd, hqcompat.2 (hzd.symm.trans h), abs_zero]) hpost
  rw [hbd, hzd, had, htd] at hp
  apply scaledPrefix_choose q ⟨i, hi⟩ rfl hq hdom hfirst hb hz hw
  all_goals
    split_ifs at hp ⊢ with hlt
    · rcases hp with ⟨rfl, rfl, rfl⟩
      first | exact had | exact htd | exact hM.isExactNatLit N i hi.le
    · rcases hp with ⟨rfl, rfl, rfl⟩
      first | exact hbd | exact hzd | exact hwd

private theorem scaledPrefix_return {dec : K → ℝ} {xs ss : List K} {N bound : ℕ}
    {best scale index : ℕ × ℕ} {s s' : Store K} {length pos initialPos : ℕ}
    (hN : 0 < N) (h : IsScaledPrefix dec xs ss N (N - 1 + 1) best scale index s)
    (hbelow : Store.Below length s s') (hindex : index.1 < length)
    (hp : pos = initialPos) (τ : Tape K) :
    ({store := s', pos := pos} : Mem K).pos = initialPos ∧ ∃ ys,
      ({store := s', pos := pos} : Mem K).readBlocks [index] [1] = some ys ∧
        (argmaxScaledAbsSpec dec bound).post [N] τ [xs, ss] ys := by
  have he : N - 1 + 1 = N := by omega
  rw [he] at h
  obtain ⟨q, b, t, w, hb, ht, hw, hbd, htd, hwd, hq, hdom, hfirst⟩ := h
  exact ⟨hp, [[w]], Mem.readBlocks_of_cons
    (Store.Below.readBlock_of hbelow hindex (Store.readBlock_one_of_get hw)) rfl,
    q, hwd, fun t => hdom t t.isLt, hfirst⟩

private theorem scaledPrefix_initial_literal {M : Machine K} {dec : K → ℝ}
    (hM : ExactModel dec M) {N : ℕ} (hN : 0 < N) {xs ss : List K}
    {best scale index : ℕ × ℕ} {s : Store K} {b w : K} {τ : Tape K}
    (hb : s.get best.1 best.2 = some b)
    (ht : s.get scale.1 scale.2 = some (vec ss 0))
    (hw : s.get index.1 index.2 = some w)
    (ha : (absoluteSpec M dec).post [] τ [[vec xs 0]] [[b]])
    (hl : M.indexFn.fn [0] [] [] = some [[w]]) :
    IsScaledPrefix dec xs ss N 1 best scale index s := by
  have he : M.lit 0 = w := by simpa [Machine.indexFn] using hl
  subst w
  exact scaledPrefix_initial hN hb ht hw
    (absoluteSpec_decode hM.toStdModel_zero ha) rfl
    (by simpa only [Rat.cast_zero] using hM.lit 0)

omit [Has IndexOp Op] in
private theorem scaledScan_absolute_geometry {s : Store K} {x : ℕ × ℕ}
    {N i scratch pos : ℕ} {xs : List K} (hx : s.readBlock x.1 x.2 N = some xs)
    (hi : i < N) (hc : 1 ≤ s.len scratch) :
    s.get x.1 (x.2 + i) = some (vec xs i) ∧
      (⟨s, pos⟩ : Mem K).Live [(x.1, x.2 + i), (scratch, 0)] ∧
      (absolute (Op := Op) (Tst := Tst)).RoomAt (⟨s, pos⟩ : Mem K) []
        ((absolute (Op := Op) (Tst := Tst)).operands []
          [(x.1, x.2 + i), (scratch, 0)]) := by
  have hget := Store.get_of_readBlock hx hi default
  refine ⟨hget, ?_, ?_⟩
  · simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨Store.lt_length_of_get hget,
      Store.lt_length_of_lt_len (lt_of_lt_of_le Nat.zero_lt_one hc)⟩
  · change 0 + 1 ≤ s.len scratch ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hc, trivial⟩

/-- The actual scalar scan selects the first ratio maximum under exact arithmetic. Compatible
zero scales and all-zero vectors are admitted, and no division instruction is executed. -/
theorem argmaxScaledAbs_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hM : ExactModel dec M) :
    (argmaxScaledAbs (Op := Op) (Tst := Tst)).Meets I (argmaxScaledAbsSpec dec bound) := by
  routine_intro [n] (x, scales, j) reads (xs, ss)
  obtain ⟨⟨hn, hnb⟩, hcompat⟩ := hpre
  change Writes .total I τ _ (Env.frame [n] [x, scales, j]) (Fp.blocks [j] [1]) _ m
  alloc as best scale
  have hxb : x.1 ≠ best := by change x.1 ≠ m.store.length + 0; omega
  have hxs' : x.1 ≠ scale := by change x.1 ≠ m.store.length + 1; omega
  have hsb : scales.1 ≠ best := by change scales.1 ≠ m.store.length + 0; omega
  have hss' : scales.1 ≠ scale := by change scales.1 ≠ m.store.length + 1; omega
  have hjb : j.1 ≠ best := by change j.1 ≠ m.store.length + 0; omega
  have hjs : j.1 ≠ scale := by change j.1 ≠ m.store.length + 1; omega
  have hbestScale : best ≠ scale := by change m.store.length + 0 ≠ m.store.length + 1; omega
  have hs0 : m.store.get scales.1 scales.2 = some (vec ss 0) := by
    simpa using Store.get_of_readBlock hss hn default
  have hxstart := Store.Below.readBlock_of hbelow_best hl.1 hxs
  have hgeom := scaledScan_absolute_geometry (Op := Op) (Tst := Tst)
    (pos := m.pos) hxstart hn hbest.ge
  have hx0 : s_best.get x.1 x.2 = some (vec xs 0) := by
    simpa only [Nat.add_zero] using hgeom.1
  call (absolute_meets hI hcmp) [] (x, (best, 0))
    as m₁ hfr₁ hpos₁ (bs) habs
  case' hlive => simpa only [Nat.add_zero] using hgeom.2.1
  case' hroom => simpa only [Nat.add_zero] using hgeom.2.2
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  step (hI .copy) as m₂ hfr₂ ⟨hpos₂, t, ht, rfl⟩
  step hlit as m₃ hfr₃ ⟨hpos₃, w, hw, hword⟩
  simp only [Machine.indexFn, Nat.add_zero] at hpos₃
  have hstart : IsScaledPrefix dec xs ss n 1 (best, 0) (scale, 0) j m₃.store :=
    scaledPrefix_initial_literal hM hn (by keep) (by keep) hw habs hword
  loop_inv (fun _ => Fp.blocks [(best, 0), (scale, 0), j] [1, 1, 1])
    (fun i μ => μ.pos = m.pos ∧
      IsScaledPrefix dec xs ss n (i + 1) (best, 0) (scale, 0) j μ.store)
    with i hi m₄ hfr hP
  case initial => exact ⟨hpos₃.trans (hpos₂.trans hpos₁), hstart⟩
  case round =>
    obtain ⟨hp, q, b, t, w, hb, ht, hw, hbd, htd, hwd, hq, hdom, hfirst⟩ := hP
    have hxs₄ : m₄.store.readBlock x.1 x.2 n = some xs := by keep
    have hss₄ : m₄.store.readBlock scales.1 scales.2 n = some ss := by keep
    have hit : i + 1 < n := by omega
    call (advanceScaled_meets hI hcmp hlit) [n, i + 1]
      (x, scales, (best, 0), (scale, 0), j) (pre := hit)
      as m₅ hfr₅ hpos₅ (bs', ts', ws') hpost
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      have hx₅ := Store.get_of_readBlock hxs₄ hit default
      have hs₅ := Store.get_of_readBlock hss₄ hit default
      exact ⟨Store.lt_length_of_get hx₅, Store.lt_length_of_get hs₅,
        Store.lt_length_of_get hb, Store.lt_length_of_get ht, Store.lt_length_of_get hw⟩
    case' hroom =>
      change 0 + 1 ≤ m₄.store.len best ∧ 0 + 1 ≤ m₄.store.len scale ∧
        j.2 + 1 ≤ m₄.store.len j.1 ∧ True
      exact ⟨Store.lt_len_of_get hb, Store.lt_len_of_get ht, Store.lt_len_of_get hw, trivial⟩
    obtain ⟨b', hb', rfl⟩ := Store.readBlock_one_eq_some.mp hbs'
    obtain ⟨t', ht', rfl⟩ := Store.readBlock_one_eq_some.mp hts'
    obtain ⟨w', hw', rfl⟩ := Store.readBlock_one_eq_some.mp hws'
    obtain ⟨c, hc, hconsider⟩ : ∃ c : K,
        (absoluteSpec M dec).post [] (τ.shift m₄.pos) [[vec xs (i + 1)]] [[c]] ∧
        (considerScaledSpec M dec).post [i + 1] (τ.shift m₄.pos)
          [[c], [vec ss (i + 1)], [b], [t], [w]] [[b'], [t'], [w']] := hpost
    refine ⟨hpos₅.trans hp, ?_⟩
    exact scaledPrefix_next hM q hit hq hcompat hdom hfirst hbd htd hwd
      (absoluteSpec_decode hM.toStdModel_zero hc) rfl hb' ht' hw' hconsider
  case exit =>
    rintro m₄ hfr ⟨hp, hstate⟩ s₄ hs₄ hbelow
    exact scaledPrefix_return hn hstate hbelow hl.2.2 hp (τ.shift m.pos)

end NLAlib.LU
