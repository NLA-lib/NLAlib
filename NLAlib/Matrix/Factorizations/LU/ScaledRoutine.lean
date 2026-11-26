/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledLoop
public import NLAlib.Ops.Logic.Geometry

/-!
# Full exact fixed-scale LU success

The original matrix is copied before factors are zero-filled, then its row norms are cached
in the same scoped arena as the residual. The actual weighted pivot loop records its row
choices and returns canonical factors. Singular matrices, zero row scales and order zero are
included. No unweighted bound on lower multipliers is asserted.

## Main results

* `NLAlib.LU.factorScaled_meets`: full actual fixed-initial-scale LU.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

omit [Inhabited K] [Has IndexOp Op] [Has IdxTst Tst] in
private theorem rowScales_packed_separated (n R : ℕ) :
    (rowScales (Op := Op) (Tst := Tst)).SeparatedAt [n, n] [(R, 0), (R, n * n)] := by
  apply Routine.separatedAt_of_blocks rfl
  change Fp.Apart [(R, n * n)] [n] ∧
    Fp.Disj (Fp.blocks [(R, n * n)] [n]) (Fp.blocks [(R, 0)] [n * n]) ∧
    Fp.Apart [] [] ∧ Fp.Disj ⊥ _
  refine ⟨by simp [Fp.Apart, Fp.blocks], ?_, trivial, Fp.disj_bot_left _⟩
  simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
    (Fp.disj_inBlock_of_le (b := R) (o := 0) (n := n * n) (o' := n * n)
      (n' := n) (by omega)).symm

omit [Inhabited K] in
private theorem scaledCalls_geometry {n R selected : ℕ} {L U H : ℕ × ℕ} {m : Mem K}
    (h : Geometry [L, U, H, (R, 0), (selected, 0)]
      [n * n, n * n, n, n * n + n, 1] m) :
    m.Live [(R, 0), (R, n * n)] ∧
      (rowScales (Op := Op) (Tst := Tst)).RoomAt m [n, n]
        ((rowScales (Op := Op) (Tst := Tst)).operands [n, n] [(R, 0), (R, n * n)]) ∧
      m.Live [(R, 0), L, U, H, (selected, 0)] ∧
      (scaledLoop (Op := Op) (Tst := Tst)).RoomAt m [n]
        ((scaledLoop (Op := Op) (Tst := Tst)).operands [n]
          [(R, 0), L, U, H, (selected, 0)]) := by
  obtain ⟨hL, hU, hH, hR, hs⟩ : L.1 < m.store.length ∧ U.1 < m.store.length ∧
      H.1 < m.store.length ∧ R < m.store.length ∧ selected < m.store.length := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using h.live
  obtain ⟨hLc, hUc, hHc, hRc, hsc⟩ : L.2 + n * n ≤ m.store.len L.1 ∧
      U.2 + n * n ≤ m.store.len U.1 ∧ H.2 + n ≤ m.store.len H.1 ∧
      n * n + n ≤ m.store.len R ∧ 1 ≤ m.store.len selected := by
    simpa only [Mem.room_cons, Mem.room_nil, Nat.zero_add, and_true] using h.room
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Mem.live_cons, Mem.live_nil, and_true] using And.intro hR hR
  · change n * n + n ≤ m.store.len R ∧ True
    exact ⟨hRc, trivial⟩
  · simpa only [Mem.live_cons, Mem.live_nil, and_true] using
      And.intro hR (And.intro hL (And.intro hU (And.intro hH hs)))
  · change (0 + (n * n + n) ≤ m.store.len R) ∧ (L.2 + n * n ≤ m.store.len L.1) ∧
      (U.2 + n * n ≤ m.store.len U.1) ∧ (H.2 + n ≤ m.store.len H.1) ∧
      (0 + 1 ≤ m.store.len selected) ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hRc, hLc, hUc, hHc, hsc, trivial⟩

omit [Inhabited K] in
private theorem scaledOutputs_geometry {n : ℕ} {L U H : ℕ × ℕ} {m : Mem K}
    (hl : m.Live [L, U, H]) (hr : m.Room [L, U, H] [n * n, n * n, n])
    (hLU : L.1 ≠ U.1) (hLH : L.1 ≠ H.1) (hUH : U.1 ≠ H.1) :
    Geometry [L, U, H] [n * n, n * n, n] m := by
  refine ⟨hl, hr, ?_⟩
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq,
    Fp.disj_sup_right, Fp.disj_bot_right, and_true]
  exact ⟨⟨Fp.disj_inBlock_of_ne hLU, Fp.disj_inBlock_of_ne hLH⟩,
    Fp.disj_inBlock_of_ne hUH⟩

private theorem factorScaledSpec_zero (dec : K → ℝ) (τ : Tape K) :
    (factorScaledSpec dec).post [0] τ [[]] [[], [], []] := by
  let B := (decodeMatrix dec 0 0 []).submatrix (luPivotPermutation id 0) id
  have hweighted : HasScaledPivotPrefix B 0 := by intro i; exact Fin.elim0 i
  have hlo : decodeMatrix dec 0 0 [] = luLower B := Subsingleton.elim _ _
  have hup : decodeMatrix dec 0 0 [] = luUpper B := Subsingleton.elim _ _
  refine ⟨id, fun i => Fin.elim0 i, fun i => le_rfl, hlo, hup, ?_, hweighted⟩
  have hLU := hweighted.isLU
  rw [← hlo, ← hup] at hLU
  exact hLU

/-- Every original matrix yields its actual fixed-scale pivot log and canonical LU factors.
The proof executes initialization, row-norm caching and the stored weighted loop; no input
pivots, nonsingularity, successful-run premise or hidden factor witness is required. -/
theorem factorScaled_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (factorScaled (Op := Op) (Tst := Tst)).Meets I (factorScaledSpec dec) := by
  routine_intro [n] (A, L, U, H) reads (as)
  have hcaller := scaledOutputs_geometry (by simpa using hl.2) hrooms hLU hLH hUH
  refine writes_ifPos rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    alloc as R selected
    have hAR : A.1 ≠ R := by change A.1 ≠ m.store.length + 0; omega
    have hRL : R ≠ L.1 := by change m.store.length + 0 ≠ L.1; omega
    have hRU : R ≠ U.1 := by change m.store.length + 0 ≠ U.1; omega
    have hRH : R ≠ H.1 := by change m.store.length + 0 ≠ H.1; omega
    have hRs : R ≠ selected := by change m.store.length + 0 ≠ m.store.length + 1; omega
    have hLs : L.1 ≠ selected := by change L.1 ≠ m.store.length + 1; omega
    have hUs : U.1 ≠ selected := by change U.1 ≠ m.store.length + 1; omega
    have hHs : H.1 ≠ selected := by change H.1 ≠ m.store.length + 1; omega
    call (initializeFactors_meets hI) [n] (A, (R, 0), L, U)
      as m₁ hfr₁ hpos₁ (rs, ls, us) hinit
    case' hlive =>
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change A.1 < s_R.length ∧ m.store.length < s_R.length ∧
        L.1 < s_R.length ∧ U.1 < s_R.length
      simp only [List.length_cons, List.length_nil] at hlen_R
      omega
    case' hroom =>
      change (0 + n * n ≤ s_R.len R) ∧ (L.2 + n * n ≤ s_R.len L.1) ∧
        (U.2 + n * n ≤ s_R.len U.1) ∧ True
      exact ⟨by rw [hR]; omega,
        by rw [(hbelow_R L.1 hl.2.1).1]; exact hroom.1,
        by rw [(hbelow_R U.1 hl.2.2.1).1]; exact hroom.2.1, trivial⟩
    obtain ⟨hcopy, rfl, rfl⟩ := hinit
    subst rs
    have hgeo := (hcaller.allocated hlen_R hsizes_R hbelow_R).of_eqOff hfr₁
    have hc₁ := scaledCalls_geometry (Op := Op) (Tst := Tst)
      (by simpa [List.range_succ, R, selected] using hgeo)
    call (rowScales_meets hI hcmp hM.neg (by simpa only [Rat.cast_zero] using hM.lit 0))
      [n, n] ((R, 0), (R, n * n))
      (pre := by trivial) (sep := rowScales_packed_separated (Op := Op) (Tst := Tst) n R)
      as m₂ hfr₂ hpos₂ (ss) hscale
    case' hlive => exact hc₁.1
    case' hroom => exact hc₁.2.1
    have hrs₂ : m₂.store.readBlock R 0 (n * n) = some as := by
      apply hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) _ hrs
      simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
        (Fp.disj_inBlock_of_le (b := R) (o := 0) (n := n * n)
          (o' := n * n) (n' := n) (by omega)).symm
    have hss₂ : m₂.store.readBlock R (0 + n * n) n = some ss := by
      simpa only [Nat.zero_add] using hss
    have hpacked := Store.readBlock_add hrs₂ hss₂
    have hc₂ := scaledCalls_geometry (Op := Op) (Tst := Tst)
      (by simpa [List.range_succ, R, selected] using hgeo.of_eqOff hfr₂)
    call (scaledLoop_meets hI hcmp hlit hQ hM) [n]
      ((R, 0), L, U, H, (selected, 0))
      as m₃ hfr₃ hpos₃ (rr, ls', us', hs) hout
    case' hlive => exact hc₂.2.2.1
    case' hroom => exact hc₂.2.2.2
    case' hpre =>
      have ha : as.length = n * n := Store.length_of_readBlock has
      have hs : ss.length = n := Store.length_of_readBlock hss
      have htake : (as ++ ss).take (n * n) = as := by rw [← ha, List.take_left]
      have hdrop : ((as ++ ss).drop (n * n)).take n = ss := by
        rw [← ha, List.drop_left, ← hs, List.take_length]
      refine ⟨rfl, rfl, ?_⟩
      have hd : ∀ i : Fin n, dec (vec ss i.val) = ‖decodeMatrix dec n n as i‖ := hscale
      simpa only [htake, hdrop] using hd
    intro s₃ hs₃ hbelow
    refine ⟨hpos₃.trans (hpos₂.trans hpos₁), [ls', us', hs], Mem.readBlocks_of_cons
      (Store.Below.readBlock_of hbelow hl.2.1 hls') (Mem.readBlocks_of_cons
        (Store.Below.readBlock_of hbelow hl.2.2.1 hus') (Mem.readBlocks_of_cons
          (Store.Below.readBlock_of hbelow hl.2.2.2 hhs) rfl)), ?_⟩
    have ha : as.length = n * n := Store.length_of_readBlock has
    have htake : (as ++ ss).take (n * n) = as := by rw [← ha, List.take_left]
    change (factorScaledSpec dec).post [n] (τ.shift m₂.pos)
      [(as ++ ss).take (n * n)] [ls', us', hs] at hout
    simpa only [factorScaledSpec, htake] using hout
  · rw [if_neg hn]
    have he : n = 0 := by omega
    subst n
    have ha : as = [] := List.eq_nil_of_length_eq_zero (Store.length_of_readBlock has)
    subst as
    exact ⟨rfl, [[], [], []], by simp [Mem.readBlocks, Store.readBlock_zero],
      factorScaledSpec_zero dec (τ.shift m.pos)⟩

end NLAlib.LU
