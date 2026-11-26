/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.RookInitialize

/-!
# Bounded actual rook search

The initialized incumbent continues only when the actual row score is strictly larger than
its column score. The cap is one less than the number of active columns. The finite visited
witness proves that the comparison is false at the cap, so termination supplies both rook
maxima. No successful run, computed pivot or host-selected stopping point is assumed.

## Main results

* `NLAlib.LU.rookSearch_meets`: total bounded search from the actual initialization contract.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Continue only on a strict stored score improvement. Three state words are updated but
unreported; the caller receives the actual incumbent pair when the bounded search stops. -/
def rookSearch : Routine Op Tst :=
  routine% [n, k] (R : n * n, best : 1, rowMaximum : 1, candidate : 1, p : 2) →
      (unreported best, unreported rowMaximum, unreported candidate, p) {
    while step < n - k - 1, (Has.inj CmpTst.lt) [] (best, rowMaximum) {
      run rookAdvance [n, k] (R, candidate, best, rowMaximum, p)
    } then {
      skip
    }
  }

variable [Inhabited K]

/-- Initialization supplies the actual stored state. The search returns the actual pair with
both active row and column maximality and its first maximal row in the selected column. -/
def rookSearchSpec (dec : K → ℝ) (bound : ℕ) : Routine.Spec K where
  pre dims t inputs := match dims, inputs with
    | [n, k], [rs, [b], [a], [d], [r, c]] =>
      k < n ∧ n ≤ bound ∧
        (rookInitializeSpec dec bound).post [n, k] t [rs] [[r, c], [b], [a], [d]]
    | _, _ => False
  post dims t inputs outputs := match inputs with
    | [rs, _, _, _, _] => (rookChoiceSpec dec bound).post dims t [rs] outputs
    | _ => False

/-- The bounded alternating search executes from its actual initialized state. Strict growth
visits a fresh active column each time, so reaching the cap rules out another improvement.
The source is read only and all reported indices are taken from stored words. -/
theorem rookSearch_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    {u : ℝ} {bound : ℕ} (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hlit : IsIndexLit M I) (hQ : IsToNat dec I) (hM : StdModel u dec M)
    (hNat : IsExactNatLit dec M bound) :
    (rookSearch (Op := Op) (Tst := Tst)).Meets I (rookSearchSpec dec bound) := by
  routine_intro [n, k] (R, best, rowMaximum, candidate, p) reads (rs, bs, ass, ds, ps)
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨a, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hass
  obtain ⟨d, hd, rfl⟩ := Store.readBlock_one_eq_some.mp hds
  obtain ⟨r, c, rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hps)
  obtain ⟨hkn, hnb, hinit⟩ := hpre
  have hpr : m.store.get p.1 p.2 = some r := by
    simpa using Store.get_of_readBlock hps (by omega : 0 < 2) default
  have hpc : m.store.get p.1 (p.2 + 1) = some c := by
    simpa using Store.get_of_readBlock hps (by omega : 1 < 2) default
  let pivot : Fin n := ⟨k, hkn⟩
  have hstart := IsRookPrefix.of_initialize_post dec rs pivot hinit hb ha hd hpr hpc
  let F := Fp.blocks [best, rowMaximum, candidate, p] [1, 1, 1, 2]
  let P : Mem K → Prop := fun μ => μ.pos = m.pos ∧ ∃ ys,
    μ.readBlocks [p] [2] = some ys ∧
      (rookChoiceSpec dec bound).post [n, k] (τ.shift m.pos) [rs] ys
  change Writes .total I τ _
    (Env.frame [n, k] [R, best, rowMaximum, candidate, p, best, rowMaximum, candidate, p]) F P m
  refine (writes_whileFuel (N := n - k - 1) rfl (fun _ => F) (fun _ _ => le_rfl) ⊥
    (fun i μ => μ.pos = m.pos ∧ IsRookPrefix dec rs pivot i best rowMaximum candidate p μ.store)
    P ⟨rfl, hstart⟩ ?_ ?_).mono (by simp) (fun _ _ h => h)
  · intro i hi μ hfr hstate
    dsimp only [F] at hfr
    obtain ⟨hpos, hs⟩ := hstate
    obtain ⟨b, a, hb, ha⟩ := hs.exists_score_words
    rw [Interp.testAt_eq rfl rfl, hcmp.test_lt hb ha]
    apply Mode.holds_some
    by_cases hbetter : dec b < dec a
    · simp only [hbetter, decide_true, ite_true]
      obtain ⟨d, next, hd, hdd, hkd⟩ := hs.exists_candidate_word
      have hrsμ : μ.store.readBlock R.1 R.2 (n * n) = some rs := by keep
      have hdsμ := Store.readBlock_one_of_get hd
      call (rookAdvance_meets hI hcmp hlit hQ hM hNat) [n, k]
        (R, candidate, best, rowMaximum, p)
        (pre := ⟨hkn, hnb, next, hkd, hdd⟩) as μ' hfr' hpos' (ds', bs', ass', ps') hpost
      obtain ⟨d', hd', rfl⟩ := Store.readBlock_one_eq_some.mp hds'
      obtain ⟨b', hb', rfl⟩ := Store.readBlock_one_eq_some.mp hbs'
      obtain ⟨a', ha', rfl⟩ := Store.readBlock_one_eq_some.mp hass'
      obtain ⟨r', c', rfl⟩ := List.length_eq_two.mp (Store.length_of_readBlock hps')
      exact ⟨hpos'.trans hpos, IsRookPrefix.advance_of_post hs hb ha hd hbetter hpost
        hb' ha' hd' (by simpa using Store.get_of_readBlock hps' (by omega : 0 < 2) default)
        (by simpa using Store.get_of_readBlock hps' (by omega : 1 < 2) default)⟩
    · simp only [hbetter, decide_false, Bool.false_eq_true, ite_false]
      exact Writes.skip (IsRookPrefix.return_of_stop hs hb ha (le_of_not_gt hbetter)
        (Store.Below.refl μ.store.length μ.store)
        (by rw [hfr.length_eq]; exact hl.2.2.2.2) hpos _)
  · intro μ hfr ⟨hpos, hs⟩
    obtain ⟨b, a, hb, ha⟩ := hs.exists_score_words
    have hstop := hs.dec_le_of_cap
      (by change n - k ≤ n - k - 1 + 1; omega) hb ha
    exact Writes.skip (IsRookPrefix.return_of_stop hs hb ha hstop
      (Store.Below.refl μ.store.length μ.store)
        (by rw [hfr.length_eq]; exact hl.2.2.2.2) hpos _)

end NLAlib.LU
