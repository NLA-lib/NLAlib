/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.ScaledConsider

/-!
# One actual scaled scan advance

A single candidate magnitude is scoped around its absolute-value computation and strict
scaled comparison. The surrounding scan retains only the incumbent magnitude and scale.

## Main results

* `NLAlib.LU.advanceScaled_meets`: actual words after one candidate advance.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst]

/-- Compute one candidate magnitude and update the three stored incumbent words. The source
and scale vectors are read only, while the single candidate word is scoped to this call. -/
def advanceScaled : Routine Op Tst :=
  routine% [n, i] (x : n, scales : n, best : 1, scale : 1, j : 1) → (best, scale, j) {
    let candidate ← alloc 1;
    run absolute [] (x[i], candidate);
    run considerScaled [i] (candidate, scales[i], best, scale, j)
  }

variable [Inhabited K]

/-- The candidate comes from the actual absolute-value call; the committed output words come
from the actual guarded scaled comparison, without a numerical model assumption. -/
def advanceScaledSpec (M : Machine K) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n, i] tape t (xs, ss, [b], [s], [j]) → ([b'], [s'], [j']) requires i < n ensures
    ∃ c : K, (absoluteSpec M dec).post [] t [[vec xs i]] [[c]] ∧
      (considerScaledSpec M dec).post [i] t
        [[c], [vec ss i], [b], [s], [j]] [[b'], [s'], [j']]

/-- The actual scoped candidate step succeeds from the primitive scalar/comparison/index
contracts. Exact ratio ordering is supplied separately by the scan's numerical proof. -/
theorem advanceScaled_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I) :
    (advanceScaled (Op := Op) (Tst := Tst)).Meets I (advanceScaledSpec M dec) := by
  routine_intro [n, i] (x, scales, best, scale, j) reads (xs, ss, bs, ts, js)
  obtain ⟨b, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hbs
  obtain ⟨t, ht, rfl⟩ := Store.readBlock_one_eq_some.mp hts
  obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hjs
  change Writes .total I τ _ (Env.frame [n, i] [x, scales, best, scale, j, best, scale, j])
    (Fp.blocks [best, scale, j] [1, 1, 1]) _ m
  alloc as candidate
  have hxc : x.1 ≠ candidate := by change x.1 ≠ m.store.length + 0; omega
  have hsc : scales.1 ≠ candidate := by change scales.1 ≠ m.store.length + 0; omega
  have hbc : best.1 ≠ candidate := by change best.1 ≠ m.store.length + 0; omega
  have htc : scale.1 ≠ candidate := by change scale.1 ≠ m.store.length + 0; omega
  have hjc : j.1 ≠ candidate := by change j.1 ≠ m.store.length + 0; omega
  have hx := Store.get_of_readBlock hxs hpre default
  have hs := Store.get_of_readBlock hss hpre default
  call (absolute_meets hI hcmp) [] ((x.1, x.2 + i), (candidate, 0))
    as m₁ hfr₁ hpos₁ (cs) hc
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change x.1 < s_candidate.length ∧ m.store.length < s_candidate.length
    simp only [List.length_singleton] at hlen_candidate
    omega
  case' hroom =>
    change 0 + 1 ≤ s_candidate.len candidate ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hcandidate.ge, trivial⟩
  obtain ⟨c, hcget, rfl⟩ := Store.readBlock_one_eq_some.mp hcs
  have hb₁ : m₁.store.get best.1 best.2 = some b := by keep
  have ht₁ : m₁.store.get scale.1 scale.2 = some t := by keep
  have hw₁ : m₁.store.get j.1 j.2 = some w := by keep
  have hs₁ : m₁.store.get scales.1 (scales.2 + i) = some (vec ss i) := by keep
  call (considerScaled_meets hI hcmp hlit) [i]
    ((candidate, 0), (scales.1, scales.2 + i), best, scale, j)
    as m₂ hfr₂ hpos₂ (bs', ts', js') hpost
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨Store.lt_length_of_get hcget, Store.lt_length_of_get hs₁,
      Store.lt_length_of_get hb₁, Store.lt_length_of_get ht₁, Store.lt_length_of_get hw₁⟩
  obtain ⟨b', hb', rfl⟩ := Store.readBlock_one_eq_some.mp hbs'
  obtain ⟨t', ht', rfl⟩ := Store.readBlock_one_eq_some.mp hts'
  obtain ⟨w', hw', rfl⟩ := Store.readBlock_one_eq_some.mp hjs'
  intro s₂ hs₂ hbelow
  refine ⟨hpos₂.trans hpos₁, [[b'], [t'], [w']],
    Mem.readBlocks_of_cons (Store.Below.readBlock_of hbelow hl.2.2.1 hbs')
      (Mem.readBlocks_of_cons (Store.Below.readBlock_of hbelow hl.2.2.2.1 hts')
        (Mem.readBlocks_of_cons (Store.Below.readBlock_of hbelow hl.2.2.2.2 hjs') rfl)), ?_⟩
  exact ⟨c, hc, hpost⟩

end NLAlib.LU
