/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ChildMath
public import NLAlib.Eigensolvers.SpectralBisection.ChildFrame
public import NLAlib.Eigensolvers.SpectralBisection.Storage

/-!
# Stored mathematical inputs at the next level

Reached children read their matrices and sizes from represented parent outcomes. Absent
children retain their initialized size words under the exact level frame. Together with the
actual next-level parameters, these facts give the same global level representation.

## Main results

* `NLAlib.SpectralBisection.StoresRecords.next_inputs`: every reached child's actual inputs.
* `NLAlib.SpectralBisection.storesLevel_succ`: the complete next-level storage invariant.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Every node reached at the next depth reads the actual packed matrix and size produced
by its reached parent's represented mathematical outcome. -/
theorem StoresRecords.next_inputs {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d lo : ℕ} {R0 beta : K} {root y : EighNode K} {path : List Bool}
    {ma ua qa ea sz kd kp : ℕ × ℕ} {m : Mem K}
    (hRecords : StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp m)
    (hlen : path.length = d + 1)
    (h : eighLoc F n fuel R0 beta 0 0 root path = some (lo, y)) :
    m.store.get sz.1 (sz.2 + n * (d + 1) + lo) = some (M.lit (y.k : ℚ)) ∧
      m.store.readBlock ma.1 (ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo)
        (2 * (y.k * y.k)) = some ((EntryCodec.pair K).packFinMatrix y.A) := by
  obtain ⟨a, side, parentLo, x, ha, _, hx, hc⟩ := eighLoc_parent F hlen h
  have hh := eighLoc_singleton_child F hc
  dsimp only at hh
  obtain ⟨hb, hslot, hy⟩ := hh
  have hp : 0 < x.k := by
    by_contra hn
    have hk : x.k ≤ 1 := by omega
    simp only [eighStep, if_pos hk, EighStep.HasChild] at hb
  have hr := (hRecords a parentLo x ha hx hp).child_inputs side hb
  subst lo
  subst y
  exact hr

/-- Represented parent outcomes and an exact level frame establish the next input level.
Only absent size cells use the initial zeros; all occupied metadata reads come from the
actual stored parent outcomes. -/
theorem storesLevel_succ {K : Type} (M : Machine K) (F : FloatMachine K ℕ ℕ)
    {n fuel d : ℕ} {R0 beta : K} {root : EighNode K} (x : ℕ → EighNode K)
    (ma ua qa ea sz kd kp lv : ℕ × ℕ) {scratch : Fp} {before after : Mem K}
    (hRecords : StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp after)
    (hZero : ∀ j < n, before.store.get sz.1 (sz.2 + n * (d + 1) + j) = some (M.lit 0))
    (hParams : after.store.readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 =
      some [(eighLevelParams F R0 root.ε root.ℓ (d + 1)).1,
        (eighLevelParams F R0 root.ε root.ℓ (d + 1)).2])
    (hReached : ∀ lo < n, 0 < (x lo).k → ∃ a : List Bool, a.length = d ∧
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x lo))
    (hPayload : ∀ lo < n, 0 < (x lo).k →
      Fp.Disj (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n)
        (stepPayloadFp n d lo ma ua qa ea sz kd kp
          (eighStep F n fuel R0 beta (x lo).A (x lo).R (x lo).ε (x lo).ℓ
            (eighTapeSample n d lo))))
    (hScratch : Fp.Disj scratch (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n))
    (hfr : before.store.EqOff
      (Fp.loopPrefix (fun lo => activeStepFp n d lo ma ua qa ea sz kd kp
        (eighStep F n fuel R0 beta (x lo).A (x lo).R (x lo).ε (x lo).ℓ
          (eighTapeSample n d lo))) n ⊔ scratch) after.store) :
    StoresLevel M F n fuel R0 beta root (d + 1) ma sz lv after := by
  refine ⟨?_, ?_, hParams⟩
  · intro path lo y hlen hy
    exact hRecords.next_inputs hlen hy
  · intro j hj hAbsent
    rw [size_get_eq_of_absent_next F x ma ua qa ea sz kd kp hj hReached hPayload
      (fun hs => hScratch _ _ hs ⟨rfl, by omega, by omega⟩) hfr hAbsent]
    exact hZero j hj

end NLAlib.SpectralBisection
