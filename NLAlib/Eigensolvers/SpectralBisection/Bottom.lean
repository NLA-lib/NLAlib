/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.BottomResult
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# Total initialization of the final bisection level

The final pass reads actual bounded node sizes and initializes every occupied slot. Its
mathematical output is the recursion-budget-zero identity and zero eigenvalues. The loop
collects ordinary output predicates over disjoint regions; no execution-state record is used.

## Main results

* `NLAlib.SpectralBisection.bottomSlotFootprint`: one node's two output regions.
* `NLAlib.SpectralBisection.writes_bottomLevel`: total initialization of every final-level node.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Actual matrix and eigenvalue payloads of one final-level node. -/
def bottomSlotFootprint (n D lo k : ℕ) (u e : ℕ × ℕ) : Fp :=
  Store.inBlock u.1 (u.2 + 2 * (n * n) * D + 2 * n * lo) (2 * (k * k)) ⊔
    Store.inBlock e.1 (e.2 + n * D + lo) k

/-- The union of the initialized node payloads, including empty slots. -/
def bottomFootprint (n D : ℕ) (ks : ℕ → ℕ) (u e : ℕ × ℕ) : Fp :=
  fun b i => ∃ lo < n, bottomSlotFootprint n D lo (ks lo) u e b i

/-- Every slot returns its actual machine identity and zero eigenvalues. Size words decode
within the explicit runtime bound; readable sizes, disjoint outputs and their capacities
suffice for total execution. The conclusion imposes no obligation on unused gaps or kinds. -/
theorem writes_bottomLevel {K Op Tst : Type} [Has ScalarOp Op] [Has IdxTst Tst]
    {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hQ : IsToNat dec I) {τ : Tape K} {m : Mem K}
    {n D : ℕ} {sz u e : ℕ × ℕ} (ks : ℕ → ℕ) (ws : ℕ → K)
    (hl : m.Live [sz, u, e])
    (hs : m.store.HoldsVec sz.1 (sz.2 + n * D) n ws)
    (hdecode : ∀ lo < n, dec (ws lo) = ks lo) (hbound : ∀ lo < n, ks lo ≤ n - lo)
    (hroom : ∀ lo < n,
      u.2 + 2 * (n * n) * D + 2 * n * lo + 2 * (ks lo * ks lo) ≤ m.store.len u.1 ∧
      e.2 + n * D + lo + ks lo ≤ m.store.len e.1)
    (hdisj : ∀ lo < n, ∀ j < n, lo ≠ j →
      Fp.Disj (bottomSlotFootprint n D lo (ks lo) u e)
        (bottomSlotFootprint n D j (ks j) u e))
    (hUE : ∀ lo < n, Fp.Disj
      (Store.inBlock u.1 (u.2 + 2 * (n * n) * D + 2 * n * lo) (2 * (ks lo * ks lo)))
      (Store.inBlock e.1 (e.2 + n * D + lo) (ks lo)))
    (hprotect : Fp.Disj (bottomFootprint n D ks u e)
      (Store.inBlock sz.1 (sz.2 + n * D) n)) :
    Writes .total I τ (bottomLevel (Op := Op) (Tst := Tst))
      (Env.frame [n, D] [sz, u, e]) (bottomFootprint n D ks u e)
      (fun m' => m'.pos = m.pos ∧ ∀ lo < n,
        BottomOutput M (ks lo) (u.1, u.2 + 2 * (n * n) * D + 2 * n * lo)
          (e.1, e.2 + n * D + lo) m'.store) m := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  refine writes_loop_disjoint
    (fun lo => bottomSlotFootprint n D lo (ks lo) u e)
    (fun lo => BottomOutput M (ks lo)
      (u.1, u.2 + 2 * (n * n) * D + 2 * n * lo) (e.1, e.2 + n * D + lo))
    rfl (fun lo hlo _ _ h => ⟨lo, hlo, h⟩) hdisj
    (fun lo _ => by
      simpa only [bottomSlotFootprint] using readsOnly_bottomOutput M (ks lo)
        (u.1, u.2 + 2 * (n * n) * D + 2 * n * lo) (e.1, e.2 + n * D + lo)) ?_
  intro lo hlo m' hfr
  have hs' := hfr.keep (Store.readsOnly_holdsVec _ _ _ _) hprotect hs
  have hc := hroom lo hlo
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hs' lo hlo) (hdecode lo hlo)
    (hbound lo hlo) ?_
  refine writes_ifPos rfl ?_
  split_ifs with hk
  · refine writes_frame rfl rfl (by room) (writes_bottomResult hS (by room)
      (by rw [hfr.len_eq]; exact hc.1) (by rw [hfr.len_eq]; exact hc.2) (hUE lo hlo))
  · have hz : ks lo = 0 := by omega
    exact ⟨rfl, by simp [BottomOutput, Store.HoldsEntries, Store.HoldsVec, hz]⟩

end NLAlib.SpectralBisection
