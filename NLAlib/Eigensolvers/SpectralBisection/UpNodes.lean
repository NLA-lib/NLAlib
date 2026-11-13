/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpNodeTotal
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# Total upward reconstruction over a complete level

The executed size queries visit every slot. A prefix-sensitive independent-loop rule keeps
future stored node inputs intact, including leaf outputs that need no reconstruction calls.
Each occupied slot returns its ordinary mathematical assembled result, and empty slots read
no output cells.

## Main results

* `NLAlib.SpectralBisection.writes_upNodes`: total reconstruction of all mathematical node results.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Actual upward iteration returns every node's assembled mathematical result. The spatial
hypotheses protect sizes, shifts, future node inputs and child outputs from earlier parent
writes. All node operation contracts and metadata bounds are explicit. -/
theorem writes_upNodes {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has MatrixOp Op] [Has IdxTst Tst] {M : Machine K} {dec : K → ℝ}
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {m : Mem K}
    {n d : ℕ} {R : K} {ma ua qa ea sz kd kp t : ℕ × ℕ}
    (ks : ℕ → ℕ) (ws : ℕ → K) (steps : ∀ lo, EighStep K (ks lo))
    (children : (lo : ℕ) → (b : Bool) →
      Matrix (Fin ((steps lo).childSize b)) (Fin ((steps lo).childSize b)) (K × K) ×
        (Fin ((steps lo).childSize b) → K))
    (hl : m.Live [ua, qa, ea, sz, kd, kp, t])
    (hSizes : m.store.HoldsVec sz.1 (sz.2 + n * d) n ws)
    (hDecode : ∀ lo < n, dec (ws lo) = ks lo) (hBound : ∀ lo < n, ks lo ≤ n - lo)
    (hSteps : ∀ lo < n, 0 < ks lo → StoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) m)
    (hChildren : ∀ lo < n, 0 < ks lo → ∀ b, (steps lo).HasChild b →
      StoresResult n (d + 1) ((steps lo).childSlot lo b) ua ea (children lo b) m.store)
    (hLit : IsExactNatLit dec M (max n 4))
    (ht : m.store.readBlock t.1 t.2 2 =
      some [M.div R (M.lit 2), M.neg (M.div R (M.lit 2))])
    (hRoom : ∀ lo < n, m.Room (resultOperands n d lo ua ea) (resultLengths (ks lo)))
    (hApart : ∀ lo < n,
      Fp.Apart (upNodeRegions n d lo ua qa ea kd kp t) (upNodeRegionLengths n (ks lo)))
    (hDisj : ∀ lo < n, ∀ j < n, lo ≠ j →
      Fp.Disj (Fp.blocks (resultOperands n d lo ua ea) (resultLengths (ks lo)))
        (Fp.blocks (resultOperands n d j ua ea) (resultLengths (ks j))))
    (hSizesProtect : Fp.Disj (resultLevelFootprint n d ks ua ea)
      (Store.inBlock sz.1 (sz.2 + n * d) n))
    (hShiftsProtect : Fp.Disj (resultLevelFootprint n d ks ua ea) (Store.inBlock t.1 t.2 2))
    (hForward : ∀ j lo, j < lo → lo < n → 0 < ks lo →
      Fp.Disj (Fp.blocks (resultOperands n d j ua ea) (resultLengths (ks j)))
        (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp (steps lo))
          (stepOutputLengths (steps lo))))
    (hChildProtect : ∀ lo < n, ∀ b, (steps lo).HasChild b →
      Fp.Disj (resultLevelFootprint n d ks ua ea)
        (Fp.blocks (resultOperands n (d + 1) ((steps lo).childSlot lo b) ua ea)
          (resultLengths ((steps lo).childSize b)))) :
    Writes .total I τ (upNodesImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [n, d] [ua, qa, ea, sz, kd, kp, t]) (resultLevelFootprint n d ks ua ea)
      (fun m' => m'.pos = m.pos ∧ ∀ lo < n,
        StoresResult n d lo ua ea
          ((steps lo).assemble (M.toFloatMachine dec mm qr unif normal) (children lo))
          m'.store) m := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  refine writes_loop_disjoint_prefix
    (fun lo => Fp.blocks (resultOperands n d lo ua ea) (resultLengths (ks lo)))
    (fun lo => StoresResult n d lo ua ea
      ((steps lo).assemble (M.toFloatMachine dec mm qr unif normal) (children lo)))
    rfl (fun lo hlo _ _ h => ⟨lo, hlo, h⟩) hDisj
    (fun lo _ => readsOnly_storesResult n d lo ua ea _) ?_
  intro lo hlo m' hfr
  have hfrAll : m.store.EqOff (resultLevelFootprint n d ks ua ea) m'.store :=
    hfr.mono (fun b i ⟨j, hj, hx⟩ => ⟨j, hj.trans hlo, hx⟩)
  have hsizes := hfrAll.keep (Store.readsOnly_holdsVec _ _ _ _) hSizesProtect hSizes
  have hshifts := hfrAll.keep (Store.readsOnly_readBlock _ _ _ _) hShiftsProtect ht
  have ht' : m'.store.get t.1 t.2 = some (M.div R (M.lit 2)) ∧
      m'.store.get t.1 (t.2 + 1) = some (M.neg (M.div R (M.lit 2))) := by
    constructor
    · simpa using Store.get_of_readBlock hshifts (j := 0) (by omega) default
    · simpa using Store.get_of_readBlock hshifts (j := 1) (by omega) default
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hsizes lo hlo) (hDecode lo hlo)
    (hBound lo hlo) (writes_ifPos rfl ?_)
  split_ifs with hpos
  · have hStep := (hSteps lo hlo hpos).of_eqOff hfr (by
      rintro b i ⟨j, hj, hx⟩ hy
      exact hForward j lo hj hlo hpos b i hx hy)
    have hChild : ∀ b, (steps lo).HasChild b →
        StoresResult n (d + 1) ((steps lo).childSlot lo b) ua ea (children lo b) m'.store := by
      intro b hb
      exact (hChildren lo hlo hpos b hb).of_eqOff hfrAll (hChildProtect lo hlo b hb)
    exact writes_frame rfl rfl (by room) (writes_upNode mm qr unif normal hS hQ hMM
      (steps lo) (children lo) hStep hChild hLit (by have := hBound lo hlo; omega)
      (by room) ht' ((hRoom lo hlo).congr hfr.len_eq) (hApart lo hlo))
  · exact ⟨rfl, storesResult_of_eq_zero (by omega) n d lo ua ea _ m'.store⟩

end NLAlib.SpectralBisection
