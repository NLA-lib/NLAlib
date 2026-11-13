/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpNodes
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.ScalarOutput

/-!
# Total upward level with computed shifts and scoped workspace

The level computes the actual rounded half-radius and its negation, reconstructs every
node from its stored outcome and child outputs, and removes its scalar workspace. Its result
is the mathematical assembly of the existing recursive bisection algorithm.

## Main results

* `NLAlib.SpectralBisection.writes_upLevel`: total stored mathematical reconstruction of one level.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- One actual upward level returns every mathematically assembled node result. The stored
radius and literal two determine its shifts through the scalar machine. All remaining
hypotheses concern actual node/child reads, decoded size bounds, output capacity and spatial
separation. Scratch is freshly allocated and removed, and the tape position is unchanged. -/
theorem writes_upLevel {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has MatrixOp Op] [Has IdxTst Tst] {M : Machine K} {dec : K → ℝ}
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {m : Mem K}
    {n d : ℕ} {R : K} {ma lv ua qa ea sz kd kp c : ℕ × ℕ}
    (ks : ℕ → ℕ) (ws : ℕ → K) (steps : ∀ lo, EighStep K (ks lo))
    (children : (lo : ℕ) → (b : Bool) →
      Matrix (Fin ((steps lo).childSize b)) (Fin ((steps lo).childSize b)) (K × K) ×
        (Fin ((steps lo).childSize b) → K))
    (hl : m.Live [lv, ua, qa, ea, sz, kd, kp, c, ma])
    (hR : m.store.get lv.1 (lv.2 + 2 * d) = some R)
    (hTwo : m.store.get c.1 (c.2 + 1) = some (M.lit 2))
    (hSizes : m.store.HoldsVec sz.1 (sz.2 + n * d) n ws)
    (hDecode : ∀ lo < n, dec (ws lo) = ks lo) (hBound : ∀ lo < n, ks lo ≤ n - lo)
    (hSteps : ∀ lo < n, 0 < ks lo → StoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) m)
    (hChildren : ∀ lo < n, 0 < ks lo → ∀ b, (steps lo).HasChild b →
      StoresResult n (d + 1) ((steps lo).childSlot lo b) ua ea (children lo b) m.store)
    (hLit : IsExactNatLit dec M (max n 4))
    (hRoom : ∀ lo < n, m.Room (resultOperands n d lo ua ea) (resultLengths (ks lo)))
    (hApart : ∀ lo < n, Fp.Apart
      (upNodeRegions n d lo ua qa ea kd kp (m.store.length, 0)) (upNodeRegionLengths n (ks lo)))
    (hDisj : ∀ lo < n, ∀ j < n, lo ≠ j →
      Fp.Disj (Fp.blocks (resultOperands n d lo ua ea) (resultLengths (ks lo)))
        (Fp.blocks (resultOperands n d j ua ea) (resultLengths (ks j))))
    (hSizesProtect : Fp.Disj (resultLevelFootprint n d ks ua ea)
      (Store.inBlock sz.1 (sz.2 + n * d) n))
    (hForward : ∀ j lo, j < lo → lo < n → 0 < ks lo →
      Fp.Disj (Fp.blocks (resultOperands n d j ua ea) (resultLengths (ks j)))
        (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp (steps lo))
          (stepOutputLengths (steps lo))))
    (hChildProtect : ∀ lo < n, ∀ b, (steps lo).HasChild b →
      Fp.Disj (resultLevelFootprint n d ks ua ea)
        (Fp.blocks (resultOperands n (d + 1) ((steps lo).childSlot lo b) ua ea)
          (resultLengths ((steps lo).childSize b)))) :
    Writes .total I τ (upLevel (Op := Op) (Tst := Tst))
      (Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c]) (resultLevelFootprint n d ks ua ea)
      (fun m' => m'.pos = m.pos ∧ ∀ lo < n, StoresResult n d lo ua ea
        ((steps lo).assemble (M.toFloatMachine dec mm qr unif normal) (children lo))
        m'.store) m := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  have hua := hl.2.1
  have hea := hl.2.2.2.1
  refine writes_allocs_preserving_post (lens := [.const 2]) (ns := [2]) rfl ?_ ?_
  · rintro s s' p hBelow ⟨hp, hr⟩
    exact ⟨hp, fun lo hlo => (hr lo hlo).of_below hBelow hua hea⟩
  intro s hs hlens hBelow
  let ρ := Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c]
  let ρt : Env := ⟨ρ.idx, ρ.buf ++ [m.store.length]⟩
  let xs : List (ScalarIns ScalarOp) :=
    [⟨.div, [⟨0, .var 2 + .const 2 * .var 1⟩, ⟨7, .var 9 + .const 1⟩], ⟨8, .const 0⟩⟩,
      ⟨.neg, [⟨8, .const 0⟩], ⟨8, .const 1⟩⟩]
  let v : ℕ → K := fun i => if i = 0 then M.div R (M.lit 2) else M.neg (M.div R (M.lit 2))
  have hT : s.len m.store.length = 2 := by simpa using hlens 0 (by simp)
  have hR₀ := ((hBelow lv.1 hl.1).2 (lv.2 + 2 * d)).trans hR
  have hTwo₀ := ((hBelow c.1 hl.2.2.2.2.2.2.2.1).2 (c.2 + 1)).trans hTwo
  have hev : ScalarIns.evalBlock M.eval ρt xs s.cellFn =
      some ((List.range 2).map fun i => ((m.store.length, 0 + i), v i)) := by
    simp [xs, v, ρt, ρ, ScalarIns.evalBlock, Operand.evalList, Operand.eval, Env.frame,
      IExp.eval, Store.cellFn, Machine.eval, hR₀, hTwo₀, List.range_succ]
  have hCall := writes_machineScalarBlock_readBlock (τ := τ) (m := ⟨s, m.pos⟩)
    (z := (m.store.length, 0)) (n := 2) (v := v) hS hev
    (show 0 + 2 ≤ s.len m.store.length by omega)
  refine Writes.seq_assoc_iff.mp ?_
  refine hCall.seq_le (Fp.inBlock_le_sup_above (by omega)) fun m₁ hfr ⟨hp, hshift⟩ => ?_
  have hBelow₁ := hBelow.trans (hfr.below_of_above (L := m.store.length) (by
    rintro b i ⟨rfl, _, _⟩
    exact le_rfl))
  have hSizes₁ := hBelow₁.keep (Store.readsOnly_holdsVec _ _ _ _) (by
    rintro b i ⟨rfl, _, _⟩
    exact hl.2.2.2.2.1) hSizes
  have hShifts : m₁.store.readBlock m.store.length 0 2 =
      some [M.div R (M.lit 2), M.neg (M.div R (M.lit 2))] := by
    simpa [v, List.range_succ] using hshift
  refine (writes_frame rfl rfl (by room) (writes_upNodes (m := m₁)
    (t := (m.store.length, 0)) mm qr unif normal hS hQ hMM
    ks ws steps children (by room) hSizes₁ hDecode hBound
    (fun lo hlo hpos => (hSteps lo hlo hpos).of_below hBelow₁
      (live_stepOutputs (m := m) (by room) (steps lo)))
    (fun lo hlo hpos b hb => (hChildren lo hlo hpos b hb).of_below hBelow₁ hua hea)
    hLit hShifts (fun lo hlo => ?_) hApart hDisj hSizesProtect ?_ hForward hChildProtect)).mono
    le_sup_left (fun _ _ h => ⟨h.1.trans hp, h.2⟩)
  · rw [Mem.room_eq_of_below hBelow₁ (by
      intro z hz
      simp only [resultOperands, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hua
      · exact hea)]
    exact hRoom lo hlo
  · exact (disj_resultLevelFootprint_above hua hea).mono le_rfl
      (fun b i h => by rcases h with ⟨rfl, _, _⟩; exact le_rfl)

end NLAlib.SpectralBisection
