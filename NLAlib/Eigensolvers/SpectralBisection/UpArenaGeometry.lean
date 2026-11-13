/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ArenaLayout
public import NLAlib.Eigensolvers.SpectralBisection.UpReadGeometry
public import NLAlib.Eigensolvers.SpectralBisection.UpNode

/-!
# Upward reconstruction inside the allocated arenas

Root-stride slot bounds place every result in its basis and eigenvalue level. The exact arena
capacities then give room independently of stored contents. Spatial separation uses the
declared arena blocks and permits different arenas in disjoint regions of the same buffer.

## Main results

* `NLAlib.SpectralBisection.resultLevelSpan`: the two full result levels.
* `NLAlib.SpectralBisection.resultLevelFootprint_le_span`: slot payload containment.
* `NLAlib.SpectralBisection.room_result_of_arenas`: result capacities from the allocation plan.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The full basis and eigenvalue reservations for one level. -/
def resultLevelSpan (n d : ℕ) (ua ea : ℕ × ℕ) : Fp :=
  Store.inBlock ua.1 (ua.2 + 2 * (n * n) * d) (2 * (n * n)) ⊔
    Store.inBlock ea.1 (ea.2 + n * d) n

/-- Complete result arena capacities, selected from the solver's canonical allocation list. -/
def resultArenaFp (n L : ℕ) (ua ea : ℕ × ℕ) : Fp :=
  Fp.blocks [ua, ea] [(arenaLengths n L).getD 2 0, (arenaLengths n L).getD 4 0]

/-- Every valid full result level lies inside its complete allocated result arenas. -/
theorem resultLevelSpan_le_resultArenaFp {n L d : ℕ} (hd : d ≤ L + 1) (ua ea : ℕ × ℕ) :
    resultLevelSpan n d ua ea ≤ resultArenaFp n L ua ea := by
  simp only [resultLevelSpan, resultArenaFp, arenaLengths, List.getD_cons_succ,
    List.getD_cons_zero, Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq]
  apply sup_le
  · apply (Fp.inBlock_le_inBlock (by omega) ?_).trans le_sup_left
    have := Nat.mul_le_mul_left (2 * (n * n)) hd
    nlinarith
  · apply (Fp.inBlock_le_inBlock (by omega) ?_).trans le_sup_right
    have := Nat.mul_le_mul_left n hd
    nlinarith

/-- Result fields are subviews of the same slot reservation used by downward outcomes.
The statement also includes empty result slots. -/
theorem resultSlot_le_downRegion {n d lo k : ℕ} (hk : k ≤ n)
    (ma ua qa ea sz kd kp : ℕ × ℕ) :
    Fp.blocks (resultOperands n d lo ua ea) (resultLengths k) ≤
      downRegion n d lo k ma ua qa ea sz kd kp := by
  let z : Fin 7 → ℕ × ℕ := fun i =>
    ((downArenaOrigins n d ma ua qa ea sz kd kp i).1,
      (downArenaOrigins n d ma ua qa ea sz kd kp i).2 + downArenaStride n i * lo)
  let len : Fin 7 → ℕ := fun i => downArenaStride n i * k
  have hu : Store.inBlock ua.1 (ua.2 + 2 * (n * n) * d + 2 * n * lo) (2 * n * k) ≤
      downRegion n d lo k ma ua qa ea sz kd kp := by
    simpa [z, len, downRegion, downArenaOrigins, downArenaStride] using
      Fp.inBlock_ofFn_le_blocks z len (1 : Fin 7)
  have he : Store.inBlock ea.1 (ea.2 + n * d + lo) k ≤
      downRegion n d lo k ma ua qa ea sz kd kp := by
    simpa [z, len, downRegion, downArenaOrigins, downArenaStride] using
      Fp.inBlock_ofFn_le_blocks z len (3 : Fin 7)
  apply sup_le
  · refine (Fp.inBlock_le_inBlock le_rfl ?_).trans hu
    have := Nat.mul_le_mul_left k hk
    nlinarith
  · exact sup_le he bot_le

/-- Both full result fields are among the current shallow outcome reads. -/
theorem resultLevelSpan_le_upReadRegion (n d : ℕ) (ma lv ua qa ea sz kd kp c : ℕ × ℕ) :
    resultLevelSpan n d ua ea ≤ upReadRegion n d ma lv ua qa ea sz kd kp c := by
  have hspan : resultLevelSpan n d ua ea ≤ downLevelRegion n d ma ua qa ea sz kd kp := by
    simpa [resultLevelSpan, resultOperands, resultLengths, Fp.blocks, downRegion,
      downLevelRegion] using resultSlot_le_downRegion (n := n) (d := d) (lo := 0)
        (k := n) le_rfl ma ua qa ea sz kd kp
  exact hspan.trans le_sup_left

/-- Every constructor's child dimensions and slots fit the parent's root-slot interval. -/
theorem childSlot_add_childSize_le {K : Type} {n lo k : ℕ} (step : EighStep K k)
    (hslot : lo + k ≤ n) (side : Bool) : step.childSlot lo side + step.childSize side ≤ n := by
  cases step <;> cases side <;> simp only [EighStep.childSlot, EighStep.childSize] <;> omega

/-- A bounded node's result payload lies inside the full result level. -/
theorem resultSlot_le_span {n d lo k : ℕ} (hslot : lo + k ≤ n) (ua ea : ℕ × ℕ) :
    Fp.blocks (resultOperands n d lo ua ea) (resultLengths k) ≤ resultLevelSpan n d ua ea := by
  apply sup_le
  · refine (Fp.inBlock_le_inBlock (by omega) ?_).trans le_sup_left
    have hk : k ≤ n := by omega
    have hkk := Nat.mul_le_mul_left k hk
    have hn := Nat.mul_le_mul_left n hslot
    nlinarith
  · apply sup_le
    · exact (Fp.inBlock_le_inBlock (by omega) (by omega)).trans le_sup_right
    · exact bot_le

/-- Every valid slot's actual result cells lie in the full current result levels. -/
theorem resultLevelFootprint_le_span {n d : ℕ} {ks : ℕ → ℕ}
    (hslot : ∀ lo < n, lo + ks lo ≤ n) (ua ea : ℕ × ℕ) :
    resultLevelFootprint n d ks ua ea ≤ resultLevelSpan n d ua ea := by
  rintro b i ⟨lo, hlo, hc⟩
  exact resultSlot_le_span (hslot lo hlo) ua ea b i hc

/-- Exact arena capacities supply room for both fields of a bounded node result. -/
theorem room_result_of_arenas {K : Type} {m : Mem K} {n L d lo k : ℕ}
    (hd : d ≤ L + 1) (hslot : lo + k ≤ n)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hRoom : m.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    m.Room (resultOperands n d lo ua ea) (resultLengths k) := by
  have hu := hRoom.getD (i := 2) (by simp [arenaOperands, arenaLengths])
  have he := hRoom.getD (i := 4) (by simp [arenaOperands, arenaLengths])
  simp only [arenaOperands, arenaLengths, List.getD_cons_succ, List.getD_cons_zero] at hu he
  simp only [Mem.Room, resultOperands, resultLengths, and_true]
  constructor
  · have hk : k ≤ n := by omega
    have hkk := Nat.mul_le_mul_left k hk
    have hn := Nat.mul_le_mul_left n hslot
    have hd' := Nat.mul_le_mul_left (2 * (n * n)) hd
    nlinarith
  · have hd' := Nat.mul_le_mul_left n hd
    nlinarith

end NLAlib.SpectralBisection
