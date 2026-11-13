/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownArena
public import NLAlib.Eigensolvers.SpectralBisection.DownNodeArena
public import NLAlib.Ops.Logic.Allocation

/-!
# Preparation geometry with fresh scalar scratch

The caller's parameter block, eleven solver arenas and fresh scalar scratch form one apart
collection. Bounded views of that collection give the parameter, sample and input separation
requirements of a downward level, including shared-buffer arena layouts.

## Main results

* `NLAlib.SpectralBisection.apart_downPrepareParents`: extend caller separation with scratch.
* `NLAlib.SpectralBisection.apart_downPrepareArena`: separated arithmetic and sample operands.
* `NLAlib.SpectralBisection.disj_downPrepareArena_read`: preparation retains all node sources.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Parameter input, solver arenas and scalar scratch, in parent-view order. -/
def downPrepareParents (par c ma ua qa ea sz kd kp lv su sg t : ℕ × ℕ) : List (ℕ × ℕ) :=
  (par :: arenaOperands c ma ua qa ea sz kd kp lv su sg) ++ [t]

/-- Capacities corresponding to the preparation parent collection. -/
def downPrepareLengths (n L : ℕ) : List ℕ := (3 :: arenaLengths n L) ++ [5]

private def prepViews (n d : ℕ) : Fin 18 → Fin 13 × ℕ × ℕ :=
  ![(1, 0, 3), (9, 2 * d, 2), (9, 2 * (d + 1), 2), (10, 0, n),
    (11, 0, 4 * (n * n)), (12, 0, 4), (0, 0, 3),
    (2, 2 * (n * n) * d, 2 * (n * n)), (6, n * d, n), (1, 0, 5),
    (2, 2 * (n * n) * (d + 1), 2 * (n * n)),
    (3, 2 * (n * n) * d, 2 * (n * n)), (4, 2 * (n * n) * d, 2 * (n * n)),
    (5, n * d, n), (6, n * (d + 1), n), (7, n * d, n), (8, n * d, n), (12, 4, 1)]

private theorem prepViews_bound {n L d : ℕ} (hd : d ≤ L) (i : Fin 18) :
    (prepViews n d i).2.1 + (prepViews n d i).2.2 ≤
      (downPrepareLengths n L).getD (prepViews n d i).1 0 := by
  have hM1 := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ L + 1 by omega)
  have hM2 := Nat.mul_le_mul_left (2 * (n * n)) (show d + 2 ≤ L + 2 by omega)
  have hS1 := Nat.mul_le_mul_left n (show d + 1 ≤ L + 1 by omega)
  have hS2 := Nat.mul_le_mul_left n (show d + 2 ≤ L + 2 by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hM1 hM2 hS1 hS2
  fin_cases i <;> simp [prepViews, downPrepareLengths, arenaLengths, Nat.mul_add] <;> omega

private def prepAddress (n d : ℕ) (par c ma ua qa ea sz kd kp lv su sg t : ℕ × ℕ)
    (i : Fin 18) : ℕ × ℕ :=
  let z := (downPrepareParents par c ma ua qa ea sz kd kp lv su sg t).getD
    (prepViews n d i).1 (0, 0)
  (z.1, z.2 + (prepViews n d i).2.1)

private theorem disj_prepViews {n L d p q : ℕ} {par c ma ua qa ea sz kd kp lv su sg t : ℕ × ℕ}
    (hd : d ≤ L)
    (hAP : Fp.Apart (downPrepareParents par c ma ua qa ea sz kd kp lv su sg t)
      (downPrepareLengths n L)) (x : Fin p → Fin 18) (y : Fin q → Fin 18)
    (hsep : ∀ i j, (prepViews n d (x i)).1 = (prepViews n d (y j)).1 →
      (prepViews n d (x i)).2.1 + (prepViews n d (x i)).2.2 ≤ (prepViews n d (y j)).2.1 ∨
      (prepViews n d (y j)).2.1 + (prepViews n d (y j)).2.2 ≤ (prepViews n d (x i)).2.1) :
    Fp.Disj
      (Fp.blocks (List.ofFn fun i => prepAddress n d par c ma ua qa ea sz kd kp lv su sg t (x i))
        (List.ofFn fun i => (prepViews n d (x i)).2.2))
      (Fp.blocks (List.ofFn fun j => prepAddress n d par c ma ua qa ea sz kd kp lv su sg t (y j))
        (List.ofFn fun j => (prepViews n d (y j)).2.2)) :=
  hAP.disj_subviews (fun i => (prepViews n d (x i)).1) (fun j => (prepViews n d (y j)).1)
    (fun i => (prepViews n d (x i)).2.1) (fun i => (prepViews n d (x i)).2.2)
    (fun j => (prepViews n d (y j)).2.1) (fun j => (prepViews n d (y j)).2.2)
    (fun i => prepViews_bound hd (x i)) (fun j => prepViews_bound hd (y j)) hsep

/-- A fresh scratch handle extends caller parameter/arena separation. -/
theorem apart_downPrepareParents {K : Type} {μ : Mem K} {n L : ℕ}
    {par c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ}
    (hl : μ.Live (par :: arenaOperands c ma ua qa ea sz kd kp lv su sg))
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hPar : Fp.Disj (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
      (arenaLengths n L)) (Store.inBlock par.1 par.2 3)) :
    Fp.Apart (downPrepareParents par c ma ua qa ea sz kd kp lv su sg (μ.store.length, 0))
      (downPrepareLengths n L) := by
  have hOld : Fp.Apart (par :: arenaOperands c ma ua qa ea sz kd kp lv su sg)
      (3 :: arenaLengths n L) := ⟨hPar.symm, hAP⟩
  apply hOld.append (by simp [Fp.Apart, Fp.blocks]) (by simp [arenaOperands, arenaLengths])
  apply (Fp.blocks_disj_above hl).mono le_rfl
  rintro b i h
  simp only [Fp.blocks, Fp.inBlock_apply, Pi.sup_apply, sup_Prop_eq, Pi.bot_apply] at h
  rcases h with ⟨rfl, _, _⟩ | h
  · exact le_rfl
  · exact False.elim h

section Views

variable {n L d : ℕ} {par c ma ua qa ea sz kd kp lv su sg t : ℕ × ℕ}
  (hd : d ≤ L)
  (hAP : Fp.Apart (downPrepareParents par c ma ua qa ea sz kd kp lv su sg t)
    (downPrepareLengths n L))

include hd hAP

/-- Parameter arithmetic and the two sample batches use separated bounded parent views. -/
theorem apart_downPrepareArena :
    Fp.Apart [c, (lv.1, lv.2 + 2 * d), (lv.1, lv.2 + 2 * (d + 1)), su, sg, t]
      [3, 2, 2, n, 4 * (n * n), 4] := by
  let x : Fin 6 → Fin 18 := ![0, 1, 2, 3, 4, 5]
  have h := hAP.subviews (fun i => (prepViews n d (x i)).1)
    (fun i => (prepViews n d (x i)).2.1) (fun i => (prepViews n d (x i)).2.2)
    (fun i => prepViews_bound hd (x i)) (by
      intro i j hij hp
      have hv := congrArg Fin.val hp
      have hij' : i.val ≠ j.val := fun he => hij (Fin.ext he)
      fin_cases i <;> fin_cases j <;> dsimp [x, prepViews] at hv hij' ⊢ <;> omega)
  simpa [x, prepViews, downPrepareParents, downPrepareLengths, arenaOperands, arenaLengths,
    List.ofFn_succ] using h

/-- The next parameters, sample blocks and scratch retain every shared readable node source. -/
theorem disj_downPrepareArena_read :
    Fp.Disj (downPrepareFp n d lv su sg t)
      (Fp.blocks [par, (lv.1, lv.2 + 2 * d), (ma.1, ma.2 + 2 * (n * n) * d),
        (sz.1, sz.2 + n * d), c] [3, 2, 2 * (n * n), n, 5]) := by
  let x : Fin 4 → Fin 18 := ![2, 5, 3, 4]
  let y : Fin 5 → Fin 18 := ![6, 1, 7, 8, 9]
  have h := disj_prepViews hd hAP x y (by
    intro i j hp
    fin_cases i <;> fin_cases j <;> simp [x, y, prepViews] at hp ⊢; omega)
  simpa [x, y, prepViews, prepAddress, downPrepareParents, arenaOperands, List.ofFn_succ,
    downPrepareFp, Fp.blocks, sup_assoc] using h

/-- All scan outputs and its last scratch cell preserve the next parameter pair. -/
theorem disj_downPrepareArena_next :
    Fp.Disj (downLevelRegion n d ma ua qa ea sz kd kp ⊔ Store.inBlock t.1 (t.2 + 4) 1)
      (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2) := by
  let x : Fin 8 → Fin 18 := ![10, 11, 12, 13, 14, 15, 16, 17]
  let y : Fin 1 → Fin 18 := ![2]
  have h := disj_prepViews hd hAP x y (by
    intro i j hp
    fin_cases i <;> fin_cases j <;> simp [x, y, prepViews] at hp)
  simpa [x, y, prepViews, prepAddress, downPrepareParents, arenaOperands, List.ofFn_succ,
    downLevelRegion, downArenaOrigins, downArenaStride, Fp.blocks, sup_assoc,
    Nat.mul_assoc] using h

/-- Shared scalar scan scratch is separate from all caller-owned output levels. -/
theorem disj_downPrepareArena_scratch :
    Fp.Disj (Store.inBlock t.1 (t.2 + 4) 1) (downLevelRegion n d ma ua qa ea sz kd kp) := by
  let x : Fin 1 → Fin 18 := ![17]
  let y : Fin 7 → Fin 18 := ![10, 11, 12, 13, 14, 15, 16]
  have h := disj_prepViews hd hAP x y (by
    intro i j hp
    fin_cases i
    fin_cases j <;> simp [x, y, prepViews] at hp)
  simpa [x, y, prepViews, prepAddress, downPrepareParents, arenaOperands, List.ofFn_succ,
    downLevelRegion, downArenaOrigins, downArenaStride, Fp.blocks, sup_assoc,
    Nat.mul_assoc] using h

/-- Preparation and all shared scratch retain the entire next size level. -/
theorem disj_downPrepareArena_size :
    Fp.Disj (downPrepareFp n d lv su sg t ⊔ Store.inBlock t.1 (t.2 + 4) 1)
      (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n) := by
  let x : Fin 5 → Fin 18 := ![2, 5, 3, 4, 17]
  let y : Fin 1 → Fin 18 := ![14]
  have h := disj_prepViews hd hAP x y (by
    intro i j hp
    fin_cases i <;> fin_cases j <;> simp [x, y, prepViews] at hp)
  simpa [x, y, prepViews, prepAddress, downPrepareParents, arenaOperands, List.ofFn_succ,
    downPrepareFp, Fp.blocks, sup_assoc] using h

end Views

/-- Fresh storage has live operands and the capacities required by preparation. -/
theorem downPrepareArena_room {K : Type} {μ : Mem K} {s : Store K} {n L d : ℕ}
    {par c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ} (hd : d ≤ L)
    (hl : μ.Live (par :: arenaOperands c ma ua qa ea sz kd kp lv su sg))
    (hr : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hlen : s.length = μ.store.length + 1) (ht : s.len μ.store.length = 5)
    (hBelow : Store.Below μ.store.length μ.store s) :
    (⟨s, 0⟩ : Mem K).Live
        [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, (μ.store.length, 0)] ∧
      0 + 5 ≤ s.len μ.store.length ∧
      lv.2 + 2 * (d + 1) + 2 ≤ s.len lv.1 ∧
      su.2 + n ≤ s.len su.1 ∧ sg.2 + 4 * (n * n) ≤ s.len sg.1 := by
  have hlv : lv.1 < μ.store.length := hl lv (by simp [arenaOperands])
  have hlu : su.1 < μ.store.length := hl su (by simp [arenaOperands])
  have hlg : sg.1 < μ.store.length := hl sg (by simp [arenaOperands])
  have hv := hr.getD (i := 8) (by simp [arenaOperands, arenaLengths])
  have hu := hr.getD (i := 9) (by simp [arenaOperands, arenaLengths])
  have hg := hr.getD (i := 10) (by simp [arenaOperands, arenaLengths])
  simp only [arenaOperands, arenaLengths, List.getD_cons_zero, List.getD_cons_succ] at hv hu hg
  refine ⟨?_, by omega, ?_, ?_, ?_⟩
  · simp only [arenaOperands, Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    omega
  · rw [(hBelow lv.1 hlv).1]; omega
  · rw [(hBelow su.1 hlu).1]; exact hu
  · rw [(hBelow sg.1 hlg).1]; exact hg

/-- Canonical solver spans and fresh five-word storage satisfy every downward level's
capacity and separation requirements. The size function appears only in its slot bounds. -/
theorem downLevelGeometry_of_arenas {K : Type} {μ : Mem K} {s : Store K} {n L d : ℕ}
    {ks : ℕ → ℕ} {par c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ} (hd : d ≤ L)
    (hslot : ∀ lo < n, lo + ks lo ≤ n)
    (hl : μ.Live (par :: arenaOperands c ma ua qa ea sz kd kp lv su sg))
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hPar : Fp.Disj (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
      (arenaLengths n L)) (Store.inBlock par.1 par.2 3))
    (hLength : s.length = μ.store.length + 1) (hTlen : s.len μ.store.length = 5)
    (hBelow : Store.Below μ.store.length μ.store s) :
    DownLevelGeometry n d ks par lv su sg ma ua qa ea sz kd kp c (μ.store.length, 0) s := by
  have hFresh := apart_downPrepareParents hl hAP hPar
  have hR := downPrepareArena_room hd hl hRoom hLength hTlen hBelow
  have hLive : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c] := by
    intro z hz
    exact hl z (by simp [arenaOperands] at hz ⊢; tauto)
  have hRoomS : (⟨s, 0⟩ : Mem K).Room
      (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L) := by
    rw [Mem.room_eq_of_below (μ := μ) (μ' := ⟨s, 0⟩) hBelow
      (fun z hz => hl z (by simp [hz]))]
    exact hRoom
  exact {
    live := hR.1
    scratch_room := hR.2.1
    prepare_apart := apart_downPrepareArena hd hFresh
    next_room := hR.2.2.1
    uniform_room := hR.2.2.2.1
    gaussian_room := hR.2.2.2.2
    prepare_read := disj_downPrepareArena_read hd hFresh
    next_disj := disj_downPrepareArena_next hd hFresh
    output_apart := apart_downArena hd hAP
    scratch_disj := disj_downPrepareArena_scratch hd hFresh
    pending := disj_downPrefix_pending hd hslot hAP hPar hLive le_rfl
    nodes := fun lo hlo hp => node_outputs_of_downArena (hslot lo hlo) hp
      (room_downArena hd hRoomS) (apart_downArena hd hAP)
      (disj_downLevelRegion_nodeInputs hlo (hslot lo hlo) hd hAP hPar)
    scratch_size := disj_downPrepareArena_size hd hFresh }

end NLAlib.SpectralBisection
