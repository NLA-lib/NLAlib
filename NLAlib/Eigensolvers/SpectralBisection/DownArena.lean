/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ArenaLayout
public import NLAlib.Eigensolvers.SpectralBisection.DownLayout
public import NLAlib.Eigensolvers.SpectralBisection.LevelInput
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Downward views of the complete bisection arenas

The seven output levels are subviews of the eleven allocated solver arenas. The same indexed
containment argument supplies their capacities and separation. Node and preparation geometry
consume these ordinary spatial facts, independently of any stored numerical values.

## Main results

* `NLAlib.SpectralBisection.apart_downArena`: separated arenas give separated output levels.
* `NLAlib.SpectralBisection.room_downArena`: arena capacities cover downward output levels.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Relative offsets of the seven downward output levels in their parent solver arenas. -/
def downArenaOffsets (n d : ℕ) : Fin 7 → ℕ :=
  ![2 * (n * n) * (d + 1), 2 * (n * n) * d, 2 * (n * n) * d,
    n * d, n * (d + 1), n * d, n * d]

/-- Each downward output level fits its parent arena throughout the prescribed depth range. -/
theorem downArenaOffsets_add_le {n L d : ℕ} (hd : d ≤ L) (i : Fin 7) :
    downArenaOffsets n d i + downArenaStride n i * n ≤
      (arenaLengths n L).getD (i.val + 1) 0 := by
  have hM := Nat.mul_le_mul_left (2 * (n * n)) (show d + 2 ≤ L + 2 by omega)
  have hQ := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ L + 1 by omega)
  have hS := Nat.mul_le_mul_left n (show d + 2 ≤ L + 2 by omega)
  have hK := Nat.mul_le_mul_left n (show d + 1 ≤ L + 1 by omega)
  fin_cases i <;> simp [downArenaOffsets, downArenaStride, arenaLengths] <;> nlinarith

variable {K : Type} {m : Mem K} {n L d : ℕ}
  {c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ}

/-- Apartness of the complete arenas supplies all seven output-level separation facts. -/
theorem apart_downArena (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n) := by
  let parent : Fin 7 → Fin (min
      (arenaOperands c ma ua qa ea sz kd kp lv su sg).length (arenaLengths n L).length) :=
    fun i => ⟨i.val + 1, by simp [arenaOperands, arenaLengths]; omega⟩
  have hv := h.subviews parent (downArenaOffsets n d) (fun i => downArenaStride n i * n)
    (fun i => downArenaOffsets_add_le hd i) (by
      intro a b hab he
      have hv := congrArg Fin.val he
      apply False.elim
      apply hab
      apply Fin.ext
      dsimp [parent] at hv
      omega)
  simpa [parent, arenaOperands, downArenaOrigins, downArenaOffsets, List.ofFn_succ] using hv

/-- Capacity of the complete arenas supplies capacity for every downward output level. -/
theorem room_downArena (hd : d ≤ L)
    (h : m.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    m.Room (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n) := by
  let parent : Fin 7 → Fin (min
      (arenaOperands c ma ua qa ea sz kd kp lv su sg).length (arenaLengths n L).length) :=
    fun i => ⟨i.val + 1, by simp [arenaOperands, arenaLengths]; omega⟩
  have hv := h.subviews parent (downArenaOffsets n d) (fun i => downArenaStride n i * n)
    (fun i => downArenaOffsets_add_le hd i)
  simpa [parent, arenaOperands, downArenaOrigins, downArenaOffsets, List.ofFn_succ] using hv

/-- The seven output arenas form a separated parent collection for every level. -/
theorem apart_outputArenas
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Apart [ma, ua, qa, ea, sz, kd, kp]
      (List.ofFn fun i : Fin 7 => (arenaLengths n L).getD (i.val + 1) 0) := by
  have ht := (h.take_drop (by rfl) 1).2.1
  have hp := (ht.take_drop (by simp [arenaOperands, arenaLengths]) 7).1
  simpa [arenaOperands, arenaLengths, List.ofFn_succ] using hp

/-- A downward origin is its parent arena capability shifted by the indexed level offset. -/
theorem downArenaOrigins_eq_parent_add (i : Fin 7) :
    downArenaOrigins n d ma ua qa ea sz kd kp i =
      ((![ma, ua, qa, ea, sz, kd, kp] i).1,
        (![ma, ua, qa, ea, sz, kd, kp] i).2 + downArenaOffsets n d i) := by
  fin_cases i <;> rfl

/-- An indexed output-level region is a view of its complete parent arena. -/
theorem downArena_le_parent (hd : d ≤ L) (i : Fin 7) :
    Store.inBlock (downArenaOrigins n d ma ua qa ea sz kd kp i).1
      (downArenaOrigins n d ma ua qa ea sz kd kp i).2 (downArenaStride n i * n) ≤
      Store.inBlock (![ma, ua, qa, ea, sz, kd, kp] i).1
        (![ma, ua, qa, ea, sz, kd, kp] i).2
        ((arenaLengths n L).getD (i.val + 1) 0) := by
  rw [downArenaOrigins_eq_parent_add]
  apply Fp.inBlock_le_inBlock (Nat.le_add_right _ _)
  simpa only [Nat.add_assoc] using
    Nat.add_le_add_left (downArenaOffsets_add_le (n := n) hd i)
      (![ma, ua, qa, ea, sz, kd, kp] i).2

/-- Corresponding output roles at different levels have disjoint word intervals. -/
theorem disj_downArena_of_lt {e : ℕ} (he : e < d) (i : Fin 7) :
    Fp.Disj
      (Store.inBlock (downArenaOrigins n e ma ua qa ea sz kd kp i).1
        (downArenaOrigins n e ma ua qa ea sz kd kp i).2 (downArenaStride n i * n))
      (Store.inBlock (downArenaOrigins n d ma ua qa ea sz kd kp i).1
        (downArenaOrigins n d ma ua qa ea sz kd kp i).2 (downArenaStride n i * n)) := by
  revert i
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, downArenaOrigins, downArenaStride,
    Matrix.cons_val_zero, Matrix.cons_val_succ, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.mul_assoc] using
      Fp.disj_inBlock_strided ma.1 ma.2 (2 * (n * n)) (Nat.succ_lt_succ he)
  · simpa only [Nat.mul_assoc] using Fp.disj_inBlock_strided ua.1 ua.2 (2 * (n * n)) he
  · simpa only [Nat.mul_assoc] using Fp.disj_inBlock_strided qa.1 qa.2 (2 * (n * n)) he
  · simpa only [one_mul] using Fp.disj_inBlock_strided ea.1 ea.2 n he
  · simpa only [one_mul] using Fp.disj_inBlock_strided sz.1 sz.2 n (Nat.succ_lt_succ he)
  · simpa only [one_mul] using Fp.disj_inBlock_strided kd.1 kd.2 n he
  · simpa only [one_mul] using Fp.disj_inBlock_strided kp.1 kp.2 n he

/-- Different downward levels write separated output regions, including child storage. -/
theorem disj_downLevelRegion_of_lt {e : ℕ} (he : e < d) (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (downLevelRegion n e ma ua qa ea sz kd kp)
      (downLevelRegion n d ma ua qa ea sz kd kp) := by
  have hp : Fp.Apart (List.ofFn (![ma, ua, qa, ea, sz, kd, kp] : Fin 7 → ℕ × ℕ))
      (List.ofFn fun i : Fin 7 => (arenaLengths n L).getD (i.val + 1) 0) := by
    simpa [List.ofFn_succ] using apart_outputArenas h
  apply hp.disj_view_collections
  · exact downArena_le_parent (by omega)
  · exact downArena_le_parent hd
  · exact disj_downArena_of_lt he

/-- Every downward output level lies in the complete seven output arenas. -/
theorem downLevelRegion_le_outputArenas (hd : d ≤ L) :
    downLevelRegion n d ma ua qa ea sz kd kp ≤
      Fp.blocks [ma, ua, qa, ea, sz, kd, kp]
        (List.ofFn fun i : Fin 7 => (arenaLengths n L).getD (i.val + 1) 0) := by
  apply Fp.blocks_ofFn_le
  intro i
  refine (downArena_le_parent hd i).trans ?_
  simpa [List.ofFn_succ] using Fp.inBlock_ofFn_le_blocks
    (![ma, ua, qa, ea, sz, kd, kp] : Fin 7 → ℕ × ℕ)
    (fun j => (arenaLengths n L).getD (j.val + 1) 0) i

/-- Updating parameters and batches preserves all output words of every level. -/
theorem disj_downSamples_outputArenas (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2 ⊔
      (Store.inBlock su.1 su.2 n ⊔ Store.inBlock sg.1 sg.2 (4 * (n * n))))
      (Fp.blocks [ma, ua, qa, ea, sz, kd, kp]
        (List.ofFn fun i : Fin 7 => (arenaLengths n L).getD (i.val + 1) 0)) := by
  have ht := (h.take_drop (by rfl) 1).2.1
  have hc := (ht.take_drop (by simp [arenaOperands, arenaLengths]) 7).2.2
  have hc' : Fp.Disj
      (Fp.blocks [ma, ua, qa, ea, sz, kd, kp]
        (List.ofFn fun i : Fin 7 => (arenaLengths n L).getD (i.val + 1) 0))
      (Fp.blocks [lv, su, sg] [2 * (L + 2), n, 4 * (n * n)]) := by
    simpa [arenaOperands, arenaLengths, List.ofFn_succ] using hc
  exact hc'.symm.mono (by fp_sub) le_rfl

/-- A completed earlier level's outputs survive the complete caller-owned effect of a later
downward level, including its parameter update and replacement sample batches. -/
theorem disj_downLevelOutputFp_previous {e : ℕ} (he : e < d) (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp)
      (downLevelRegion n e ma ua qa ea sz kd kp) :=
  Fp.disj_sup_left.mpr
    ⟨(disj_downSamples_outputArenas hd h).mono le_rfl
        (downLevelRegion_le_outputArenas (by omega)),
      (disj_downLevelRegion_of_lt he hd h).symm⟩

private def downOutputViews (n d : ℕ) : Fin 10 → Fin 11 × ℕ × ℕ :=
  ![(8, 2 * (d + 1), 2), (9, 0, n), (10, 0, 4 * (n * n)),
    (1, 2 * (n * n) * (d + 1), 2 * (n * n)),
    (2, 2 * (n * n) * d, 2 * (n * n)),
    (3, 2 * (n * n) * d, 2 * (n * n)),
    (4, n * d, n), (5, n * (d + 1), n), (6, n * d, n), (7, n * d, n)]

private theorem downOutputViews_bound (hd : d ≤ L) (i : Fin 10) :
    (downOutputViews n d i).2.1 + (downOutputViews n d i).2.2 ≤
      (arenaLengths n L).getD (downOutputViews n d i).1 0 := by
  have hM := Nat.mul_le_mul_left (2 * (n * n)) (show d + 2 ≤ L + 2 by omega)
  have hQ := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ L + 1 by omega)
  have hS := Nat.mul_le_mul_left n (show d + 2 ≤ L + 2 by omega)
  have hK := Nat.mul_le_mul_left n (show d + 1 ≤ L + 1 by omega)
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hM hQ hS hK
  fin_cases i <;>
    dsimp [downOutputViews, arenaLengths] <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.zero_add] <;>
    (try ring_nf at hM hQ hS hK ⊢) <;> omega

private def inputViews (n e : ℕ) : Fin 3 → Fin 11 × ℕ × ℕ :=
  ![(1, 2 * (n * n) * e, 2 * (n * n)), (5, n * e, max n 1), (8, 2 * e, 2)]

private theorem inputViews_bound {e : ℕ} (he : e ≤ L) (i : Fin 3) :
    (inputViews n e i).2.1 + (inputViews n e i).2.2 ≤
      (arenaLengths n L).getD (inputViews n e i).1 0 := by
  have hM := Nat.mul_le_mul_left (2 * (n * n)) (show e + 1 ≤ L + 2 by omega)
  have hS := Nat.mul_le_mul_left n (show e + 1 ≤ L + 2 by omega)
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at hM hS
  fin_cases i <;> dsimp [inputViews, arenaLengths]
    <;> simp only [List.getD_cons_zero, List.getD_cons_succ]
  · simpa [Nat.mul_add, Nat.mul_assoc] using hM
  · by_cases hn : n = 0
    · simp [hn]
    · rw [max_eq_left (by omega)]
      simpa only [Nat.mul_add, Nat.mul_one] using hS.trans (Nat.le_add_right _ 1)
  · omega

/-- A level's caller-owned writes preserve every earlier or current level's mathematical
inputs. The size footprint includes the initialized root word when the dimension is zero. -/
theorem disj_downLevelOutputFp_levelInput {e : ℕ} (he : e ≤ d) (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp)
      (levelInputFp n e ma sz lv) := by
  have hsep (i : Fin 10) (j : Fin 3)
      (hp : (downOutputViews n d i).1 = (inputViews n e j).1) :
      (downOutputViews n d i).2.1 + (downOutputViews n d i).2.2 ≤
          (inputViews n e j).2.1 ∨
        (inputViews n e j).2.1 + (inputViews n e j).2.2 ≤
          (downOutputViews n d i).2.1 := by
    have hM := Nat.mul_le_mul_left (2 * (n * n)) he
    have hS := Nat.mul_le_mul_left n he
    simp only [Nat.mul_assoc] at hM hS
    have hpn := congrArg Fin.val hp
    fin_cases i <;> fin_cases j <;> dsimp [downOutputViews, inputViews] at hp ⊢ <;>
      dsimp [downOutputViews, inputViews] at hpn <;> try (exfalso; omega)
    · omega
    · right
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
      omega
    · by_cases hn : n = 0
      · simp [hn]
      · right
        rw [max_eq_left (by omega)]
        simp only [Nat.mul_add, Nat.mul_one]
        omega
  have hv := h.disj_subviews
    (fun i => (downOutputViews n d i).1) (fun j => (inputViews n e j).1)
    (fun i => (downOutputViews n d i).2.1) (fun i => (downOutputViews n d i).2.2)
    (fun j => (inputViews n e j).2.1) (fun j => (inputViews n e j).2.2)
    (downOutputViews_bound hd) (inputViews_bound (he.trans hd)) hsep
  simpa [downOutputViews, inputViews, arenaOperands, downLevelOutputFp, downLevelRegion,
    levelInputFp, downArenaOrigins, downArenaStride, List.ofFn_succ, Fp.blocks,
    sup_assoc, Nat.mul_assoc] using hv

/-- Future size levels remain initialized until their parent level executes. -/
theorem disj_downLevelOutputFp_futureSizes {e : ℕ} (he : d + 2 ≤ e)
    (heL : e ≤ L + 1) (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp)
      (Store.inBlock sz.1 (sz.2 + n * e) n) := by
  have hsize : n * e + n ≤ (arenaLengths n L).getD 5 0 := by
    have hm := Nat.mul_le_mul_left n (show e + 1 ≤ L + 2 by omega)
    simpa [arenaLengths, Nat.mul_add] using hm.trans (Nat.le_add_right _ 1)
  have hsep (i : Fin 10) (_ : Fin 1) (hp : (downOutputViews n d i).1 = 5) :
      (downOutputViews n d i).2.1 + (downOutputViews n d i).2.2 ≤ n * e ∨
        n * e + n ≤ (downOutputViews n d i).2.1 := by
    have hm := Nat.mul_le_mul_left n he
    have hpn := congrArg Fin.val hp
    fin_cases i <;> dsimp [downOutputViews] at hpn ⊢ <;> try (exfalso; omega)
    left
    simpa [Nat.mul_add, Nat.mul_two, Nat.add_assoc] using hm
  have hv := h.disj_subviews
    (fun i => (downOutputViews n d i).1) (fun _ : Fin 1 => (5 : Fin 11))
    (fun i => (downOutputViews n d i).2.1) (fun i => (downOutputViews n d i).2.2)
    (fun _ => n * e) (fun _ => n)
    (downOutputViews_bound hd) (fun _ => hsize) hsep
  simpa [downOutputViews, arenaOperands, downLevelOutputFp, downLevelRegion,
    downArenaOrigins, downArenaStride, List.ofFn_succ, Fp.blocks, sup_assoc,
    Nat.mul_assoc] using hv

/-- The complete caller-owned level effect remains inside the allocated arenas. -/
theorem downLevelOutputFp_le_arenas (hd : d ≤ L) :
    downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp ≤
      Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L) := by
  have hv := Fp.blocks_subviews_le
    (zs := arenaOperands c ma ua qa ea sz kd kp lv su sg) (ls := arenaLengths n L)
    (fun i => (downOutputViews n d i).1)
    (fun i => (downOutputViews n d i).2.1) (fun i => (downOutputViews n d i).2.2)
    (downOutputViews_bound hd)
  simpa [downOutputViews, arenaOperands, downLevelOutputFp, downLevelRegion,
    downArenaOrigins, downArenaStride, List.ofFn_succ, Fp.blocks, sup_assoc,
    Nat.mul_assoc] using hv

/-- Level arithmetic and outputs preserve the shared constant words. -/
theorem disj_downLevelOutputFp_constants (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp)
      (Store.inBlock c.1 c.2 5) := by
  have hv := h.disj_subviews
    (fun i => (downOutputViews n d i).1) (fun _ : Fin 1 => (0 : Fin 11))
    (fun i => (downOutputViews n d i).2.1) (fun i => (downOutputViews n d i).2.2)
    (fun _ => 0) (fun _ => 5)
    (downOutputViews_bound hd) (fun _ => le_rfl) (by
      intro i _ hp
      have hpn := congrArg Fin.val hp
      fin_cases i <;> dsimp [downOutputViews] at hpn <;> omega)
  simpa [downOutputViews, arenaOperands, downLevelOutputFp, downLevelRegion,
    downArenaOrigins, downArenaStride, List.ofFn_succ, Fp.blocks, sup_assoc,
    Nat.mul_assoc] using hv

/-- Scanning nodes preserves both complete stored sampling batches. -/
theorem disj_downLevelRegion_batches (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (downLevelRegion n d ma ua qa ea sz kd kp)
      (Store.inBlock su.1 su.2 n ⊔ Store.inBlock sg.1 sg.2 (4 * (n * n))) := by
  have ht := (h.take_drop (by rfl) 1).2.1
  have hc := (ht.take_drop (by simp [arenaOperands, arenaLengths]) 7).2.2
  have hc' : Fp.Disj
      (Fp.blocks [ma, ua, qa, ea, sz, kd, kp]
        (List.ofFn fun i : Fin 7 => (arenaLengths n L).getD (i.val + 1) 0))
      (Fp.blocks [lv, su, sg] [2 * (L + 2), n, 4 * (n * n)]) := by
    simpa [arenaOperands, arenaLengths, List.ofFn_succ] using hc
  exact hc'.mono (downLevelRegion_le_outputArenas hd) (by fp_sub)

/-- Every node's actual readable inputs are protected from the entire output-level scan. -/
theorem disj_downLevelRegion_nodeInputs {par : ℕ × ℕ} {lo k : ℕ}
    (hlo : lo < n) (hslot : lo + k ≤ n) (hd : d ≤ L)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hPar : Fp.Disj
      (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
      (Store.inBlock par.1 par.2 3)) :
    Fp.Disj (downLevelRegion n d ma ua qa ea sz kd kp)
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k)) := by
  have hsub : downLevelRegion n d ma ua qa ea sz kd kp ≤
      downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp := le_sup_right
  have hkeep := Fp.disj_sup_right.mpr
    ⟨hPar.mono (hsub.trans (downLevelOutputFp_le_arenas hd)) le_rfl,
      Fp.disj_sup_right.mpr ⟨(disj_downLevelOutputFp_constants hd h).mono hsub le_rfl,
        Fp.disj_sup_right.mpr
          ⟨(disj_downLevelOutputFp_levelInput le_rfl hd h).mono hsub le_rfl,
            disj_downLevelRegion_batches hd h⟩⟩⟩
  refine hkeep.mono le_rfl ?_
  have hmat : Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo)
      (2 * (k * k)) ≤ Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d) (2 * (n * n)) := by
    apply Fp.inBlock_le_inBlock (by omega)
    have hk : k ≤ n := by omega
    have hsq := Nat.mul_le_mul_left k hk
    have hs := Nat.mul_le_mul_left n hslot
    nlinarith
  have hg : 2 * ((2 * n) * n) = 4 * (n * n) := by ring
  simp only [nodeInputs, nodeInputLengths, Fp.blocks_cons, Fp.blocks_nil,
    sup_le_iff, bot_le, and_true]
  repeat' constructor
  all_goals first
    | exact hmat.trans (by fp_sub [levelInputFp])
    | fp_sub [levelInputFp, hg]

/-- Completed slot reservations and a fresh scalar scratch word preserve every pending
size query and active node input. Freshness is a buffer-handle bound, so no input capacity
arithmetic is needed to protect the reads from scratch. -/
theorem disj_downPrefix_pending {par t : ℕ × ℕ} {ks : ℕ → ℕ}
    (hd : d ≤ L) (hslot : ∀ lo < n, lo + ks lo ≤ n)
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hPar : Fp.Disj
      (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
      (Store.inBlock par.1 par.2 3))
    (hl : m.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
    (ht : m.store.length ≤ t.1) (lo : ℕ) (hlo : lo < n) :
    Fp.Disj
      (Fp.loopPrefix (fun j => downRegion n d j (ks j) ma ua qa ea sz kd kp) lo ⊔
        Store.inBlock t.1 (t.2 + 4) 1)
      (Store.inBlock sz.1 (sz.2 + n * d + lo) 1 ⊔
        if 0 < ks lo then
          Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo))
        else ⊥) := by
  have hprefix : Fp.loopPrefix (fun j => downRegion n d j (ks j)
      ma ua qa ea sz kd kp) lo ≤ downLevelRegion n d ma ua qa ea sz kd kp := by
    rintro b i ⟨j, hj, hc⟩
    exact downRegion_le_level (hslot j (by omega)) ma ua qa ea sz kd kp b i hc
  have hInputs : m.Live (nodeInputs n d lo par lv su sg ma c) := by
    apply live_nodeInputs
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    tauto
  have hsz : sz.1 < m.store.length := hl sz (by simp)
  have hReads : ∀ z ∈ (sz.1, sz.2 + n * d + lo) ::
      nodeInputs n d lo par lv su sg ma c, z.1 < t.1 := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hsz.trans_le ht
    · exact (hInputs z hz).trans_le ht
  have hFresh := (Fp.blocks_disj_above (ls := 1 :: nodeInputLengths n (ks lo)) hReads).symm
  have hScratch : Store.inBlock t.1 (t.2 + 4) 1 ≤ Fp.above t.1 := by
    rintro b i ⟨rfl, _, _⟩
    exact le_rfl
  have hLevel := (disj_downLevelOutputFp_levelInput le_rfl hd h).mono
    le_sup_right (G' := Store.inBlock sz.1 (sz.2 + n * d + lo) 1)
    (by fp_sub [levelInputFp])
  have hNode := disj_downLevelRegion_nodeInputs hlo (hslot lo hlo) hd h hPar
  have hTarget : (Store.inBlock sz.1 (sz.2 + n * d + lo) 1 ⊔
      if 0 < ks lo then
        Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo))
      else ⊥) ≤
      Store.inBlock sz.1 (sz.2 + n * d + lo) 1 ⊔
        Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)) := by
    apply sup_le_sup_left
    split_ifs <;> first | exact le_rfl | exact bot_le
  exact Fp.disj_sup_left.mpr
    ⟨(Fp.disj_sup_right.mpr ⟨hLevel, hNode⟩).mono hprefix hTarget,
      hFresh.mono hScratch hTarget⟩

end NLAlib.SpectralBisection
