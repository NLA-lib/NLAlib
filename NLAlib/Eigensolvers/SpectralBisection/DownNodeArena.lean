/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLayout
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Node output views inside a downward level

Leaf, one-child and two-child outputs are bounded subviews of the seven output-level
reservations. The same relative-offset bounds supply both room and separation; no stored
numeric values or successful-run assumptions enter this geometry.

## Main results

* `NLAlib.SpectralBisection.node_outputs_of_downArena`: all bounded node output layouts.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private def leafParents : Fin 3 → Fin 7 := ![1, 3, 5]
private def childParents : Fin 3 → Fin 7 := ![0, 4, 5]
private def threeOffsets (n lo : ℕ) : Fin 3 → ℕ := ![2 * n * lo, lo, lo]
private def leafLengths (k : ℕ) : Fin 3 → ℕ := ![2 * (k * k), k, 1]
private def childLengths (k : ℕ) : Fin 3 → ℕ := ![2 * (k * k), 1, 1]

private theorem three_view_bounds {n lo k : ℕ} (hslot : lo + k ≤ n) (hk : 0 < k)
    (child : Bool) (i : Fin 3) :
    threeOffsets n lo i + (if child then childLengths k else leafLengths k) i ≤
      (List.ofFn fun j : Fin 7 => downArenaStride n j * n).getD
        ((if child then childParents else leafParents) i) 0 := by
  have hkk := Nat.mul_le_mul_left k (show k ≤ n by omega)
  have hn := Nat.mul_le_mul_left n hslot
  cases child <;> fin_cases i <;>
    simp [threeOffsets, leafLengths, childLengths, leafParents, childParents,
      downArenaStride] <;> nlinarith

private theorem three_parent_injective (child : Bool) :
    Function.Injective (if child then childParents else leafParents) := by
  cases child <;> decide

private theorem leaf_output_views {K : Type} {m : Mem K} {n d lo k : ℕ}
    {ma ua qa ea sz kd kp : ℕ × ℕ} (hslot : lo + k ≤ n) (hk : 0 < k)
    (hRoom : m.Room (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n))
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n)) :
    m.Room [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] ∧
    Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] := by
  have hr := hRoom.subviews leafParents (threeOffsets n lo) (leafLengths k)
    (three_view_bounds hslot hk false)
  have ha := hAP.subviews leafParents (threeOffsets n lo) (leafLengths k)
    (three_view_bounds hslot hk false)
    (fun i j hne he => False.elim (hne (three_parent_injective false he)))
  constructor
  · simpa [leafParents, threeOffsets, leafLengths, downArenaOrigins, List.ofFn_succ] using hr
  · simpa [leafParents, threeOffsets, leafLengths, downArenaOrigins, List.ofFn_succ] using ha

private theorem child_output_views {K : Type} {m : Mem K} {n d lo k : ℕ}
    {ma ua qa ea sz kd kp : ℕ × ℕ} (hslot : lo + k ≤ n) (hk : 0 < k)
    (hRoom : m.Room (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n))
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n)) :
    m.Room [(ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (sz.1, sz.2 + n * (d + 1) + lo), (kd.1, kd.2 + n * d + lo)]
      [2 * (k * k), 1, 1] ∧
    Fp.Apart [(ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (sz.1, sz.2 + n * (d + 1) + lo), (kd.1, kd.2 + n * d + lo)]
      [2 * (k * k), 1, 1] := by
  have hr := hRoom.subviews childParents (threeOffsets n lo) (childLengths k)
    (three_view_bounds hslot hk true)
  have ha := hAP.subviews childParents (threeOffsets n lo) (childLengths k)
    (three_view_bounds hslot hk true)
    (fun i j hne he => False.elim (hne (three_parent_injective true he)))
  constructor
  · simpa [childParents, threeOffsets, childLengths, downArenaOrigins, List.ofFn_succ] using hr
  · simpa [childParents, threeOffsets, childLengths, downArenaOrigins, List.ofFn_succ] using ha

private def splitParents : Fin 8 → Fin 7 := ![2, 2, 0, 0, 4, 4, 5, 6]
private def splitOffsets (n lo k r : ℕ) : Fin 8 → ℕ :=
  ![2 * n * lo, 2 * n * lo + 2 * (k * r), 2 * n * lo, 2 * n * (lo + r),
    lo, lo + r, lo, lo]
private def splitLengths (k r : ℕ) : Fin 8 → ℕ :=
  ![2 * (k * r), 2 * (k * (k - r)), 2 * (r * r), 2 * ((k - r) * (k - r)), 1, 1, 1, 1]

private theorem split_view_bounds {n lo k r : ℕ} (hslot : lo + k ≤ n)
    (hr : 0 < r) (hrk : r < k) (i : Fin 8) :
    splitOffsets n lo k r i + splitLengths k r i ≤
      (List.ofFn fun j : Fin 7 => downArenaStride n j * n).getD (splitParents i) 0 := by
  have hk : k ≤ n := by omega
  have hkk := Nat.mul_le_mul_left k hk
  have hrr := Nat.mul_le_mul_left r ((Nat.le_of_lt hrk).trans hk)
  have hmr := Nat.mul_le_mul_left (k - r) ((Nat.sub_le k r).trans hk)
  have hn := Nat.mul_le_mul_left n hslot
  have hleft := Nat.mul_le_mul_left k (Nat.le_of_lt hrk)
  have hs := Nat.add_sub_of_le (Nat.le_of_lt hrk)
  have hns := congrArg (fun x : ℕ => n * x) hs
  have hks := congrArg (fun x : ℕ => k * x) hs
  fin_cases i <;> simp [splitOffsets, splitLengths, splitParents, downArenaStride] <;> nlinarith

private theorem split_parent_separation {n lo k r : ℕ} (hr : 0 < r)
    (hrn : r ≤ n) (i j : Fin 8) (hne : i ≠ j) (he : splitParents i = splitParents j) :
    splitOffsets n lo k r i + splitLengths k r i ≤ splitOffsets n lo k r j ∨
      splitOffsets n lo k r j + splitLengths k r j ≤ splitOffsets n lo k r i := by
  have hp := congrArg Fin.val he
  have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
  clear he hne
  have hrr := Nat.mul_le_mul_left r hrn
  fin_cases i <;> fin_cases j <;>
    dsimp [splitParents, splitOffsets, splitLengths] at hp hne' ⊢ <;>
      first | omega | (left; nlinarith) | (right; nlinarith)

private theorem split_output_views {K : Type} {m : Mem K} {n d lo k r : ℕ}
    {ma ua qa ea sz kd kp : ℕ × ℕ} (hslot : lo + k ≤ n) (hr : 0 < r) (hrk : r < k)
    (hRoom : m.Room (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n))
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n)) :
    m.Room (splitOutputs n d lo k r ma qa sz kd kp) (splitOutputLengths k r) ∧
    Fp.Apart (splitOutputs n d lo k r ma qa sz kd kp) (splitOutputLengths k r) := by
  have hb := split_view_bounds hslot hr hrk
  have hs := split_parent_separation (n := n) (lo := lo) (k := k) hr (by omega)
  have hroom := hRoom.subviews splitParents (splitOffsets n lo k r) (splitLengths k r) hb
  have hap := hAP.subviews splitParents (splitOffsets n lo k r) (splitLengths k r) hb hs
  constructor
  · simpa [splitParents, splitOffsets, splitLengths, downArenaOrigins, splitOutputs,
      splitOutputLengths, List.ofFn_succ, Nat.add_assoc] using hroom
  · simpa [splitParents, splitOffsets, splitLengths, downArenaOrigins, splitOutputs,
      splitOutputLengths, List.ofFn_succ, Nat.add_assoc] using hap

/-- Every bounded node branch has capacity, separated outputs and protected readable inputs. -/
theorem node_outputs_of_downArena {K : Type} {m : Mem K} {n d lo k : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c : ℕ × ℕ}
    (hslot : lo + k ≤ n) (hk : 0 < k)
    (hRoom : m.Room (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n))
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n))
    (hRead : Fp.Disj (downLevelRegion n d ma ua qa ea sz kd kp)
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) :
    (m.Room [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
        (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] ∧
      Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
        (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] ∧
      Fp.Disj (Fp.blocks [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
        (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1])
        (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) ∧
    ∀ r ≤ k, m.Room (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r) ∧
      Fp.Apart (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r) ∧
      Fp.Disj (Fp.blocks (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r))
        (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k)) := by
  have hkn : k ≤ n := by omega
  have hlevel := downRegion_le_level (d := d) hslot ma ua qa ea sz kd kp
  have hleaf := leaf_output_views hslot hk hRoom hAP
  refine ⟨⟨hleaf.1, hleaf.2,
    hRead.mono ((leafFp_le_downRegion hkn hk ma ua qa ea sz kd kp).trans hlevel) le_rfl⟩, ?_⟩
  intro r hr
  have hprotect := hRead.mono
    ((branchFp_le_downRegion hkn hk hr ma ua qa ea sz kd kp).trans hlevel) le_rfl
  by_cases hedge : r = k ∨ r = 0
  · have hc := child_output_views hslot hk hRoom hAP
    simp only [branchOutputs, branchLengths, if_pos hedge] at hprotect ⊢
    exact ⟨hc.1, hc.2, hprotect⟩
  · have hs := split_output_views hslot (show 0 < r by omega) (show r < k by omega) hRoom hAP
    simp only [branchOutputs, branchLengths, if_neg hedge] at hprotect ⊢
    exact ⟨hs.1, hs.2, hprotect⟩

end NLAlib.SpectralBisection
