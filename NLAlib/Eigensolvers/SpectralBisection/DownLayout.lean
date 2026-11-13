/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownGeometry
public import NLAlib.Eigensolvers.SpectralBisection.NodeData
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# Spatial requirements of a downward level

One storage-geometry predicate collects capacities and separation for preparation and the
active slot scan. It contains no execution phase, numerical result or successful-run premise.

## Main results

* `NLAlib.SpectralBisection.DownLevelGeometry`: reusable downward storage requirements.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The exact words written by preparation, including reusable scalar scratch. -/
def downPrepareFp (n d : ℕ) (lv su sg t : ℕ × ℕ) : Fp :=
  (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2 ⊔ Store.inBlock t.1 t.2 4) ⊔
    (Store.inBlock su.1 su.2 n ⊔ Store.inBlock sg.1 sg.2 (4 * (n * n)))

/-- The caller-owned output regions of one allocated downward level. -/
def downLevelOutputFp (n d : ℕ) (lv su sg ma ua qa ea sz kd kp : ℕ × ℕ) : Fp :=
  (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2 ⊔
    (Store.inBlock su.1 su.2 n ⊔ Store.inBlock sg.1 sg.2 (4 * (n * n)))) ⊔
    downLevelRegion n d ma ua qa ea sz kd kp

/-- Capacities and spatial separation for one level, independently of stored numeric words. -/
structure DownLevelGeometry {K : Type} (n d : ℕ) (ks : ℕ → ℕ)
    (par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ) (s : Store K) : Prop where
  /-- All caller operands are live handles. -/
  live : (⟨s, 0⟩ : Mem K).Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t]
  /-- The shared scalar scratch has five words. -/
  scratch_room : t.2 + 5 ≤ s.len t.1
  /-- Parameter operands and both batches are separated. -/
  prepare_apart : Fp.Apart
      [c, (lv.1, lv.2 + 2 * d), (lv.1, lv.2 + 2 * (d + 1)), su, sg, t]
      [3, 2, 2, n, 4 * (n * n), 4]
  /-- The next parameter pair fits. -/
  next_room : lv.2 + 2 * (d + 1) + 2 ≤ s.len lv.1
  /-- The uniform batch fits. -/
  uniform_room : su.2 + n ≤ s.len su.1
  /-- The Gaussian batch fits. -/
  gaussian_room : sg.2 + 4 * (n * n) ≤ s.len sg.1
  /-- Preparation preserves all shared readable source blocks. -/
  prepare_read : Fp.Disj (downPrepareFp n d lv su sg t)
      (Fp.blocks [par, (lv.1, lv.2 + 2 * d),
        (ma.1, ma.2 + 2 * (n * n) * d), (sz.1, sz.2 + n * d), c]
        [3, 2, 2 * (n * n), n, 5])
  /-- The scan preserves the newly computed parameter pair. -/
  next_disj : Fp.Disj (downLevelRegion n d ma ua qa ea sz kd kp ⊔
      Store.inBlock t.1 (t.2 + 4) 1) (Store.inBlock lv.1 (lv.2 + 2 * (d + 1)) 2)
  /-- The seven output levels are apart. -/
  output_apart : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n)
  /-- Shared scan scratch is separate from output levels. -/
  scratch_disj : Fp.Disj (Store.inBlock t.1 (t.2 + 4) 1)
      (downLevelRegion n d ma ua qa ea sz kd kp)
  /-- Completed slot reservations preserve pending size and source reads. -/
  pending : ∀ lo < n, Fp.Disj
      (Fp.loopPrefix (fun j => downRegion n d j (ks j) ma ua qa ea sz kd kp) lo ⊔
        Store.inBlock t.1 (t.2 + 4) 1)
      (Store.inBlock sz.1 (sz.2 + n * d + lo) 1 ⊔
        if 0 < ks lo then
          Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)) else ⊥)
  /-- Every bounded node outcome has room and separated outputs. -/
  nodes : ∀ lo < n, 0 < ks lo →
      ((⟨s, 0⟩ : Mem K).Room [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
          [2 * (ks lo * ks lo), ks lo, 1] ∧
        Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
          [2 * (ks lo * ks lo), ks lo, 1] ∧
        Fp.Disj (Fp.blocks [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
          [2 * (ks lo * ks lo), ks lo, 1])
          (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)))) ∧
      ∀ r ≤ ks lo,
        (⟨s, 0⟩ : Mem K).Room (branchOutputs n d lo (ks lo) r ma qa sz kd kp)
          (branchLengths (ks lo) r) ∧
        Fp.Apart (branchOutputs n d lo (ks lo) r ma qa sz kd kp) (branchLengths (ks lo) r) ∧
        Fp.Disj (Fp.blocks (branchOutputs n d lo (ks lo) r ma qa sz kd kp)
          (branchLengths (ks lo) r))
          (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)))
  /-- Preparation and scan scratch cannot alter any next-level size word. -/
  scratch_size : Fp.Disj (downPrepareFp n d lv su sg t ⊔ Store.inBlock t.1 (t.2 + 4) 1)
    (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n)

end NLAlib.SpectralBisection
