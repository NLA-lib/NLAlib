/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownGeometry
public import NLAlib.Eigensolvers.SpectralBisection.ChildStorage

/-!
# Separation of payload words and child-size metadata

Node payloads occupy six of the seven output arenas. The next size arena remains separate,
including when all arenas are disjoint views of one buffer.

## Main results

* `NLAlib.SpectralBisection.disj_stepPayloadFp_size`: payloads exclude next-level size words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A non-size output role remains separate from next-level size words. -/
theorem disj_downArena_slot_size {n d lo k : ℕ} (hslot : lo + k ≤ n)
    (ma ua qa ea sz kd kp : ℕ × ℕ)
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n)) (i : Fin 7) (hi : i ≠ 4) :
    Fp.Disj
      (Store.inBlock (downArenaOrigins n d ma ua qa ea sz kd kp i).1
        ((downArenaOrigins n d ma ua qa ea sz kd kp i).2 + downArenaStride n i * lo)
        (downArenaStride n i * k))
      (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n) := by
  let origins := downArenaOrigins n d ma ua qa ea sz kd kp
  let target := fun i : Fin 7 => ((origins i).1,
    (origins i).2 + downArenaStride n i * lo)
  let sizes := fun i : Fin 7 => downArenaStride n i * k
  have h := hAP.disj_getD (i := i.val) (j := 4) (by simp) (by simp)
    (by intro he; apply hi; exact Fin.ext he)
  have hs : Store.inBlock (target i).1 (target i).2 (sizes i) ≤
      Store.inBlock (origins i).1 (origins i).2 (downArenaStride n i * n) := by
    apply Fp.inBlock_le_inBlock (by dsimp [target]; omega)
    have hm := Nat.mul_le_mul_left (downArenaStride n i) hslot
    rw [Nat.mul_add] at hm
    dsimp [target, sizes]
    omega
  apply (show Fp.Disj
    (Store.inBlock (origins i).1 (origins i).2 (downArenaStride n i * n))
    (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n) from by
      fin_cases i <;> simpa [origins, downArenaOrigins, downArenaStride] using h).mono hs le_rfl

/-- A mathematical outcome's payload is separate from the complete next-level size arena. -/
theorem disj_stepPayloadFp_size {K : Type} {n d lo k : ℕ} (hslot : lo + k ≤ n)
    (hpos : 0 < k) (ma ua qa ea sz kd kp : ℕ × ℕ) (step : EighStep K k)
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n)) :
    Fp.Disj (stepPayloadFp n d lo ma ua qa ea sz kd kp step)
      (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n) := by
  let origins := downArenaOrigins n d ma ua qa ea sz kd kp
  let target := fun i : Fin 7 => ((origins i).1,
    (origins i).2 + downArenaStride n i * lo)
  let sizes := fun i : Fin 7 => downArenaStride n i * k
  have hk : k ≤ n := by omega
  have hmul := Nat.mul_le_mul_left (2 * k) hk
  have hrole := disj_downArena_slot_size hslot ma ua qa ea sz kd kp hAP
  have hfinish (source : List (ℕ × ℕ)) (lengths : List ℕ) {m : ℕ}
      (parent : Fin m → Fin 7) (hlen : min source.length lengths.length = m)
      (hp : ∀ i, parent i ≠ 4)
      (hv : ∀ i : Fin m,
        Store.inBlock (source.getD i (0, 0)).1 (source.getD i (0, 0)).2
          (lengths.getD i 0) ≤
          Store.inBlock (target (parent i)).1 (target (parent i)).2 (sizes (parent i))) :
      Fp.Disj (Fp.blocks source lengths)
        (Store.inBlock sz.1 (sz.2 + n * (d + 1)) n) := by
    apply Fp.Disj.symm
    apply Fp.disj_blocks_of_forall_getD
    intro i hi
    have hi' : i < m := by omega
    exact ((hrole (parent ⟨i, hi'⟩) (hp _)).mono (hv _) le_rfl).symm
  cases step with
  | leaf U values =>
    let source := [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
    let parent : Fin 3 → Fin 7 := ![1, 3, 5]
    apply hfinish source [2 * (k * k), k, 1] parent (by rfl)
    · intro i; fin_cases i <;> simp [parent]
    · intro i
      fin_cases i <;> apply Fp.inBlock_le_inBlock <;>
        simp [source, parent, target, sizes, origins, downArenaOrigins, downArenaStride] <;>
        nlinarith
  | shift side A sigma =>
    let source := [(ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
      (kd.1, kd.2 + n * d + lo)]
    let parent : Fin 2 → Fin 7 := ![0, 5]
    apply hfinish source [2 * (k * k), 1] parent (by rfl)
    · intro i; fin_cases i <;> simp [parent]
    · intro i
      fin_cases i <;> apply Fp.inBlock_le_inBlock <;>
        simp [source, parent, target, sizes, origins, downArenaOrigins, downArenaStride] <;>
        nlinarith
  | split r hr Qp Qm Ap Am sigma =>
    have hleft := Nat.mul_le_mul_left (2 * r) (hr.trans hk)
    have hright := Nat.mul_le_mul_left (2 * (k - r)) ((Nat.sub_le k r).trans hk)
    have hsum := Nat.sub_add_cancel hr
    have hmatrix : 2 * n * r + 2 * ((k - r) * (k - r)) ≤ 2 * n * k := by
      calc
        _ ≤ 2 * n * r + 2 * n * (k - r) := by nlinarith
        _ = 2 * n * k := by rw [← Nat.mul_add, Nat.add_sub_of_le hr]
    have hq := congrArg (fun z : ℕ => 2 * k * z) (Nat.add_sub_of_le hr)
    let parent : Fin 6 → Fin 7 := ![2, 2, 0, 0, 5, 6]
    apply hfinish _ _ parent (by rfl)
    · intro i; fin_cases i <;> simp [parent]
    · intro i
      fin_cases i <;> apply Fp.inBlock_le_inBlock <;>
        simp [parent, target, sizes, origins, downArenaOrigins,
          downArenaStride] <;> nlinarith

end NLAlib.SpectralBisection
