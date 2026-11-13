/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Arena
public import NLAlib.Ops.Logic.BlockPartition

/-!
# Splitting the slot reservation of a bisection node

Child square matrices use their own size squared words within consecutive groups of root
slots. The two rectangular bases instead fill the parent's square payload contiguously.
These rules include zero-size children and expose the same reservation invariant used for
whole-level disjointness and superadditive cost bounds.

## Main results

* `NLAlib.SpectralBisection.split_matrix_blocks`: child payloads are apart inside parent slots.
* `NLAlib.SpectralBisection.split_basis_blocks`: bases are apart and fill one square payload.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The two child matrices fit the parent's slot reservation and have disjoint payloads. -/
theorem split_matrix_blocks (buf off n k kp : ℕ) (hk : k ≤ n) (hp : kp ≤ k) :
    Fp.Apart [(buf, off), (buf, off + 2 * n * kp)]
      [2 * (kp * kp), 2 * ((k - kp) * (k - kp))] ∧
      Fp.blocks [(buf, off), (buf, off + 2 * n * kp)]
        [2 * (kp * kp), 2 * ((k - kp) * (k - kp))] ≤ Store.inBlock buf off (2 * n * k) := by
  have hleft := Nat.mul_le_mul_left (2 * kp) (hp.trans hk)
  have hright := Nat.mul_le_mul_left (2 * (k - kp)) ((Nat.sub_le k kp).trans hk)
  simpa only [Nat.add_sub_of_le hp, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Fp.split_strided buf off (2 * n) kp (k - kp) (2 * (kp * kp))
      (2 * ((k - kp) * (k - kp))) (by nlinarith) (by nlinarith)

/-- Both child matrix capacities follow from the parent slot reservation's capacity. -/
theorem room_split_matrix_blocks {K : Type} {m : Mem K} {buf off n k kp : ℕ}
    (hk : k ≤ n) (hp : kp ≤ k) (hroom : off + 2 * n * k ≤ m.store.len buf) :
    m.Room [(buf, off), (buf, off + 2 * n * kp)]
      [2 * (kp * kp), 2 * ((k - kp) * (k - kp))] := by
  have hleft := Nat.mul_le_mul_left (2 * kp) (hp.trans hk)
  have hright := Nat.mul_le_mul_left (2 * (k - kp)) ((Nat.sub_le k kp).trans hk)
  have hz : off + (kp + (k - kp)) * (2 * n) ≤ m.store.len buf := by
    simpa only [Nat.add_sub_of_le hp, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hroom
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Mem.room_split_strided (m := m) (buf := buf) (off := off) (stride := 2 * n)
      (a := kp) (b := k - kp) (x := 2 * (kp * kp)) (y := 2 * ((k - kp) * (k - kp)))
      (by nlinarith) (by nlinarith) hz

/-- The two rectangular bases are apart and together occupy the whole parent square payload. -/
theorem split_basis_blocks (buf off k kp : ℕ) (hp : kp ≤ k) :
    Fp.Apart [(buf, off), (buf, off + 2 * (k * kp))]
      [2 * (k * kp), 2 * (k * (k - kp))] ∧
      Fp.blocks [(buf, off), (buf, off + 2 * (k * kp))]
        [2 * (k * kp), 2 * (k * (k - kp))] = Store.inBlock buf off (2 * (k * k)) := by
  constructor
  · simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (Fp.split_strided buf off (2 * k) kp (k - kp) (2 * (k * kp))
        (2 * (k * (k - kp))) (by nlinarith) (by nlinarith)).1
  · simp only [Fp.blocks, sup_bot_eq, Fp.inBlock_add]
    congr 1
    have := Nat.sub_add_cancel hp
    nlinarith

end NLAlib.SpectralBisection
