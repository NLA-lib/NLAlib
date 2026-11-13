/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.LeafPacked
public import NLAlib.Eigensolvers.SpectralBisection.NodeData

/-!
# Stored mathematical leaf outcomes in level arenas

The ordinary packed leaf contract is the leaf case of the shared stored-outcome predicate.
The slot geometry specifies only addresses and capacities; the mathematical matrix and values
come from actual executed scalar operations.

## Main results

* `NLAlib.SpectralBisection.writes_downLeaf`: an actual leaf stores its mathematical outcome.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Separating the leaf's output tuple from the actual node inputs also separates it from
its source matrix, including when both occupy disjoint views of one arena. -/
theorem apart_downLeaf {n d lo k : ℕ} {par lv su sg ma ua ea kd c : ℕ × ℕ}
    (hAP : Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1])
    (hDisj : Fp.Disj (Fp.blocks [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1])
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) :
    Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo),
      (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo)]
      [2 * (k * k), k, 1, 2 * (k * k)] := by
  have hA : Store.inBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ≤
      Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) := by
    simpa [nodeInputs, nodeInputLengths] using
      Fp.inBlock_getD_le_blocks (nodeInputs n d lo par lv su sg ma c)
        (nodeInputLengths n k) (i := 6) (by simp [nodeInputs, nodeInputLengths])
  exact hAP.append (by simp [Fp.Apart]) rfl (hDisj.mono le_rfl (sup_le hA bot_le))

/-- A diagonal or zero leaf stores the corresponding constructor of the mathematical step. -/
theorem writes_downLeaf {K Op Tst Su Sg : Type} [Inhabited K] [Has ScalarOp Op]
    [Has IndexOp Op] {M : Machine K} {dec : K → ℝ} {mm : MatMulMap (K × K)}
    {qr : QRMap (K × K)} {unif : K → Su → K} {normal : Sg → K × K}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I)
    (diagonal : Bool) {τ : Tape K} {μ : Mem K} {n d lo k : ℕ}
    {ma ua qa ea sz kd kp : ℕ × ℕ} (R : K) (A : Matrix (Fin k) (Fin k) (K × K))
    (hl : μ.Live [ma, ua, ea, kd])
    (hA : μ.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hRoom : μ.Room [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1])
    (hAP : Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
      (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo),
      (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo)]
      [2 * (k * k), k, 1, 2 * (k * k)]) :
    Writes .total I τ (leaf diagonal)
      (Env.frame [k] [(ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo),
        (ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
        (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)])
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp
        (.leaf ((M.toFloatMachine dec mm qr unif normal).identityMat k)
          (fun i => if diagonal then (A i i).1 else M.lit 0))) [2 * (k * k), k, 1])
      (fun μ' => μ'.pos = μ.pos ∧ StoresStep M R n d lo ma ua qa ea sz kd kp
        (.leaf ((M.toFloatMachine dec mm qr unif normal).identityMat k)
          (fun i => if diagonal then (A i i).1 else M.lit 0)) μ') μ := by
  have hLive : ma.1 < μ.store.length ∧ ua.1 < μ.store.length ∧
      ea.1 < μ.store.length ∧ kd.1 < μ.store.length := by simpa [Mem.Live] using hl
  rcases hLive with ⟨hlma, hlua, hlea, hlkd⟩
  have hkind : kd.2 + n * d + lo < μ.store.len kd.1 := by
    have h := hRoom.2.2.1
    dsimp at h
    omega
  exact (writes_leaf_packed (dec := dec) (mm := mm) (qr := qr) (unif := unif)
    (normal := normal) (τ := τ) hS hL diagonal A (by room) hA hRoom.1 hRoom.2.1
    hkind hAP).mono le_rfl fun _ _ h => ⟨h.1, ⟨trivial, h.2⟩⟩

end NLAlib.SpectralBisection
