/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Deflation
public import NLAlib.Eigensolvers.SpectralBisection.Compression
public import NLAlib.Ops.Logic.IndexBlock

/-!
# Stored outputs of a spectral bisection split

A split executes its two sampled deflations, two compressions and four dimension-literal
writes. Its result is one tuple of actual packed bases, child matrices and metadata. Spatial
apartness and the generic block-sequence rule preserve earlier results automatically; no
program-specific execution state or successful-run hypothesis is introduced.

## Main results

* `NLAlib.SpectralBisection.splitOutputs` describes the eight output regions.
* `NLAlib.SpectralBisection.writes_split` collects their actual mathematical values.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The two bases, two child matrices, two child sizes, parent kind and parent split size. -/
def splitOutputs (n d lo k kp : ℕ) (ma qa sz kd ks : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo),
    (qa.1, qa.2 + 2 * (n * n) * d + 2 * n * lo + 2 * (k * kp)),
    (ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * lo),
    (ma.1, ma.2 + 2 * (n * n) * (d + 1) + 2 * n * (lo + kp)),
    (sz.1, sz.2 + n * (d + 1) + lo), (sz.1, sz.2 + n * (d + 1) + lo + kp),
    (kd.1, kd.2 + n * d + lo), (ks.1, ks.2 + n * d + lo)]

/-- Word lengths of a split's basis, matrix and scalar outputs. -/
def splitOutputLengths (k kp : ℕ) : List ℕ :=
  [2 * (k * kp), 2 * (k * (k - kp)), 2 * (kp * kp), 2 * ((k - kp) * (k - kp)), 1, 1, 1, 1]

/-- Stored samples, projectors, parent matrix, two scalar constants and two shifts. -/
def splitInputs (n d lo : ℕ) (sg pp pm ma c t : ℕ × ℕ) : List (ℕ × ℕ) :=
  [sg, pp, pm, (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo),
    (c.1, c.2 + 1), (c.1, c.2 + 4), t, (t.1, t.2 + 1)]

/-- Word lengths of a split's readable source blocks. -/
def splitInputLengths (n k : ℕ) : List ℕ :=
  [2 * ((2 * n) * n), 2 * (k * k), 2 * (k * k), 2 * (k * k), 1, 1, 1, 1]

/-- The split returns both actual computed bases, their shifted compressions, and the machine
words for both sizes, kind four and the split size. Explicit interior, slot, readable-input,
output-capacity and spatial-disjointness assumptions suffice for total execution. -/
theorem writes_split {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has IndexOp Op] [Has MatrixOp Op]
    {M : Machine K} (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K) {I : Interp Op Tst K}
    (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    {τ : Tape K} {μ : Mem K} {n d lo k kp : ℕ} {sg pp pm ma qa sz kd ks c t : ℕ × ℕ}
    (S : ℕ → ℕ → K × K) (Pp Pm A : Matrix (Fin k) (Fin k) (K × K))
    (two scale sigmaP sigmaM : K) (hInterior : 0 < kp ∧ kp < k) (hslot : lo + k ≤ n)
    (hl : μ.Live [sg, pp, pm, ma, qa, sz, kd, ks, c, t])
    (hread : μ.readBlocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k) =
      some [(EntryCodec.pair K).packMatrix n (2 * n) S, (EntryCodec.pair K).packFinMatrix Pp,
        (EntryCodec.pair K).packFinMatrix Pm, (EntryCodec.pair K).packFinMatrix A,
        [two], [scale], [sigmaP], [sigmaM]])
    (hroom : μ.Room (splitOutputs n d lo k kp ma qa sz kd ks) (splitOutputLengths k kp))
    (hap : Fp.Apart (splitOutputs n d lo k kp ma qa sz kd ks) (splitOutputLengths k kp))
    (hprotect : Fp.Disj (Fp.blocks (splitOutputs n d lo k kp ma qa sz kd ks)
      (splitOutputLengths k kp))
      (Fp.blocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k))) :
    let Qp := (qr (mm Pp (sampledGaussian M k lo 0 S scale))).1.submatrix id
      (Fin.castLE hInterior.2.le)
    let Qm := (qr (mm Pm (sampledGaussian M k lo 1 S scale))).1.submatrix id
      (Fin.castLE (Nat.sub_le k kp))
    let F := M.toFloatMachine dec mm qr unif normal
    let Ap := F.hermShift (F.hermAvg (mm (mm (F.conjTransposeMat Qp) A) Qp) two) sigmaP
    let Am := F.hermShift (F.hermAvg (mm (mm (F.conjTransposeMat Qm) A) Qm) two) sigmaM
    Writes .total I τ (split (Op := Op) (Tst := Tst))
      (Env.frame [n, d, lo, k, kp] [sg, pp, pm, ma, qa, sz, kd, ks, c, t])
      (Fp.blocks (splitOutputs n d lo k kp ma qa sz kd ks) (splitOutputLengths k kp))
      (fun μ' => μ'.pos = μ.pos ∧
        μ'.readBlocks (splitOutputs n d lo k kp ma qa sz kd ks) (splitOutputLengths k kp) =
          some [(EntryCodec.pair K).packFinMatrix Qp, (EntryCodec.pair K).packFinMatrix Qm,
            (EntryCodec.pair K).packFinMatrix Ap, (EntryCodec.pair K).packFinMatrix Am,
            [M.lit (kp : ℚ)], [M.lit ((k - kp : ℕ) : ℚ)], [M.lit 4], [M.lit (kp : ℚ)]]) μ := by
  have hprot (i : Fin 8) := hprotect.inBlock_getD_left (i := i)
    (by simp [splitOutputs, splitOutputLengths])
  have hpair (i j : Fin 8) (hij : i ≠ j) := hap.disj_getD
    (i := i) (j := j) (by simp [splitOutputs, splitOutputLengths])
    (by simp [splitOutputs, splitOutputLengths]) (Fin.val_ne_of_ne hij)
  simp only [splitInputs, splitInputLengths] at hread
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  dsimp only [splitOutputs, splitOutputLengths, Fp.Apart] at hap
  obtain ⟨hs₀, hs₁, hs₂, hs₃, hs₄, hs₅, hs₆, hs₇, _⟩ := hap
  simp only [splitOutputs, splitOutputLengths, Mem.room_cons, Mem.room_nil, and_true] at hroom
  obtain ⟨hc₀, hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇⟩ := hroom
  refine (writes_frame rfl rfl (by room) (writes_deflate (sg := sg) (sq := (c.1, c.2 + 4)) (p := pp)
    hS hMM hQR S scale Pp (by simp) hslot hInterior.2.le (by room)
    (Store.holdsEntries_of_readBlock_packMatrix rfl
      (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Mem.readBlocks_getD hread (i := 0) (by simp)))
    (by simpa using Mem.get_of_readBlocks_getD hread (i := 5) (by simp) rfl rfl)
    (by simpa using Mem.readBlocks_getD hread (i := 1) (by simp)) (by room))).seq_readBlock hs₀ ?_
  intro μ₁ hfr₁ hp₁ hQp₁
  have hr₁ := Mem.readBlocks_of_eqOff hfr₁ (by
    simpa [splitOutputs, splitOutputLengths, splitInputs, splitInputLengths]
      using hprot 0) hread
  refine (writes_frame rfl rfl (by room) (writes_deflate (sg := sg) (sq := (c.1, c.2 + 4)) (p := pm)
    hS hMM hQR S scale Pm (by simp) hslot (Nat.sub_le k kp) (by room)
    (Store.holdsEntries_of_readBlock_packMatrix rfl
      (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Mem.readBlocks_getD hr₁ (i := 0) (by simp)))
    (by simpa using Mem.get_of_readBlocks_getD hr₁ (i := 5) (by simp) rfl rfl)
    (by simpa using Mem.readBlocks_getD hr₁ (i := 2) (by simp)) (by room))).seq_readBlock hs₁ ?_
  intro μ₂ hfr₂ hp₂ hQm₂
  have hr₂ := Mem.readBlocks_of_eqOff hfr₂ (by
    simpa [splitOutputs, splitOutputLengths, splitInputs, splitInputLengths]
      using hprot 1) hr₁
  have hQp₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) (by
    simpa [splitOutputs, splitOutputLengths] using hpair 1 0 (by simp)) hQp₁
  refine (writes_frame rfl rfl (by room) (writes_compress dec mm qr unif normal hS hMM
    _ A two sigmaP (by room) hQp₂ (by simpa using Mem.readBlocks_getD hr₂ (i := 3) (by simp))
    (by simpa using Mem.get_of_readBlocks_getD hr₂ (i := 4) (by simp) rfl rfl)
    (by simpa using Mem.get_of_readBlocks_getD hr₂ (i := 6) (by simp) rfl rfl)
    (by room) ?_)).seq_readBlock hs₂ ?_
  · exact (hprot 2).mono le_rfl (Fp.inBlock_getD_le_blocks _ _ (i := 6)
      (by simp [splitInputs, splitInputLengths])) |>.symm
  intro μ₃ hfr₃ hp₃ hAp₃
  have hr₃ := Mem.readBlocks_of_eqOff hfr₃ (by
    simpa [splitOutputs, splitOutputLengths, splitInputs, splitInputLengths]
      using hprot 2) hr₂
  have hQm₃ := hfr₃.keep (Store.readsOnly_readBlock _ _ _ _) (by
    simpa [splitOutputs, splitOutputLengths] using hpair 2 1 (by simp)) hQm₂
  refine (writes_frame rfl rfl (by room) (writes_compress dec mm qr unif normal hS hMM
    _ A two sigmaM (by room) hQm₃ (by simpa using Mem.readBlocks_getD hr₃ (i := 3) (by simp))
    (by simpa using Mem.get_of_readBlocks_getD hr₃ (i := 4) (by simp) rfl rfl)
    (by simpa using Mem.get_of_readBlocks_getD hr₃ (i := 7) (by simp) rfl rfl)
    (by room) ?_)).seq_readBlock hs₃ ?_
  · exact (hprot 3).mono le_rfl (Fp.inBlock_getD_le_blocks _ _ (i := 7)
      (by simp [splitInputs, splitInputLengths])) |>.symm
  intro μ₄ hfr₄ hp₄ hAm₄
  exact writes_indexBlock (ρ := Env.frame [n, d, lo, k, kp]
    [sg, pp, pm, ma, qa, sz, kd, ks, c, t]) (m := μ₄)
    (ns := [kp, k - kp, 4, kp])
    (zs := [(sz.1, sz.2 + n * (d + 1) + lo), (sz.1, sz.2 + n * (d + 1) + lo + kp),
      (kd.1, kd.2 + n * d + lo), (ks.1, ks.2 + n * d + lo)]) hL
    [(.var 4, ⟨5, .var 10 + .var 0 * (.var 1 + .const 1) + .var 2⟩),
      (.var 3 - .var 4, ⟨5, .var 10 + .var 0 * (.var 1 + .const 1) + .var 2 + .var 4⟩),
      (.const 4, ⟨6, .var 11 + .var 0 * .var 1 + .var 2⟩),
      (.var 4, ⟨7, .var 12 + .var 0 * .var 1 + .var 2⟩)]
    rfl rfl ⟨hs₄, hs₅, hs₆, hs₇, trivial⟩ ⟨by room, by room, by room, by room, trivial⟩

end NLAlib.SpectralBisection
