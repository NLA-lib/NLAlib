/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Logic.MatrixPacked
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Actual split reconstruction from child outputs

The two stored bases multiply their respective child bases. Their eigenvalues receive the
stored positive and negative half-radius by explicit scalar broadcast operations. Four ordinary
output blocks expose the exact two products and two shifted eigenvalue vectors.

## Main results

* `NLAlib.SpectralBisection.writes_upSplitResult`: total reconstruction of all four blocks.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The two matrix products and shifted child eigenvalues are the actual four stored blocks.
The output regions may share arena buffers with other regions; their complete spatial
separation and capacities are explicit. No spectral or successful-execution premise is used. -/
theorem writes_upSplitResult {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
    {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I)
    (mm : ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) (K × K) →
      Matrix (Fin m) (Fin n) (K × K) → Matrix (Fin l) (Fin n) (K × K))
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    {τ : Tape K} {m : Mem K} {k kp : ℕ} {qp qm up um ep em sigma u e : ℕ × ℕ}
    (Qp : Matrix (Fin k) (Fin kp) (K × K)) (Qm : Matrix (Fin k) (Fin (k - kp)) (K × K))
    (Up : Matrix (Fin kp) (Fin kp) (K × K))
    (Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (K × K)) (vp vm : List K) (s : K)
    (hl : m.Live [qp, qm, up, um, ep, em, sigma, u, e])
    (hread : m.readBlocks [qp, qm, up, um, ep, em, sigma]
      [kp * k * 2, (k - kp) * k * 2, kp * kp * 2, (k - kp) * (k - kp) * 2, kp, k - kp, 1] =
      some [(EntryCodec.pair K).packFinMatrix Qp, (EntryCodec.pair K).packFinMatrix Qm,
        (EntryCodec.pair K).packFinMatrix Up, (EntryCodec.pair K).packFinMatrix Um, vp, vm, [s]])
    (hroom : m.Room [u, (u.1, u.2 + 2 * (k * kp)), e, (e.1, e.2 + kp)]
      [kp * k * 2, (k - kp) * k * 2, kp, k - kp])
    (hap : Fp.Apart [u, (u.1, u.2 + 2 * (k * kp)), e, (e.1, e.2 + kp)]
      [kp * k * 2, (k - kp) * k * 2, kp, k - kp])
    (hprotect : Fp.Disj (Fp.blocks [u, (u.1, u.2 + 2 * (k * kp)), e, (e.1, e.2 + kp)]
      [kp * k * 2, (k - kp) * k * 2, kp, k - kp])
      (Fp.blocks [qp, qm, up, um, ep, em, sigma]
        [kp * k * 2, (k - kp) * k * 2, kp * kp * 2, (k - kp) * (k - kp) * 2,
          kp, k - kp, 1])) :
    Writes .total I τ (upSplitResultImpl (Op := Op) (Tst := Tst)).body
      (Env.frame [k, kp] [qp, qm, up, um, ep, em, sigma, u, e])
      (Fp.blocks [u, (u.1, u.2 + 2 * (k * kp)), e, (e.1, e.2 + kp)]
        [kp * k * 2, (k - kp) * k * 2, kp, k - kp])
      (fun m' => m'.pos = m.pos ∧ m'.readBlocks
        [u, (u.1, u.2 + 2 * (k * kp)), e, (e.1, e.2 + kp)]
        [kp * k * 2, (k - kp) * k * 2, kp, k - kp] =
        some [(EntryCodec.pair K).packFinMatrix (mm Qp Up),
          (EntryCodec.pair K).packFinMatrix (mm Qm Um),
          vp.map (fun v => M.add v s), vm.map (fun v => M.sub v s)]) m := by
  have hprot (i : Fin 4) := hprotect.inBlock_getD_left (i := i) (by simp)
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hroom
  obtain ⟨hc₀, hc₁, hc₂, hc₃⟩ := hroom
  simp only [Fp.Apart] at hap
  obtain ⟨hd₀, hd₁, hd₂, _, _⟩ := hap
  refine (writes_matrixMul_packFinMatrix (EntryCodec.pair K) mm hMM Qp Up rfl rfl rfl
    (by room) (by simpa using Mem.readBlocks_getD hread (i := 0) (by simp))
    (by simpa using Mem.readBlocks_getD hread (i := 2) (by simp)) hc₀).seq_readBlock hd₀ ?_
  intro m₁ hfr₁ _ _
  have hr₁ := Mem.readBlocks_of_eqOff hfr₁ (by simpa using hprot 0) hread
  refine (writes_matrixMul_packFinMatrix (EntryCodec.pair K) mm hMM Qm Um rfl rfl rfl
    (by room) (by simpa using Mem.readBlocks_getD hr₁ (i := 1) (by simp))
    (by simpa using Mem.readBlocks_getD hr₁ (i := 3) (by simp)) (by room)).seq_readBlock hd₁ ?_
  intro m₂ hfr₂ _ _
  have hr₂ := Mem.readBlocks_of_eqOff hfr₂ (by simpa using hprot 1) hr₁
  refine (writes_frame rfl rfl (by room) (writes_scalarBroadcast_readBlock (hS .add)
    (by simpa using Mem.readBlocks_getD hr₂ (i := 4) (by simp))
    (by simpa using Mem.get_of_readBlocks_getD hr₂ (i := 6) (by simp) rfl rfl)
    (by room) (Or.inl ?_) ?_)).seq_readBlock hd₂ ?_
  · exact (hprot 2).mono le_rfl (Fp.inBlock_getD_le_blocks _ _ (i := 4) (by simp)) |>.symm
  · exact (hprot 2).mono le_rfl (Fp.inBlock_getD_le_blocks _ _ (i := 6) (by simp)) |>.symm
  intro m₃ hfr₃ _ _
  have hr₃ := Mem.readBlocks_of_eqOff hfr₃ (by simpa using hprot 2) hr₂
  exact (writes_frame rfl rfl (by room) (writes_scalarBroadcast_readBlock
    (x := em) (a := sigma) (y := (e.1, e.2 + kp)) (n := k - kp) (hS .sub)
    (by simpa using Mem.readBlocks_getD hr₃ (i := 5) (by simp))
    (by simpa using Mem.get_of_readBlocks_getD hr₃ (i := 6) (by simp) rfl rfl)
    (by room) (Or.inl ((hprot 3).mono le_rfl
      (Fp.inBlock_getD_le_blocks _ _ (i := 5) (by simp)) |>.symm))
    ((hprot 3).mono le_rfl
      (Fp.inBlock_getD_le_blocks _ _ (i := 6) (by simp)) |>.symm))).readBlocks_singleton

end NLAlib.SpectralBisection
