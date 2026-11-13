/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.NodeLayout
public import NLAlib.Eigensolvers.SpectralBisection.NodeScalars
public import NLAlib.Eigensolvers.SpectralBisection.Projectors

/-!
# Total mathematical preparation of a bisection node

The actual scalar setup, shifted matrix, sign parameters and projector program are composed
on caller-owned scratch. One tuple records both computed projectors, the retained signed
half-radii and the unchanged original inputs. This is a collection of ordinary stored reads,
not a separate execution-phase state.

## Main results

* `NLAlib.SpectralBisection.writes_nodePrepare`: exact stored preparation on actual words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Preparation computes the existing capped-sign projectors while retaining every original
input and the signed half-radius words needed by the selected branch. -/
theorem writes_nodePrepare {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op]
    [Has IndexOp Op] [Has MatrixOp Op] [Has CmpTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    {τ : Tape K} {μ : Mem K} {n L fuel d lo k : ℕ}
    {par lv su sg ma qa sz kd ks c t sp w b tm pp pm : ℕ × ℕ}
    (R0 beta R eps U : K) (S : ℕ → ℕ → K × K)
    (A : Matrix (Fin k) (Fin k) (K × K)) (h01 : dec (M.lit 0) ≠ dec (M.lit 1))
    (hl : μ.Live [par, lv, su, sg, ma, qa, sz, kd, ks, c, t, sp, w, b, tm, pp, pm])
    (hread : μ.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) =
      some (nodeInputWords M n R0 beta R eps U S A))
    (hsroom : μ.Room [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
    (hsap : Fp.Apart [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
    (hsprotect : Fp.Disj (Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) :
    let F := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    let W := F.hermShift A (M.mul (M.div R (M.lit ((L + d : ℕ) : ℚ))) U)
    let B := newtonSchulzSign F beta (M.mul (M.lit 2) R) fuel W
    let Pp := F.hermScale (F.hermShift B (M.neg (M.lit 1))) (M.lit 2)
    let Pm := F.hermScale (F.negMat (F.hermShift B (M.lit 1))) (M.lit 2)
    Writes .total I τ (nodePrepare (Op := Op) (Tst := Tst))
      (Env.frame [n, L, fuel, d, lo, k] [par, lv, su, sg, ma, qa, sz, kd, ks, c,
        t, sp, w, b, tm, pp, pm])
      (Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
      (fun μ' => μ'.pos = μ.pos ∧
        μ'.readBlocks ([pp, pm, t] ++ nodeInputs n d lo par lv su sg ma c)
          ([2 * (k * k), 2 * (k * k), 2] ++ nodeInputLengths n k) =
          some ([(EntryCodec.pair K).packFinMatrix Pp, (EntryCodec.pair K).packFinMatrix Pm,
            [M.div R (M.lit 2), M.neg (M.div R (M.lit 2))]] ++
              nodeInputWords M n R0 beta R eps U S A)) μ := by
  dsimp only
  let scratchFp := Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k)
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  rcases hl with ⟨hpar, hlv, hsu, hsg, hma, hqa, hsz, hkd, hks, hc, htl, hspl,
    hwl, hbl, html, hppl, hpml⟩
  obtain ⟨ht, hsp, hw, hb, htm, hpp, hpm, -⟩ := hsroom
  have hCarry {G : Fp} := hsap.disj_tail_head hsprotect (m := 2) (by omega) (G := G)
  have hScalarSub : Fp.blocks [t, (t.1, t.2 + 2), (t.1, t.2 + 3)] [2, 1, 2] ≤
      Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k) := by
    fp_sub [nodeScratchLengths]
  have hscalars := writes_nodeScalars (M := M) (μ := μ) (τ := τ)
    (L := L) (d := d) (lo := lo)
    (lv := lv) (c := c) (su := su) (t := t) hS hL R (M.lit 2) U
    (by kept) (by kept) (by kept) (by omega)
    (hsprotect.mono
      ((Fp.inBlock_le_inBlock le_rfl (by omega)).trans le_sup_left)
      (by fp_sub [nodeInputs, nodeInputLengths, Fp.cells]))
  let ρ := Env.frame [n, L, fuel, d, lo, k]
    [par, lv, su, sg, ma, qa, sz, kd, ks, c, t, sp, w, b, tm, pp, pm]
  refine (hscalars.keep_readBlocks hread (hsprotect.mono hScalarSub le_rfl)).frame_seq_le
    (ρ := ρ) rfl rfl (by room) hScalarSub ?_
  clear hscalars
  intro μ₁ hfr₁ ⟨⟨hp₁, hscalar⟩, hread₁⟩
  have hhalf₁ : μ₁.store.readBlock t.1 t.2 2 =
      some [M.div R (M.lit 2), M.neg (M.div R (M.lit 2))] := by kept
  have hcarry₁ := Mem.readBlocks_of_cons (a := t) (n := 2)
    (by simpa using hhalf₁) hread₁
  have hwSub : Store.inBlock w.1 w.2 (2 * (k * k)) ≤
      Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k) := by
    fp_sub [nodeScratchLengths]
  have hShift := Hermitian.writes_shift_packed
    (M := M) (dec := dec) (mm := mm) (qr := qr) (unif := M.mul)
    (normal := fun z : K × K => M.normalWords z.1 z.2) (μ := μ₁) (τ := τ)
    (x := (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo)) (c := (t.1, t.2 + 4)) (y := w) hS A _
    (hsprotect.symm.mono (by fp_sub [nodeInputs, nodeInputLengths]) hwSub)
    (hsap.1.mono (by fp_sub) (by fp_sub [nodeScratchLengths]))
    (by kept) (by kept) (by room) (by room)
  refine (hShift.keep_readBlocks hcarry₁ (hCarry (by fp_sub))).frame_seq_le
    rfl rfl (by room) hwSub ?_
  clear hShift
  intro μ₂ hfr₂ ⟨⟨hp₂, hW₂⟩, hcarry₂⟩
  have hParams := writes_signParameters (M := M) (I := I) (μ := μ₂) (τ := τ)
    (d := d) (lv := lv) (par := par) (two := (c.1, c.2 + 1)) (sp := sp) hS R beta (M.lit 2)
    (by kept) (by kept) (by kept) (by room)
    (hsprotect.symm.mono (by fp_sub [nodeInputs, nodeInputLengths, Fp.cells])
      (le_sup_left.trans le_sup_right))
  refine (hParams.keep_readBlocks
    (Mem.readBlocks_of_cons (a := w) (n := 2 * (k * k)) hW₂ hcarry₂)
    (Fp.disj_sup_right.mpr ⟨hsap.2.1.mono le_rfl le_sup_left, hCarry (by fp_sub)⟩)).frame_seq_le
      rfl rfl (by room) (by fp_sub [nodeScratchLengths]) ?_
  clear hParams
  intro μ₃ hfr₃ ⟨⟨hp₃, hsp₃⟩, hcarry₃⟩
  obtain ⟨hW₃, hkeep₃⟩ := Mem.readBlocks_cons_iff.mp hcarry₃
  have hC₃ : μ₃.store.readBlock c.1 c.2 5 = some
      [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf] := by kept
  have hc4 := Store.readBlock_sub hC₃ (o := 0) (n := 4) (by omega)
  have hProjApart := apart_nodeProjectors hsap hsprotect
  have hProj := writes_nodeProjectors (M := M) (dec := dec) (mm := mm)
    (qr := qr) (unif := M.mul) (normal := fun z : K × K => M.normalWords z.1 z.2)
    (m := μ₃) (τ := τ) (fuel := fuel) (w := w) (sp := sp) (c := c)
    (b := b) (t := tm) (pp := pp) (pm := pm)
    hS hC hMM hL
    ((M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)).hermShift A
      (M.mul (M.div R (M.lit ((L + d : ℕ) : ℚ))) U))
    beta (M.mul (M.lit 2) R) h01 (by room) hProjApart (by simpa only [Nat.cast_add] using hW₃) hsp₃
    (by simpa using hc4)
    (by room) (by room) (by room) (by room)
  refine ((hProj.keep_readBlocks hkeep₃ (hCarry (by fp_sub))).mono (G := scratchFp)
    (by fp_sub [scratchFp, nodeScratchLengths]) ?_).in_frame rfl rfl (by room)
  clear hProj
  intro μ₄ _ ⟨⟨hp₄, hprojectors⟩, hkeep₄⟩
  have hread₄ := Mem.readBlocks_append hprojectors hkeep₄
  exact ⟨hp₄.trans (hp₃.trans (hp₂.trans hp₁)), hread₄⟩

end NLAlib.SpectralBisection
