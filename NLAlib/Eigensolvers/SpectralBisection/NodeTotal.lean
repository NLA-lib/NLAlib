/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.NodePrepare
public import NLAlib.Eigensolvers.SpectralBisection.NodeOutput
public import NLAlib.Eigensolvers.SpectralBisection.Index

/-!
# Total nonleaf bisection step on caller-owned workspace

Preparation, the rounded trace, its clamp and bounded natural query, and the selected branch
compose into the existing mathematical `eighStep`. Every premise describes primitive behavior,
actual readable words, capacity or spatial separation. The ordinary `StoresStep` predicate
represents the complete returned outcome, including the shift needed by upward reconstruction.

## Main results

* `NLAlib.SpectralBisection.writes_nodeBody`: total refinement of the actual nonleaf node body.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The ordinary preparation tuple supplies every actual input of the selected branch. -/
private theorem splitInputs_of_prepared {K : Type} {M : Machine K} {μ : Mem K} {n d lo k : ℕ}
    {par lv su sg ma c t pp pm : ℕ × ℕ} {R0 beta R eps U : K}
    {S : ℕ → ℕ → K × K} {A Pp Pm : Matrix (Fin k) (Fin k) (K × K)}
    (h : μ.readBlocks ([pp, pm, t] ++ nodeInputs n d lo par lv su sg ma c)
      ([2 * (k * k), 2 * (k * k), 2] ++ nodeInputLengths n k) =
      some ([(EntryCodec.pair K).packFinMatrix Pp, (EntryCodec.pair K).packFinMatrix Pm,
        [M.div R (M.lit 2), M.neg (M.div R (M.lit 2))]] ++
          nodeInputWords M n R0 beta R eps U S A)) :
    μ.readBlocks (splitInputs n d lo sg pp pm ma c t) (splitInputLengths n k) =
      some [(EntryCodec.pair K).packMatrix n (2 * n) S, (EntryCodec.pair K).packFinMatrix Pp,
        (EntryCodec.pair K).packFinMatrix Pm, (EntryCodec.pair K).packFinMatrix A,
        [M.lit 2], [M.sqrtHalf], [M.div R (M.lit 2)], [M.neg (M.div R (M.lit 2))]] := by
  obtain ⟨hPp, hrest⟩ := Mem.readBlocks_cons_iff.mp h
  obtain ⟨hPm, hrest⟩ := Mem.readBlocks_cons_iff.mp hrest
  obtain ⟨hhalf, hread⟩ := Mem.readBlocks_cons_iff.mp hrest
  obtain ⟨_, _, _, _, _, hSG, hA, hC⟩ := nodeInputs_reads (M := M) hread
  have htwo := Store.get_of_readBlock hC (j := 1) (by simp) (M.lit 0)
  have hscale := Store.get_of_readBlock hC (j := 4) (by simp) (M.lit 0)
  have hpositive := Store.get_of_readBlock hhalf (j := 0) (by simp) (M.lit 0)
  have hnegative := Store.get_of_readBlock hhalf (j := 1) (by simp) (M.lit 0)
  simp only [List.getD_cons_zero, List.getD_cons_succ,
    Nat.add_zero] at htwo hscale hpositive hnegative
  change μ.readBlocks [sg, pp, pm, (ma.1, ma.2 + 2 * (n * n) * d + 2 * n * lo),
    (c.1, c.2 + 1), (c.1, c.2 + 4), t, (t.1, t.2 + 1)]
    [2 * ((2 * n) * n), 2 * (k * k), 2 * (k * k), 2 * (k * k), 1, 1, 1, 1] = _
  reads

/-- Sparse index workspace avoids both retained half-radius words and the node's inputs. -/
private theorem indexCells_disjoint_prepared {n d lo k : ℕ}
    {par lv su sg ma c t sp w b tm pp pm : ℕ × ℕ}
    (hsap : Fp.Apart [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
    (hsprotect : Fp.Disj (Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) :
    Fp.Disj (indexCells t)
      (Fp.blocks ([pp, pm, t] ++ nodeInputs n d lo par lv su sg ma c)
        ([2 * (k * k), 2 * (k * k), 2] ++ nodeInputLengths n k)) := by
  have hIndexT : indexCells t ≤ Store.inBlock t.1 t.2 7 := by fp_sub [indexCells]
  have hIndexInputs : Fp.Disj (indexCells t)
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k)) :=
    hsprotect.mono (hIndexT.trans le_sup_left) le_rfl
  simp only [List.cons_append, List.nil_append, Fp.blocks_cons, Fp.disj_sup_right]
  refine ⟨hsap.1.mono hIndexT (by fp_sub [nodeScratchLengths]),
    hsap.1.mono hIndexT (by fp_sub [nodeScratchLengths]), ?_, hIndexInputs⟩
  disjoint [indexCells]

/-- A nonleaf node executes totally and stores exactly the existing mathematical step on its
actual inputs. All bounded split cases have sufficient separated output capacity. No scratch
initialization, numerical-accuracy or successful-run premise is assumed. -/
theorem writes_nodeBody {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) {τ : Tape K} {μ : Mem K} {n L fuel d lo k : ℕ}
    {par lv su sg ma ua qa ea sz kd ks c t sp w b tm pp pm : ℕ × ℕ}
    (R0 beta R eps U : K) (S : ℕ → ℕ → K × K)
    (A : Matrix (Fin k) (Fin k) (K × K)) (hk : 2 ≤ k) (hslot : lo + k ≤ n)
    (hactive : ¬ dec R ≤ dec (M.mul eps R0)) (hexact : IsExactNatLit dec M (max k 4))
    (hl : μ.Live [par, lv, su, sg, ma, qa, sz, kd, ks, c, t, sp, w, b, tm, pp, pm])
    (hread : μ.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) =
      some (nodeInputWords M n R0 beta R eps U S A))
    (hsroom : μ.Room [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
    (hsap : Fp.Apart [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
    (hsprotect : Fp.Disj (Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k)))
    (houtputs : ∀ r ≤ k,
      μ.Room (branchOutputs n d lo k r ma qa sz kd ks) (branchLengths k r) ∧
      Fp.Apart (branchOutputs n d lo k r ma qa sz kd ks) (branchLengths k r) ∧
      Fp.Disj (Fp.blocks (branchOutputs n d lo k r ma qa sz kd ks) (branchLengths k r))
        (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) ⊔
          Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))) :
    let F := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    let step := eighStep F n fuel R0 beta A R eps (L + d) (storedNodeSample n lo U S)
    Writes .total I τ (nodeBody (Op := Op) (Tst := Tst))
      (Env.frame [n, L, fuel, d, lo, k] [par, lv, su, sg, ma, qa, sz, kd, ks, c,
        t, sp, w, b, tm, pp, pm])
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd ks step) (stepOutputLengths step) ⊔
        Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k))
      (fun μ' => μ'.pos = μ.pos ∧ StoresStep M R n d lo ma ua qa ea sz kd ks step μ') μ := by
  let F := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
  let W := F.hermShift A (M.mul (M.div R (M.lit ((L + d : ℕ) : ℚ))) U)
  let B := newtonSchulzSign F beta (M.mul (M.lit 2) R) fuel W
  let Pp := F.hermScale (F.hermShift B (M.neg (M.lit 1))) (M.lit 2)
  let Pm := F.hermScale (F.negMat (F.hermShift B (M.lit 1))) (M.lit 2)
  let kp := min k (F.toNat (M.add (F.traceRe Pp) (M.div (M.lit 1) (M.lit 2))))
  have hkp : kp ≤ k := min_le_left _ _
  dsimp only
  rw [eighStep_eq_branchOutcome M dec mm qr hslot hk R R0 beta eps U S A hactive]
  have hl0 := hl
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  rcases hl with ⟨hpar, hlv, hsu, hsg, hma, hqa, hsz, hkd, hks, hc, htl, hspl,
    hwl, hbl, html, hppl, hpml⟩
  have h01 : dec (M.lit 0) ≠ dec (M.lit 1) := by
    have hz := hexact 0 (by omega)
    have ho := hexact 1 (by omega)
    norm_num only [Nat.cast_zero, Nat.cast_one] at hz ho
    simpa only [hz, ho] using (zero_ne_one : (0 : ℝ) ≠ 1)
  refine (writes_nodePrepare (μ := μ) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (d := d) (lo := lo) (k := k)
    (par := par) (lv := lv) (su := su) (sg := sg) (ma := ma) (qa := qa)
    (sz := sz) (kd := kd) (ks := ks) (c := c) (t := t) (sp := sp)
    (w := w) (b := b) (tm := tm) (pp := pp) (pm := pm) M dec mm qr hS hL hC hMM
    R0 beta R eps U S A h01 hl0 hread hsroom hsap hsprotect).frame_seq_le
    rfl rfl (by room) le_sup_right ?_
  intro μ₁ hfr₁ ⟨hp₁, hprepared₁⟩
  obtain ⟨hPp₁, hrest₁⟩ := Mem.readBlocks_cons_iff.mp hprepared₁
  obtain ⟨_, hrest₁⟩ := Mem.readBlocks_cons_iff.mp hrest₁
  obtain ⟨_, hinputs₁⟩ := Mem.readBlocks_cons_iff.mp hrest₁
  obtain ⟨_, _, _, _, _, _, _, hC₁⟩ := nodeInputs_reads (M := M) hinputs₁
  have hhalf₁ := Store.get_of_readBlock hC₁ (j := 2) (by simp) (M.lit 0)
  have hIndexT : indexCells t ≤ Store.inBlock t.1 t.2 7 := by fp_sub [indexCells]
  have hIndexProtect := indexCells_disjoint_prepared
    (n := n) (d := d) (lo := lo) (par := par) (lv := lv) (su := su) (sg := sg)
    (ma := ma) (c := c) hsap hsprotect
  have hIndex := writes_nodeSplitIndex (M := M) dec mm qr M.mul
    (fun z : K × K => M.normalWords z.1 z.2) (μ := μ₁) (τ := τ)
    (k := k) (pp := pp) (c := c) (t := t) hS hL hC Pp (M.div (M.lit 1) (M.lit 2))
    (by room) hPp₁ (by simpa using hhalf₁) (by rw [hfr₁.len_eq]; exact hsroom.1)
    (Fp.disj_sup_right.mpr ⟨hsap.1.mono le_rfl (by fp_sub [nodeScratchLengths]),
      hsprotect.mono (by fp_sub [nodeScratchLengths])
        (by fp_sub [nodeInputs, nodeInputLengths])⟩)
  refine (hIndex.keep_readBlocks hprepared₁ hIndexProtect).frame_seq_le
    rfl rfl (by room)
      ((hIndexT.trans le_sup_left).trans le_sup_right) ?_
  clear hIndex
  intro μ₂ hfr₂ ⟨⟨hp₂, hclip⟩, hprepared₂⟩
  refine writes_bindIdx_of_isIndex hQ (v := kp) rfl rfl
    (BlockFn.readBlocks_cells_one.mpr ⟨_, hclip, rfl⟩) ?_ hkp ?_
  · simpa only [F, Machine.toFloatMachine, kp, List.flatten_cons, List.flatten_nil,
      List.append_nil] using
      (toNatFn_clampWord (w := M.add (F.traceRe Pp) (M.div (M.lit 1) (M.lit 2)))
        (by simpa only [Nat.cast_zero] using hexact 0 (by omega)) (hexact k (by omega)))
  have hroom₂ := (houtputs kp hkp).1.congr fun b => (hfr₂.len_eq b).trans (hfr₁.len_eq b)
  have hBranchInputs : Fp.blocks (splitInputs n d lo sg pp pm ma c t)
      (splitInputLengths n k) ≤
      Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) ⊔
        Fp.blocks [t, sp, w, b, tm, pp, pm] (nodeScratchLengths k) := by
    fp_sub [splitInputs, splitInputLengths, nodeInputs, nodeInputLengths, nodeScratchLengths]
  have hBranch := writes_nodeBranch (M := M) (μ := μ₂) (τ := τ)
    (n := n) (d := d) (lo := lo) (k := k) (kp := kp) (ua := ua) (ea := ea)
    (sg := sg) (pp := pp) (pm := pm) (ma := ma) (qa := qa) (sz := sz)
    (kd := kd) (ks := ks) (c := c) (t := t) dec mm qr hS hL hMM hQR
    S Pp Pm A R (by omega) hkp hslot (by room) (splitInputs_of_prepared (M := M) hprepared₂)
    (by simpa only [stepOutputs_branchOutcome, stepOutputLengths_branchOutcome] using hroom₂)
    (by simpa only [stepOutputs_branchOutcome, stepOutputLengths_branchOutcome]
      using (houtputs kp hkp).2.1)
    (by simpa only [stepOutputs_branchOutcome, stepOutputLengths_branchOutcome] using
      (houtputs kp hkp).2.2.mono le_rfl hBranchInputs)
  refine hBranch.mono le_sup_left ?_ |>.in_frame rfl rfl (by room)
  clear hBranch
  intro μ₃ _ ⟨hp₃, hstep⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hstep⟩

end NLAlib.SpectralBisection
