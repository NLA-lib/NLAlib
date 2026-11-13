/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLeaf
public import NLAlib.Eigensolvers.SpectralBisection.NodeSolve

/-!
# Actual tolerance dispatch for a nontrivial downward slot

The program multiplies the stored tolerance and root radius, compares the actual result with
the current radius, and executes a zero leaf or the explicit allocated node. The returned
outcome is the corresponding existing mathematical step, with no successful-run premise.

## Main results

* `NLAlib.SpectralBisection.writes_downLarge`: total dispatch for a slot of size at least two.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The actual threshold computation and query choose the same leaf or nonleaf step as the
mathematical algorithm. Capacity and spatial premises concern actual input and output regions. -/
theorem writes_downLarge {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) {τ : Tape K} {μ : Mem K} {n L fuel d lo k : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ}
    (R0 beta R eps U : K) (S : ℕ → ℕ → K × K) (A : Matrix (Fin k) (Fin k) (K × K))
    (hk : 2 ≤ k) (hslot : lo + k ≤ n) (hexact : IsExactNatLit dec M (max k 4))
    (hl : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t])
    (hread : μ.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) =
      some (nodeInputWords M n R0 beta R eps U S A))
    (ht : t.2 + 5 ≤ μ.store.len t.1)
    (hprotect : Fp.Disj (Store.inBlock t.1 (t.2 + 4) 1)
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k)))
    (hleaf : μ.Room [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
        (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] ∧
      Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
        (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] ∧
      Fp.Disj (Fp.blocks [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
        (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1])
        (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k)))
    (houtputs : ∀ r ≤ k,
      μ.Room (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r) ∧
      Fp.Apart (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r) ∧
      Fp.Disj (Fp.blocks (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r))
        (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) :
    let N := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    let outcome := eighStep N n fuel R0 beta A R eps (L + d) (storedNodeSample n lo U S)
    Writes .total I τ (downLargeImpl (node (Op := Op) (Tst := Tst))).body
      (Env.frame [n, L, fuel, d, lo, k] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t])
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp outcome) (stepOutputLengths outcome) ⊔
        Store.inBlock t.1 (t.2 + 4) 1)
      (fun μ' => μ'.pos = μ.pos ∧ StoresStep M R n d lo ma ua qa ea sz kd kp outcome μ') μ := by
  classical
  dsimp only
  generalize hout : eighStep
    (M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2))
    n fuel R0 beta A R eps (L + d) (storedNodeSample n lo U S) = outcome
  have hLive : par.1 < μ.store.length ∧ lv.1 < μ.store.length ∧ su.1 < μ.store.length ∧
      sg.1 < μ.store.length ∧ ma.1 < μ.store.length ∧ ua.1 < μ.store.length ∧
      qa.1 < μ.store.length ∧ ea.1 < μ.store.length ∧ sz.1 < μ.store.length ∧
      kd.1 < μ.store.length ∧ kp.1 < μ.store.length ∧ c.1 < μ.store.length ∧
      t.1 < μ.store.length := by simpa [Mem.Live] using hl
  rcases hLive with ⟨hpar, hlv, hsu, hsg, hma, hua, hqa, hea, hsz, hkd, hkp, hc, htt⟩
  have hr := nodeInputs_reads hread
  have hmul := writes_call_bin (md := .total) (τ := τ) (m := μ)
    (ρ := Env.frame [n, L, fuel, d, lo, k]
      [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t]) (hS .mul)
    (ins := [⟨1, .var 7 + (.const 2 * .var 3 + .const 1)⟩, ⟨0, .var 6⟩])
    (outs := [⟨12, .var 18 + .const 4⟩])
    (x := (lv.1, lv.2 + 2 * d + 1)) (y := par) (z := (t.1, t.2 + 4))
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Nat.add_assoc]) rfl
    trivial hr.2.2.2.1 hr.1 rfl (fun _ => ⟨by room, by dsimp; omega⟩)
  refine hmul.seq_le le_sup_right fun ν hfr hm => ?_
  have hread' := Mem.readBlocks_of_eqOff hfr hprotect hread
  have hr' := nodeInputs_reads hread'
  refine writes_ite rfl rfl (hC.test_le hr'.2.2.1 hm.2) ?_
  by_cases hle : dec R ≤ dec (M.mul eps R0)
  · simp only [hle, decide_true, if_true]
    have hEq : outcome = .leaf
        ((M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)).identityMat k)
        (fun _ => M.lit 0) := by
      rw [← hout]
      simp [eighStep, show ¬ k ≤ 1 by omega, Machine.toFloatMachine, hle]
    rw [hEq]
    have hLeaf := writes_downLeaf (dec := dec) (mm := mm) (qr := qr) (unif := M.mul)
      (normal := fun z : K × K => M.normalWords z.1 z.2) (τ := τ)
      (n := n) (d := d) (lo := lo) (ma := ma) (ua := ua) (ea := ea) (kd := kd)
      (qa := qa) (sz := sz) (kp := kp) hS hL false R A (by room) hr'.2.2.2.2.2.2.1
      (hleaf.1.congr hfr.len_eq) (apart_downLeaf hleaf.2.1 hleaf.2.2)
    exact (writes_frame rfl
      (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Nat.add_assoc])
      (by room) hLeaf).mono le_sup_left fun _ _ h => ⟨h.1.trans hm.1, h.2⟩
  · simp only [hle, decide_false, Bool.false_eq_true, if_false]
    have hn := writes_node M dec mm qr (τ := τ) (μ := ν)
      (n := n) (L := L) (fuel := fuel) (d := d) (lo := lo) (k := k)
      (par := par) (lv := lv) (su := su) (sg := sg) (ma := ma) (ua := ua)
      (qa := qa) (ea := ea) (sz := sz) (kd := kd) (ks := kp) (c := c) hS hL hC hMM hQR hQ
      R0 beta R eps U S A hk hslot hle hexact (by room) hread'
      (fun r hr => ⟨(houtputs r hr).1.congr hfr.len_eq, (houtputs r hr).2⟩)
    rw [hout] at hn
    exact (writes_frame rfl rfl (by room) hn).mono le_sup_left
      fun _ _ h => ⟨h.1.trans hm.1, h.2⟩

end NLAlib.SpectralBisection
