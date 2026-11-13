/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLarge

/-!
# Total dispatch of each active downward slot

A positive stored size selects a diagonal leaf at size one. Larger slots execute the actual
rounded tolerance comparison, followed by a zero leaf or the explicit node program. Every
branch returns one existing mathematical bisection-step constructor in the level arenas.

## Main results

* `NLAlib.SpectralBisection.writes_downNode`: the actual active-slot dispatch stores its step.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Every active slot returns the existing mathematical step, including both leaf cases and
all nonleaf outcomes. Writable geometry and operation contracts replace success-only premises. -/
theorem writes_downNode {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) {τ : Tape K} {μ : Mem K} {n L fuel d lo k : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ}
    (R0 beta R eps U : K) (S : ℕ → ℕ → K × K) (A : Matrix (Fin k) (Fin k) (K × K))
    (hk : 0 < k) (hslot : lo + k ≤ n) (hexact : IsExactNatLit dec M (max k 4))
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
    Writes .total I τ (downNodeImpl (node (Op := Op) (Tst := Tst))).body
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
  by_cases hk1 : k = 1
  · subst k
    let leafResult : EighStep K 1 := .leaf
      ((M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)).identityMat 1)
      (fun i => (A i i).1)
    have hEq : outcome = leafResult := by rw [← hout]; simp [leafResult, eighStep]
    rw [hEq]
    refine (writes_ifPos (n := 1) (P := fun ν => ν.pos = μ.pos ∧
      StoresStep M R n d lo ma ua qa ea sz kd kp leafResult ν) rfl ?_).seq_le le_sup_left ?_
    · simp only [Nat.zero_lt_one, if_true]
      have hLeaf := writes_downLeaf (dec := dec) (mm := mm) (qr := qr) (unif := M.mul)
        (normal := fun z : K × K => M.normalWords z.1 z.2) (τ := τ)
        (n := n) (d := d) (lo := lo) (ma := ma) (ua := ua) (ea := ea) (kd := kd)
        (qa := qa) (sz := sz) (kp := kp) hS hL true R A (by room)
        (nodeInputs_reads hread).2.2.2.2.2.2.1 hleaf.1
        (apart_downLeaf hleaf.2.1 hleaf.2.2)
      exact writes_frame rfl
        (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame, Env.pushIdx,
          Nat.add_assoc]) (by room) hLeaf
    · intro ν _ hpost
      exact writes_ifPos (n := 0) rfl (by simpa using hpost)
  · have hk2 : 2 ≤ k := by omega
    refine (writes_ifPos (n := 0) (F := ⊥) (P := fun ν => ν = μ)
      (by simp [IExp.eval, Env.frame, show 1 - (k - 1) = 0 by omega])
      (by simp)).seq_le bot_le ?_
    intro ν _ hν
    subst ν
    refine writes_ifPos (n := k - 1) rfl ?_
    rw [if_pos (by omega)]
    have hLarge := writes_downLarge M dec mm qr (τ := τ) (μ := μ)
      (n := n) (L := L) (fuel := fuel) (d := d) (lo := lo) (k := k)
      (par := par) (lv := lv) (su := su) (sg := sg) (ma := ma) (ua := ua)
      (qa := qa) (ea := ea) (sz := sz) (kd := kd) (kp := kp) (c := c) (t := t)
      hS hL hC hMM hQR hQ R0 beta R eps U S A hk2 hslot hexact hl hread ht hprotect
      hleaf houtputs
    dsimp only at hLarge
    rw [hout] at hLarge
    exact writes_frame rfl rfl (by room) hLarge

end NLAlib.SpectralBisection
