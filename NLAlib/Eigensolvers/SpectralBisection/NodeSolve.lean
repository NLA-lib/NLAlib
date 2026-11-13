/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.NodeTotal
public import NLAlib.Eigensolvers.SpectralBisection.NodeLayout
public import NLAlib.Ops.Logic.Allocation

/-!
# Total allocated spectral bisection node

The node allocates its scratch, executes its mathematical stages and releases every temporary
buffer. Its output is the existing mathematical node outcome represented in the caller's
arenas. No scratch contents are supplied as input, and no successful-run premise is used.

## Main results

* `NLAlib.SpectralBisection.writes_node`: total stored outcome of the actual allocated node.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The nonleaf node returns the existing mathematical step on its actual stored inputs.
Every possible bounded split has writable, separated arena outputs; exact bounded literals
justify all metadata conversions. Scratch is fresh and requires no initialized values.
Numerical accuracy and the law of the stored samples are separate assumptions. -/
theorem writes_node {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) {τ : Tape K} {μ : Mem K} {n L fuel d lo k : ℕ}
    {par lv su sg ma ua qa ea sz kd ks c : ℕ × ℕ}
    (R0 beta R eps U : K) (S : ℕ → ℕ → K × K)
    (A : Matrix (Fin k) (Fin k) (K × K)) (hk : 2 ≤ k) (hslot : lo + k ≤ n)
    (hactive : ¬ dec R ≤ dec (M.mul eps R0)) (hexact : IsExactNatLit dec M (max k 4))
    (hl : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, ks, c])
    (hread : μ.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) =
      some (nodeInputWords M n R0 beta R eps U S A))
    (houtputs : ∀ r ≤ k,
      μ.Room (branchOutputs n d lo k r ma qa sz kd ks) (branchLengths k r) ∧
      Fp.Apart (branchOutputs n d lo k r ma qa sz kd ks) (branchLengths k r) ∧
      Fp.Disj (Fp.blocks (branchOutputs n d lo k r ma qa sz kd ks) (branchLengths k r))
        (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) :
    Writes .total I τ (node (Op := Op) (Tst := Tst))
      (Env.frame [n, L, fuel, d, lo, k] [par, lv, su, sg, ma, qa, sz, kd, ks, c])
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd ks
        (eighStep (M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2))
          n fuel R0 beta A R eps (L + d) (storedNodeSample n lo U S)))
        (stepOutputLengths
          (eighStep (M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2))
            n fuel R0 beta A R eps (L + d) (storedNodeSample n lo U S))))
      (fun μ' => μ'.pos = μ.pos ∧ StoresStep M R n d lo ma ua qa ea sz kd ks
        (eighStep (M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2))
          n fuel R0 beta A R eps (L + d) (storedNodeSample n lo U S)) μ') μ := by
  let N := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
  let outcome := eighStep N n fuel R0 beta A R eps (L + d) (storedNodeSample n lo U S)
  have hInputLive : μ.Live (nodeInputs n d lo par lv su sg ma c) :=
    live_nodeInputs (fun z hz => hl z (by simp at hz ⊢; tauto))
  have hOutputLive (r : ℕ) : μ.Live (branchOutputs n d lo k r ma qa sz kd ks) :=
    live_branchOutputs (fun z hz => hl z (by simp at hz ⊢; tauto))
  have hOutcomeLive : μ.Live (stepOutputs n d lo ma ua qa ea sz kd ks outcome) :=
    live_stepOutputs (fun z hz => hl z (by simp at hz ⊢; tauto)) outcome
  allocs_preserving (nodeScratchLengths k)
  case sizes => rfl
  case keep =>
    intro s s' p hBelow hp
    exact ⟨hp.1, StoresStep.of_below hBelow hOutcomeLive hp.2⟩
  intro store hlength hlens hBelow
  let scratch := (List.range 7).map fun i => (μ.store.length + i, 0)
  have hsAbove : Fp.blocks scratch (nodeScratchLengths k) ≤ Fp.above μ.store.length := by
    apply Fp.blocks_le_above
    rintro z hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
    exact Nat.le_add_right _ _
  have hsRoom : (⟨store, μ.pos⟩ : Mem K).Room scratch (nodeScratchLengths k) := by
    simpa only [scratch, nodeScratchLengths, List.length_cons, List.length_nil] using
      Mem.room_allocs ⟨store, μ.pos⟩ μ.store.length (nodeScratchLengths k) hlens
  have hsApart : Fp.Apart scratch (nodeScratchLengths k) := by
    simpa only [scratch, nodeScratchLengths, List.length_cons, List.length_nil] using
      Fp.apart_allocs μ.store.length (nodeScratchLengths k)
  have hsProtect : Fp.Disj (Fp.blocks scratch (nodeScratchLengths k))
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k)) :=
    (Fp.blocks_disj_above hInputLive).symm.mono hsAbove le_rfl
  have hlOld : (⟨store, μ.pos⟩ : Mem K).Live
      [par, lv, su, sg, ma, qa, sz, kd, ks, c] := by
    intro z hz
    exact (hl z (by simp at hz ⊢; tauto)).trans_le (by
      rw [hlength]; exact Nat.le_add_right _ _)
  have hlScratch : (⟨store, μ.pos⟩ : Mem K).Live scratch := by
    simpa only [scratch, nodeScratchLengths, List.length_cons, List.length_nil] using
      Mem.live_allocs ⟨store, μ.pos⟩ μ.store.length (nodeScratchLengths k) hlength
  have hlBody := (Mem.live_append (⟨store, μ.pos⟩ : Mem K) _ _).mpr ⟨hlOld, hlScratch⟩
  have hout (r : ℕ) (hr : r ≤ k) := houtputs r hr
  have hout' (r : ℕ) (hr : r ≤ k) :
      (⟨store, μ.pos⟩ : Mem K).Room (branchOutputs n d lo k r ma qa sz kd ks)
        (branchLengths k r) ∧
      Fp.Apart (branchOutputs n d lo k r ma qa sz kd ks) (branchLengths k r) ∧
      Fp.Disj (Fp.blocks (branchOutputs n d lo k r ma qa sz kd ks) (branchLengths k r))
        (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k) ⊔
          Fp.blocks scratch (nodeScratchLengths k)) := by
    refine ⟨?_, (hout r hr).2.1, Fp.disj_sup_right.mpr ⟨(hout r hr).2.2, ?_⟩⟩
    · rw [Mem.room_eq_of_below hBelow (hOutputLive r)]
      exact (hout r hr).1
    · exact (Fp.blocks_disj_above (hOutputLive r)).mono le_rfl hsAbove
  have hbody := writes_nodeBody (μ := ⟨store, μ.pos⟩) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (d := d) (lo := lo) (k := k) (ua := ua) (ea := ea)
    M dec mm qr hS hL hC hMM hQR hQ
    R0 beta R eps U S A hk hslot hactive hexact
    hlBody ((Mem.readBlocks_eq_of_below (m := μ) (m' := ⟨store, μ.pos⟩)
      (ls := nodeInputLengths n k) hBelow hInputLive).trans hread)
    hsRoom hsApart hsProtect hout'
  exact (hbody.in_frame rfl rfl hlBody).mono
    (sup_le le_sup_left (hsAbove.trans le_sup_right)) (fun _ _ h => h)

end NLAlib.SpectralBisection
