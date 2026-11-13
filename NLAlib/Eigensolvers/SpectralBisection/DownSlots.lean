/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownNode
public import NLAlib.Eigensolvers.SpectralBisection.DownGeometry
public import NLAlib.Eigensolvers.SpectralBisection.StepRead
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# A complete downward slot scan

Actual stored size words determine the active nodes. Mathematical slot intervals separate
output reservations; a precise completed-prefix frame retains each pending node's input matrix
and size word. The scan reuses one scalar scratch cell and returns the existing stored step at
every active slot, without introducing an execution-stage record.

## Main results

* `NLAlib.SpectralBisection.writes_downNodes`: the actual size-query loop stores all active steps.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The actual subtree of the downward loop before its stored-size query. This abbreviation
does not add a frame or alter any instruction of the program. -/
abbrev downSlotsBody {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
    [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst] : Stmt Op Tst :=
  match (downNodesImpl (node (Op := Op) (Tst := Tst))).body with
  | .loop _ body => body
  | _ => .abort

/-- One stored-size query and its active-node branch satisfy total correctness from actual
word reads and node output geometry. Inactive slots perform no node call. -/
theorem writes_downSlot {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) {τ : Tape K} {μ : Mem K} {n L fuel d lo k : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ}
    (A : Matrix (Fin k) (Fin k) (K × K)) (R0 beta R eps U : K) (S : ℕ → ℕ → K × K)
    (hslot : lo + k ≤ n) (hexact : IsExactNatLit dec M (max n 4))
    (hl : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t])
    (ht : t.2 + 5 ≤ μ.store.len t.1)
    (hsize : μ.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit (k : ℕ)))
    (hread : 0 < k → μ.readBlocks (nodeInputs n d lo par lv su sg ma c)
      (nodeInputLengths n k) = some (nodeInputWords M n R0 beta R eps U S A))
    (hprotect : 0 < k → Fp.Disj (Store.inBlock t.1 (t.2 + 4) 1)
      (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k)))
    (hgeometry : 0 < k →
      (μ.Room [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] ∧
        Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1] ∧
        Fp.Disj (Fp.blocks [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)] [2 * (k * k), k, 1])
          (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) ∧
      ∀ r ≤ k, μ.Room (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r) ∧
        Fp.Apart (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r) ∧
        Fp.Disj (Fp.blocks (branchOutputs n d lo k r ma qa sz kd kp) (branchLengths k r))
          (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n k))) :
    let N := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    let outcome := eighStep N n fuel R0 beta A R eps (L + d) (storedNodeSample n lo U S)
    Writes .total I τ (downSlotsBody (Op := Op) (Tst := Tst))
      ((Env.frame [n, L, fuel, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t]).pushIdx lo)
      (activeStepFp n d lo ma ua qa ea sz kd kp outcome ⊔ Store.inBlock t.1 (t.2 + 4) 1)
      (fun ν => ν.pos = μ.pos ∧ if 0 < k then
        StoresStep M R n d lo ma ua qa ea sz kd kp outcome ν else True) μ := by
  dsimp only
  have hkn : k ≤ n := by omega
  refine writes_bindIdx_of_decode_nat (x := (sz.1, sz.2 + n * d + lo)) (n := k)
    (B := n - lo) hQ
    (by simp [Operand.eval, IExp.eval, Env.frame, Env.pushIdx, Nat.add_assoc])
    rfl hsize (hexact k (hkn.trans (Nat.le_max_left _ _))) (by omega) ?_
  refine writes_ifPos (n := k) rfl ?_
  by_cases hpos : 0 < k
  · rw [if_pos hpos]
    have hg := hgeometry hpos
    have hn := writes_downNode M dec mm qr (τ := τ) (μ := μ)
      (n := n) (L := L) (fuel := fuel) (d := d) (lo := lo) (k := k)
      (par := par) (lv := lv) (su := su) (sg := sg) (ma := ma) (ua := ua)
      (qa := qa) (ea := ea) (sz := sz) (kd := kd) (kp := kp) (c := c) (t := t)
      hS hL hC hMM hQR hQ R0 beta R eps U S A hpos hslot
      (hexact.mono (max_le_max hkn le_rfl)) hl (hread hpos) ht (hprotect hpos) hg.1 hg.2
    refine (writes_frame rfl rfl hl hn).mono ?_ ?_
    · simp only [activeStepFp, if_pos hpos]
      exact le_rfl
    · intro ν _ h
      exact ⟨h.1, by simpa only [if_pos hpos] using h.2⟩
  · rw [if_neg hpos]
    exact ⟨rfl, by simp only [if_neg hpos]⟩

/-- The actual bounded size queries and active-node calls return one mathematical stored step
per positive-size slot. A partition of slot intervals and one apart collection of output levels
retain all completed outcomes; pending inputs are protected by the exact prefix frame. -/
theorem writes_downNodes {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
    [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) {τ : Tape K} {μ : Mem K} {n L fuel d : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ}
    (ks : ℕ → ℕ) (A : (lo : ℕ) → Matrix (Fin (ks lo)) (Fin (ks lo)) (K × K))
    (R0 beta R eps : K) (U : ℕ → K) (S : ℕ → ℕ → K × K)
    (hslot : ∀ lo < n, lo + ks lo ≤ n)
    (hintervals : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (Finset.Ico i (i + ks i)) (Finset.Ico j (j + ks j)))
    (hexact : IsExactNatLit dec M (max n 4))
    (hl : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t])
    (ht : t.2 + 5 ≤ μ.store.len t.1)
    (hsizes : ∀ lo < n, μ.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit (ks lo : ℕ)))
    (hread : ∀ lo < n, 0 < ks lo →
      μ.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)) =
        some (nodeInputWords M n R0 beta R eps (U lo) S (A lo)))
    (hAP : Fp.Apart (List.ofFn (downArenaOrigins n d ma ua qa ea sz kd kp))
      (List.ofFn fun i => downArenaStride n i * n))
    (hscratch : Fp.Disj (Store.inBlock t.1 (t.2 + 4) 1)
      (downLevelRegion n d ma ua qa ea sz kd kp))
    (hpending : ∀ lo < n, Fp.Disj
      (Fp.loopPrefix (fun j => downRegion n d j (ks j) ma ua qa ea sz kd kp) lo ⊔
        Store.inBlock t.1 (t.2 + 4) 1)
      (Store.inBlock sz.1 (sz.2 + n * d + lo) 1 ⊔
        if 0 < ks lo then
          Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)) else ⊥))
    (hgeometry : ∀ lo < n, 0 < ks lo →
      (μ.Room [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
          [2 * (ks lo * ks lo), ks lo, 1] ∧
        Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
          [2 * (ks lo * ks lo), ks lo, 1] ∧
        Fp.Disj (Fp.blocks [(ua.1, ua.2 + 2 * (n * n) * d + 2 * n * lo),
          (ea.1, ea.2 + n * d + lo), (kd.1, kd.2 + n * d + lo)]
          [2 * (ks lo * ks lo), ks lo, 1])
          (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)))) ∧
      ∀ r ≤ ks lo,
        μ.Room (branchOutputs n d lo (ks lo) r ma qa sz kd kp) (branchLengths (ks lo) r) ∧
        Fp.Apart (branchOutputs n d lo (ks lo) r ma qa sz kd kp) (branchLengths (ks lo) r) ∧
        Fp.Disj (Fp.blocks (branchOutputs n d lo (ks lo) r ma qa sz kd kp)
          (branchLengths (ks lo) r))
          (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)))) :
    let N := M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2)
    let steps := fun lo => eighStep N n fuel R0 beta (A lo) R eps (L + d)
      (storedNodeSample n lo (U lo) S)
    Writes .total I τ (downNodesImpl (node (Op := Op) (Tst := Tst))).body
      (Env.frame [n, L, fuel, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t])
      (Fp.loopPrefix (fun lo => activeStepFp n d lo ma ua qa ea sz kd kp (steps lo)) n ⊔
        Store.inBlock t.1 (t.2 + 4) 1)
      (fun μ' => μ'.pos = μ.pos ∧ ∀ lo < n, 0 < ks lo →
        StoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) μ') μ := by
  classical
  dsimp only
  let steps := fun lo => eighStep
    (M.toFloatMachine dec mm qr M.mul (fun z : K × K => M.normalWords z.1 z.2))
    n fuel R0 beta (A lo) R eps (L + d) (storedNodeSample n lo (U lo) S)
  let region := fun lo => activeStepFp n d lo ma ua qa ea sz kd kp (steps lo)
  let result := fun lo store => if 0 < ks lo then
    StoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) ⟨store, μ.pos⟩ else True
  have hSub (lo : ℕ) (hi : lo < n) :
      region lo ≤ downRegion n d lo (ks lo) ma ua qa ea sz kd kp :=
    activeStepFp_le_downRegion M dec mm qr (hslot lo hi) R0 beta R eps (U lo) S (A lo)
      ma ua qa ea sz kd kp
  refine (writes_loop_disjoint_prefix_scratch (I := I) (τ := τ)
    region result rfl (fun lo hi b x hx => Or.inl ⟨lo, hi, hx⟩)
    le_sup_right (fun i hi j hj hij =>
      (disj_downRegion (hslot i hi) (hslot j hj) (hintervals i hi j hj hij)
        ma ua qa ea sz kd kp hAP).mono (hSub i hi) (hSub j hj))
    (fun lo hi => hscratch.mono le_rfl
      ((hSub lo hi).trans (downRegion_le_level (hslot lo hi) _ _ _ _ _ _ _)))
    ?_ ?_).mono le_rfl ?_
  · intro lo hi
    exact readsOnly_activeStoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) μ.pos
  · intro lo hi μ' hfr
    have hfrCoarse : μ.store.EqOff
        (Fp.loopPrefix (fun j => downRegion n d j (ks j) ma ua qa ea sz kd kp) lo ⊔
          Store.inBlock t.1 (t.2 + 4) 1) μ'.store :=
      hfr.mono (sup_le ((Fp.loopPrefix_mono (fun j hj => hSub j (by omega))).trans
        le_sup_left) le_sup_right)
    have hsize := hfrCoarse.keep (Store.readsOnly_get sz.1 (sz.2 + n * d + lo)
      (M.lit (ks lo : ℕ))) ((hpending lo hi).mono le_rfl le_sup_left) (hsizes lo hi)
    have hinput (hpos : 0 < ks lo) : Fp.Disj
          (Fp.loopPrefix (fun j => downRegion n d j (ks j) ma ua qa ea sz kd kp) lo ⊔
            Store.inBlock t.1 (t.2 + 4) 1)
          (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo))) := by
      have hp := hpending lo hi
      rw [if_pos hpos] at hp
      exact hp.mono le_rfl le_sup_right
    have hLive : μ'.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t] := by
      simpa only [Mem.Live, hfr.length_eq] using hl
    have hSlot := writes_downSlot M dec mm qr hS hL hC hMM hQR hQ
      (τ := τ) (μ := μ') (L := L) (fuel := fuel) (A lo) R0 beta R eps (U lo) S
      (hslot lo hi) hexact hLive (by rw [hfr.len_eq]; exact ht) hsize
      (fun hpos => Mem.readBlocks_of_eqOff hfrCoarse (hinput hpos) (hread lo hi hpos))
      (fun hpos => (hinput hpos).mono le_sup_right le_rfl)
      (fun hpos => by
        have hg := hgeometry lo hi hpos
        exact ⟨⟨hg.1.1.congr hfr.len_eq, hg.1.2⟩,
          fun r hr => ⟨(hg.2 r hr).1.congr hfr.len_eq, (hg.2 r hr).2⟩⟩)
    refine hSlot.mono le_rfl ?_
    intro μ'' _ h
    refine ⟨h.1, ?_⟩
    by_cases hpos : 0 < ks lo
    · have hs := h.2
      rw [if_pos hpos] at hs
      simpa only [result, steps, if_pos hpos] using StoresStep.of_store_eq
        (μ := μ'') (ν := ⟨μ''.store, μ.pos⟩) rfl hs
    · simp only [result, if_neg hpos]
  · intro μ' _ h; refine ⟨h.1, fun lo hi hpos => ?_⟩
    have hs : StoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) ⟨μ'.store, μ.pos⟩ := by
      simpa only [result, if_pos hpos] using h.2 lo hi
    simpa only [steps] using StoresStep.of_store_eq (μ := ⟨μ'.store, μ.pos⟩) (ν := μ') rfl hs

end NLAlib.SpectralBisection
