/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownSlots
public import NLAlib.Eigensolvers.SpectralBisection.DownNodeWork
public import NLAlib.Eigensolvers.SpectralBisection.DownPrepareReads
public import NLAlib.Eigensolvers.SpectralBisection.SlotWork
public import NLAlib.Ops.Logic.WeightedLoop

/-!
# Actual matrix-kernel work of downward slot scans

The bounded size query selects the local cost at the actual stored size. The word proof's
completed-prefix frame preserves later sizes, so the scan charges the mathematical partition
rather than the static union of all possible query answers.

## Main results

* `NLAlib.SpectralBisection.downSlot_kernelWeight_le_of_exec`: actual selected-node work.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A slot's bounded query chooses its actual stored size. Queries and inactive-slot guards
have zero matrix weight, and the active body has the existing local node bound. The initial
count and live scratch history are arbitrary. -/
theorem downSlot_kernelWeight_le_of_exec {K : Type}
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} {dec : K → ℝ} (hQ : IsToNat dec I)
    (T : ℕ → ℕ) (W : DenseOp → List ℕ → ℕ) {τ : Tape K} {n L cap d lo k : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ} {word : K}
    {a b : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hSize : a.mem.store.get sz.1 (sz.2 + n * d + lo) = some word)
    (hDecode : dec word = k) (hBound : k ≤ n - lo)
    (hr : evalCounted I W τ downSlotsBody
      ((Env.frame [n, L, cap, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t]).pushIdx lo)
      a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost + (2 * cap + 9) * T k := by
  have hidx := hQ.index_eq_of_decode_nat (m := a.mem)
    (x := (sz.1, sz.2 + n * d + lo)) hSize hDecode
  dsimp only [downSlotsBody, downNodesImpl] at hr
  rw [evalCounted] at hr
  simp only [Operand.evalList, Operand.eval, Env.pushIdx, Env.frame, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, IExp.eval,
    Nat.ofNat_pos, Nat.lt_add_one, IExp.eval_sub, Option.map_some,
    Option.bind_some, hidx, hBound, ↓reduceIte] at hr
  have he := evalCounted_weight_le
    (Dense.matrixWeight (MatrixOp.dimensionWeight T)) (fun _ _ => 0) hr
  have ht : Count.lift (Sum.elim (Dense.matrixWeight (MatrixOp.dimensionWeight T))
      (fun (_ : CmpTst ⊕ IdxTst) _ => 0))
      (a.tick (Has.inj IdxTst.toNat) []).cost = Dense.kernelWeight T a.cost := by
    simp [St.tick, Dense.kernelWeight, map_add, Count.test, Count.lift_single]
  rw [ht] at he
  refine he.trans (Nat.add_le_add_left ?_ _)
  apply stmtWeightedCost_ifZero_le
  intro i
  apply stmtWeightedCost_frame_le (d := [n, L, cap, d, lo, k])
  · simp [IExp.evalList, IExp.eval]
  · exact fun os => downNode_matrixWork_le T n L cap d lo k os

/-- The actual scan charges its selected stored sizes, with arbitrary prior counts. Its
ordinary per-slot word rule preserves exactly the pending inputs used by later size queries. -/
theorem downNodes_kernelWeight_sum_le_of_exec {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hC : IsCmp dec I) (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    (hQR : IsMatrixQR (EntryCodec.pair K) qr I) (hQ : IsToNat dec I)
    {τ : Tape K} {μ : Mem K} {n L fuel d : ℕ}
    {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ}
    (ks : ℕ → ℕ) (A : (lo : ℕ) → Matrix (Fin (ks lo)) (Fin (ks lo)) (K × K))
    (R0 beta R eps : K) (U : ℕ → K) (S : ℕ → ℕ → K × K)
    (hslot : ∀ lo < n, lo + ks lo ≤ n) (hexact : IsExactNatLit dec M (max n 4))
    (hsizes : ∀ lo < n, μ.store.get sz.1 (sz.2 + n * d + lo) = some (M.lit (ks lo : ℕ)))
    (hread : ∀ lo < n, 0 < ks lo →
      μ.readBlocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo)) =
        some (nodeInputWords M n R0 beta R eps (U lo) S (A lo)))
    (hG : DownLevelGeometry n d ks par lv su sg ma ua qa ea sz kd kp c t μ.store)
    (T : ℕ → ℕ) (W : DenseOp → List ℕ → ℕ)
    {a b : St DenseOp (CmpTst ⊕ IdxTst) K} (hmem : a.mem = μ)
    (hr : evalCounted I W τ (downNodesImpl (node (Op := DenseOp)
      (Tst := CmpTst ⊕ IdxTst))).body
      (Env.frame [n, L, fuel, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost +
      ∑ lo ∈ Finset.range n, (2 * fuel + 9) * T (ks lo) := by
  subst μ
  let region := fun lo => downRegion n d lo (ks lo) ma ua qa ea sz kd kp
  let pre :=  fun i => Fp.loopPrefix region i ⊔ Store.inBlock t.1 (t.2 + 4) 1
  have hsize (lo : ℕ) (hlo : lo < n) (ν : Mem K)
      (hfr : a.mem.store.EqOff (pre lo) ν.store) :=
    hfr.keep (Store.readsOnly_get sz.1 (sz.2 + n * d + lo) _)
      ((hG.pending lo hlo).mono le_rfl le_sup_left) (hsizes lo hlo)
  have hb := evalCounted_loop_weight_of_writes (I := I) (W := W) (a := a) (b := b)
    (body := downSlotsBody) (n := .var 0) (N := n)
    (ρ := Env.frame [n, L, fuel, d]
      [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t]) rfl pre (fun i _ => sup_le_sup
      (fun z j ⟨k, hk, hc⟩ => ⟨k, by omega, hc⟩) le_rfl)
    (fun _ _ => True) trivial ?_ (Dense.kernelWeight T)
    (fun lo => (2 * fuel + 9) * T (ks lo)) ?_ hr
  · exact hb.1
  · intro lo hlo ν hfr _
    have hg := hG.congr hfr.length_eq hfr.len_eq
    have hi : 0 < ks lo → Fp.Disj (pre lo)
        (Fp.blocks (nodeInputs n d lo par lv su sg ma c) (nodeInputLengths n (ks lo))) := by
      intro hp
      have h := hG.pending lo hlo
      rw [if_pos hp] at h
      exact h.mono le_rfl le_sup_right
    have hw := writes_downSlot M dec mm qr (τ := τ) (μ := ν)
      (n := n) (L := L) (fuel := fuel) (d := d) (lo := lo)
      hS hL hC hMM hQR hQ (A lo) R0 beta R eps (U lo) S (hslot lo hlo) hexact
      hg.live hg.scratch_room (hsize lo hlo ν hfr)
      (fun hp => Mem.readBlocks_of_eqOff hfr (hi hp) (hread lo hlo hp))
      (fun hp => (hi hp).mono le_sup_right le_rfl) (fun hp =>
        ⟨⟨(hg.nodes lo hlo hp).1.1.congr (fun _ => rfl), (hg.nodes lo hlo hp).1.2⟩,
          fun r hr => ⟨((hg.nodes lo hlo hp).2 r hr).1.congr (fun _ => rfl),
            ((hg.nodes lo hlo hp).2 r hr).2⟩⟩)
    refine hw.mono (sup_le ?_ le_sup_right) (fun _ _ _ => trivial)
    exact (activeStepFp_le_downRegion M dec mm qr (hslot lo hlo)
      R0 beta R eps (U lo) S (A lo) ma ua qa ea sz kd kp).trans
      (fun z j hj => Or.inl ⟨lo, by omega, hj⟩)
  · intro lo hlo x y hfr _ hxy
    exact downSlot_kernelWeight_le_of_exec hQ T W (hsize lo hlo x.mem hfr)
      (hexact (ks lo) (by have := hslot lo hlo; omega))
      (by have := hslot lo hlo; omega) hxy

end NLAlib.SpectralBisection
