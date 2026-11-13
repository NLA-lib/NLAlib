/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpNodes
public import NLAlib.Eigensolvers.SpectralBisection.UpWork
public import NLAlib.Ops.Logic.WeightedLoop

/-!
# Actual matrix-kernel work across an upward slot scan

The stored size selects the actual local kernel bound. The same prefix footprint used by
the word proof protects future size words, outcomes and child results from earlier writes.

## Main results

* `NLAlib.SpectralBisection.upNodes_kernelWeight_le_of_exec`: partition-sensitive slot sum.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private abbrev upSlotsBody : Stmt DenseOp (CmpTst ⊕ IdxTst) :=
  match (upNodesImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body with
  | .loop _ body => body
  | _ => .abort


private theorem round_weight {K : Type} {I : Interp DenseOp (CmpTst ⊕ IdxTst) K}
    {dec : K → ℝ} (hQ : IsToNat dec I) (T : ℕ → ℕ) (W : DenseOp → List ℕ → ℕ)
    {τ : Tape K} {n d lo k : ℕ} {ua qa ea sz kd kp t : ℕ × ℕ} {w : K}
    {a b : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hSize : a.mem.store.get sz.1 (sz.2 + n * d + lo) = some w)
    (hDecode : dec w = k) (hBound : k ≤ n - lo)
    (hr : evalCounted I W τ upSlotsBody
      ((Env.frame [n, d] [ua, qa, ea, sz, kd, kp, t]).pushIdx lo) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost + 2 * T k := by
  have hidx := hQ.index_eq_of_decode_nat (m := a.mem)
    (x := (sz.1, sz.2 + n * d + lo)) hSize hDecode
  dsimp only [upSlotsBody, upNodesImpl] at hr
  rw [evalCounted] at hr
  simp only [Operand.evalList, Operand.eval, Env.pushIdx, Env.frame, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
    Nat.reduceLT, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, IExp.eval,
    Nat.ofNat_pos, Nat.one_lt_ofNat, Nat.lt_add_one, IExp.eval_sub, Option.map_some,
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
  apply stmtWeightedCost_frame_le_of_length (d := [n, d, lo, k])
  · simp [IExp.evalList, IExp.eval]
  · exact fun os hos => weightedCost_upNode_le T n d lo k os hos


section

variable {K Su Sg : Type} [Inhabited K] {M : Machine K} {dec : K → ℝ}
  (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K)
  {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} (hS : IsScalar M I) (hQ : IsToNat dec I)
  (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {m : Mem K}
  {n d : ℕ} {R : K} {ma ua qa ea sz kd kp t : ℕ × ℕ}
  (ks : ℕ → ℕ) (ws : ℕ → K) (steps : ∀ lo, EighStep K (ks lo))
  (children : (lo : ℕ) → (b : Bool) →
    Matrix (Fin ((steps lo).childSize b)) (Fin ((steps lo).childSize b)) (K × K) ×
      (Fin ((steps lo).childSize b) → K))
  (hl : m.Live [ua, qa, ea, sz, kd, kp, t])
  (hSizes : m.store.HoldsVec sz.1 (sz.2 + n * d) n ws)
  (hDecode : ∀ lo < n, dec (ws lo) = ks lo) (hBound : ∀ lo < n, ks lo ≤ n - lo)
  (hSteps : ∀ lo < n, 0 < ks lo → StoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) m)
  (hChildren : ∀ lo < n, 0 < ks lo → ∀ b, (steps lo).HasChild b →
    StoresResult n (d + 1) ((steps lo).childSlot lo b) ua ea (children lo b) m.store)
  (hLit : IsExactNatLit dec M (max n 4))
  (ht : m.store.readBlock t.1 t.2 2 =
    some [M.div R (M.lit 2), M.neg (M.div R (M.lit 2))])
  (hRoom : ∀ lo < n, m.Room (resultOperands n d lo ua ea) (resultLengths (ks lo)))
  (hApart : ∀ lo < n,
    Fp.Apart (upNodeRegions n d lo ua qa ea kd kp t) (upNodeRegionLengths n (ks lo)))
  (hSizesProtect : Fp.Disj (resultLevelFootprint n d ks ua ea)
    (Store.inBlock sz.1 (sz.2 + n * d) n))
  (hShiftsProtect : Fp.Disj (resultLevelFootprint n d ks ua ea) (Store.inBlock t.1 t.2 2))
  (hForward : ∀ j lo, j < lo → lo < n → 0 < ks lo →
    Fp.Disj (Fp.blocks (resultOperands n d j ua ea) (resultLengths (ks j)))
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp (steps lo))
        (stepOutputLengths (steps lo))))
  (hChildProtect : ∀ lo < n, ∀ b, (steps lo).HasChild b →
    Fp.Disj (resultLevelFootprint n d ks ua ea)
      (Fp.blocks (resultOperands n (d + 1) ((steps lo).childSlot lo b) ua ea)
        (resultLengths ((steps lo).childSize b))))

include mm qr unif normal hS hQ hMM hl hSizes hDecode hBound hSteps hChildren hLit ht
  hRoom hApart hSizesProtect hShiftsProtect hForward hChildProtect in
private theorem writes_round (lo : ℕ) (hlo : lo < n) (m' : Mem K)
    (hfr : m.store.EqOff (Fp.loopPrefix
      (fun j => Fp.blocks (resultOperands n d j ua ea) (resultLengths (ks j))) lo) m'.store) :
    Writes .total I τ upSlotsBody
      ((Env.frame [n, d] [ua, qa, ea, sz, kd, kp, t]).pushIdx lo)
      (Fp.blocks (resultOperands n d lo ua ea) (resultLengths (ks lo))) (fun _ => True) m' := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  have hfrAll : m.store.EqOff (resultLevelFootprint n d ks ua ea) m'.store :=
    hfr.mono (fun b i ⟨j, hj, hx⟩ => ⟨j, hj.trans hlo, hx⟩)
  have hsizes := hfrAll.keep (Store.readsOnly_holdsVec _ _ _ _) hSizesProtect hSizes
  have hshifts := hfrAll.keep (Store.readsOnly_readBlock _ _ _ _) hShiftsProtect ht
  have ht' : m'.store.get t.1 t.2 = some (M.div R (M.lit 2)) ∧
      m'.store.get t.1 (t.2 + 1) = some (M.neg (M.div R (M.lit 2))) := by
    constructor
    · simpa using Store.get_of_readBlock hshifts (j := 0) (by omega) default
    · simpa using Store.get_of_readBlock hshifts (j := 1) (by omega) default
  refine writes_bindIdx_of_decode_nat hQ rfl rfl (hsizes lo hlo) (hDecode lo hlo)
    (hBound lo hlo) (writes_ifPos rfl ?_)
  split_ifs with hpos
  · have hStep := (hSteps lo hlo hpos).of_eqOff hfr (by
      rintro b i ⟨j, hj, hx⟩ hy
      exact hForward j lo hj hlo hpos b i hx hy)
    have hChild : ∀ b, (steps lo).HasChild b →
        StoresResult n (d + 1) ((steps lo).childSlot lo b) ua ea (children lo b) m'.store := by
      intro b hb
      exact (hChildren lo hlo hpos b hb).of_eqOff hfrAll (hChildProtect lo hlo b hb)
    exact (writes_frame rfl rfl (by room) (writes_upNode mm qr unif normal hS hQ hMM
      (steps lo) (children lo) hStep hChild hLit (by have := hBound lo hlo; omega)
      (by room) ht' ((hRoom lo hlo).congr hfr.len_eq) (hApart lo hlo))).mono
      le_rfl (fun _ _ _ => trivial)

include mm qr unif normal hS hQ hMM hl hSizes hDecode hBound hSteps hChildren hLit ht
  hRoom hApart hSizesProtect hShiftsProtect hForward hChildProtect in
/-- Actual upward slot iteration accumulates the costs at the stored node sizes, starting
from arbitrary prior counts and live scratch. The total word theorem supplies termination
separately; this auxiliary bound concerns that same existing counted evaluator. -/
theorem upNodes_kernelWeight_le_of_exec (T : ℕ → ℕ) (W : DenseOp → List ℕ → ℕ)
    {a b : St DenseOp (CmpTst ⊕ IdxTst) K} (hmem : a.mem = m)
    (hr : evalCounted I W τ (upNodesImpl (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      (Env.frame [n, d] [ua, qa, ea, sz, kd, kp, t]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost +
      ∑ lo ∈ Finset.range n, 2 * T (ks lo) := by
  subst m
  let region := fun lo => Fp.blocks (resultOperands n d lo ua ea) (resultLengths (ks lo))
  have hb := evalCounted_loop_weight_of_writes (I := I) (W := W) (a := a) (b := b)
    rfl (Fp.loopPrefix region) (fun i _ b x ⟨j, hj, hx⟩ => ⟨j, by omega, hx⟩)
    (fun _ _ => True) trivial ?_ (Dense.kernelWeight T) (fun lo => 2 * T (ks lo)) ?_ hr
  · exact hb.1
  · intro lo hlo m' hfr _
    exact (writes_round mm qr unif normal hS hQ hMM ks ws steps children
      hl hSizes hDecode hBound hSteps hChildren hLit ht hRoom hApart
      hSizesProtect hShiftsProtect hForward hChildProtect lo hlo m' hfr).mono
      (fun b x hx => ⟨lo, by omega, hx⟩) (fun _ _ _ => trivial)
  · intro lo hlo x y hfr _ hxy
    have hfrAll : a.mem.store.EqOff (resultLevelFootprint n d ks ua ea) x.mem.store :=
      hfr.mono (fun b i ⟨j, hj, hx⟩ => ⟨j, hj.trans hlo, hx⟩)
    have hsizes := hfrAll.keep (Store.readsOnly_holdsVec _ _ _ _) hSizesProtect hSizes
    exact round_weight hQ T W (hsizes lo hlo) (hDecode lo hlo) (hBound lo hlo) hxy

end


end NLAlib.SpectralBisection
