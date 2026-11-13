/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpLevel
public import NLAlib.Eigensolvers.SpectralBisection.UpSlotsWork
public import NLAlib.Ops.Logic.Count

/-!
# Actual matrix-kernel work of an allocated upward level

The scalar shift prefix has zero matrix weight. Its actual writes supply the stored shifts
for the slot scan, and allocation/cleanup preserve the counted kernel increment.

## Main results

* `NLAlib.SpectralBisection.upLevel_kernelWeight_sum_le_of_exec`: actual parent-size costs.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private abbrev upLevelBody : Stmt DenseOp (CmpTst ⊕ IdxTst) :=
  (upLevel (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).splitAllocations.2

private def shiftsIns : List (ScalarIns ScalarOp) :=
  [⟨.div, [⟨0, .var 2 + .const 2 * .var 1⟩, ⟨7, .var 9 + .const 1⟩], ⟨8, .const 0⟩⟩,
    ⟨.neg, [⟨8, .const 0⟩], ⟨8, .const 1⟩⟩]

section

variable {K Su Sg : Type} [Inhabited K] {M : Machine K} {dec : K → ℝ}
  (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K)
  {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} (hS : IsScalar M I) (hQ : IsToNat dec I)
  (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {τ : Tape K} {m : Mem K}
  {n d : ℕ} {R : K} {ma lv ua qa ea sz kd kp c : ℕ × ℕ}
  (ks : ℕ → ℕ) (ws : ℕ → K) (steps : ∀ lo, EighStep K (ks lo))
  (children : (lo : ℕ) → (b : Bool) →
    Matrix (Fin ((steps lo).childSize b)) (Fin ((steps lo).childSize b)) (K × K) ×
      (Fin ((steps lo).childSize b) → K))
  (hl : m.Live [lv, ua, qa, ea, sz, kd, kp, c, ma])
  (hR : m.store.get lv.1 (lv.2 + 2 * d) = some R)
  (hTwo : m.store.get c.1 (c.2 + 1) = some (M.lit 2))
  (hSizes : m.store.HoldsVec sz.1 (sz.2 + n * d) n ws)
  (hDecode : ∀ lo < n, dec (ws lo) = ks lo) (hBound : ∀ lo < n, ks lo ≤ n - lo)
  (hSteps : ∀ lo < n, 0 < ks lo → StoresStep M R n d lo ma ua qa ea sz kd kp (steps lo) m)
  (hChildren : ∀ lo < n, 0 < ks lo → ∀ b, (steps lo).HasChild b →
    StoresResult n (d + 1) ((steps lo).childSlot lo b) ua ea (children lo b) m.store)
  (hLit : IsExactNatLit dec M (max n 4))
  (hRoom : ∀ lo < n, m.Room (resultOperands n d lo ua ea) (resultLengths (ks lo)))
  (hApart : ∀ lo < n, Fp.Apart
    (upNodeRegions n d lo ua qa ea kd kp (m.store.length, 0)) (upNodeRegionLengths n (ks lo)))
  (hSizesProtect : Fp.Disj (resultLevelFootprint n d ks ua ea)
    (Store.inBlock sz.1 (sz.2 + n * d) n))
  (hForward : ∀ j lo, j < lo → lo < n → 0 < ks lo →
    Fp.Disj (Fp.blocks (resultOperands n d j ua ea) (resultLengths (ks j)))
      (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp (steps lo))
        (stepOutputLengths (steps lo))))
  (hChildProtect : ∀ lo < n, ∀ b, (steps lo).HasChild b →
    Fp.Disj (resultLevelFootprint n d ks ua ea)
      (Fp.blocks (resultOperands n (d + 1) ((steps lo).childSlot lo b) ua ea)
        (resultLengths ((steps lo).childSize b))))

include mm qr unif normal hS hQ hMM hl hR hTwo hSizes hDecode hBound hSteps hChildren hLit
  hRoom hApart hSizesProtect hForward hChildProtect in
private theorem body_weight (T : ℕ → ℕ) (W : DenseOp → List ℕ → ℕ)
    {a b : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hLength : a.mem.store.length = m.store.length + 1)
    (hT : a.mem.store.len m.store.length = 2)
    (hBelow : Store.Below m.store.length m.store a.mem.store)
    (hr : evalCounted I W τ upLevelBody
      ⟨(Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c]).idx,
        (Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c]).buf ++ [m.store.length]⟩ a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost +
      ∑ lo ∈ Finset.range n, 2 * T (ks lo) := by
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl
  let ρ := Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c]
  let ρt : Env := ⟨ρ.idx, ρ.buf ++ [m.store.length]⟩
  let v : ℕ → K := fun i => if i = 0 then M.div R (M.lit 2) else M.neg (M.div R (M.lit 2))
  let scalar : Stmt DenseOp (CmpTst ⊕ IdxTst) := Stmt.scalarBlock (shiftsIns.map ScalarIns.lift)
  have hR₀ := ((hBelow lv.1 hl.1).2 (lv.2 + 2 * d)).trans hR
  have hTwo₀ := ((hBelow c.1 hl.2.2.2.2.2.2.2.1).2 (c.2 + 1)).trans hTwo
  have hev : ScalarIns.evalBlock M.eval ρt shiftsIns a.mem.store.cellFn =
      some ((List.range 2).map fun i => ((m.store.length, 0 + i), v i)) := by
    simp [shiftsIns, v, ρt, ρ, ScalarIns.evalBlock, Operand.evalList, Operand.eval, Env.frame,
      IExp.eval, Store.cellFn, Machine.eval, hR₀, hTwo₀, List.range_succ]
  have hCall := writes_machineScalarBlock_readBlock (τ := τ) (m := a.mem)
    (z := (m.store.length, 0)) (n := 2) (v := v) hS hev
    (by simpa only [Nat.zero_add] using le_of_eq hT.symm)
  dsimp only [upLevelBody, upLevel, Stmt.splitAllocations, Stmt.alloc] at hr
  rw [evalCounted] at hr
  obtain ⟨a₁, h₁, hr⟩ := Option.bind_eq_some_iff.mp hr
  rw [evalCounted] at hr
  obtain ⟨a₂, h₂, hr⟩ := Option.bind_eq_some_iff.mp hr
  have hs : evalCounted I W τ scalar ρt a = some a₂ := by
    simp only [scalar, shiftsIns, List.map_cons, List.map_nil, Stmt.scalarBlock,
      ScalarIns.lift, ScalarIns.stmt]
    rw [evalCounted, h₁, Option.bind_some]
    exact h₂
  obtain ⟨hfr, hp, hshift⟩ := hCall.post_of_evalCounted hs
  have hc := evalCounted_weight_le (Dense.matrixWeight (MatrixOp.dimensionWeight T))
    (fun _ _ => 0) hs
  rw [stmtWeightedCost_matrix_zero_of_allOps _ _ (by rfl), Nat.add_zero] at hc
  have hBelow₂ := hBelow.trans (hfr.below_of_above (L := m.store.length) (by
    rintro z i ⟨rfl, _, _⟩
    exact le_rfl))
  have hSizes₂ := hBelow₂.keep (Store.readsOnly_holdsVec _ _ _ _) (by
    rintro z i ⟨rfl, _, _⟩
    exact hl.2.2.2.2.1) hSizes
  have hShifts : a₂.mem.store.readBlock m.store.length 0 2 =
      some [M.div R (M.lit 2), M.neg (M.div R (M.lit 2))] := by
    simpa [v, List.range_succ] using hshift
  have hrNodes := evalCounted_frame_body (d := [n, d])
    (as := [ua, qa, ea, sz, kd, kp, (m.store.length, 0)]) rfl rfl hr
  have hn := upNodes_kernelWeight_le_of_exec mm qr unif normal hS hQ hMM ks ws steps children
    (by room) hSizes₂ hDecode hBound
    (fun lo hlo hpos => (hSteps lo hlo hpos).of_below hBelow₂
      (live_stepOutputs (m := m) (by room) (steps lo)))
    (fun lo hlo hpos b hb => (hChildren lo hlo hpos b hb).of_below hBelow₂
      hl.2.1 hl.2.2.2.1) hLit hShifts (fun lo hlo => ?_) hApart hSizesProtect ?_
    hForward hChildProtect T W rfl hrNodes
  · exact hn.trans (Nat.add_le_add_right hc _)
  · rw [Mem.room_eq_of_below hBelow₂ (by
      intro z hz
      simp only [resultOperands, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hl.2.1
      · exact hl.2.2.2.1)]
    exact hRoom lo hlo
  · exact (disj_resultLevelFootprint_above hl.2.1 hl.2.2.2.1).mono le_rfl
      (fun z i h => by rcases h with ⟨rfl, _, _⟩; exact le_rfl)

include mm qr unif normal hS hQ hMM hl hR hTwo hSizes hDecode hBound hSteps hChildren hLit
  hRoom hApart hSizesProtect hForward hChildProtect in
/-- One allocated upward level adds the matrix costs at its actual parent sizes. Its scalar
prologue and allocation/cleanup contribute zero to this projection, for arbitrary prior
count history and live scratch. Termination is supplied by the existing total word theorem. -/
theorem upLevel_kernelWeight_sum_le_of_exec (T : ℕ → ℕ) (W : DenseOp → List ℕ → ℕ)
    {a b : St DenseOp (CmpTst ⊕ IdxTst) K} (hmem : a.mem = m)
    (hr : evalCounted I W τ (upLevel (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      (Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost +
      ∑ lo ∈ Finset.range n, 2 * T (ks lo) := by
  subst m
  let p := (upLevel (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).splitAllocations
  have he : IExp.evalList (Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c]).idx
      (p.1.map Prod.snd) = some [2] := rfl
  rw [← Stmt.allocsAs_splitAllocations
    (upLevel (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))] at hr
  obtain ⟨inner, final, hb, hlen, hlens, hBelow, hpos, hcost, hfinal⟩ :=
    evalCounted_allocsAs_inv he hr
  have hT : inner.mem.store.len a.mem.store.length = 2 := by
    simpa using hlens 0 (by simp)
  have hw := body_weight mm qr unif normal hS hQ hMM ks ws steps children
    hl hR hTwo hSizes hDecode hBound hSteps hChildren hLit hRoom hApart
    hSizesProtect hForward hChildProtect T W (by simpa using hlen) hT hBelow (by
      simpa using hb)
  simpa only [hcost, hfinal] using hw

end

end NLAlib.SpectralBisection
