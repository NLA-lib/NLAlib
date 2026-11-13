/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpwardWork
public import NLAlib.Eigensolvers.SpectralBisection.UpLevelReferenceWork

/-!
# Matrix-kernel work of the complete reverse pass

The actual stored slot partitions justify two root-size kernel charges per upward level.
The existing eleven-arena geometry preserves the mathematical inputs and child results
through reverse iteration. Prior counts and live scratch are arbitrary.

## Main results

* `NLAlib.SpectralBisection.upwardPass_kernelWeight_le_of_arenas`: actual full upward work.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section Reference

variable {K Su Sg : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K))
  (qr : QRMap (K × K)) (n base fuel L : ℕ) (R0 eps beta : K) (ell : ℕ)
  (A : Matrix (Fin n) (Fin n) (K × K)) (τ : Tape K)
  (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "X" => (fun d => nodeAtSlot F n fuel R0 beta (EighNode.mk n A R0 eps ell) d)
local notation "KS" => (fun d lo => EighNode.k (X d lo))
local notation "ST" => (fun d lo => eighStep F n fuel R0 beta (EighNode.A (X d lo))
  (EighNode.R (X d lo)) (EighNode.ε (X d lo)) (EighNode.ℓ (X d lo)) (eighTapeSample n d lo))

/-- With the complete solver's arena capacity and apartness, the actual reverse pass adds
at most two root-size kernel charges per level. The supplied size cost is monotone and
superadditive. All input/model/storage prerequisites are explicit; there is no phase
execution callback or numerical-accuracy premise in this resource statement. -/
theorem upwardPass_kernelWeight_le_of_arenas (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {m : Mem K}
    (hl : m.Live (arenaOperands c ma ua qa ea sz kd kp lv su sg))
    (hRoom : m.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hLevel : ∀ d ≤ L, StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma sz lv m)
    (hRecords : ∀ d ≤ L, StoresRecords M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
      d ma ua qa ea sz kd kp m)
    (hBottom : StoresLevelResults F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
      0 (L + 1) ua ea m.store)
    (hTwo : m.store.get c.1 (c.2 + 1) = some (M.lit 2))
    (hLit : IsExactNatLit dec M (max n 4))
    (T : ℕ → ℕ) (hT : Monotone T) (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (W : DenseOp → List ℕ → ℕ) {a b : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hmem : a.mem = m)
    (hrun : evalCounted I W τ (upwardPass (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      (Env.frame [n, L] [lv, ua, qa, ea, sz, kd, kp, c]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost + (L + 1) * (2 * T n) := by
  have hBound (d lo : ℕ) := nodeAtSlot_k_le F n fuel R0 eps beta ell A d lo
  have hSlot (d lo : ℕ) (hlo : lo < n) : lo + KS d lo ≤ n := by
    dsimp only
    have := hBound d lo
    omega
  have hLive : m.Live [lv, ua, qa, ea, sz, kd, kp, c, ma] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hl _ (by simp [arenaOperands])
  apply upwardPass_weight_le_of_levels (M := M) (dec := dec) (mm := mm) (qr := qr)
    (n := n) (base := base) (fuel := fuel) (L := L) (R0 := R0) (eps := eps) (beta := beta)
    (ell := ell) (A := A) (τ := τ) (ma := ma) (lv := lv) (ua := ua) (qa := qa)
    (ea := ea) (sz := sz) (kd := kd) (kp := kp) (c := c) (m := m)
    unif normal hS hQ hMM hLive hBottom hLit
    (fun d => upReadRegion n d ma lv ua qa ea sz kd kp c) hLevel hRecords hTwo
    (fun d _ => readsOnly_storesLevel_upReadRegion M F n fuel R0 eps beta ell d A
      ma lv ua qa ea sz kd kp c m.pos)
    (fun d _ => readsOnly_storesRecords_upReadRegion M dec mm qr n base fuel τ
      R0 eps beta ell d A ma lv ua qa ea sz kd kp c m.pos)
    (fun d _ => constant_le_upReadRegion n d ma lv ua qa ea sz kd kp c)
    (fun r hr => disj_upwardPrefix_upReadRegion (by omega) KS (fun d _ => hSlot d)
      c ma ua qa ea sz kd kp lv su sg hAP)
    (fun r _ m' hfr lo hlo => room_result_of_arenas (by omega) (hSlot (L - r) lo hlo)
      c ma ua qa ea sz kd kp lv su sg (hRoom.congr hfr.len_eq))
    (fun r hr m' hfr lo hlo => apart_upNode_of_arenas (by omega) hlo
      (hSlot (L - r) lo hlo) c ma ua qa ea sz kd kp lv su sg (hl.congr hfr.length_eq) hAP)
    (fun d hd lo hlo j hj hne => disj_results_of_arenas (by omega)
      (hSlot d lo hlo) (hSlot d j hj)
      (disjoint_nodeAtSlot_intervals F n fuel R0 eps beta ell A d lo j hne)
      c ma ua qa ea sz kd kp lv su sg hAP)
    (fun d hd => disj_resultLevel_sizes_of_arenas (by omega) (KS d) (hSlot d)
      c ma ua qa ea sz kd kp lv su sg hAP)
    (fun d hd j lo hjl hlo hp => disj_results_step_of_arenas M dec mm qr base fuel τ
      R0 beta (X d lo) hd (hSlot d j (by omega)) (hSlot d lo hlo) hp
      (disjoint_nodeAtSlot_intervals F n fuel R0 eps beta ell A d j lo (by omega))
      c ma ua qa ea sz kd kp lv su sg hAP)
    (fun d hd lo hlo side _ => disj_resultLevel_child_of_arenas hd (KS d) (hSlot d)
      (ST d lo) (hSlot d lo hlo) side c ma ua qa ea sz kd kp lv su sg hAP)
    (Dense.kernelWeight T) (2 * T n) ?_ hmem hrun
  intro r hr x y hfr ⟨hp, hResults⟩ hxy
  have hd : L + 1 - r = (L - r) + 1 := by omega
  rw [hd] at hResults
  have hG := disj_upwardPrefix_upReadRegion (r := r) (by omega) KS (fun d _ => hSlot d)
    c ma ua qa ea sz kd kp lv su sg hAP
  have hL := hfr.keep
    (readsOnly_storesLevel_upReadRegion M F n fuel R0 eps beta ell (L - r) A
      ma lv ua qa ea sz kd kp c m.pos) hG (hLevel (L - r) (by omega))
  have hRec := hfr.keep
    (readsOnly_storesRecords_upReadRegion M dec mm qr n base fuel τ
      R0 eps beta ell (L - r) A ma lv ua qa ea sz kd kp c m.pos)
    hG (hRecords (L - r) (by omega))
  have hRec' : StoresRecords M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
      (L - r) ma ua qa ea sz kd kp x.mem := by
    intro path lo z hx hy hz
    exact StoresStep.of_store_eq (μ := ⟨x.mem.store, m.pos⟩) (ν := x.mem) rfl
      (hRec path lo z hx hy hz)
  have hC := hfr.keep ((Store.readsOnly_get _ _ _).mono
    (constant_le_upReadRegion n (L - r) ma lv ua qa ea sz kd kp c)) hG hTwo
  exact upLevel_kernelWeight_le_reference (M := M) (dec := dec) (mm := mm) (qr := qr)
    (n := n) (base := base) (fuel := fuel) (R0 := R0) (eps := eps) (beta := beta)
    (ell := ell) (A := A) (d := L - r) (budget := r) (τ := τ) (m := x.mem)
    unif normal hS hQ hMM hL hRec' hResults (hLive.congr hfr.length_eq) hC hLit
    (fun lo hlo => room_result_of_arenas (by omega) (hSlot (L - r) lo hlo)
      c ma ua qa ea sz kd kp lv su sg (hRoom.congr hfr.len_eq))
    (fun lo hlo => apart_upNode_of_arenas (by omega) hlo (hSlot (L - r) lo hlo)
      c ma ua qa ea sz kd kp lv su sg (hl.congr hfr.length_eq) hAP)
    (disj_resultLevel_sizes_of_arenas (by omega) (KS (L - r)) (hSlot (L - r))
      c ma ua qa ea sz kd kp lv su sg hAP)
    (fun j lo hjl hlo hp => disj_results_step_of_arenas M dec mm qr base fuel τ
      R0 beta (X (L - r) lo) (by omega) (hSlot (L - r) j (by omega))
      (hSlot (L - r) lo hlo) hp
      (disjoint_nodeAtSlot_intervals F n fuel R0 eps beta ell A (L - r) j lo (by omega))
      c ma ua qa ea sz kd kp lv su sg hAP)
    (fun lo hlo side _ => disj_resultLevel_child_of_arenas (by omega)
      (KS (L - r)) (hSlot (L - r)) (ST (L - r) lo) (hSlot (L - r) lo hlo) side
      c ma ua qa ea sz kd kp lv su sg hAP) T hT hadd W rfl hxy

end Reference

end NLAlib.SpectralBisection
