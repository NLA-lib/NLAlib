/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpwardPass
public import NLAlib.Eigensolvers.SpectralBisection.UpNodeArena
public import NLAlib.Eigensolvers.SpectralBisection.UpProtection

/-!
# Complete upward reconstruction from allocated solver arenas

The canonical eleven-arena capacities and spatial separation discharge every local and
cross-level reconstruction condition. Initial mathematical levels, stored outcomes and bottom
identity/zero results suffice for total execution of the existing reverse-depth loop.

## Main results

* `NLAlib.SpectralBisection.writes_upwardPass_of_arenas`: root reconstruction from full arenas.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section Reference

variable {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has IdxTst Tst] (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K))
  (qr : QRMap (K × K)) (n base fuel L : ℕ) (R0 eps beta : K) (ell : ℕ)
  (A : Matrix (Fin n) (Fin n) (K × K)) (τ : Tape K)
  (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "X" => (fun d => nodeAtSlot F n fuel R0 beta (EighNode.mk n A R0 eps ell) d)
local notation "KS" => (fun d lo => EighNode.k (X d lo))
local notation "ST" => (fun d lo => eighStep F n fuel R0 beta (EighNode.A (X d lo))
  (EighNode.R (X d lo)) (EighNode.ε (X d lo)) (EighNode.ℓ (X d lo)) (eighTapeSample n d lo))

/-- Full arena capacity and apartness supply every geometric prerequisite for actual upward
execution. The returned root is exactly the existing pure recursion with budget `L + 1`. -/
theorem writes_upwardPass_of_arenas (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
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
    (hLit : IsExactNatLit dec M (max n 4)) :
    Writes .total I τ (upwardPass (Op := Op) (Tst := Tst)).body
      (Env.frame [n, L] [lv, ua, qa, ea, sz, kd, kp, c]) (resultArenaFp n L ua ea)
      (fun m' => m'.pos = m.pos ∧ StoresResult n 0 0 ua ea
        (eighAux F n fuel R0 beta (L + 1) A R0 eps ell
          (eighSlotTree F n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩)) m'.store) m := by
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
  refine (writes_upwardPass (M := M) (dec := dec) (mm := mm) (qr := qr)
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
      (ST d lo) (hSlot d lo hlo) side c ma ua qa ea sz kd kp lv su sg hAP)).mono ?_
    (fun _ _ h => h)
  rintro b i ⟨j, hj, hc⟩
  exact resultLevelSpan_le_resultArenaFp (L := L) (by omega) ua ea b i
    (resultLevelFootprint_le_span (d := L - j) (hSlot (L - j)) ua ea b i hc)

end Reference

end NLAlib.SpectralBisection
