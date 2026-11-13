/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.BottomReference
public import NLAlib.Eigensolvers.SpectralBisection.ResultGeometry
public import NLAlib.Eigensolvers.SpectralBisection.UpArenaGeometry

/-!
# The bottom traversal inside the solver arenas

Readable mathematical sizes and the full arena capacities suffice to initialize the final
result level. The output is the ordinary zero-budget recursive result family, without any
assumption on unused output words or successful execution.

## Main results

* `NLAlib.SpectralBisection.writes_bottomLevel_stored`: total bottom-level initialization.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IdxTst Tst]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {n L D fuel base : ℕ} {τ : Tape K} {μ : Mem K}
  (R0 eps beta : K) (A : Matrix (Fin n) (Fin n) (K × K))
  {c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ}

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "nodes" => (fun lo => nodeAtSlot F n fuel R0 beta (EighNode.mk n A R0 eps L) D lo)
local notation "KS" => (fun lo => EighNode.k (nodes lo))

/-- Arena capacities and mathematical slot disjointness give total bottom initialization. -/
theorem writes_bottomLevel_stored {I : Interp Op Tst K}
    (hS : IsScalar M I) (hQ : IsToNat dec I) (hexact : IsExactNatLit dec M (max n 4))
    (hD : D ≤ L + 1) (hl : μ.Live [sz, ua, ea])
    (hLevel : StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, L⟩ D ma sz lv μ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Writes .total I τ (bottomLevel (Op := Op) (Tst := Tst))
      (Env.frame [n, D] [sz, ua, ea]) (resultLevelSpan n D ua ea)
      (fun ν => ν.pos = μ.pos ∧ StoresLevelResults F n fuel R0 beta
        ⟨n, A, R0, eps, L⟩ 0 D ua ea ν.store) μ := by
  have hbound (lo : ℕ) : KS lo ≤ n - lo :=
    nodeAtSlot_k_le F n fuel R0 eps beta L A D lo
  have hslot (lo : ℕ) (hlo : lo < n) : lo + KS lo ≤ n := by
    have := hbound lo
    omega
  have hThree := apart_resultLevel_size_of_arenas hD c ma ua qa ea sz kd kp lv su sg hAP
  have hUE : Fp.Disj (Store.inBlock ua.1 (ua.2 + 2 * (n * n) * D) (2 * (n * n)))
      (Store.inBlock ea.1 (ea.2 + n * D) n) := hThree.1.mono le_rfl le_sup_left
  have hBothSize : Fp.Disj (resultLevelSpan n D ua ea)
      (Store.inBlock sz.1 (sz.2 + n * D) n) := by
    simpa [resultLevelSpan, Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using
      (hThree.take_drop (by simp) 2).2.2
  have hSub : bottomFootprint n D KS ua ea ≤ resultLevelSpan n D ua ea := by
    rintro buf off ⟨lo, hlo, hc⟩
    apply resultSlot_le_span (hslot lo hlo) ua ea buf off
    simpa only [bottomSlotFootprint, resultOperands, resultLengths, Fp.blocks_cons,
      Fp.blocks_nil, sup_bot_eq] using hc
  have hw := writes_bottomLevel (M := M) (dec := dec) (m := μ) (τ := τ) hS hQ
    KS (fun lo => M.lit (KS lo : ℚ)) hl hLevel.nodeAtSlot_sizes
    (fun lo hlo => hexact _ (by have := hbound lo; omega)) (fun lo _ => hbound lo)
    (fun lo hlo => by
      simpa [Mem.Room, resultOperands, resultLengths] using
        room_result_of_arenas hD (hslot lo hlo) c ma ua qa ea sz kd kp lv su sg hRoom)
    (fun lo hlo j hj hne => by
      simpa [bottomSlotFootprint, resultOperands, resultLengths, Fp.blocks_cons,
        Fp.blocks_nil, sup_bot_eq] using
        disj_resultSlots (hslot lo hlo) (hslot j hj)
          (disjoint_nodeAtSlot_intervals F n fuel R0 eps beta L A D lo j hne) ua ea hUE)
    (fun lo hlo => hUE.mono (resultMatrix_le_level (hslot lo hlo) ua)
      (resultValues_le_level (hslot lo hlo) ea)) (hBothSize.mono hSub le_rfl)
  refine hw.mono hSub ?_
  intro ν _ ⟨hp, hSlots⟩
  exact ⟨hp, storesLevelResults_zero_of_bottom M dec mm qr n base fuel D τ R0 eps beta L A
    ua ea ν.store hSlots⟩

end

end NLAlib.SpectralBisection
