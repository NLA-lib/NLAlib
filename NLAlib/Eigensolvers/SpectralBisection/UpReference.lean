/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpMath
public import NLAlib.Eigensolvers.SpectralBisection.SlotNodes

/-!
# Relating slot reconstruction to recursive matrix results

Typed slot lookups supply the mathematical nodes needed by the executable level theorem.
Ordinary assembled slot results give the global reached-node result family, including empty
roots without requiring a nonexistent positive slot.

## Main results

* `NLAlib.SpectralBisection.storesLevelResults_of_slot_assemblies`: slot-to-path result bridge.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A stored mathematical level supplies every actual size word used by bounded queries. -/
theorem StoresLevel.nodeAtSlot_sizes {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d : ℕ} {R0 beta : K} {root : EighNode K} {ma sz lv : ℕ × ℕ} {m : Mem K}
    (h : StoresLevel M F n fuel R0 beta root d ma sz lv m) :
    m.store.HoldsVec sz.1 (sz.2 + n * d) n
      (fun lo => M.lit ((nodeAtSlot F n fuel R0 beta root d lo).k : ℚ)) :=
  fun _ hlo => h.nodeAtSlot_size hlo

/-- The actual parameter tuple contains the common radius read by upward reconstruction. -/
theorem StoresLevel.radius_read {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d : ℕ} {R0 beta : K} {root : EighNode K} {ma sz lv : ℕ × ℕ} {m : Mem K}
    (h : StoresLevel M F n fuel R0 beta root d ma sz lv m) :
    m.store.get lv.1 (lv.2 + 2 * d) =
      some (eighLevelParams F R0 root.ε root.ℓ d).1 := by
  simpa using Store.get_of_readBlock h.2.2 (j := 0) (by omega) (M.lit 0)

/-- A reached positive lookup has its stored mathematical outcome with the common radius. -/
theorem StoresRecords.nodeAtSlot_step {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d lo : ℕ} {R0 eps beta : K} {ell : ℕ}
    {A : Matrix (Fin n) (Fin n) (K × K)} {ma ua qa ea sz kd kp : ℕ × ℕ} {m : Mem K}
    (h : StoresRecords M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma ua qa ea sz kd kp m)
    (hp : 0 < (nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo).k) :
    let x := nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo
    StoresStep M (eighLevelParams F R0 eps ell d).1 n d lo ma ua qa ea sz kd kp
      (eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)) m := by
  obtain ⟨a, ha, hx⟩ := exists_eighLoc_of_nodeAtSlot_k_pos hp
  have hr := h a lo _ ha hx hp
  have hR := (nodeAtSlot_params F n fuel R0 eps beta ell A d lo).1
  dsimp only
  rw [← hR]
  exact hr

/-- Positive lookup nodes select their occupied child results from the next result level. -/
theorem StoresLevelResults.nodeAtSlot_children {K : Type} {F : FloatMachine K ℕ ℕ}
    {n fuel budget d lo : ℕ} {R0 beta : K} {root : EighNode K} {ua ea : ℕ × ℕ}
    {s : Store K} (h : StoresLevelResults F n fuel R0 beta root budget (d + 1) ua ea s)
    (hp : 0 < (nodeAtSlot F n fuel R0 beta root d lo).k) :
    let x := nodeAtSlot F n fuel R0 beta root d lo
    let step := eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
    ∀ side, step.HasChild side → StoresResult n (d + 1) (step.childSlot lo side) ua ea
      (eighNodeChildren F n fuel R0 beta budget d lo x side) s := by
  obtain ⟨a, ha, hx⟩ := exists_eighLoc_of_nodeAtSlot_k_pos hp
  exact fun side hb => h.children ha hx side hb

/-- Slot assembly results establish the recursive mathematical output for every reached node.
Zero-dimensional nodes require no stored cells, so the empty root is included. -/
theorem storesLevelResults_of_slot_assemblies {K : Type} (F : FloatMachine K ℕ ℕ)
    (n fuel budget d : ℕ) (R0 eps beta : K) (ell : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (ua ea : ℕ × ℕ) (s : Ops.Store K)
    (hSlots : ∀ lo < n,
      let x := nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo
      let step := eighStep F n fuel R0 beta x.A x.R x.ε x.ℓ (eighTapeSample n d lo)
      StoresResult n d lo ua ea
        (step.assemble F (eighNodeChildren F n fuel R0 beta budget d lo x)) s) :
    StoresLevelResults F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ (budget + 1) d ua ea s := by
  intro path lo x hlen hx
  by_cases hp : 0 < x.k
  · have hlo : lo < n := by have := (add_k_le_and_of_eighLoc hx).1; omega
    have hs := hSlots lo hlo
    dsimp only at hs
    rw [nodeAtSlot_eq_of_eighLoc hlen hx hp] at hs
    rw [eighNodeResult_succ]
    exact hs
  · exact storesResult_of_eq_zero (by omega) n d lo ua ea _ s

/-- Assembly uses only scalar arithmetic and matrix multiplication, so changing sampler
seed types or sampler functions does not change an assembled result. -/
theorem assemble_toFloatMachine_samplers {K Su Sg Vu Vg : Type} (M : Ops.Machine K)
    (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (unif' : K → Vu → K) (normal' : Vg → K × K) {k : ℕ} (step : EighStep K k)
    (children : (side : Bool) →
      Matrix (Fin (step.childSize side)) (Fin (step.childSize side)) (K × K) ×
        (Fin (step.childSize side) → K)) :
    step.assemble (M.toFloatMachine dec mm qr unif normal) children =
      step.assemble (M.toFloatMachine dec mm qr unif' normal') children := by
  cases step <;> rfl

end NLAlib.SpectralBisection
