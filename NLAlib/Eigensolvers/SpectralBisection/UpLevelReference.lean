/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpLevel
public import NLAlib.Eigensolvers.SpectralBisection.UpReference

/-!
# Executable upward levels compute the recursive mathematical result

The input level and stored outcomes supply all actual dimensions and metadata. Occupied
children supply ordinary recursive result pairs. Capacity and spatial arena conditions remain
explicit; reconstruction returns the existing pure recursion with one more unit of budget.

## Main results

* `NLAlib.SpectralBisection.writes_upLevel_eighAux`: total recursive result reconstruction.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section Reference

variable {K Su Sg Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op]
  [Has IdxTst Tst] (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K))
  (qr : QRMap (K × K)) (n base fuel : ℕ) (R0 eps beta : K) (ell : ℕ)
  (A : Matrix (Fin n) (Fin n) (K × K)) (d budget : ℕ) (τ : Tape K)

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "X" => nodeAtSlot F n fuel R0 beta (EighNode.mk n A R0 eps ell) d
local notation "ST" => (fun lo => eighStep F n fuel R0 beta (EighNode.A (X lo))
  (EighNode.R (X lo)) (EighNode.ε (X lo)) (EighNode.ℓ (X lo)) (eighTapeSample n d lo))
local notation "KS" => (fun lo => EighNode.k (X lo))

/-- One actual upward level computes the existing pure recursion at every reached node.
No execution premise or numerical quality assumption is required. -/
theorem writes_upLevel_eighAux (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp Op Tst K} (hS : IsScalar M I) (hQ : IsToNat dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) {m : Mem K}
    {ma lv ua qa ea sz kd kp c : ℕ × ℕ}
    (hLevel : StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d ma sz lv m)
    (hRecords : StoresRecords M F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
      d ma ua qa ea sz kd kp m)
    (hResults : StoresLevelResults F n fuel R0 beta ⟨n, A, R0, eps, ell⟩
      budget (d + 1) ua ea m.store)
    (hl : m.Live [lv, ua, qa, ea, sz, kd, kp, c, ma])
    (hTwo : m.store.get c.1 (c.2 + 1) = some (M.lit 2))
    (hLit : IsExactNatLit dec M (max n 4))
    (hRoom : ∀ lo < n, m.Room (resultOperands n d lo ua ea) (resultLengths (KS lo)))
    (hApart : ∀ lo < n, Fp.Apart
      (upNodeRegions n d lo ua qa ea kd kp (m.store.length, 0))
      (upNodeRegionLengths n (KS lo)))
    (hDisj : ∀ lo < n, ∀ j < n, lo ≠ j →
      Fp.Disj (Fp.blocks (resultOperands n d lo ua ea) (resultLengths (KS lo)))
        (Fp.blocks (resultOperands n d j ua ea) (resultLengths (KS j))))
    (hSizesProtect : Fp.Disj (resultLevelFootprint n d KS ua ea)
      (Store.inBlock sz.1 (sz.2 + n * d) n))
    (hForward : ∀ j lo, j < lo → lo < n → 0 < KS lo →
      Fp.Disj (Fp.blocks (resultOperands n d j ua ea) (resultLengths (KS j)))
        (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp (ST lo))
          (stepOutputLengths (ST lo))))
    (hChildProtect : ∀ lo < n, ∀ side, (ST lo).HasChild side →
      Fp.Disj (resultLevelFootprint n d KS ua ea)
        (Fp.blocks (resultOperands n (d + 1) ((ST lo).childSlot lo side) ua ea)
          (resultLengths ((ST lo).childSize side)))) :
    Writes .total I τ (upLevel (Op := Op) (Tst := Tst))
      (Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c])
      (resultLevelFootprint n d KS ua ea)
      (fun m' => m'.pos = m.pos ∧ StoresLevelResults F n fuel R0 beta
        ⟨n, A, R0, eps, ell⟩ (budget + 1) d ua ea m'.store) m := by
  have hBound := nodeAtSlot_k_le F n fuel R0 eps beta ell A d
  have hw := writes_upLevel (τ := τ) (m := m) mm qr unif normal hS hQ hMM KS
    (fun lo => M.lit (KS lo : ℚ)) ST
    (fun lo => eighNodeChildren F n fuel R0 beta budget d lo (X lo))
    hl hLevel.radius_read hTwo hLevel.nodeAtSlot_sizes
    (fun lo _ => hLit _ (by dsimp only; have := hBound lo; omega))
    (fun lo _ => hBound lo) (fun _ _ hp => hRecords.nodeAtSlot_step hp)
    (fun _ _ hp => hResults.nodeAtSlot_children hp) hLit hRoom hApart hDisj
    hSizesProtect hForward hChildProtect
  refine hw.mono le_rfl fun m' _ ⟨hp, hs⟩ => ⟨hp, ?_⟩
  apply storesLevelResults_of_slot_assemblies F n fuel budget d R0 eps beta ell A ua ea
  intro lo hlo
  have h := hs lo hlo
  have he : (ST lo).assemble (M.toFloatMachine dec mm qr unif normal)
      (eighNodeChildren F n fuel R0 beta budget d lo (X lo)) =
      (ST lo).assemble F (eighNodeChildren F n fuel R0 beta budget d lo (X lo)) := by
    exact assemble_toFloatMachine_samplers M dec mm qr unif normal _ _ (ST lo) _
  rw [he] at h
  exact h

end Reference

end NLAlib.SpectralBisection
