/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpLevelWork
public import NLAlib.Eigensolvers.SpectralBisection.UpLevelReference
public import NLAlib.Eigensolvers.SpectralBisection.SlotWork

/-!
# Partition-sensitive work at one mathematical upward level

The stored size words select the existing typed mathematical slot lookup. Its disjoint
interval partition reduces the sum of superadditive matrix-size costs to one root-size cost.
The resource statement concerns the actual counted source run and arbitrary prior history.

## Main results

* `NLAlib.SpectralBisection.upLevel_kernelWeight_le_reference`: two root-size charges per level.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section Reference

variable {K Su Sg : Type} [Inhabited K] (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K))
  (qr : QRMap (K × K)) (n base fuel : ℕ) (R0 eps beta : K) (ell : ℕ)
  (A : Matrix (Fin n) (Fin n) (K × K)) (d budget : ℕ) (τ : Tape K)

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "X" => nodeAtSlot F n fuel R0 beta (EighNode.mk n A R0 eps ell) d
local notation "ST" => (fun lo => eighStep F n fuel R0 beta (EighNode.A (X lo))
  (EighNode.R (X lo)) (EighNode.ε (X lo)) (EighNode.ℓ (X lo)) (eighTapeSample n d lo))
local notation "KS" => (fun lo => EighNode.k (X lo))

/-- Under the same stored mathematical inputs and spatial prerequisites as upward assembly,
actual matrix work is at most two root-size charges. The supplied size cost is monotone and
superadditive. The starting count and live scratch are arbitrary. -/
theorem upLevel_kernelWeight_le_reference (unif : K → Su → K) (normal : Sg → K × K)
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} (hS : IsScalar M I) (hQ : IsToNat dec I)
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
    (hSizesProtect : Fp.Disj (resultLevelFootprint n d KS ua ea)
      (Store.inBlock sz.1 (sz.2 + n * d) n))
    (hForward : ∀ j lo, j < lo → lo < n → 0 < KS lo →
      Fp.Disj (Fp.blocks (resultOperands n d j ua ea) (resultLengths (KS j)))
        (Fp.blocks (stepOutputs n d lo ma ua qa ea sz kd kp (ST lo))
          (stepOutputLengths (ST lo))))
    (hChildProtect : ∀ lo < n, ∀ side, (ST lo).HasChild side →
      Fp.Disj (resultLevelFootprint n d KS ua ea)
        (Fp.blocks (resultOperands n (d + 1) ((ST lo).childSlot lo side) ua ea)
          (resultLengths ((ST lo).childSize side))))
    (T : ℕ → ℕ) (hT : Monotone T) (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (W : DenseOp → List ℕ → ℕ) {a b : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hmem : a.mem = m)
    (hrun : evalCounted I W τ (upLevel (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst))
      (Env.frame [n, d] [lv, ua, qa, ea, sz, kd, kp, c]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost + 2 * T n := by
  have hBound := nodeAtSlot_k_le F n fuel R0 eps beta ell A d
  have hw := upLevel_kernelWeight_sum_le_of_exec (τ := τ) (m := m)
    mm qr unif normal hS hQ hMM KS (fun lo => M.lit (KS lo : ℚ)) ST
    (fun lo => eighNodeChildren F n fuel R0 beta budget d lo (X lo))
    hl hLevel.radius_read hTwo hLevel.nodeAtSlot_sizes
    (fun lo _ => hLit _ (by dsimp only; have := hBound lo; omega))
    (fun lo _ => hBound lo) (fun _ _ hp => hRecords.nodeAtSlot_step hp)
    (fun _ _ hp => hResults.nodeAtSlot_children hp) hLit hRoom hApart
    hSizesProtect hForward hChildProtect T W hmem hrun
  have hs := sum_slotWork_le F n fuel R0 eps beta ell A d hT hadd
  have hsum : (∑ lo ∈ Finset.range n, 2 * T (KS lo)) ≤ 2 * T n := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left 2 hs
  exact hw.trans (Nat.add_le_add_left hsum _)

end Reference

end NLAlib.SpectralBisection
