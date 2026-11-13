/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLevelWords
public import NLAlib.Eigensolvers.SpectralBisection.DownLevelRecords

/-!
# Stored mathematical levels of the actual downward program

The program consumes stored root parameters and level inputs. Its actual sample windows
identify the indexed tape machine, and exact output frames retain every unoccupied size word.

## Main results

* `NLAlib.SpectralBisection.writes_downLevel_stored`: next inputs and current step records.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has SampleOp Op] [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {I : Interp Op Tst K} {τ : Tape K} {μ : Mem K} {n L fuel d base : ℕ}
  {par lv su sg ma ua qa ea sz kd kp c t : ℕ × ℕ}
  (R0 eps0 beta : K) (A : Matrix (Fin n) (Fin n) (K × K))

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "root" => EighNode.mk n A R0 eps0 L
local notation "nodes" => (fun lo => nodeAtSlot F n fuel R0 beta root d lo)
local notation "params" => eighLevelParams F R0 eps0 L d
local notation "rawStep" => (fun lo => eighStep
  (Machine.toFloatMachine M dec mm qr (Machine.mul M)
    (fun z : K × K => Machine.normalWords M (Prod.fst z) (Prod.snd z)))
  n fuel R0 beta (EighNode.A (nodes lo)) (Prod.fst params) (Prod.snd params) (L + d)
  (storedNodeSample n lo (vec (levelUniformWords n base τ d) lo)
    (levelGaussianMatrix n base τ d)))
local notation "scanRegion" => (Fp.loopPrefix
  (fun lo => activeStepFp n d lo ma ua qa ea sz kd kp (rawStep lo)) n)
local notation "scratchRegion" => (downPrepareFp n d lv su sg t ⊔
  Store.inBlock (Prod.fst t) (Prod.snd t + 4) 1)

/-- One complete actual level stores its mathematical outcomes and the next level inputs.
All execution assumptions concern primitive contracts, actual input words and bounded storage. -/
theorem writes_downLevel_stored (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I)
    (hexact : IsExactNatLit dec M (max n 4))
    (hPos : μ.pos = base + d * levelSampleSize n)
    (hLevel : StoresLevel M F n fuel R0 beta root d ma sz lv μ)
    (hpar : μ.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hc : μ.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf])
    (hGeometry : DownLevelGeometry n d (fun lo => (nodes lo).k)
      par lv su sg ma ua qa ea sz kd kp c t μ.store)
    (hZero : ∀ j < n, μ.store.get sz.1 (sz.2 + n * (d + 1) + j) = some (M.lit 0)) :
    Writes .total I τ (downLevelImpl (node (Op := Op) (Tst := Tst))).body
      (Env.frame [n, L, fuel, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c, t])
      (downPrepareFp n d lv su sg t ⊔ (scanRegion ⊔ Store.inBlock t.1 (t.2 + 4) 1))
      (fun ν => ν.pos = base + (d + 1) * levelSampleSize n ∧
        StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp ν ∧
        StoresLevel M F n fuel R0 beta root (d + 1) ma sz lv ν) μ := by
  classical
  have hslot (lo : ℕ) (hlo : lo < n) : lo + (nodes lo).k ≤ n := by
    have hk := nodeAtSlot_k_le F n fuel R0 eps0 beta L A d lo
    change (nodes lo).k ≤ n - lo at hk
    omega
  have hW := writes_downLevelImpl M dec mm qr (τ := τ) (L := L) (fuel := fuel)
    hS hL hC hMM hQR hQ hSample
    (fun lo => (nodes lo).k) (fun lo => (nodes lo).A) R0 eps0 beta params.1 params.2
    hslot (fun i _ j _ hij => disjoint_nodeAtSlot_intervals F n fuel R0 eps0 beta L A d i j hij)
    hexact (fun lo hi => hLevel.nodeAtSlot_size hi)
    (fun _ _ hp => hLevel.nodeAtSlot_matrix hp) hpar hLevel.2.2 hc
    hGeometry
  rw [hPos] at hW
  refine hW.mono le_rfl ?_
  intro ν hfr h
  have hRecords := storesRecords_of_downSlots M dec mm qr n base τ fuel R0 eps0 beta L A d
    ma ua qa ea sz kd kp ν h.2.2
  have hParams : ν.store.readBlock lv.1 (lv.2 + 2 * (d + 1)) 2 =
      some [(eighLevelParams F R0 eps0 L (d + 1)).1,
        (eighLevelParams F R0 eps0 L (d + 1)).2] := by
    simpa only [eighLevelParams, eighNextParams, tapeMachine, Machine.toFloatMachine,
      Nat.cast_ofNat] using h.2.1
  have hFrame : μ.store.EqOff (scanRegion ⊔ scratchRegion) ν.store := by
    refine hfr.mono ?_
    intro b i hcell
    rcases hcell with hprep | (hscan | ht)
    · exact Or.inr (Or.inl hprep)
    · exact Or.inl hscan
    · exact Or.inr (Or.inr ht)
  have hNextLevel := storesLevel_succ_of_downFrame M dec mm qr n base τ fuel R0 eps0 beta L A d
    ma ua qa ea sz kd kp lv scratchRegion μ ν hRecords hZero hParams
      hGeometry.output_apart hGeometry.scratch_size hFrame
  refine ⟨?_, hRecords, hNextLevel⟩
  rw [h.1]
  simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]

end

end NLAlib.SpectralBisection
