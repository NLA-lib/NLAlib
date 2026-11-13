/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownLevelStored
public import NLAlib.Eigensolvers.SpectralBisection.RecordTransport

/-!
# A scoped downward level

Five scalar scratch words are allocated locally. The stored mathematical level and outcomes
survive cleanup because they depend only on the caller-owned arena handles.

## Main results

* `NLAlib.SpectralBisection.writes_downLevel`: total allocated level with stored outcomes.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has SampleOp Op] [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {I : Interp Op Tst K} {τ : Tape K} {μ : Mem K} {n L fuel d base : ℕ}
  {par lv su sg ma ua qa ea sz kd kp c : ℕ × ℕ}
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
/-- A complete allocated level returns its records and successor inputs, then frees scratch.
The geometry premise describes arbitrary fresh storage, independently of all numeric words. -/
theorem writes_downLevel (hS : IsScalar M I) (hL : IsIndexLit M I) (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I)
    (hexact : IsExactNatLit dec M (max n 4))
    (hl : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
    (hPos : μ.pos = base + d * levelSampleSize n)
    (hLevel : StoresLevel M F n fuel R0 beta root d ma sz lv μ)
    (hpar : μ.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hc : μ.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf])
    (hZero : ∀ j < n, μ.store.get sz.1 (sz.2 + n * (d + 1) + j) = some (M.lit 0))
    (hGeometry : ∀ s : Store K, s.length = μ.store.length + 1 →
      s.len μ.store.length = 5 → Store.Below μ.store.length μ.store s →
        DownLevelGeometry n d (fun lo => (nodes lo).k)
          par lv su sg ma ua qa ea sz kd kp c (μ.store.length, 0) s) :
    Writes .total I τ (downLevel (node (Op := Op) (Tst := Tst)))
      (Env.frame [n, L, fuel, d] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
      (downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp)
      (fun ν => ν.pos = base + (d + 1) * levelSampleSize n ∧
        StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp ν ∧
        StoresLevel M F n fuel R0 beta root (d + 1) ma sz lv ν) μ := by
  have hLive := hl
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hLive
  rcases hLive with ⟨hlpar, hllv, hlsu, hlsg, hlma, hlua, hlqa, hlea, hlsz, hlkd, hlkp, hlc⟩
  have hSurvive : ∀ z ∈ [ma, ua, qa, ea, sz, kd, kp], z.1 < μ.store.length := by
    simpa using (show μ.Live [ma, ua, qa, ea, sz, kd, kp] by room)
  apply writes_allocs_preserving_post (lens := [.const 5]) (ns := [5]) rfl
  · intro s s' p hBelow h
    exact ⟨h.1, h.2.1.of_below hBelow hSurvive, h.2.2.of_below hBelow hlma hlsz hllv⟩
  · intro s hlength hlens hBelow
    have ht : s.len μ.store.length = 5 := by simpa using hlens 0 (by simp)
    have hGeo := hGeometry s (by simpa using hlength) ht hBelow
    have hW := writes_downLevel_stored M dec mm qr R0 eps0 beta A
      (τ := τ) (n := n) (L := L) (fuel := fuel) (d := d) (base := base)
      (μ := ⟨s, μ.pos⟩) (t := (μ.store.length, 0)) hS hL hC hMM hQR hQ hSample
      hexact hPos (hLevel.of_below hBelow hlma hlsz hllv)
      ((hBelow.readBlock hlpar _ _).trans hpar) ((hBelow.readBlock hlc _ _).trans hc)
      hGeo (fun j hj => ((hBelow sz.1 hlsz).2 _).trans (hZero j hj))
    refine (hW.in_frame rfl rfl hGeo.live).mono ?_ (fun _ _ h => h)
    apply downFrame_le_output_scratch _ _ _ _ _ _ _ _ _ _ _ ?_ le_rfl
    apply activeStepPrefix_le_downLevel
    intro lo hlo
    have hk := nodeAtSlot_k_le F n fuel R0 eps0 beta L A d lo
    change (nodes lo).k ≤ n - lo at hk
    omega

end

end NLAlib.SpectralBisection
