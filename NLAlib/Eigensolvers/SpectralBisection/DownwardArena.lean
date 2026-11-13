/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.DownwardPass
public import NLAlib.Eigensolvers.SpectralBisection.DownArena
public import NLAlib.Eigensolvers.SpectralBisection.DownTapeFrame
public import NLAlib.Eigensolvers.SpectralBisection.DownPrepareArena

/-!
# Downward traversal on separated solver arenas

The canonical eleven arena spans imply all cross-level effect separation. The actual traversal
uses the same stored inputs, indexed tape machine and counted sampling schedule.

## Main results

* `NLAlib.SpectralBisection.writes_downwardPass_of_arenas`: the complete downward traversal.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has SampleOp Op] [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {I : Interp Op Tst K} {τ : Tape K} {μ : Mem K} {n L fuel base : ℕ}
  {par lv su sg ma ua qa ea sz kd kp c : ℕ × ℕ}
  (R0 eps0 beta : K) (A : Matrix (Fin n) (Fin n) (K × K))

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "root" => EighNode.mk n A R0 eps0 L
local notation "nodes" => (fun d lo => nodeAtSlot F n fuel R0 beta root d lo)
local notation "region" => (fun d => downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp)

/-- The eleven allocated arena capacities and separation imply total correctness of the
complete downward traversal. Every local node and fresh-scratch obligation is derived from
this layout; no per-level execution or geometry callback is assumed. -/
theorem writes_downwardPass_of_arenas (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hC : IsCmp dec I)
    (hMM : IsMatrixMul (EntryCodec.pair K) mm I) (hQR : IsMatrixQR (EntryCodec.pair K) qr I)
    (hQ : IsToNat dec I) (hSample : IsSample I)
    (hexact : IsExactNatLit dec M (max n 4))
    (hl : μ.Live [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
    (hPos : μ.pos = base)
    (hLevel : StoresLevel M F n fuel R0 beta root 0 ma sz lv μ)
    (hpar : μ.store.readBlock par.1 par.2 3 = some [R0, eps0, beta])
    (hc : μ.store.readBlock c.1 c.2 5 =
      some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf])
    (hZero : ∀ e, 1 ≤ e → e ≤ L + 1 → ∀ lo < n,
      μ.store.get sz.1 (sz.2 + n * e + lo) = some (M.lit 0))
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hPar : Fp.Disj (Store.inBlock par.1 par.2 3)
      (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))) :
    Writes .total I τ (downwardPass (node (Op := Op) (Tst := Tst))).body
      (Env.frame [n, L, fuel] [par, lv, su, sg, ma, ua, qa, ea, sz, kd, kp, c])
      (Fp.loopPrefix region (L + 1))
      (fun ν => ν.pos = base + (L + 1) * levelSampleSize n ∧
        ν.store.readBlock par.1 par.2 3 = some [R0, eps0, beta] ∧
        ν.store.readBlock c.1 c.2 5 =
          some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf] ∧
        (∀ e ≤ L + 1, StoresLevel M F n fuel R0 beta root e ma sz lv ν) ∧
        ∀ e ≤ L, StoresRecords M F n fuel R0 beta root e ma ua qa ea sz kd kp ν) μ := by
  apply writes_downwardPass M dec mm qr R0 eps0 beta A
    hS hL hC hMM hQR hQ hSample hexact hl hPos hLevel hpar hc hZero
  · intro d hd ν hlength hlens s hSlength hTlen hBelow
    have hArenaLive : μ.Live (par :: arenaOperands c ma ua qa ea sz kd kp lv su sg) := by
      intro z hz
      exact hl z (by simp [arenaOperands] at hz ⊢; tauto)
    apply downLevelGeometry_of_arenas (μ := ν) hd ?_
      (hArenaLive.congr hlength) (hRoom.congr hlens) hAP hPar.symm hSlength hTlen hBelow
    intro lo hlo
    have hk := nodeAtSlot_k_le F n fuel R0 eps0 beta L A d lo
    change (nodes d lo).k ≤ n - lo at hk
    omega
  · intro d hd
    exact Fp.disj_sup_right.mpr
      ⟨hPar.symm.mono (downLevelOutputFp_le_arenas hd) le_rfl,
        disj_downLevelOutputFp_constants hd hAP⟩
  · intro d hd e he
    exact disj_downLevelOutputFp_levelInput he hd hAP
  · intro d hd e he heL
    exact disj_downLevelOutputFp_futureSizes he heL hd hAP
  · intro d hd e he a lo x _ hx hp
    exact (disj_downLevelOutputFp_previous he hd hAP).mono le_rfl
      (stepFp_tapeMachine_le_downLevel M dec mm qr n base τ e lo fuel R0 beta x.R x.ε x.ℓ x.A
        (add_k_le_and_of_eighLoc hx).1 hp ma ua qa ea sz kd kp)

end

end NLAlib.SpectralBisection
