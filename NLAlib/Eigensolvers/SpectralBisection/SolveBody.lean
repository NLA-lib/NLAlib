/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.InitialArena
public import NLAlib.Eigensolvers.SpectralBisection.DownwardArena
public import NLAlib.Eigensolvers.SpectralBisection.Reconstruct

/-!
# The complete caller-owned spectral-bisection solver

The initializer, downward pass and root reconstruction compose into the existing pure
recursive solver. The hypotheses describe local primitive contracts, actual inputs and the
allocated arena layout. No execution, success or numerical-accuracy premise is assumed.

## Main results

* `NLAlib.SpectralBisection.writes_solveBody`: total refinement on caller-owned arenas.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has IndexOp Op]
  [Has SampleOp Op] [Has MatrixOp Op] [Has CmpTst Tst] [Has IdxTst Tst]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {n L fuel base : ℕ} {τ : Tape K} {μ : Mem K}
  (R0 eps beta : K) (A : Matrix (Fin n) (Fin n) (K × K))
  {a par u dv c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ}

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "root" => EighNode.mk n A R0 eps L
local notation "RES" => eighAux F n fuel R0 beta (L + 1) A R0 eps L
  (eighSlotTree F n fuel R0 beta 0 0 root)
local notation "ARENA" => Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
  (arenaLengths n L)

/-- Initialization and the two actual traversals return exactly the mathematical solver. -/
theorem writes_solveBody {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I)
    (hC : IsCmp dec I) (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    (hQR : IsMatrixQR (EntryCodec.pair K) qr I) (hQ : IsToNat dec I) (hSample : IsSample I)
    (hLit : IsExactNatLit dec M (max n 4)) (hPos : μ.pos = base)
    (hl : μ.Live ([a, par, u, dv] ++ arenaOperands c ma ua qa ea sz kd kp lv su sg))
    (hA : μ.store.readBlock a.1 a.2 (2 * (n * n)) =
      some ((EntryCodec.pair K).packFinMatrix A))
    (hPar : μ.store.readBlock par.1 par.2 3 = some [R0, eps, beta])
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hOutRoom : μ.Room [u, dv] [2 * (n * n), n])
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hSource : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock par.1 par.2 3))
    (hOutput : Fp.Disj (Store.inBlock u.1 u.2 (2 * (n * n))) (Store.inBlock dv.1 dv.2 n))
    (hProtect : Fp.Disj ARENA (Fp.blocks [a, par, u, dv] [2 * (n * n), 3, 2 * (n * n), n])) :
    Writes .total I τ (solveBody (node (Op := Op) (Tst := Tst)))
      (Env.frame [n, L, fuel] [a, par, u, dv, c, ma, ua, qa, ea, sz, kd, kp, lv, su, sg])
      (ARENA ⊔ Fp.blocks [u, dv] [2 * (n * n), n])
      (fun ν => ν.pos = base + (L + 1) * levelSampleSize n ∧
        StoresResult n 0 0 u dv RES ν.store) μ := by
  simp only [arenaOperands, List.cons_append, List.nil_append, Mem.live_cons,
    Mem.live_nil, and_true] at hl
  rcases hl with ⟨ha, hpar, hu, hdv, hc, hma, hua, hqa, hea, hsz, hkd, hkp, hlv, hsu, hsg⟩
  have hInputs : Fp.Disj ARENA (Fp.blocks [a, par] [2 * (n * n), 3]) :=
    hProtect.mono le_rfl (by fp_sub)
  have hOutputs : Fp.Disj ARENA (Fp.blocks [u, dv] [2 * (n * n), n]) :=
    hProtect.mono le_rfl (by fp_sub)
  have hInit := writes_initializeArenas_stored (μ := μ) (τ := τ)
    M F fuel R0 eps beta A hS hL (by room) hRoom hAP hSource hInputs hA hPar
  refine hInit.frame_seq_le rfl rfl (by room) le_sup_left ?_
  clear hInit
  intro μ₁ hfr₁ ⟨hp₁, hPar₁, hC₁, hLevel₁, hZero₁⟩
  have hParSep : Fp.Disj (Store.inBlock par.1 par.2 3) ARENA :=
    hInputs.symm.mono (by fp_sub) le_rfl
  have hDown := writes_downwardPass_of_arenas (μ := μ₁) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (base := base)
    M dec mm qr R0 eps beta A hS hL hC hMM hQR hQ hSample hLit (by room)
    (hp₁.trans hPos) hLevel₁ hPar₁ hC₁ hZero₁ (hRoom.congr hfr₁.len_eq) hAP hParSep
  have hDownSub : Fp.loopPrefix
      (fun d => downLevelOutputFp n d lv su sg ma ua qa ea sz kd kp) (L + 1) ≤ ARENA := by
    rintro buf off ⟨d, hd, hcell⟩
    exact downLevelOutputFp_le_arenas (by omega) buf off hcell
  refine hDown.frame_seq_le rfl rfl (by room) (hDownSub.trans le_sup_left) ?_
  clear hDown
  intro μ₂ hfr₂ ⟨hp₂, _, hC₂, hLevels₂, hRecords₂⟩
  have hTwo₂ := Store.get_of_readBlock hC₂ (j := 1) (by simp) (M.lit 0)
  have hReconstruct := writes_reconstructResult (μ := μ₂) (τ := τ)
    (n := n) (L := L) (fuel := fuel) (base := base)
    M dec mm qr R0 eps beta A hS hQ hMM hLit (by room [arenaOperands])
    (hRoom.congr fun buf => (hfr₂.len_eq buf).trans (hfr₁.len_eq buf))
    (hOutRoom.congr fun buf => (hfr₂.len_eq buf).trans (hfr₁.len_eq buf))
    hAP hOutput hOutputs hLevels₂ hRecords₂ (by simpa using hTwo₂)
  have hReconSub : resultArenaFp n L ua ea ⊔ Fp.blocks [u, dv] [2 * (n * n), n] ≤
      ARENA ⊔ Fp.blocks [u, dv] [2 * (n * n), n] :=
    sup_le_sup (by fp_sub [resultArenaFp, arenaOperands, arenaLengths]) le_rfl
  refine (hReconstruct.mono hReconSub ?_).in_frame rfl rfl (by room)
  clear hReconstruct
  intro ν _ ⟨hp₃, hResult⟩
  exact ⟨hp₃.trans hp₂, hResult⟩

end

end NLAlib.SpectralBisection
