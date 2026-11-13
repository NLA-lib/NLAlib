/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.BottomArena
public import NLAlib.Eigensolvers.SpectralBisection.UpwardArena
public import NLAlib.Eigensolvers.SpectralBisection.RootCopy
public import NLAlib.Eigensolvers.SpectralBisection.SolveLayout

/-!
# Reconstruct the root result from the stored downward tree

Bottom initialization and the reverse traversal produce the existing recursive result, which
is copied into the supplied output views. Shallow mathematical inputs and outcomes survive
the bottom writes by the common read-footprint rule.

## Main results

* `NLAlib.SpectralBisection.writes_reconstructResult`: exact total root reconstruction.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has MatrixOp Op] [Has IdxTst Tst]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {n L fuel base : ℕ} {τ : Tape K} {μ : Mem K}
  (R0 eps beta : K) (A : Matrix (Fin n) (Fin n) (K × K))
  {c ma ua qa ea sz kd kp lv su sg u dv : ℕ × ℕ}

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "root" => EighNode.mk n A R0 eps L
local notation "RES" => eighAux F n fuel R0 beta (L + 1) A R0 eps L
  (eighSlotTree F n fuel R0 beta 0 0 root)

/-- Bottom-result writes preserve every shallower level, node record and the scalar two.
This is a storage statement: only the bottom footprint, unchanged tape position and canonical
arena separation are required, independently of the program producing that frame. -/
theorem stored_upwardInputs_of_bottom_frame {ν : Mem K}
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hLevels : ∀ d ≤ L + 1, StoresLevel M F n fuel R0 beta root d ma sz lv μ)
    (hRecords : ∀ d ≤ L, StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp μ)
    (hTwo : μ.store.get c.1 (c.2 + 1) = some (M.lit 2))
    (hFrame : μ.store.EqOff (resultLevelSpan n (L + 1) ua ea) ν.store)
    (hPos : ν.pos = μ.pos) :
    (∀ d ≤ L, StoresLevel M F n fuel R0 beta root d ma sz lv ν) ∧
      (∀ d ≤ L, StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp ν) ∧
      ν.store.get c.1 (c.2 + 1) = some (M.lit 2) := by
  have hSep (d : ℕ) (hd : d ≤ L) := disj_resultLevelSpan_upReadRegion hd le_rfl
    (show d < L + 1 by omega) c ma ua qa ea sz kd kp lv su sg hAP
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact hFrame.keep (readsOnly_storesLevel_upReadRegion M F n fuel R0 eps beta L d A
      ma lv ua qa ea sz kd kp c μ.pos) (hSep d hd) (hLevels d (by omega))
  · intro d hd
    simpa only [← hPos] using
      hFrame.keep (readsOnly_storesRecords_upReadRegion M dec mm qr n base fuel τ
        R0 eps beta L d A ma lv ua qa ea sz kd kp c μ.pos) (hSep d hd) (hRecords d hd)
  · exact hFrame.keep (Store.readsOnly_get c.1 (c.2 + 1) (M.lit 2))
      ((hSep 0 (by omega)).mono le_rfl
        (constant_le_upReadRegion n 0 ma lv ua qa ea sz kd kp c)) hTwo

/-- Complete root reconstruction from actual stored levels and node outcomes. -/
theorem writes_reconstructResult {I : Interp Op Tst K} (hS : IsScalar M I)
    (hQ : IsToNat dec I) (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    (hLit : IsExactNatLit dec M (max n 4))
    (hl : μ.Live (arenaOperands c ma ua qa ea sz kd kp lv su sg ++ [u, dv]))
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hOutRoom : μ.Room [u, dv] [2 * (n * n), n])
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hOutput : Fp.Disj (Store.inBlock u.1 u.2 (2 * (n * n))) (Store.inBlock dv.1 dv.2 n))
    (hProtect : Fp.Disj (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
      (arenaLengths n L)) (Fp.blocks [u, dv] [2 * (n * n), n]))
    (hLevels : ∀ d ≤ L + 1, StoresLevel M F n fuel R0 beta root d ma sz lv μ)
    (hRecords : ∀ d ≤ L, StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp μ)
    (hTwo : μ.store.get c.1 (c.2 + 1) = some (M.lit 2)) :
    Writes .total I τ (reconstructResult (Op := Op) (Tst := Tst)).body
      (Env.frame [n, L] [c, ua, qa, ea, sz, kd, kp, lv, u, dv])
      (resultArenaFp n L ua ea ⊔ Fp.blocks [u, dv] [2 * (n * n), n])
      (fun ν => ν.pos = μ.pos ∧ StoresResult n 0 0 u dv RES ν.store) μ := by
  have hlArena := ((Mem.live_append μ _ _).mp hl).1
  simp only [arenaOperands, List.cons_append, List.nil_append, Mem.live_cons,
    Mem.live_nil, and_true] at hl
  rcases hl with ⟨hc, hma, hua, hqa, hea, hsz, hkd, hkp, hlv, hsu, hsg, hu, hdv⟩
  have hBottom := writes_bottomLevel_stored M dec mm qr R0 eps beta A hS hQ hLit
    (D := L + 1) (by omega) (by room) (hLevels _ le_rfl) hAP hRoom
  refine hBottom.frame_seq_le rfl rfl (by room)
    ((resultLevelSpan_le_resultArenaFp (L := L) le_rfl ua ea).trans le_sup_left) ?_
  clear hBottom
  intro μ₁ hfr₁ ⟨hp₁, hBottom⟩
  obtain ⟨hLevels₁, hRecords₁, hTwo₁⟩ := stored_upwardInputs_of_bottom_frame
    M dec mm qr R0 eps beta A hAP hLevels hRecords hTwo hfr₁ hp₁
  have hUp := writes_upwardPass_of_arenas M dec mm qr n base fuel L R0 eps beta L A τ
    c ma ua qa ea sz kd kp lv su sg M.mul (fun z : K × K => M.normalWords z.1 z.2)
    hS hQ hMM (hlArena.congr hfr₁.length_eq) (hRoom.congr hfr₁.len_eq) hAP
    hLevels₁ hRecords₁ hBottom hTwo₁ hLit
  refine hUp.frame_seq_le rfl rfl (by room) le_sup_left ?_
  clear hUp
  intro μ₂ hfr₂ ⟨hp₂, hRoot⟩
  have hCopy := writes_rootResultCopy (μ := μ₂) (τ := τ) hS RES (by room)
    (apart_rootCopy_of_arenas hAP hOutput hProtect) hRoot
    (hOutRoom.congr fun buf => (hfr₂.len_eq buf).trans (hfr₁.len_eq buf))
  refine (hCopy.mono le_sup_right ?_).in_frame rfl rfl (by room)
  clear hCopy
  intro ν _ ⟨hp₃, hread⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), (storesResult_iff_readBlocks (m := ν)).mpr
    (by simpa [resultOperands, resultLengths] using hread)⟩

end

end NLAlib.SpectralBisection
