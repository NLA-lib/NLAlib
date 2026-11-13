/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Reconstruct
public import NLAlib.Eigensolvers.SpectralBisection.UpwardArenaWork
public import NLAlib.Eigensolvers.SpectralBisection.ZeroWork
public import NLAlib.Ops.Logic.Count

/-!
# Actual matrix-kernel work of complete reconstruction

The recursion-boundary and final-copy fragments contain no matrix primitive. Their actual
counted runs surround the reverse pass, whose stored slot partitions bound its kernel work.
The word-level bottom frame supplies the unchanged upper-level mathematical inputs.

## Main results

* `NLAlib.SpectralBisection.reconstructResult_kernelWeight_le_of_arenas`: complete reconstruction.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K : Type} [Inhabited K]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  {n L fuel base : ℕ} {τ : Tape K} {μ : Mem K}
  (R0 eps beta : K) (A : Matrix (Fin n) (Fin n) (K × K))
  {c ma ua qa ea sz kd kp lv su sg u dv : ℕ × ℕ}

local notation "F" => tapeMachine M dec mm qr n base τ
local notation "root" => EighNode.mk n A R0 eps L

/-- The allocated solver's complete reconstruction adds two root-size kernel charges per
upward level. Scalar bottom initialization and output copies have zero matrix weight.
All storage/model prerequisites are explicit; no phase execution callback is assumed.
The actual execution premise is auxiliary to the existing total word-level solver proof. -/
theorem reconstructResult_kernelWeight_le_of_arenas
    {I : Interp DenseOp (CmpTst ⊕ IdxTst) K} (hS : IsScalar M I)
    (hQ : IsToNat dec I) (hMM : IsMatrixMul (EntryCodec.pair K) mm I)
    (hLit : IsExactNatLit dec M (max n 4))
    (hl : μ.Live (arenaOperands c ma ua qa ea sz kd kp lv su sg))
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hLevels : ∀ d ≤ L + 1, StoresLevel M F n fuel R0 beta root d ma sz lv μ)
    (hRecords : ∀ d ≤ L, StoresRecords M F n fuel R0 beta root d ma ua qa ea sz kd kp μ)
    (hTwo : μ.store.get c.1 (c.2 + 1) = some (M.lit 2))
    (T : ℕ → ℕ) (hT : Monotone T) (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (W : DenseOp → List ℕ → ℕ) {a b : St DenseOp (CmpTst ⊕ IdxTst) K}
    (hmem : a.mem = μ)
    (hrun : evalCounted I W τ (reconstructResult (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body
      (Env.frame [n, L] [c, ua, qa, ea, sz, kd, kp, lv, u, dv]) a = some b) :
    Dense.kernelWeight T b.cost ≤ Dense.kernelWeight T a.cost + (L + 1) * (2 * T n) := by
  subst μ
  have hlArena := hl
  simp only [arenaOperands, Mem.live_cons, Mem.live_nil, and_true] at hl
  rcases hl with ⟨hc, hma, hua, hqa, hea, hsz, hkd, hkp, hlv, hsu, hsg⟩
  dsimp only [reconstructResult] at hrun
  rw [evalCounted] at hrun
  obtain ⟨a₁, hBottomRun, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  rw [evalCounted] at hrun
  obtain ⟨a₂, hUpRun, hCopyRun⟩ := Option.bind_eq_some_iff.mp hrun
  have hBottomRaw := evalCounted_frame_body (d := [n, L + 1])
    (as := [sz, ua, ea]) rfl rfl hBottomRun
  have hBottom := writes_bottomLevel_stored (μ := a.mem) M dec mm qr R0 eps beta A
    hS hQ hLit
    (D := L + 1) (by omega) (by room) (hLevels _ le_rfl) hAP hRoom
  obtain ⟨hfr, hp, hBottomResults⟩ := hBottom.post_of_evalCounted hBottomRaw
  obtain ⟨hLevels₁, hRecords₁, hTwo₁⟩ := stored_upwardInputs_of_bottom_frame
    (μ := a.mem) (ν := a₁.mem) M dec mm qr R0 eps beta A hAP hLevels hRecords hTwo hfr hp
  have hUpRaw := evalCounted_frame_body (d := [n, L])
    (as := [lv, ua, qa, ea, sz, kd, kp, c]) rfl rfl hUpRun
  have hUp := upwardPass_kernelWeight_le_of_arenas (m := a₁.mem)
    M dec mm qr n base fuel L R0 eps beta L A τ
    c ma ua qa ea sz kd kp lv su sg M.mul (fun z : K × K => M.normalWords z.1 z.2)
    hS hQ hMM (hlArena.congr hfr.length_eq) (hRoom.congr hfr.len_eq) hAP
    hLevels₁ hRecords₁ hBottomResults hTwo₁ hLit T hT hadd W rfl hUpRaw
  have hBottomCost := evalCounted_weight_le (Dense.matrixWeight (MatrixOp.dimensionWeight T))
    (fun _ _ => 0) hBottomRaw
  rw [bottomLevel_matrixWork_zero, Nat.add_zero] at hBottomCost
  have hCopyRaw := evalCounted_frame_body (d := [n]) (as := [ua, ea, u, dv]) rfl rfl hCopyRun
  have hCopyCost := evalCounted_weight_le (Dense.matrixWeight (MatrixOp.dimensionWeight T))
    (fun _ _ => 0) hCopyRaw
  rw [rootResultCopy_matrixWork_zero, Nat.add_zero] at hCopyCost
  exact hCopyCost.trans (hUp.trans (Nat.add_le_add_right hBottomCost _))

end

end NLAlib.SpectralBisection
