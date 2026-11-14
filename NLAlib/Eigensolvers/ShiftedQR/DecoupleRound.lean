/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DecoupleState

/-!
# One actual capped-decoupling visit

The visit reads the scalar scan flag. A decoupled block is retained; otherwise the fixed scalar
iteration runs and the resulting actual work matrix is scanned again. The mathematical
potential, conditioning and unitary-conjugacy invariants follow from the same accepted step.

## Main results

* `NLAlib.ShiftedQR.decoupleRound`: the flag-controlled scalar visit.
* `NLAlib.ShiftedQR.decoupleRound_writes`: its total invariant-preservation theorem.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-- The accepted-step mathematics establishes the next exact decoupling state. -/
private theorem decoupleInv_step {n m F j : ℕ} {τ B θ α γ δ : ℝ}
    {H₀ H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ}
    {w r : ℕ × ℕ} {μ : Mem ℝ}
    (hyp : RapidDecouplingHyps H₀ τ B θ α γ δ m F) (hkn : 2 ^ m ≤ n) (hτ : 0 ≤ τ)
    (hU : HasOrthonormalCols U) (hH : H = Uᴴ * H₀ * U) (hHess : IsUpperHessenberg H)
    (hκ : ∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
      H * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B)
    (hψ : hessenbergPotential (2 ^ m) H ≤ (1 - γ) ^ j * hessenbergPotential (2 ^ m) H₀)
    (hdec : ¬IsDecoupledAbs τ H) (hlen : ss.length = 2 ^ m)
    (hss : IsOptimalRitzValues θ H ss)
    (hW : HoldsMatrix w (shqrAcceptStep τ B θ α γ m H ss) μ.store)
    (hR : ScanHolds (shqrAcceptStep τ B θ α γ m H ss) (τ ^ 2) n r μ.store) :
    DecoupleInv H₀ τ B θ α γ m (j + 1) w r μ := by
  obtain ⟨U', hU', hH'⟩ := shqrAcceptStep_exists_unitary τ B θ α γ m ss hU hH
  have hstep := hyp.step hkn hτ hHess hdec hκ hψ hlen (fun _ => hss)
  have hHess' : IsUpperHessenberg (shqrAcceptStep τ B θ α γ m H ss) :=
    hHess.isUpperHessenberg_multiShiftedQRStep _
  exact ⟨U', _, hU', hH', hHess', hstep.1, hstep.2, hW, hR⟩

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- Only undecoupled blocks execute a scalar strategy iteration and a new scalar scan. -/
def decoupleRound (Iter : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, M] (W, Params, Const) → (W, R) {
    if (Has.inj CmpTst.isZero) [] (R[3]) {
      run Iter.body [N, m, k, M] (W, Params, Const, W);
      run (scan (Op := O) (Tst := Q)).body [N] (W, Const, R)
    } else { skip }
  }

/-- A visit retains an already decoupled block or executes the actual scalar step and rescan.
Read-only parameter and constant views remain outside both write regions. -/
theorem decoupleRound_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I) (hC : IsCmp id I)
    {θ : ℝ} (Iter : Impl O Q) (hIter : IterationContract θ Iter I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M j : ℕ} {τ B α γ δ : ℝ} {w p c r : ℕ × ℕ}
    {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hyp : RapidDecouplingHyps H₀ τ B θ α γ δ m F) (hkn : 2 ^ m ≤ n) (hτ : 0 ≤ τ)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊) (hMpos : 0 < M)
    (hInv : DecoupleInv H₀ τ B θ α γ m j w r μ)
    (hParams : μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ])
    (hConst : μ.store.readBlock c.1 c.2 2 = some [τ ^ 2, (1 - γ) ^ (2 * (2 ^ m))])
    (hl : μ.Live [w, p, c, w, r])
    (hw : w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1)
    (hr : r.2 + 5 ≤ μ.store.len r.1)
    (hWR : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock r.1 r.2 5))
    (hSep : Fp.Disj
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
      (Store.inBlock p.1 p.2 5 ⊔ Store.inBlock c.1 c.2 2)) :
    Writes .total I tape (decoupleRound Iter).body
      (Env.frame [n + 1, m, 2 ^ m, M] [w, p, c, w, r])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
      (fun μ' => μ'.pos = μ.pos ∧ DecoupleInv H₀ τ B θ α γ m (j + 1) w r μ') μ := by
  obtain ⟨U, H, hU, hH, hHess, hκ, hψ, hW, hScan⟩ := hInv
  unfold decoupleRound
  by_cases hdec : IsDecoupledAbs τ H
  · have hflag := (hScan.flag_iff hτ).mpr hdec
    have ht : I.test (Has.inj CmpTst.isZero) [] [(r.1, r.2 + 3)] μ = some false := by
      simpa using hC.test_isZero (d := []) (x := (r.1, r.2 + 3)) hflag
    refine writes_ite rfl rfl ht ?_
    exact (Writes.skip (I := I) (τ := tape) (md := .total)
      ⟨rfl, DecoupleInv.stopped hU hH hHess hκ hdec hW hScan⟩).mono bot_le
        (fun _ _ hp => hp)
  · have hnone : ¬(scanPrefix H (τ ^ 2) n).isSome = true :=
      fun hs => hdec ((scanPrefix_isSome_iff_isDecoupledAbs H hτ).mp hs)
    have hflag : μ.store.get r.1 (r.2 + 3) = some (0 : ℝ) := by
      simpa [hnone] using hScan.1
    have ht : I.test (Has.inj CmpTst.isZero) [] [(r.1, r.2 + 3)] μ = some true := by
      simpa using hC.test_isZero (d := []) (x := (r.1, r.2 + 3)) hflag
    refine writes_ite rfl rfl ht ?_
    have hLiveIter : μ.Live [w, p, c, w] := by
      simpa [Mem.Live] using (And.intro (hl w (by simp))
        (And.intro (hl p (by simp)) (And.intro (hl c (by simp)) (hl w (by simp)))))
    have hstep := hIter (tape := tape) H hHess hkn hτ (zero_le_one.trans hyp.one_le)
      hM hMpos hW hParams hConst hLiveIter hw (hSep.mono le_sup_left le_rfl)
    refine hstep.frame_seq_le rfl rfl hLiveIter le_sup_left ?_
    intro μ₁ hfr₁ ⟨hp₁, ss, hlen, hss, hW₁⟩
    have hConst₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _)
      (hSep.mono le_sup_left le_sup_right) hConst
    have hThreshold : μ₁.store.get c.1 c.2 = some (τ ^ 2) := by
      simpa [vec] using Store.get_of_readBlock hConst₁ (j := 0) (by omega) (0 : ℝ)
    have hLiveScan : μ₁.Live [w, c, r] := by
      have hl₁ := hl.congr hfr₁.length_eq
      simpa [Mem.Live] using (And.intro (hl₁ w (by simp))
        (And.intro (hl₁ c (by simp)) (hl₁ r (by simp))))
    have hscan := scan_writes (τ := tape) hS hE hL hC hW₁ hThreshold hLiveScan
      (by rw [hfr₁.len_eq]; exact hr) hWR.symm
      (hSep.mono le_sup_right (by fp_sub))
    refine (hscan.in_frame rfl rfl hLiveScan).mono le_sup_right ?_
    intro μ₂ hfr₂ ⟨hp₂, hScan₂⟩
    have hW₂ := hW₁.of_eqOff hfr₂ hWR.symm
    exact ⟨hp₂.trans hp₁, decoupleInv_step hyp hkn hτ hU hH hHess hκ
      (hψ hdec) hdec hlen hss hW₂ hScan₂⟩

end NLAlib.ShiftedQR
