/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DecoupleLoop

/-!
# Initial scan and capped scalar decoupling

The initial scan uses the actual squared tolerance word. The following finite loop preserves
its stored scan invariant and returns a decoupled unitary conjugate.

## Main results

* `NLAlib.ShiftedQR.decouplePrepared`: initial scan followed by the finite loop.
* `NLAlib.ShiftedQR.decouplePrepared_writes`: total correctness with actual constant words.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- Initialize the actual scan before entering the flag-controlled counted loop. -/
def decouplePrepared (Iter : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M] (W, Params, Const) → (W, R) {
    run (scan (Op := O) (Tst := Q)).body [N] (W, Const, R);
    run (decoupleLoop Iter).body [N, m, k, F, M] (W, Params, Const, W, R)
  }

/-- Initial scan and capped iteration return an actual decoupled matrix under raw hypotheses. -/
theorem decouplePrepared_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hC : IsCmp id I) {θ : ℝ} (Iter : Impl O Q) (hIter : IterationContract θ Iter I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M : ℕ} {τ B α γ δ : ℝ} {w p c r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hyp : RapidDecouplingHyps H τ B θ α γ δ m F) (hHess : IsUpperHessenberg H)
    (hkn : 2 ^ m ≤ n) (hτ : 0 ≤ τ)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hMpos : 0 < M) (hW : HoldsMatrix w H μ.store)
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
    Writes .total I tape (decouplePrepared Iter).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [w, p, c, w, r])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (U H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HasOrthonormalCols U ∧
          H' = Uᴴ * H * U ∧ IsUpperHessenberg H' ∧ IsDecoupledAbs τ H' ∧
          HoldsMatrix w H' μ'.store ∧ ScanHolds H' (τ ^ 2) n r μ'.store) μ := by
  have ht : μ.store.get c.1 c.2 = some (τ ^ 2) := by
    simpa [vec] using Store.get_of_readBlock hConst (j := 0) (by omega) (0 : ℝ)
  have hlScan : μ.Live [w, c, r] := by
    simpa [Mem.Live] using (And.intro (hl w (by simp))
      (And.intro (hl c (by simp)) (hl r (by simp))))
  have hs := scan_writes (τ := tape) hS hE hL hC hW ht hlScan hr hWR.symm
    (hSep.mono le_sup_right (by fp_sub))
  unfold decouplePrepared
  refine hs.frame_seq_le rfl rfl hlScan le_sup_right ?_
  intro μ₁ hfr ⟨hp, hScan⟩
  have hW₁ := hW.of_eqOff hfr hWR.symm
  have hP₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ _)
    (hSep.mono le_sup_right le_sup_left) hParams
  have hC₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ _)
    (hSep.mono le_sup_right le_sup_right) hConst
  have hi := DecoupleInv.init hyp hHess hW₁ hScan
  have hb := decoupleLoop_writes (tape := tape) hS hE hL hC Iter hIter hyp
    hkn hτ hM hMpos hi hP₁ hC₁
    (hl.congr hfr.length_eq) (by rw [hfr.len_eq]; exact hw)
    (by rw [hfr.len_eq]; exact hr) hWR hSep
  refine (hb.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl ?_
  intro _ _ ⟨hp', ho⟩
  exact ⟨hp'.trans hp, ho⟩

end NLAlib.ShiftedQR
