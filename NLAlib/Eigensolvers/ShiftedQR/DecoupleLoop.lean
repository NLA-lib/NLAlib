/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DecoupleRound

/-!
# The finite scalar decoupling loop

Each visit reads the stored scan flag and retains a decoupled matrix. The quantitative
potential bound excludes an undecoupled matrix at the explicit iteration cap.

## Main results

* `NLAlib.ShiftedQR.decoupleLoop`: the counted scalar loop.
* `NLAlib.ShiftedQR.decoupleLoop_writes`: total execution and unconditional decoupling.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- Run the fixed flag-controlled visit at most the supplied number of iterations. -/
def decoupleLoop (Iter : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M] (W, Params, Const) → (W, R) {
    for j < F {
      run (decoupleRound Iter).body [N, m, k, M] (W, Params, Const, W, R)
    }
  }

/-- The finite loop returns a decoupled stored matrix under raw spectral hypotheses. -/
theorem decoupleLoop_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hC : IsCmp id I) {θ : ℝ} (Iter : Impl O Q) (hIter : IterationContract θ Iter I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M : ℕ} {τ B α γ δ : ℝ} {w p c r : ℕ × ℕ}
    {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hyp : RapidDecouplingHyps H₀ τ B θ α γ δ m F) (hkn : 2 ^ m ≤ n) (hτ : 0 ≤ τ)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hMpos : 0 < M) (hInv : DecoupleInv H₀ τ B θ α γ m 0 w r μ)
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
    Writes .total I tape (decoupleLoop Iter).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [w, p, c, w, r])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (U H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HasOrthonormalCols U ∧
          H = Uᴴ * H₀ * U ∧ IsUpperHessenberg H ∧ IsDecoupledAbs τ H ∧
          HoldsMatrix w H μ'.store ∧ ScanHolds H (τ ^ 2) n r μ'.store) μ := by
  unfold decoupleLoop
  refine (writes_loop rfl
    (fun _ => Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
    (fun _ _ => le_rfl) (fun j μ' => μ'.pos = μ.pos ∧ DecoupleInv H₀ τ B θ α γ m j w r μ')
    ⟨rfl, hInv⟩ ?_).mono le_rfl ?_
  · intro j _ μ' hfr ⟨hp, hi⟩
    have hP := hfr.keep (Store.readsOnly_readBlock _ _ _ _) (hSep.mono le_rfl le_sup_left)
      hParams
    have hCst := hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      (hSep.mono le_rfl le_sup_right) hConst
    have hw' := decoupleRound_writes (tape := tape) hS hE hL hC Iter hIter hyp
      hkn hτ hM hMpos hi hP hCst
      (hl.congr hfr.length_eq) (by rw [hfr.len_eq]; exact hw)
      (by rw [hfr.len_eq]; exact hr) hWR hSep
    refine (hw'.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_rfl ?_
    intro _ _ ⟨hp', hi'⟩
    exact ⟨hp'.trans hp, hi'⟩
  · intro _ _ ⟨hp, hi⟩
    exact ⟨hp, hi.decoupled_at_cap hyp hkn⟩

end NLAlib.ShiftedQR
