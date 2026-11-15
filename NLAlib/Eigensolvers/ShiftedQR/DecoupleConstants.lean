/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DecouplePrepared

/-!
# Actual per-block constants and decoupling

The squared tolerance and contraction power are computed once before the initial scan.
No iteration or spectral trajectory is supplied as a runtime primitive.

## Main results

* `NLAlib.ShiftedQR.decoupleWithConstants`: the scalar initialized decoupling body.
* `NLAlib.ShiftedQR.decoupleWithConstants_writes`: total correctness with reserved constants.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- Compute actual constant words once, then initialize the scan and run the finite loop. -/
def decoupleWithConstants (Iter : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M] (W, Params, Const) → (W, R) {
    run iterationConstants.body [k] (Params, Const, Const[1]);
    run (decouplePrepared Iter).body [N, m, k, F, M] (W, Params, Const, W, R)
  }

/-- Actual scalar constant initialization composes with total finite decoupling. -/
theorem decoupleWithConstants_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hC : IsCmp id I) {θ : ℝ} (Iter : Impl O Q) (hIter : IterationContract θ Iter I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n m F M : ℕ} {τ B α γ δ : ℝ} {w p c r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hyp : RapidDecouplingHyps H τ B θ α γ δ m F) (hHess : IsUpperHessenberg H)
    (hkn : 2 ^ m ≤ n) (hτ : 0 ≤ τ)
    (hM : M = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ m) B θ α ((1 - γ) ^ 2)⌉₊)
    (hMpos : 0 < M) (hW : HoldsMatrix w H μ.store)
    (hParams : μ.store.readBlock p.1 p.2 5 = some [τ, B, θ, α, γ])
    (hl : μ.Live [w, p, c, w, r])
    (hw : w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1)
    (hr : r.2 + 5 ≤ μ.store.len r.1) (hc : c.2 + 2 ≤ μ.store.len c.1)
    (hWR : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock r.1 r.2 5))
    (hWP : Fp.Disj
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5)
      (Store.inBlock p.1 p.2 5))
    (hConstSep : Fp.Disj (Store.inBlock c.1 c.2 2)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock r.1 r.2 5 ⊔ Store.inBlock p.1 p.2 5)) :
    Writes .total I tape (decoupleWithConstants Iter).body
      (Env.frame [n + 1, m, 2 ^ m, F, M] [w, p, c, w, r])
      ((Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock r.1 r.2 5) ⊔
        Store.inBlock c.1 c.2 2)
      (fun μ' => μ'.pos = μ.pos ∧
        ∃ (U H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HasOrthonormalCols U ∧
          H' = Uᴴ * H * U ∧ IsUpperHessenberg H' ∧ IsDecoupledAbs τ H' ∧
          HoldsMatrix w H' μ'.store ∧ ScanHolds H' (τ ^ 2) n r μ'.store) μ := by
  have hOut : Fp.blocks [c, (c.1, c.2 + 1)] [1, 1] ≤ Store.inBlock c.1 c.2 2 := by
    fp_sub
  have hconst := iterationConstants_writes (k := 2 ^ m) (τ := tape)
    (a := c) (b := (c.1, c.2 + 1)) hS hE hParams
    (hConstSep.symm.mono le_sup_right (by fp_sub))
    (by intro b i h0 h1; dsimp [Store.inBlock] at h0 h1; omega)
    (by omega) (by omega)
  have hlConst : μ.Live [p, c, (c.1, c.2 + 1)] := by
    simpa [Mem.Live] using (And.intro (hl p (by simp))
      (And.intro (hl c (by simp)) (hl c (by simp))))
  unfold decoupleWithConstants
  refine hconst.frame_seq_le rfl rfl hlConst (hOut.trans le_sup_right) ?_
  intro μ₁ hfr ⟨hp, hReads⟩
  obtain ⟨x, y, hx, hy, he⟩ := BlockFn.readBlocks_cells_two.mp hReads
  have he' : x = τ ^ 2 ∧ y = (1 - γ) ^ (2 * (2 ^ m)) := by simpa using he.symm
  rw [he'.1] at hx
  rw [he'.2] at hy
  have hCst : μ₁.store.readBlock c.1 c.2 2 =
      some [τ ^ 2, (1 - γ) ^ (2 * (2 ^ m))] := by
    simp [Store.readBlock_succ, hx, hy]
  have hW₁ := hW.of_eqOff hfr (hConstSep.mono hOut (by fp_sub))
  have hP₁ := hfr.keep (Store.readsOnly_readBlock _ _ _ _)
    (hConstSep.mono hOut le_sup_right) hParams
  have hb := decouplePrepared_writes (tape := tape) hS hE hL hC Iter hIter hyp hHess
    hkn hτ hM hMpos hW₁ hP₁ hCst (hl.congr hfr.length_eq)
    (by rw [hfr.len_eq]; exact hw) (by rw [hfr.len_eq]; exact hr) hWR
    (Fp.disj_sup_right.mpr ⟨hWP, hConstSep.symm.mono le_sup_left le_rfl⟩)
  refine (hb.in_frame rfl rfl (hl.congr hfr.length_eq)).mono le_sup_left ?_
  intro _ _ ⟨hp', ho⟩
  exact ⟨hp'.trans hp, ho⟩

end NLAlib.ShiftedQR
