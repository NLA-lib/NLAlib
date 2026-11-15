/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DecoupleConstants

/-!
# Scoped exact scalar decoupling

Two per-block constant words are allocated, computed once, and released after the actual
scan and finite iteration loop. The public local contract follows from raw spectral hypotheses.

## Main results

* `NLAlib.ShiftedQR.decouple`: the scoped scalar implementation.
* `NLAlib.ShiftedQR.decouple_contract`: its total local decoupling guarantee.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- Allocate only two persistent per-block constant words around the actual scalar loop. -/
def decouple (Iter : Impl O Q) : Impl O Q :=
  opsImpl% [N, m, k, F, M] (W, Params) → (W, R) {
    let Const ← alloc 2;
    run (decoupleWithConstants Iter).body [N, m, k, F, M] (W, Params, Const, W, R)
  }

/-- The scoped implementation satisfies the worklist's local decoupling interface. -/
theorem decouple_contract {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hE : ExactModel id Mch) (hL : IsIndexLit Mch I)
    (hC : IsCmp id I) {θ : ℝ} (Iter : Impl O Q) (hIter : IterationContract θ Iter I) :
    DecouplingContract θ (decouple Iter) I := by
  intro n m F M τ B α γ δ w p r tape μ H hHess hyp hkn hτ hM hMpos hW hP hl hw hr hWR hPW
  have hwl := hl w (by simp)
  have hpl := hl p (by simp)
  have hrl := hl r (by simp)
  unfold decouple
  refine writes_allocs_preserving_post (lens := [.const 2]) (ns := [2]) rfl ?_ ?_
  · intro s s' pos hBelow ⟨hp, U, H', hU, hH', hHess', hdec, hW', hR⟩
    refine ⟨hp, U, H', hU, hH', hHess', hdec, hW'.of_below hBelow hwl, ?_⟩
    exact ⟨((hBelow r.1 hrl).2 _).trans hR.1, ((hBelow r.1 hrl).2 _).trans hR.2⟩
  · intro s hs hlens hBelow
    let c : ℕ × ℕ := (μ.store.length, 0)
    let μ₁ : Mem ℝ := ⟨s, μ.pos⟩
    have hc : s.len c.1 = 2 := by simpa [c] using hlens 0 (by simp)
    have hl₁ : μ₁.Live [w, p, c, w, r] := by
      simp only [Mem.live_cons, Mem.live_nil, and_true]
      change w.1 < s.length ∧ p.1 < s.length ∧ μ.store.length < s.length ∧
        w.1 < s.length ∧ r.1 < s.length
      simp only [List.length_cons, List.length_nil] at hs
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    have hConstSep : Fp.Disj (Store.inBlock c.1 c.2 2)
        (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
          Store.inBlock r.1 r.2 5 ⊔ Store.inBlock p.1 p.2 5) := by
      apply Fp.disj_sup_right.mpr
      refine ⟨Fp.disj_sup_right.mpr ⟨?_, ?_⟩, ?_⟩ <;>
        exact Fp.disj_inBlock_of_ne (by dsimp [c]; omega)
    have hb := decoupleWithConstants_writes (tape := tape) hS hE hL hC Iter hIter hyp hHess
      hkn hτ hM hMpos (hW.of_below hBelow hwl)
      ((hBelow.readBlock hpl p.2 5).trans hP) hl₁
      (by rw [(hBelow w.1 hwl).1]; exact hw)
      (by rw [(hBelow r.1 hrl).1]; exact hr)
      (by change 0 + 2 ≤ s.len c.1; omega) hWR hPW.symm hConstSep
    refine (hb.in_frame rfl rfl hl₁).mono ?_ (fun _ _ hp => hp)
    exact sup_le le_sup_left (Fp.inBlock_le_sup_above (by dsimp [c]; omega))

end NLAlib.ShiftedQR
