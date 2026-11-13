/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus.Alg
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Combining the two Hutch++ trace contributions

The denominator comes from the actual dimension-literal instruction. Exact arithmetic
identifies that stored word with the probe count. The positivity premise used by the
estimator's numerical theorem remains separate from local field-operation execution.

## Main results

* `NLAlib.HutchPlusPlus.writes_combineTrace` returns the low-rank sum plus the residual mean.
-/

@[expose] public section

namespace NLAlib.HutchPlusPlus

open Ops

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has ScalarOp Op] [Has IndexOp Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {m : Mem 𝕜}

/-- Combine actual stored sums through the dimension literal, division and addition.
The scalar machine is exact; no successful-execution premise is required. -/
theorem writes_combineTrace (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hLit : IsIndexLit (RCLikeBlas.machine : Machine 𝕜) I)
    {ell : ℕ} {t out : ℕ × ℕ} (lo hi : 𝕜) (hl : m.Live [t, out])
    (hLo : m.store.readBlock out.1 out.2 1 = some [lo])
    (hHi : m.store.readBlock t.1 (t.2 + 1) 1 = some [hi])
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 2 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I τ combineTrace.body (Env.frame [ell] [t, out])
      (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [lo + hi / (ell : 𝕜)]) m := by
  have ht₀ : Store.inBlock t.1 t.2 1 ≤ Store.inBlock t.1 t.2 2 :=
    Fp.inBlock_le_inBlock le_rfl (by omega)
  have ht₁ : Store.inBlock t.1 (t.2 + 1) 1 ≤ Store.inBlock t.1 t.2 2 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  unfold combineTrace
  dsimp only
  refine Writes.seq_le (writes_indexLit hLit rfl rfl (by change t.2 < m.store.len t.1; omega))
    (ht₀.trans le_sup_left) ?_
  intro m₁ hfr₁ ⟨hp₁, he⟩
  have he' : m₁.store.get t.1 t.2 = some (ell : 𝕜) := by
    simpa [RCLikeBlas.machine] using he
  have hDen : m₁.store.readBlock t.1 t.2 1 = some [(ell : 𝕜)] := by
    simp [Store.readBlock, he']
  have hHi₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ [hi])
    (Fp.disj_inBlock_of_le (by omega)) hHi
  have hLo₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ [lo]) (hTO.mono ht₀ le_rfl) hLo
  have hl₁ := hl.congr hfr₁.length_eq
  refine Writes.seq_le (writes_call_fn1 (hS .div) (xs := [[hi], [(ell : 𝕜)]])
    rfl rfl rfl rfl rfl trivial
    (by simp only [Mem.live_append, Mem.live_cons, Mem.live_nil];
        exact ⟨⟨hl₁ t (by simp), hl₁ t (by simp), trivial⟩, hl₁ t (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, hHi₁, hDen]) rfl rfl
    (by change t.2 + 1 + 1 ≤ m₁.store.len t.1; rw [hfr₁.len_eq]; omega))
    (ht₁.trans le_sup_left) ?_
  intro m₂ hfr₂ ⟨hp₂, hMean⟩
  have hLo₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ [lo]) (hTO.mono ht₁ le_rfl) hLo₁
  have hl₂ := hl₁.congr hfr₂.length_eq
  refine (writes_call_fn1 (hS .add) (xs := [[lo], [hi / (ell : 𝕜)]])
    rfl rfl rfl rfl rfl trivial
    (by simp only [Mem.live_append, Mem.live_cons, Mem.live_nil];
        exact ⟨⟨hl₂ out (by simp), hl₂ t (by simp), trivial⟩, hl₂ out (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, RCLikeBlas.machine, hLo₂, hMean]) rfl rfl
    (by simpa only [hfr₂.len_eq, hfr₁.len_eq] using ho)).mono le_sup_right ?_
  intro m₃ _ ⟨hp₃, hv⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hv⟩

end NLAlib.HutchPlusPlus
