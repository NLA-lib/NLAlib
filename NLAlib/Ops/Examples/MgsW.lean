/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Examples.GramSchmidt

/-!
# Test case: modified Gram–Schmidt in the logic layer

The certificate of `NLAlib.Ops.Examples.mgs` against `mgsRel`, proved with block
specifications: one allocation, one loop in the standard invariant form, a named step per call.

## Main results

* `NLAlib.Ops.Examples.mgs_spec_w`: the certificate (the statement of `mgs_spec`).
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Inhabited K]

/-- **The certificate of `mgs`**, by block specifications. -/
theorem mgs_spec_w {M : Machine K} {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ a, dec (M.neg a) = -dec a) :
    (mgsImpl (Op := Op) (Tst := Tst)).Meets J .total ((mgsRel dec ε).spec (MgsOperands ok)) := by
  cert_intro [n, k] (Q, x) → (w, R) reads (qs, ws)
  obtain ⟨hok, rfl, hQw, hQR, hwR⟩ := hadm
  refine writes_alloc rfl fun s₁ hs₁ ht hB => ?_
  refine Writes.seq_le (writes_loop rfl
    (fun j => Store.inBlock w.1 w.2 n ⊔ Store.inBlock R.1 R.2 j ⊔ Store.inBuf μ.store.length)
    (fun j _ => by fp_sub)
    (fun j m' => m'.pos = μ.pos ∧ ∃ ws' r, m'.store.readBlock w.1 w.2 n = some ws' ∧
      m'.store.readBlock R.1 R.2 j = some r ∧
      MgsRec dec (ε.dot n) ε.axpy n (fun j i => vec qs (j * n + i)) (vec ws) j (vec ws') r)
    ⟨rfl, ws, [], by kept, rfl, .zero⟩ fun j hj m₁ hfr ⟨hpos, ws', r, hw', hr', hrec⟩ => ?_)
    (by fp_sub) fun m₁ hfr ⟨hpos, ws', r, hw', hr', hrec⟩ => ?_
  · step hJ.dot as m₂ hfr₂ ⟨hpos₂, ρ, hρ, hρrel⟩
    step (hS .neg) as m₃ hfr₃ ⟨hpos₃, t, ht, htrel⟩
    step hJ.axpy as m₄ hfr₄ ⟨hpos₄, zs, hzs, hzrel⟩
    exact ⟨by rw [hpos₄, hpos₃, hpos₂, hpos], zs, r ++ [ρ], hzs,
      Store.readBlock_succ_of (by kept) (by kept),
      hrec.step (hρrel.congr (fun i hi => vec_drop_take hi) fun _ _ => rfl) (htrel ▸ hneg ρ)
        (hzrel.congr (fun i hi => vec_drop_take hi) (fun _ _ => rfl) fun _ _ => rfl)⟩
  · step hJ.nrm2 as m₂ hfr₂ ⟨hpos₂, ν, hν, hνrel⟩
    intro s₂ _ hB₂
    exact ⟨by simp [hpos₂, hpos], [ws', r ++ [ν]], Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (Store.readBlock_succ_of (by kept) (by kept)) rfl),
      r, ν, rfl, hrec, hνrel⟩

end NLAlib.Ops.Examples
