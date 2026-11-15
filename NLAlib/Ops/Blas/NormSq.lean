/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Tactic

/-!
# Squared modulus of an interleaved scalar pair

The squared components and their sum are computed by two real multiplications and one
addition. The exact word theorem is local to these three calls and uses a separate three-word
view for their outputs.

## Main results

* `NLAlib.Ops.PairScalar.normSq`: the scalar implementation.
* `NLAlib.Ops.PairScalar.normSq_writes`: its total exact word guarantee.
-/

@[expose] public section

namespace NLAlib.Ops.PairScalar

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Compute the squared components in output cells zero and one, and their sum in cell two. -/
def normSq : Impl Op Tst := opsImpl% [] (X) → (T) {
  call (Has.inj ScalarOp.mul) [] (X, X) → (T);
  call (Has.inj ScalarOp.mul) [] (X[1], X[1]) → (T[1]);
  call (Has.inj ScalarOp.add) [] (T, T[1]) → (T[2])
}

/-- Two scalar squares and one addition return the exact sum of squares in output cell two.
The input pair and the three-word output view are spatially separate; both may share a buffer. -/
theorem normSq_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {x t : ℕ × ℕ} {xr xi : ℝ}
    (hxr : m.store.get x.1 x.2 = some xr)
    (hxi : m.store.get x.1 (x.2 + 1) = some xi)
    (hroom : t.2 + 3 ≤ m.store.len t.1)
    (hsep : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock t.1 t.2 3)) :
    Writes .total I τ (normSq (Op := Op) (Tst := Tst)).body (Env.frame [] [x, t])
      (Store.inBlock t.1 t.2 3)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get t.1 (t.2 + 2) = some (xr ^ 2 + xi ^ 2)) m := by
  have hxLive := Store.lt_length_of_get hxr
  have htLive := Store.lt_length_of_lt_len (show t.2 < m.store.len t.1 by omega)
  unfold normSq
  refine (writes_call_bin (hS .mul) rfl rfl trivial hxr hxr rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hRe⟩
  have hxi₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
    (hsep.symm.mono (by fp_sub) (by fp_sub)) hxi
  refine (writes_call_bin (hS .mul) rfl rfl trivial hxi₁ hxi₁ rfl
    (fun _ => ⟨by room, by room⟩)).seq_le (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hIm⟩
  have hRe₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hRe
  refine (writes_call_bin (hS .add) rfl rfl trivial hRe₂ hIm rfl
    (fun _ => ⟨by room, by room⟩)).mono (by fp_sub) ?_
  intro m₃ _ ⟨hp₃, hSum⟩
  have hmul (u v : ℝ) : M.mul u v = u * v := hE.mul u v
  have hadd (u v : ℝ) : M.add u v = u + v := hE.add u v
  exact ⟨hp₃.trans (hp₂.trans hp₁), by simpa only [hmul, hadd, pow_two] using hSum⟩

end NLAlib.Ops.PairScalar
