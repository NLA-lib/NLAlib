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
* `NLAlib.Ops.PairScalar.normSq_writes_word`: its total word guarantee on any scalar machine.
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

/-- Two scalar squares and one addition store the machine word `fl(fl(xr·xr) + fl(xi·xi))` in
output cell two, on any scalar machine. The input pair and the three-word output view are
spatially separate; both may share a buffer. -/
theorem normSq_writes_word {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ}
    {x t : ℕ × ℕ} {xr xi : ℝ}
    (hxr : m.store.get x.1 x.2 = some xr)
    (hxi : m.store.get x.1 (x.2 + 1) = some xi)
    (hroom : t.2 + 3 ≤ m.store.len t.1)
    (hsep : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock t.1 t.2 3)) :
    Writes .total I τ (normSq (Op := Op) (Tst := Tst)).body (Env.frame [] [x, t])
      (Store.inBlock t.1 t.2 3)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get t.1 (t.2 + 2) = some (M.add (M.mul xr xr) (M.mul xi xi))) m := by
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
  exact ⟨hp₃.trans (hp₂.trans hp₁), hSum⟩

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
  have hmul (u v : ℝ) : M.mul u v = u * v := hE.mul u v
  have hadd (u v : ℝ) : M.add u v = u + v := hE.add u v
  simpa only [hmul, hadd, pow_two] using normSq_writes_word (τ := τ) hS hxr hxi hroom hsep

/-- Under the standard model with $0 \le u \le 1$, the rounded sum of rounded squares
$\mathrm{fl}(\mathrm{fl}(x^2) + \mathrm{fl}(y^2))$ lies between $(1-u)^2(x^2+y^2)$ and
$(1+u)^2(x^2+y^2)$. -/
theorem _root_.NLAlib.Ops.StdModel.add_mul_self_bounds {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) (hu : 0 ≤ u) (hu1 : u ≤ 1) (x y : ℝ) :
    (1 - u) ^ 2 * (x ^ 2 + y ^ 2) ≤ M.add (M.mul x x) (M.mul y y) ∧
      M.add (M.mul x x) (M.mul y y) ≤ (1 + u) ^ 2 * (x ^ 2 + y ^ 2) := by
  have hp := abs_le.mp (hM.mul x x)
  have hq := abs_le.mp (hM.mul y y)
  have hs := abs_le.mp (hM.add (M.mul x x) (M.mul y y))
  simp only [id_eq] at hp hq hs
  have hx : 0 ≤ x * x := mul_self_nonneg x
  have hy : 0 ≤ y * y := mul_self_nonneg y
  rw [abs_of_nonneg hx] at hp
  rw [abs_of_nonneg hy] at hq
  have hS : (1 - u) * (x * x + y * y) ≤ M.mul x x + M.mul y y := by nlinarith
  have hS' : M.mul x x + M.mul y y ≤ (1 + u) * (x * x + y * y) := by nlinarith
  have hS0 : 0 ≤ M.mul x x + M.mul y y := by nlinarith
  rw [abs_of_nonneg hS0] at hs
  constructor <;> nlinarith

end NLAlib.Ops.PairScalar
