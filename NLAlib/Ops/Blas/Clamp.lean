/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# Clamping a stored word before index conversion

The clamp compares the actual decoded input with two stored endpoint words and copies the
selected word. No arithmetic or conversion is hidden in the comparisons. With endpoints
exactly decoding to zero and a natural bound, the subsequent toNat query always succeeds
within the bound, even when the original word decodes to a negative value.

## Main results

* `NLAlib.Ops.clampRoutine`: the clamp in place, `[] (lo : 1, hi : 1, x : 1) → (x)`, on the
  tree `NLAlib.Ops.clamp`.
* `NLAlib.Ops.clampRoutine_meets`: its judgment.
* `NLAlib.Ops.toNatFn_clampWord` gives the bounded natural floor of the selected word.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Select the stored lower endpoint below the interval, the upper endpoint above it, and the
input otherwise. Numerical endpoint order is only needed for interval interpretations. -/
noncomputable def clampWord (dec : K → ℝ) (lo hi x : K) : K :=
  if dec lo ≤ dec x then if dec hi ≤ dec x then hi else x else lo

/-- Clamp one input word between two stored endpoint words. The three inputs and one output
may alias. Copying the interior input makes the output independent of its prior contents. -/
def clamp : Stmt Op Tst :=
  .ite (Has.inj CmpTst.le) [] [⟨0, .var 0⟩, ⟨2, .var 2⟩]
    (.ite (Has.inj CmpTst.le) [] [⟨1, .var 1⟩, ⟨2, .var 2⟩]
      (.call (Has.inj ScalarOp.copy) [] [⟨1, .var 1⟩] [⟨3, .var 3⟩])
      (.call (Has.inj ScalarOp.copy) [] [⟨2, .var 2⟩] [⟨3, .var 3⟩]))
    (.call (Has.inj ScalarOp.copy) [] [⟨0, .var 0⟩] [⟨3, .var 3⟩])

/-- The clamp changes exactly its output cell, for any aliasing of its four operands. A step in
the proof of `NLAlib.Ops.clampRoutine_meets`; callers use that judgment. -/
private theorem clamp_wp {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I) {md : Mode} {τ : Tape K}
    {a b x z : ℕ × ℕ} {lo hi w : K} {m : Mem K}
    (ha : m.store.get a.1 a.2 = some lo) (hb : m.store.get b.1 b.2 = some hi)
    (hx : m.store.get x.1 x.2 = some w) (hz : z.2 < m.store.len z.1)
    {Q : Mem K → Prop} (hQ : Q (m.upd z (clampWord dec lo hi w))) :
    Wp md I τ clamp (Env.frame [] [a, b, x, z]) Q m := by
  classical
  refine wp_ite rfl rfl (hC.test_le ha hx) ?_
  by_cases h0 : dec lo ≤ dec w
  · simp only [h0, decide_true, if_true]
    refine wp_ite rfl rfl (hC.test_le hb hx) ?_
    by_cases h1 : dec hi ≤ dec w
    · simp only [h1, decide_true, if_true]
      exact wp_call_un (hS .copy) rfl rfl rfl trivial hb rfl hz
        (by simpa [clampWord, h0, h1] using hQ)
    · simp only [h1, decide_false, Bool.false_eq_true, if_false]
      exact wp_call_un (hS .copy) rfl rfl rfl trivial hx rfl hz
        (by simpa [clampWord, h0, h1] using hQ)
  · simp only [h0, decide_false, Bool.false_eq_true, if_false]
    exact wp_call_un (hS .copy) rfl rfl rfl trivial ha rfl hz
      (by simpa [clampWord, h0] using hQ)

/-- Clamp a word in place between two stored endpoints: `[] (lo : 1, hi : 1, x : 1) → (x)`, the
tree `NLAlib.Ops.clamp` with its input and its output on `x`; `x` is apart from the endpoints. -/
def clampRoutine : Routine Op Tst :=
  routine% [] (lo : 1, hi : 1, x : 1) → (x) by blocks := clamp

/-- The cell holds the clamp `NLAlib.Ops.clampWord` of the word it held. -/
noncomputable def clampSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [] ([lo], [hi], [w]) → (zs) ensures zs = [clampWord dec lo hi w]

/-- The clamp meets its specification under the scalar copy and the exact comparison, with no
assumption on the order of the endpoints. -/
theorem clampRoutine_meets {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I) :
    (clampRoutine (Op := Op) (Tst := Tst)).Meets I (clampSpec dec) := by
  routine_intro [] (a, b, x) reads (los, his, ws)
  obtain ⟨lo, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hlos
  obtain ⟨hi, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hhis
  obtain ⟨w, hx, rfl⟩ := Store.readBlock_one_eq_some.mp hws
  have hz : x.2 < m.store.len x.1 := by omega
  have key : Writes .total I τ (clamp (Op := Op) (Tst := Tst)) (Env.frame [] [a, b, x, x])
      (Store.inBlock x.1 x.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get x.1 x.2 = some (clampWord dec lo hi w)) m := by
    apply clamp_wp hS hC ha hb hx hz
    exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _, rfl,
      Store.get_upd_self hz _⟩
  exact key.mono (by fp_sub) fun m' _ ⟨hpos, hget⟩ =>
    ⟨hpos, [_], Mem.readBlocks_of_cons (Store.readBlock_one_of_get hget) rfl, rfl⟩

/-- With endpoints decoding to zero and `bound`, the selected word converts to the bounded
natural floor. Negative input is clamped before conversion rather than admitted as an index. -/
theorem toNatFn_clampWord {dec : K → ℝ} {lo hi w : K} {bound : ℕ}
    (hlo : dec lo = 0) (hhi : dec hi = bound) :
    toNatFn dec [clampWord dec lo hi w] = some (min bound ⌊dec w⌋₊) := by
  classical
  unfold clampWord
  rw [hlo, hhi]
  split_ifs with h0 hk
  · simp only [toNatFn, hhi, Nat.cast_nonneg, ↓reduceIte, Nat.floor_natCast]
    rw [min_eq_left (Nat.le_floor hk)]
  · simp only [toNatFn, h0, ↓reduceIte]
    rw [min_eq_right ((Nat.floor_lt h0).mpr (not_le.mp hk)).le]
  · simp only [toNatFn, hlo, le_refl, ↓reduceIte, Nat.floor_zero]
    rw [Nat.floor_eq_zero.mpr (by linarith), min_zero]

end NLAlib.Ops
