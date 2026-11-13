/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Clamping a stored word before index conversion

The clamp compares the actual decoded input with two stored endpoint words and copies the
selected word. No arithmetic or conversion is hidden in the comparisons. With endpoints
exactly decoding to zero and a natural bound, the subsequent toNat query always succeeds
within the bound, even when the original word decodes to a negative value.

## Main results

* `NLAlib.Ops.clamp` is the fixed scalar program.
* `NLAlib.Ops.wp_clamp` identifies its entire updated memory, permitting operand aliases.
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
def clamp : Impl Op Tst where
  nd := 0
  nin := 3
  nout := 1
  body := .ite (Has.inj CmpTst.le) [] [⟨0, .var 0⟩, ⟨2, .var 2⟩]
    (.ite (Has.inj CmpTst.le) [] [⟨1, .var 1⟩, ⟨2, .var 2⟩]
      (.call (Has.inj ScalarOp.copy) [] [⟨1, .var 1⟩] [⟨3, .var 3⟩])
      (.call (Has.inj ScalarOp.copy) [] [⟨2, .var 2⟩] [⟨3, .var 3⟩]))
    (.call (Has.inj ScalarOp.copy) [] [⟨0, .var 0⟩] [⟨3, .var 3⟩])

/-- The total functional clamp changes exactly its output cell. The scalar copy contract and
exact comparison contract use the same interpretation; input words are actual readable cells. -/
theorem wp_clamp {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I) {md : Mode} {τ : Tape K}
    {a b x z : ℕ × ℕ} {lo hi w : K} {m : Mem K}
    (ha : m.store.get a.1 a.2 = some lo) (hb : m.store.get b.1 b.2 = some hi)
    (hx : m.store.get x.1 x.2 = some w) (hz : z.2 < m.store.len z.1)
    {Q : Mem K → Prop} (hQ : Q (m.upd z (clampWord dec lo hi w))) :
    Wp md I τ clamp.body (Env.frame [] [a, b, x, z]) Q m := by
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

/-- Framed version of the functional clamp, with its selected output and preserved tape
position. No initialization or nonaliasing assumption is needed on the output. -/
theorem writes_clamp {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I) {md : Mode} {τ : Tape K}
    {a b x z : ℕ × ℕ} {lo hi w : K} {m : Mem K}
    (ha : m.store.get a.1 a.2 = some lo) (hb : m.store.get b.1 b.2 = some hi)
    (hx : m.store.get x.1 x.2 = some w) (hz : z.2 < m.store.len z.1) :
    Writes md I τ clamp.body (Env.frame [] [a, b, x, z]) (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get z.1 z.2 = some (clampWord dec lo hi w)) m := by
  apply wp_clamp hS hC ha hb hx hz
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _, rfl,
    Store.get_upd_self hz _⟩

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

/-- A clamp followed by a bounded index binder always passes its conversion guard when its
endpoints decode to zero and the bound. The callback receives the precise bounded floor and
an arbitrary framed post-state. This applies to computed split sizes, including negative or
oversized initial words, without an execution-success assumption. -/
theorem writes_clamp_bindIdx [Has IdxTst Tst] {M : Machine K} {dec : K → ℝ}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hC : IsCmp dec I) (hQ : IsToNat dec I)
    {τ : Tape K} {ρ : Env} {m : Mem K} {args : List Operand} {out : Operand}
    {bound : IExp} {body : Stmt Op Tst} {a b x z : ℕ × ℕ} {lo hi w : K} {B : ℕ}
    {F : Fp} {P : Mem K → Prop}
    (hargs : Operand.evalList ρ args = some [a, b, x, z])
    (hout : out.eval ρ = some z) (hB : bound.eval ρ.idx = some B)
    (ha : m.store.get a.1 a.2 = some lo) (hb : m.store.get b.1 b.2 = some hi)
    (hx : m.store.get x.1 x.2 = some w) (hz : z.2 < m.store.len z.1)
    (hlo : dec lo = 0) (hhi : dec hi = B)
    (hbody : ∀ m', m.store.EqOff (Store.inBlock z.1 z.2 1) m'.store →
      m'.pos = m.pos → m'.store.get z.1 z.2 = some (clampWord dec lo hi w) →
      Writes .total I τ body (ρ.pushIdx (min B ⌊dec w⌋₊)) F P m') :
    Writes .total I τ
      (.seq (.frame [] args clamp.body) (.bindIdx (Has.inj IdxTst.toNat) [out] bound body))
      ρ (Store.inBlock z.1 z.2 1 ⊔ F) P m := by
  have hl : m.Live [a, b, x, z] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    exact ⟨Store.lt_length_of_get ha, Store.lt_length_of_get hb,
      Store.lt_length_of_get hx, Store.lt_length_of_lt_len hz⟩
  refine (writes_frame rfl hargs hl (writes_clamp hS hC ha hb hx hz)).seq
    fun m' hfr ⟨hpos, hget⟩ => ?_
  refine writes_bindIdx_of_isIndex hQ (v := min B ⌊dec w⌋₊)
    (by simp [Operand.evalList, hout]) hB
    (BlockFn.readBlocks_cells_one.mpr ⟨_, hget, rfl⟩) ?_ (min_le_left _ _) ?_
  · simpa using toNatFn_clampWord (w := w) hlo hhi
  · exact hbody m' hfr hpos hget

end NLAlib.Ops
