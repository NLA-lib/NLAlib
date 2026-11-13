/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Logic.Writes

/-!
# Stored sizes and bounded index binders

A dimension literal is an ordinary operation, with a one-cell footprint and no tape advance.
An exactly decoded natural is read by the existing toNat query, with the binder's bound checked
explicitly. These rules hide store and conversion bookkeeping without hiding an executed call.

## Main results

* `NLAlib.Ops.writes_indexLit` writes a dimension using the scalar machine's literal function.
* `NLAlib.Ops.writes_bindIdx_of_decode_nat` binds a readable exactly decoded natural.
* `NLAlib.Ops.writes_indexLit_bindIdx` composes the write/read roundtrip in total mode.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}

/-- A dimension literal writes its machine word in one cell and preserves the tape position.
Only writable capacity is required; the cell need not be initialized. -/
theorem writes_indexLit [Has IndexOp Op] {M : Machine K} (hI : IsIndexLit M I)
    {e : IExp} {out : Operand} {n : ℕ} {z : ℕ × ℕ}
    (he : e.eval ρ.idx = some n) (ho : out.eval ρ = some z)
    (hz : z.2 < m.store.len z.1) :
    Writes .total I τ (.call (Has.inj IndexOp.lit) [e] [] [out]) ρ
      (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some (M.lit (n : ℚ))) m := by
  refine (writes_call_cell hI (d := [n]) (a := [])
    (by simp [IExp.evalList, he]) rfl (by simp [Operand.evalList, ho])
    rfl rfl rfl trivial (fun _ => ?_)).mono le_rfl ?_
  · refine ⟨?_, ⟨[], rfl, [[M.lit (n : ℚ)]], rfl, rfl⟩, hz⟩
    simpa using Store.lt_length_of_lt_len hz
  · rintro m' _ ⟨hpos, xs, v, _, hv, hrel⟩
    have hv' : M.lit (n : ℚ) = v := by
      simpa [Machine.indexFn, BlockFn.rel] using hrel
    exact ⟨by simpa [Machine.indexFn] using hpos, hv'.symm ▸ hv⟩

/-- Bind a readable natural word, under the actual conversion contract and the explicit
runtime upper bound. The body is proved at that natural, with no guessed conversion result. -/
theorem writes_bindIdx_of_decode_nat [Has IdxTst Tst] {md : Mode} {dec : K → ℝ}
    (hI : IsToNat dec I) {input : Operand} {bound : IExp} {body : Stmt Op Tst}
    {x : ℕ × ℕ} {w : K} {n B : ℕ} {F : Fp} {P : Mem K → Prop}
    (ha : input.eval ρ = some x) (hB : bound.eval ρ.idx = some B)
    (hx : m.store.get x.1 x.2 = some w) (hw : dec w = n) (hn : n ≤ B)
    (h : Writes md I τ body (ρ.pushIdx n) F P m) :
    Writes md I τ (.bindIdx (Has.inj IdxTst.toNat) [input] bound body) ρ F P m :=
  writes_bindIdx (by simp [Operand.evalList, ha]) hB
    (hI.index_eq_of_decode_nat hx hw) hn h

/-- A stored dimension can be read back by a bounded index binder when its literal is exact.
The continuation receives an arbitrary framed post-state, not a concrete chain of updates.
Both the writing call and the index query remain in the executed statement. -/
theorem writes_indexLit_bindIdx [Has IndexOp Op] [Has IdxTst Tst] {dec : K → ℝ}
    {M : Machine K} (hL : IsIndexLit M I) (hQ : IsToNat dec I)
    {e bound : IExp} {cell : Operand} {body : Stmt Op Tst} {n B : ℕ} {z : ℕ × ℕ}
    {F : Fp} {P : Mem K → Prop} (he : e.eval ρ.idx = some n)
    (hB : bound.eval ρ.idx = some B) (hz : cell.eval ρ = some z)
    (hroom : z.2 < m.store.len z.1) (hexact : IsExactNatLit dec M B) (hn : n ≤ B)
    (hbody : ∀ m', m.store.EqOff (Store.inBlock z.1 z.2 1) m'.store →
      m'.pos = m.pos → m'.store.get z.1 z.2 = some (M.lit (n : ℚ)) →
        Writes .total I τ body (ρ.pushIdx n) F P m') :
    Writes .total I τ
      (.seq (.call (Has.inj IndexOp.lit) [e] [] [cell])
        (.bindIdx (Has.inj IdxTst.toNat) [cell] bound body)) ρ
      (Store.inBlock z.1 z.2 1 ⊔ F) P m := by
  refine (writes_indexLit hL he hz hroom).seq fun m' hfr ⟨hpos, hget⟩ => ?_
  exact writes_bindIdx_of_decode_nat hQ hz hB hget (hexact n hn) hn
    (hbody m' hfr hpos hget)

end NLAlib.Ops
