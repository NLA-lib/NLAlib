/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Tactic
public import NLAlib.Ops.Catalog.Scalar

/-!
# Unary scalar maps over stored vectors

A unary scalar operation applied independently to a vector is one counted loop. Its proof
uses only the scalar block function, so negation, conversion, and other unary operations reuse
the same memory argument.

## Main results

* `NLAlib.Ops.unaryMap` is the implementation of a unary operation over a vector.
* `NLAlib.Ops.wp_unaryMap_of_disj_or_eq` permits disjoint regions of the same arena buffer.
* `NLAlib.Ops.wp_unaryMap` identifies the complete updated memory for distinct buffers or
  exactly in-place operands, from the operation's functional contract.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Inhabited K]

/-- Apply one unary operation to each entry of a vector, without scratch allocations.
The operation reads one cell and writes one cell. -/
def unaryMap (o : Op) : Impl Op Tst where
  nd := 1
  nin := 1
  nout := 1
  body := .loop (.var 0) (.call o [] [⟨0, .var 1 + .var 3⟩] [⟨1, .var 2 + .var 3⟩])

/-- The unary map's complete primitive count is one call per entry. -/
theorem stmtCost_unaryMap (o : Op) (n x y : ℕ) :
    stmtCost (unaryMap (Tst := Tst) o).body [n, x, y] = n • Count.one o [] := by
  simp [unaryMap, stmtCost, useCost]

/-- A unary map has only the workspace of a primitive call, independently of vector length. -/
theorem stmtPeak_unaryMap_le (o : Op) (W : Op → List ℕ → ℕ) (n x y : ℕ) :
    stmtPeak W (unaryMap (Tst := Tst) o).body [n, x, y] ≤ W o [] := by
  simp only [unaryMap, stmtPeak]
  exact Finset.sup_le fun _ _ => le_rfl

/-- The unary map writes the mapped input vector to the output buffer and preserves all other
memory and the random-tape position. Inputs are stored words and the output has room;
operands may coincide exactly or occupy disjoint blocks of the same buffer. -/
theorem wp_unaryMap_of_disj_or_eq {o : Op} {f : K → K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.un fun x => some (f x)) AnyOperands) {md : Mode}
    {τ : Tape K} {n : ℕ} {x y : ℕ × ℕ} {m : Mem K} {xs : List K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hy : y.2 + n ≤ m.store.len y.1) {Q : Mem K → Prop}
    (hQ : Q (m.updBlock y (xs.map f))) :
    Wp md I τ (unaryMap o).body (Env.frame [n] [x, y]) Q m := by
  have hxs := Store.length_of_readBlock hx
  have hgx : ∀ k < n, m.store.get x.1 (x.2 + k) = some (vec xs k) :=
    fun k hk => Store.get_of_readBlock hx hk default
  refine wp_loop (k := n) rfl (fun i m' => ∃ s', m' = ⟨s', m.pos⟩ ∧
    m.store.EqOff (Store.inBlock y.1 y.2 i) s' ∧
    s'.readBlock y.1 y.2 i = some ((xs.take i).map f))
    ⟨_, rfl, Store.EqOff.refl _ _, rfl⟩ ?_ ?_
  · rintro i hi m' ⟨s', rfl, hfr, hr⟩
    have hlen := hfr.len_eq y.1
    refine wp_call_un hI rfl rfl rfl trivial (a := vec xs i) ?_ rfl ?_ ?_
    · rw [← hgx i hi]
      exact hfr.get_eq (by
        rcases hxy with hdisj | rfl
        · intro hw
          exact hdisj x.1 (x.2 + i) ⟨rfl, by omega, by omega⟩
            ⟨hw.1, hw.2.1, by have := hw.2.2; omega⟩
        · rintro ⟨_, h1, h2⟩
          omega)
    · store_simp
    · refine ⟨_, rfl, (hfr.mono fun b j h => ?_).upd ⟨rfl, by omega, by omega⟩ _, ?_⟩
      · exact ⟨h.1, h.2.1, by have := h.2.2; omega⟩
      · have htake : xs.take (i + 1) = xs.take i ++ [vec xs i] := by
          rw [List.take_add_one, vec, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega)]
          rfl
        rw [htake, List.map_append, List.map_singleton]
        exact Store.readBlock_upd_concat hr (by omega) _
  · rintro m' ⟨s', rfl, hfr, hr⟩
    rw [show xs.take n = xs by exact List.take_of_length_le (by omega)] at hr
    simpa [hfr.eq_updBlock hr, Mem.updBlock] using hQ

/-- A unary map between distinct buffers, or exactly in place, is a specialization of the
block-disjoint rule. The complete output memory and tape position are unchanged by this
specialization; no new execution proof is needed. -/
theorem wp_unaryMap {o : Op} {f : K → K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.un fun x => some (f x)) AnyOperands) {md : Mode}
    {τ : Tape K} {n : ℕ} {x y : ℕ × ℕ} {m : Mem K} {xs : List K}
    (hxy : x.1 ≠ y.1 ∨ x = y) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hy : y.2 + n ≤ m.store.len y.1) {Q : Mem K → Prop}
    (hQ : Q (m.updBlock y (xs.map f))) :
    Wp md I τ (unaryMap o).body (Env.frame [n] [x, y]) Q m :=
  wp_unaryMap_of_disj_or_eq hI (hxy.imp Fp.disj_inBlock_of_ne id) hx hy hQ

end NLAlib.Ops
