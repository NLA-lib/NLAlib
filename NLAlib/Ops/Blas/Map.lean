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
# Scalar maps over stored vectors

Unary and binary scalar operations applied independently to vectors are counted loops. Their
proofs use only the scalar block functions, so arithmetic and conversion kernels reuse the
same memory argument, including exact in-place aliases.

## Main results

* `NLAlib.Ops.unaryMap` and `NLAlib.Ops.binaryMap` implement pointwise scalar maps.
* `NLAlib.Ops.writes_binaryMap` permits exact aliases or disjoint input/output views.
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

/-- Apply one binary scalar operation to corresponding entries of two stored vectors.
The output may be exactly either input, or spatially disjoint from it. -/
def binaryMap (o : Op) : Impl Op Tst where
  nd := 1
  nin := 2
  nout := 1
  body := .loop (.var 0) (.call o []
    [⟨0, .var 1 + .var 4⟩, ⟨1, .var 2 + .var 4⟩] [⟨2, .var 3 + .var 4⟩])

/-- A binary map performs one declared scalar call per output word. -/
theorem stmtCost_binaryMap (o : Op) (n x y z : ℕ) :
    stmtCost (binaryMap (Tst := Tst) o).body [n, x, y, z] = n • Count.one o [] := by
  simp [binaryMap, stmtCost, useCost]

/-- The only workspace of a binary map is the workspace of its scalar operation. -/
theorem stmtPeak_binaryMap_le (o : Op) (W : Op → List ℕ → ℕ) (n x y z : ℕ) :
    stmtPeak W (binaryMap (Tst := Tst) o).body [n, x, y, z] ≤ W o [] := by
  simp only [binaryMap, stmtPeak]
  exact Finset.sup_le fun _ _ => le_rfl

omit [Inhabited K] in
/-- A binary scalar map writes its pointwise mathematical result. Exact aliases and
spatially separate input/output views are admitted independently for both inputs. -/
theorem writes_binaryMap {o : Op} {f : K → K → K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.bin fun x y => some (f x y)) AnyOperands)
    {τ : Tape K} {m : Mem K} {n : ℕ} {x y z : ℕ × ℕ} {vx vy : ℕ → K}
    (hx : m.store.HoldsVec x.1 x.2 n vx) (hy : m.store.HoldsVec y.1 y.2 n vy)
    (hz : z.2 + n ≤ m.store.len z.1)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z)
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock z.1 z.2 n) ∨ y = z) :
    Writes .total I τ (binaryMap (Tst := Tst) o).body (Env.frame [n] [x, y, z])
      (Store.inBlock z.1 z.2 n)
      (fun m' => m'.store.HoldsVec z.1 z.2 n (fun i => f (vx i) (vy i)) ∧ m'.pos = m.pos) m := by
  refine writes_fill rfl (fun i => f (vx i) (vy i)) (fun _ => m.pos) rfl
    fun i hi m' hfr _ hpos => ?_
  have hread (a : ℕ × ℕ) (v : ℕ → K) (ha : m.store.HoldsVec a.1 a.2 n v)
      (haz : Fp.Disj (Store.inBlock a.1 a.2 n) (Store.inBlock z.1 z.2 n) ∨ a = z) :
      m'.store.get a.1 (a.2 + i) = some (v i) := by
    rw [hfr.get_eq ?_]
    · exact ha i hi
    · intro hw
      rcases haz with hd | rfl
      · exact hd _ _ ⟨rfl, by omega, by omega⟩
          ⟨hw.1, hw.2.1, by have := hw.2.2; omega⟩
      · rcases hw with ⟨_, h₁, h₂⟩
        omega
  have hroom : z.2 + i < m'.store.len z.1 := by rw [hfr.len_eq]; omega
  refine wp_call_bin hI rfl rfl rfl trivial (hread x vx hx hxz) (hread y vy hy hyz)
    rfl hroom ?_
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
    Store.get_upd_self hroom _, hpos⟩

end NLAlib.Ops
