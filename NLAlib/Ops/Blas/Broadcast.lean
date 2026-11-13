/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Map

/-!
# Binary scalar operations with a stored broadcast operand

One loop applies a binary operation to a vector and one stored scalar. The vector may be
updated exactly in place or copied between disjoint regions of one arena.

## Main results

* `NLAlib.Ops.scalarBroadcast`: the explicit vector/scalar loop.
* `NLAlib.Ops.writes_scalarBroadcast`: its total pointwise mathematical result.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Apply a binary scalar operation with a fixed stored right operand. -/
def scalarBroadcast {Op Tst : Type} (o : Op) : Impl Op Tst where
  nd := 1
  nin := 2
  nout := 1
  body := .loop (.var 0)
    (.call o [] [⟨0, .var 1 + .var 4⟩, ⟨1, .var 2⟩] [⟨2, .var 3 + .var 4⟩])

/-- A stored broadcast operation returns its pointwise value. The vector operands may alias
exactly; the broadcast scalar must be disjoint from the entire output vector. -/
theorem writes_scalarBroadcast {K Op Tst : Type} {o : Op} {f : K → K → K}
    {I : Interp Op Tst K} (hI : I.IsFn .total o (.bin fun x y => some (f x y)) AnyOperands)
    {τ : Tape K} {m : Mem K} {n : ℕ} {x a y : ℕ × ℕ} {v : ℕ → K} {c : K}
    (hx : m.store.HoldsVec x.1 x.2 n v) (ha : m.store.get a.1 a.2 = some c)
    (hy : y.2 + n ≤ m.store.len y.1)
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hay : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock y.1 y.2 n)) :
    Writes .total I τ (scalarBroadcast (Tst := Tst) o).body (Env.frame [n] [x, a, y])
      (Store.inBlock y.1 y.2 n)
      (fun m' => m'.store.HoldsVec y.1 y.2 n (fun i => f (v i) c) ∧ m'.pos = m.pos) m := by
  refine writes_fill rfl (fun i => f (v i) c) (fun _ => m.pos) rfl
    fun i hi m' hfr _ hpos => ?_
  have hget : m'.store.get x.1 (x.2 + i) = some (v i) := by
    rw [hfr.get_eq ?_]
    · exact hx i hi
    · intro hw
      rcases hxy with hd | rfl
      · exact hd _ _ ⟨rfl, by omega, by omega⟩ ⟨hw.1, hw.2.1, by have := hw.2.2; omega⟩
      · rcases hw with ⟨_, h₁, h₂⟩
        omega
  have hscalar : m'.store.get a.1 a.2 = some c := by
    rw [hfr.get_eq ?_]
    · exact ha
    · intro hw
      exact hay _ _ ⟨rfl, le_rfl, by omega⟩ ⟨hw.1, hw.2.1, by have := hw.2.2; omega⟩
  have hz : y.2 + i < m'.store.len y.1 := by rw [hfr.len_eq]; omega
  refine wp_call_bin hI rfl rfl rfl trivial hget hscalar rfl hz ?_
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _,
    Store.get_upd_self hz _, hpos⟩

/-- Packed vector readback of the same broadcast loop. -/
theorem writes_scalarBroadcast_readBlock {K Op Tst : Type} [Inhabited K]
    {o : Op} {f : K → K → K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.bin fun x y => some (f x y)) AnyOperands)
    {τ : Tape K} {m : Mem K} {n : ℕ} {x a y : ℕ × ℕ} {xs : List K} {c : K}
    (hx : m.store.readBlock x.1 x.2 n = some xs) (ha : m.store.get a.1 a.2 = some c)
    (hy : y.2 + n ≤ m.store.len y.1)
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hay : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock y.1 y.2 n)) :
    Writes .total I τ (scalarBroadcast (Tst := Tst) o).body (Env.frame [n] [x, a, y])
      (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock y.1 y.2 n = some (xs.map fun v => f v c)) m := by
  refine (writes_scalarBroadcast hI (Store.holdsVec_of_readBlock hx) ha hy hxy hay).mono
    le_rfl ?_
  intro m' _ ⟨hv, hp⟩
  refine ⟨hp, Store.readBlock_eq_some_iff.mpr ⟨?_, ?_⟩⟩
  · simp only [List.length_map, Store.length_of_readBlock hx]
  · intro j hj
    rw [hv j hj]
    have hj' : j < xs.length := by rw [Store.length_of_readBlock hx]; exact hj
    simp [vec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']

end NLAlib.Ops
