/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Map
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# Binary scalar operations with a stored broadcast operand

One loop applies a binary operation to a vector and one stored scalar. The vector may be
updated exactly in place or copied between disjoint regions of one arena.

## Main results

* `NLAlib.Ops.scalarBroadcastRoutine`, `NLAlib.Ops.scalarBroadcastInPlaceRoutine`: the loop as a
  routine `[n] (x : n, a : 1) → (y : n)`, and in place `[n] (x : n, a : 1) → (x)`, on the tree
  `NLAlib.Ops.scalarBroadcast`.
* `NLAlib.Ops.scalarBroadcastRoutine_meets`, `NLAlib.Ops.scalarBroadcastInPlaceRoutine_meets`:
  their judgments.
* `NLAlib.Ops.scalarBroadcast_writes`: the common proof of the two, for either layout.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Apply a binary scalar operation with a fixed stored right operand. -/
def scalarBroadcast {Op Tst : Type} (o : Op) : Stmt Op Tst :=
  .loop (.var 0)
    (.call o [] [⟨0, .var 1 + .var 4⟩, ⟨1, .var 2⟩] [⟨2, .var 3 + .var 4⟩])

/-- A stored broadcast operation returns its pointwise value. The vector operands may alias
exactly; the broadcast scalar must be disjoint from the entire output vector.
One tree, two routines: the common proof of `NLAlib.Ops.scalarBroadcastRoutine_meets` (output
apart) and `NLAlib.Ops.scalarBroadcastInPlaceRoutine_meets` (output on the vector), stated for
either layout. -/
theorem scalarBroadcast_writes {K Op Tst : Type} {o : Op} {f : K → K → K}
    {I : Interp Op Tst K} (hI : I.IsFn .total o (.bin fun x y => some (f x y)) AnyOperands)
    {τ : Tape K} {m : Mem K} {n : ℕ} {x a y : ℕ × ℕ} {v : ℕ → K} {c : K}
    (hx : m.store.HoldsVec x.1 x.2 n v) (ha : m.store.get a.1 a.2 = some c)
    (hy : y.2 + n ≤ m.store.len y.1)
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hay : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock y.1 y.2 n)) :
    Writes .total I τ (scalarBroadcast (Tst := Tst) o) (Env.frame [n] [x, a, y])
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

/-- Packed vector readback of the same broadcast loop, for either layout: the two judgments
read at operands. Kept because the block-sequence rule `NLAlib.Ops.Writes.seq_readBlock` takes
its statement in this form, and because `NLAlib.Ops.RCLikeScalar.scal` is proved once for both
of its layouts. -/
theorem scalarBroadcast_writes_readBlock {K Op Tst : Type} [Inhabited K]
    {o : Op} {f : K → K → K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.bin fun x y => some (f x y)) AnyOperands)
    {τ : Tape K} {m : Mem K} {n : ℕ} {x a y : ℕ × ℕ} {xs : List K} {c : K}
    (hx : m.store.readBlock x.1 x.2 n = some xs) (ha : m.store.get a.1 a.2 = some c)
    (hy : y.2 + n ≤ m.store.len y.1)
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hay : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock y.1 y.2 n)) :
    Writes .total I τ (scalarBroadcast (Tst := Tst) o) (Env.frame [n] [x, a, y])
      (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock y.1 y.2 n = some (xs.map fun v => f v c)) m := by
  refine (scalarBroadcast_writes hI (Store.holdsVec_of_readBlock hx) ha hy hxy hay).mono
    le_rfl ?_
  intro m' _ ⟨hv, hp⟩
  refine ⟨hp, Store.readBlock_eq_some_iff.mpr ⟨?_, ?_⟩⟩
  · simp only [List.length_map, Store.length_of_readBlock hx]
  · intro j hj
    rw [hv j hj]
    have hj' : j < xs.length := by rw [Store.length_of_readBlock hx]; exact hj
    simp [vec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']

/-- A binary operation with a stored right operand, applied entrywise:
`[n] (x : n, a : 1) → (y : n)`, the output apart from the vector and the scalar. -/
def scalarBroadcastRoutine {Op Tst : Type} (o : Op) : Routine Op Tst :=
  routine% [n] (x : n, a : 1) → (y : n) by blocks := scalarBroadcast o

/-- The same loop in place: `[n] (x : n, a : 1) → (x)`, the tree with its output on the
vector; the scalar is apart from the vector. -/
def scalarBroadcastInPlaceRoutine {Op Tst : Type} (o : Op) : Routine Op Tst :=
  routine% [n] (x : n, a : 1) → (x) by blocks := scalarBroadcast o

/-- The written block is the block read with `f · c` applied to each word, `c` the stored
scalar. -/
def scalarBroadcastSpec {K : Type} (f : K → K → K) : Routine.Spec K :=
  spec% [n] (xs, [c]) → (ys) ensures ys = xs.map fun v => f v c

/-- The broadcast loop with its output apart meets its specification, for an operation that is
the total function `f`. -/
theorem scalarBroadcastRoutine_meets {K Op Tst : Type} [Inhabited K] {o : Op} {f : K → K → K}
    {I : Interp Op Tst K} (hI : I.IsFn .total o (.bin fun x y => some (f x y)) AnyOperands) :
    (scalarBroadcastRoutine (Tst := Tst) o).Meets I (scalarBroadcastSpec f) := by
  routine_intro [n] (x, a, y) reads (xs, cs)
  obtain ⟨c, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hcs
  have hd : Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock x.1 x.2 n) ∧
      Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock a.1 a.2 1) := by
    have h : Fp.Disj (Fp.blocks [y] [n]) (Fp.blocks [x, a] [n, 1]) := hblocks.2.1
    exact Fp.disj_sup_right.mp (by simpa [Fp.blocks] using h)
  exact (scalarBroadcast_writes_readBlock hI hxs ha hroom (.inl hd.1.symm) hd.2.symm).mono
    (by fp_sub) fun m' _ ⟨hp, hr⟩ => ⟨hp, [_], Mem.readBlocks_of_cons hr rfl, rfl⟩

/-- The broadcast loop in place meets the same specification. -/
theorem scalarBroadcastInPlaceRoutine_meets {K Op Tst : Type} [Inhabited K] {o : Op}
    {f : K → K → K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.bin fun x y => some (f x y)) AnyOperands) :
    (scalarBroadcastInPlaceRoutine (Tst := Tst) o).Meets I (scalarBroadcastSpec f) := by
  routine_intro [n] (x, a) reads (xs, cs)
  obtain ⟨c, ha, rfl⟩ := Store.readBlock_one_eq_some.mp hcs
  have hd : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock a.1 a.2 1) := by
    have h : Fp.Disj (Fp.blocks [x] [n]) (Fp.blocks [a] [1]) := hblocks.2.1
    simpa [Fp.blocks] using h
  exact (scalarBroadcast_writes_readBlock hI hxs ha hroom (.inr rfl) hd.symm).mono
    (by fp_sub) fun m' _ ⟨hp, hr⟩ => ⟨hp, [_], Mem.readBlocks_of_cons hr rfl, rfl⟩

end NLAlib.Ops
