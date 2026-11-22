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
# Stored outputs of unary scalar maps

The ordinary mapped word list and the unchanged tape position are consequences of the unary
map's total weakest-precondition rule, including disjoint views in the same buffer.

## Main results

* `NLAlib.Ops.unaryMapRoutine`, `NLAlib.Ops.unaryMapInPlaceRoutine`: the map as a routine
  `[n] (x : n) → (y : n)`, and in place `[n] (x : n) → (x)`, on the tree `NLAlib.Ops.unaryMap`.
* `NLAlib.Ops.unaryMapRoutine_meets`, `NLAlib.Ops.unaryMapInPlaceRoutine_meets`: their
  judgments.
* `NLAlib.Ops.unaryMap_writes_of_disj_or_eq`: the common proof of the two, for either layout.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A unary map stores the mapped word vector and preserves the tape position, with its output
apart from its input or on it. One tree, two routines: the common proof of
`NLAlib.Ops.unaryMapRoutine_meets` (output apart) and
`NLAlib.Ops.unaryMapInPlaceRoutine_meets` (output on the input), stated for either layout; it
is also the two judgments read at operands, for callers inside a loop or block-sequence
rule. -/
theorem unaryMap_writes_of_disj_or_eq {K Op Tst : Type} [Inhabited K] {o : Op} {f : K → K}
    {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.un fun x => some (f x)) AnyOperands) {md : Mode}
    {τ : Tape K} {n : ℕ} {x y : ℕ × ℕ} {m : Mem K} {xs : List K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hy : y.2 + n ≤ m.store.len y.1) :
    Writes md I τ (unaryMap o) (Env.frame [n] [x, y]) (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock y.1 y.2 n = some (xs.map f)) m := by
  have hw := Writes.of_wp_eq_updBlock (unaryMap_wp_of_disj_or_eq (md := md) (τ := τ) hI hxy hx hy
    (Q := fun m' => m' = m.updBlock y (xs.map f)) rfl)
  have hlen := Store.length_of_readBlock hx
  rw [List.length_map, hlen] at hw
  refine hw.mono le_rfl fun m' _ he => ?_
  subst m'
  have hr := Store.readBlock_updBlock_self (s := m.store) (b := y.1) (off := y.2)
    (xs := xs.map f) (by simpa [List.length_map, hlen] using hy)
  exact ⟨rfl, by simpa [List.length_map, hlen] using hr⟩

/-- A unary operation applied entrywise: `[n] (x : n) → (y : n)`, the two blocks apart; they
may be in one buffer. -/
def unaryMapRoutine {Op Tst : Type} (o : Op) : Routine Op Tst :=
  routine% [n] (x : n) → (y : n) by blocks := unaryMap o

/-- The same map in place: `[n] (x : n) → (x)`, the tree with its output on its input. -/
def unaryMapInPlaceRoutine {Op Tst : Type} (o : Op) : Routine Op Tst :=
  routine% [n] (x : n) → (x) by blocks := unaryMap o

/-- The written block is the block read with `f` applied to each word. -/
def unaryMapSpec {K : Type} (f : K → K) : Routine.Spec K :=
  spec% [n] (xs) → (ys) ensures ys = xs.map f

/-- The unary map with its output apart meets its specification, for an operation that is the
total function `f`. -/
theorem unaryMapRoutine_meets {K Op Tst : Type} [Inhabited K] {o : Op} {f : K → K}
    {I : Interp Op Tst K} (hI : I.IsFn .total o (.un fun x => some (f x)) AnyOperands) :
    (unaryMapRoutine (Tst := Tst) o).Meets I (unaryMapSpec f) := by
  routine_intro [n] (x, y) reads (xs)
  have hd : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) := by
    have h : Fp.Disj (Fp.blocks [y] [n]) (Fp.blocks [x] [n]) := hblocks.2.1
    simpa [Fp.blocks] using h.symm
  exact (unaryMap_writes_of_disj_or_eq hI (.inl hd) hxs hroom).mono (by fp_sub)
    fun m' _ ⟨hp, hr⟩ => ⟨hp, [_], Mem.readBlocks_of_cons hr rfl, rfl⟩

/-- The unary map in place meets the same specification. -/
theorem unaryMapInPlaceRoutine_meets {K Op Tst : Type} [Inhabited K] {o : Op} {f : K → K}
    {I : Interp Op Tst K} (hI : I.IsFn .total o (.un fun x => some (f x)) AnyOperands) :
    (unaryMapInPlaceRoutine (Tst := Tst) o).Meets I (unaryMapSpec f) := by
  routine_intro [n] (x) reads (xs)
  exact (unaryMap_writes_of_disj_or_eq hI (.inr rfl) hxs hroom).mono (by fp_sub)
    fun m' _ ⟨hp, hr⟩ => ⟨hp, [_], Mem.readBlocks_of_cons hr rfl, rfl⟩

end NLAlib.Ops
