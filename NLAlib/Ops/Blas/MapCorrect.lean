/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Map

/-!
# Stored outputs of unary scalar maps

The ordinary mapped word list and the unchanged tape position are consequences of the unary
map's total weakest-precondition rule, including disjoint views in the same buffer.

## Main results

* `NLAlib.Ops.writes_unaryMap_of_disj_or_eq`: complete stored output of a scalar map.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A unary map stores the mapped word vector and preserves the tape position. -/
theorem writes_unaryMap_of_disj_or_eq {K Op Tst : Type} [Inhabited K] {o : Op} {f : K → K}
    {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.un fun x => some (f x)) AnyOperands) {md : Mode}
    {τ : Tape K} {n : ℕ} {x y : ℕ × ℕ} {m : Mem K} {xs : List K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hy : y.2 + n ≤ m.store.len y.1) :
    Writes md I τ (unaryMap o).body (Env.frame [n] [x, y]) (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock y.1 y.2 n = some (xs.map f)) m := by
  have hw := Writes.of_wp_eq_updBlock (wp_unaryMap_of_disj_or_eq (md := md) (τ := τ) hI hxy hx hy
    (Q := fun m' => m' = m.updBlock y (xs.map f)) rfl)
  have hlen := Store.length_of_readBlock hx
  rw [List.length_map, hlen] at hw
  refine hw.mono le_rfl fun m' _ he => ?_
  subst m'
  have hr := Store.readBlock_updBlock_self (s := m.store) (b := y.1) (off := y.2)
    (xs := xs.map f) (by simpa [List.length_map, hlen] using hy)
  exact ⟨rfl, by simpa [List.length_map, hlen] using hr⟩

end NLAlib.Ops
