/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Footprint

/-!
# Scalar addresses within separated regions

Straight-line scalar evaluation uses address inequality to simplify an updated cell function.
Region separation supplies that inequality uniformly for all bounded component offsets,
including disjoint regions of the same buffer.

## Main results

* `NLAlib.Ops.Fp.Disj.ne_offsets`: bounded cells of separated blocks have different addresses.
-/

@[expose] public section

namespace NLAlib.Ops.Fp

/-- Bounded component offsets in disjoint blocks name distinct scalar cells. -/
theorem Disj.ne_offsets {b o n b' o' n' : ℕ}
    (h : Disj (Store.inBlock b o n) (Store.inBlock b' o' n'))
    {i j : ℕ} (hi : i < n) (hj : j < n') : (b, o + i) ≠ (b', o' + j) := by
  intro he
  rcases h.ne_cells (b := b) (i := o + i) (b' := b') (j := o' + j)
    ⟨rfl, by omega, by omega⟩ ⟨rfl, by omega, by omega⟩ with hb | ho
  · exact hb (congrArg Prod.fst he)
  · exact ho (congrArg Prod.snd he)

end NLAlib.Ops.Fp
