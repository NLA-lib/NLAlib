/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Layout

/-!
# Reading the next word through a vector-prefix frame

Pointwise scalar lowerings can update a vector in place or write a disjoint view.
The next original input word remains readable through the completed output prefix
and disjoint reusable workspace. This fact applies to every such pointwise loop.

## Main results

* `NLAlib.Ops.Store.EqOff.get_prefix` preserves the next word under admitted aliasing.
-/

@[expose] public section

namespace NLAlib.Ops

/-- The next input word survives earlier pointwise writes and disjoint workspace updates.
An exact input/output alias is allowed; a shifted overlapping alias is excluded. -/
theorem Store.EqOff.get_prefix {K : Type} {s s' : Store K} {x y : ℕ × ℕ}
    {n i : ℕ} {scratch : Fp}
    (hfr : s.EqOff (Store.inBlock y.1 y.2 i ⊔ scratch) s')
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hs : Fp.Disj scratch (Store.inBlock x.1 x.2 n)) (hi : i < n) :
    s'.get x.1 (x.2 + i) = s.get x.1 (x.2 + i) := by
  apply hfr.get_eq
  rintro (hw | hw)
  · rcases hxy with hd | rfl
    · exact hd _ _ ⟨rfl, by omega, by omega⟩
        ⟨hw.1, hw.2.1, by have := hw.2.2; omega⟩
    · rcases hw with ⟨_, hlo, hhi⟩
      omega
  · exact hs _ _ hw ⟨rfl, by omega, by omega⟩

end NLAlib.Ops
