/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Level1

/-!
# One column of a saved-pivot Schur update

The residual update saves its pivot row and column before overwriting the matrix. For each
column, it forms the product of the saved coefficient and row entry, then calls the actual
scalar multiply-add loop. This routine describes the words computed on any scalar machine;
the factorization and rounding arguments consume its judgment.

## Main results

* `NLAlib.LU.schurColumn_meets`: the scalar column update meets its word specification.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Update one residual column by the saved column multiplied by the coefficient and the
saved row entry. The coefficient product and every multiply-add are scalar calls. -/
def schurColumn : Routine Op Tst := routine% [n] (a : 1, x : n, y : 1, z : n) → (z) {
  let t ← alloc 1;
  call (Has.inj ScalarOp.mul) [] (a, y) → (t);
  run (axpyLoopRoutine (Op := Op) (Tst := Tst)) [n] (t, x, z)
}

variable [Inhabited K]

/-- On any machine, the written column contains its original entries plus the products of
the saved column with the computed coefficient product. No accuracy law is assumed. -/
def schurColumnSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] ([a], xs, [b], zs) → (ws) ensures
    ws = axpyF M (M.mul a b) (vec xs) (vec zs) n

/-- The saved-pivot column update returns the actual machine multiply-add words. Its only
net writes are the updated column, and the tape position and input blocks are preserved. -/
theorem schurColumn_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (schurColumn (Op := Op) (Tst := Tst)).Meets I (schurColumnSpec M) := by
  routine_intro [n] (a, x, y, z) reads (as, xs, ys, zs)
  obtain ⟨av, ha, rfl⟩ := Store.readBlock_one_eq_some.mp has
  obtain ⟨bv, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hys
  obtain ⟨hla, hlx, hly, hlz⟩ := hl
  change Writes .total I τ _ (Env.frame [n] [a, x, y, z, z]) (Fp.blocks [z] [n]) _ m
  alloc as t
  have htz : t ≠ z.1 := by
    change m.store.length ≠ z.1
    exact Nat.ne_of_gt hlz
  step (hI .mul) as m₁ hfr₁ ⟨hpos₁, v, hv, rfl⟩
  call (axpyLoopRoutine_meets_exact hI) [n] ((t, 0), x, z)
    as m₂ hfr₂ hpos₂ (ws) hpost
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change m.store.length < m₁.store.length ∧ x.1 < m₁.store.length ∧ z.1 < m₁.store.length
    simp only [List.length_singleton] at hlen_t
    exact ⟨by omega, by omega, by omega⟩
  intro s₂ hs₂ hB₂
  refine ⟨?_, [ws], Mem.readBlocks_of_cons ?_ rfl, hpost⟩
  · change m₂.pos = m.pos + 0
    omega
  · exact Store.Below.readBlock_of hB₂ hlz hws

end NLAlib.LU
