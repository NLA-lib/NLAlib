/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Footprint

/-!
# Projections of successful tuples of stored reads

A known input tuple supplies its indexed block and singleton-cell reads. The projection rules
are independent of program execution, so call tactics can reuse them without importing any
sequential-program reasoning.

## Main results

* `NLAlib.Ops.Mem.readBlocks_getD`: project a valid input block.
* `NLAlib.Ops.Mem.get_of_readBlocks_getD`: project an input singleton cell.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type}

/-- Project any valid block from a tuple of successful block reads. -/
theorem Mem.readBlocks_getD {m : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    {xs : List (List K)} (h : m.readBlocks zs ls = some xs) {i : ℕ}
    (hi : i < min zs.length ls.length) :
    m.store.readBlock (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 (ls.getD i 0) =
      some (xs.getD i []) := by
  induction zs generalizing ls xs i with
  | nil => simp at hi
  | cons z zs ih =>
    cases ls with
    | nil => simp at hi
    | cons l ls =>
      obtain ⟨x, xs', hx, hxs, rfl⟩ := Mem.readBlocks_cons_eq_some.mp h
      cases i with
      | zero => simpa only [List.getD_cons_zero] using hx
      | succ i =>
        simpa only [List.getD_cons_succ] using ih hxs (by simpa using hi)

/-- Project a scalar cell represented by a singleton block in a collected read tuple. -/
theorem Mem.get_of_readBlocks_getD {m : Mem K} {zs : List (ℕ × ℕ)} {ls : List ℕ}
    {xs : List (List K)} (h : m.readBlocks zs ls = some xs) {i : ℕ} {v : K}
    (hi : i < min zs.length ls.length) (hlen : ls.getD i 0 = 1)
    (hval : xs.getD i [] = [v]) :
    m.store.get (zs.getD i (0, 0)).1 (zs.getD i (0, 0)).2 = some v := by
  have hr := Mem.readBlocks_getD h hi
  rw [hlen, hval] at hr
  simpa using Store.get_of_readBlock hr (j := 0) Nat.zero_lt_one v

end NLAlib.Ops
