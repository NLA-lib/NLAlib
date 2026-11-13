/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Logic.Function.Basic
public import NLAlib.Ops.Attr
public import NLAlib.Ops.Frame

/-!
# Automation for reads after writes

## Main results

* `store_side [facts]` proves the side conditions of the store lemmas: two handles are different,
  a handle is a buffer of the store, an offset is in or out of a block, a cell is in or out of a
  footprint. It uses the hypotheses, linear arithmetic, and the given facts as rewriting rules.
* `store_simp [facts]` rewrites reads, lengths and positions through updates, using the
  hypotheses and the given facts, with `store_side` for the side conditions.

Handles are given as an injective family `B : ι → ℕ` (`hB : Function.Injective B`), so that the
handles of a hundred buffers are told apart by deciding `i ≠ j` on the indices, with one
hypothesis. Hypotheses `b ≠ b'` in the context work too.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Two handles of an injective family with different indices are different. -/
theorem ne_of_injective {ι : Type} {B : ι → ℕ} (hB : Function.Injective B) {i j : ι}
    (h : i ≠ j) : B i ≠ B j := fun e => h (hB e)

/-- The side conditions of the store lemmas. See the module docstring. -/
syntax "store_side" (" [" Lean.Parser.Tactic.simpLemma,+ "]")? : tactic

macro_rules
  | `(tactic| store_side) => `(tactic| first
      | assumption
      | omega
      | exact ne_of_injective (by assumption) (by decide)
      | solve_by_elim -exfalso (maxDepth := 2)
      | exact Store.lt_length_push (by solve_by_elim -exfalso (maxDepth := 2)) _
      | exact Store.length_lt_length_push _ _
      | exact Nat.ne_of_lt (by solve_by_elim -exfalso (maxDepth := 2))
      | exact Nat.ne_of_gt (by solve_by_elim -exfalso (maxDepth := 2))
      | (simp (disch := solve_by_elim -exfalso (maxDepth := 2)) [*, Mem.store_upd,
          Mem.store_updBlock, Mem.store_advance, Mem.live_cons,
          Mem.live_nil, Store.length_upd, Store.length_updBlock, Store.len_upd,
          Store.len_updBlock, Store.len_push_top, Store.len_push_of_lt, Store.length_push,
          Store.inBlock, Store.inBuf, Pi.sup_apply, sup_Prop_eq, List.length_append,
          List.length_cons, List.length_nil, and_true, true_and, not_or, not_and, not_lt,
          not_le, ne_eq]
         <;> (try intros) <;> first | done | omega | fail "store_side")
      | fail "store_side")
  | `(tactic| store_side [$ts,*]) => `(tactic| first
      | assumption
      | omega
      | exact ne_of_injective (by assumption) (by decide)
      | solve_by_elim -exfalso (maxDepth := 2)
      | exact Store.lt_length_push (by solve_by_elim -exfalso (maxDepth := 2)) _
      | exact Store.length_lt_length_push _ _
      | exact Nat.ne_of_lt (by solve_by_elim -exfalso (maxDepth := 2))
      | exact Nat.ne_of_gt (by solve_by_elim -exfalso (maxDepth := 2))
      | (simp (disch := solve_by_elim -exfalso (maxDepth := 2)) [*, Mem.store_upd,
          Mem.store_updBlock, Mem.store_advance, Mem.live_cons,
          Mem.live_nil, Store.length_upd, Store.length_updBlock, Store.len_upd,
          Store.len_updBlock, Store.len_push_top, Store.len_push_of_lt, Store.length_push,
          Store.inBlock, Store.inBuf, Pi.sup_apply, sup_Prop_eq, List.length_append,
          List.length_cons, List.length_nil, and_true, true_and, not_or, not_and, not_lt,
          not_le, ne_eq, $ts,*]
         <;> (try intros) <;> first | done | omega | fail "store_side")
      | fail "store_side")

/-- Rewrite reads, lengths and positions through updates, then try linear arithmetic. See the
module docstring. -/
syntax "store_simp" (" [" Lean.Parser.Tactic.simpLemma,+ "]")? : tactic

macro_rules
  | `(tactic| store_simp) => `(tactic|
      (try simp (disch := store_side) only [*, storeNF, Mem.store_upd, Mem.pos_upd,
        Mem.store_updBlock, Mem.pos_updBlock,
        Mem.store_advance, Mem.pos_advance, Mem.live_cons, Mem.live_nil, Mem.readBlocks_cons,
        Mem.readBlocks_nil, List.cons_append, List.nil_append, Store.length_upd,
        Store.length_updBlock, Store.length_push, Store.len_upd, Store.len_updBlock,
        Store.shape_upd, Store.shape_updBlock, Store.get_upd_self, Store.get_upd_of_buf_ne,
        Store.get_upd_of_idx_ne, Store.get_updBlock_of_buf_ne, Store.get_updBlock_of_lt,
        Store.get_updBlock_of_ge, Store.get_push_of_lt, Store.readBlock_upd_of_buf_ne,
        Store.readBlock_upd_of_lt, Store.readBlock_upd_of_ge, Store.readBlock_updBlock_of_buf_ne,
        Store.readBlock_updBlock_of_le, Store.readBlock_updBlock_of_ge,
        Store.readBlock_updBlock_same, Store.readBlock_push_of_lt, Store.len_push_of_lt,
        Store.len_push_top, Store.pop_push, Store.pop_upd_of_lt, Store.pop_upd_top,
        Store.pop_updBlock_of_lt, Store.pop_updBlock_top, Store.readBlock_pop_of_lt,
        Store.get_pop_of_lt, Store.len_pop_of_lt, Option.bind_some, Option.map_some,
        Option.isSome_some, and_self, and_true, true_and, implies_true]) <;> try omega)
  | `(tactic| store_simp [$ts,*]) => `(tactic|
      (try simp (disch := store_side [$ts,*]) only [*, storeNF, Mem.store_upd, Mem.pos_upd,
        Mem.store_updBlock, Mem.pos_updBlock,
        Mem.store_advance, Mem.pos_advance, Mem.live_cons, Mem.live_nil, Mem.readBlocks_cons,
        Mem.readBlocks_nil, List.cons_append, List.nil_append, Store.length_upd,
        Store.length_updBlock, Store.length_push, Store.len_upd, Store.len_updBlock,
        Store.shape_upd, Store.shape_updBlock, Store.get_upd_self, Store.get_upd_of_buf_ne,
        Store.get_upd_of_idx_ne, Store.get_updBlock_of_buf_ne, Store.get_updBlock_of_lt,
        Store.get_updBlock_of_ge, Store.get_push_of_lt, Store.readBlock_upd_of_buf_ne,
        Store.readBlock_upd_of_lt, Store.readBlock_upd_of_ge, Store.readBlock_updBlock_of_buf_ne,
        Store.readBlock_updBlock_of_le, Store.readBlock_updBlock_of_ge,
        Store.readBlock_updBlock_same, Store.readBlock_push_of_lt, Store.len_push_of_lt,
        Store.len_push_top, Store.pop_push, Store.pop_upd_of_lt, Store.pop_upd_top,
        Store.pop_updBlock_of_lt, Store.pop_updBlock_top, Store.readBlock_pop_of_lt,
        Store.get_pop_of_lt, Store.len_pop_of_lt, Option.bind_some, Option.map_some,
        Option.isSome_some, and_self, and_true, true_and, implies_true, $ts,*]) <;> try omega)

end NLAlib.Ops
