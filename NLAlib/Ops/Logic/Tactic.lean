/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Scalar

/-!
# The tactics of a program proof

Each tactic has one goal shape and either closes its goal, or leaves exactly the goals its
docstring names (under those names), or **fails with a message naming the goal it could not
prove**. None of them can prove something false: they build ordinary proof terms, checked by the
kernel. None of them silently leaves a side goal for the end of the proof.

* `step h [facts] as m₁ with x hx`: goal `Wp … (.seq (.call …) c) … m`, `Wp … (.call …) … m`,
  or `Writes …` of them. Leaves the continuation from the fresh memory `m₁`, with the outputs `x`
  and the contract's relation `hx`; the running frame, the lengths and the kept reads updated.
* `frame [facts]`: goal `s.EqOff F s'`, `s'` a chain of updates over `s` or over a store with a
  frame in the context. Leaves nothing.
* `fp_mem [facts]`, `fp_sub [facts]`: goals `F b i`, `¬ F b i`, `F ≤ G`. Leave nothing.
* `disjoint [facts]`: goals `Fp.Disj F G`, `Fp.Apart zs ls`, handles different. Leaves nothing.
* `idx [facts]`: offset arithmetic. Leaves nothing.
* `checkpoint m₁`: goal `Wp … m` with `m` a chain of updates. Leaves the goal at the fresh
  `m₁`, with its frame and reads.
* `alloc as t₁ … tₖ`: goal `Writes … (.alloc …)` or `Writes … (Stmt.allocs …)`. Leaves the body
  at a fresh store, with the handles `tᵢ` and their lengths.
* `loop_inv F P with …`: goal `Writes … (.loop …)` (also two loops, a fill, `whileFuel`). Leaves
  the start and the round, from a fresh memory.
* `keep`: after a step. Restates for the new memory every read fact of the context that is off
  the step's footprint.
* `cert_intro [n, k] (Q, w) → (w', R) reads (qs, ws)`: goal `R.Meets I .total (B.spec adm)`.
  Leaves the body as a `Writes`, with named dimensions, operands and inputs.
* `decode`: layer-1 vectors and matrices of stored blocks. Leaves the mathematical goal.
* `count_eval`: `staticCost s idx = C`. Leaves nothing.

`step` is the call step of `NLAlib.Ops.Tactic` (`wp_call`) on the footprint rules
(`NLAlib.Ops.writes_call` and its shapes): it applies `Writes.then_` (or `Writes.seq`), picks the
rule by the shape of the outputs, discharges the side goals with `store_simp`, `store_side`,
`idx`, `disjoint` and the facts, unifies the inputs read with the reads in the context, and
introduces the fresh memory and the outputs. The running frame `hfr : m₀.store.EqOff F m.store`
of the block is replaced by `hfr.trans' hfr₁`, the lengths `hlen : ∀ b, m₁.store.len b = …` are
restated, and `keep` restates the reads. A side goal it cannot discharge makes it fail, naming
the goal (`step!` leaves it instead, under its name: `hadm`, `hpre`, `hap`).

**Phase A**: the syntax of each tactic with its contract; provisional implementations for
`frame` and `fp_sub` (the others fail with "phase B").

## Main results

The tactics `step`, `frame`, `fp_sub`, `checkpoint`, `alloc`, `loop_inv`, `keep`, `cert_intro`,
`decode` (and `fp_mem`, `disjoint`, `idx`, `count_eval` in their files).
-/

@[expose] public section

namespace NLAlib.Ops

/-- **`fp_sub`**: an inclusion of footprints `F ≤ G`. See `fp_mem`. -/
syntax "fp_sub" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| fp_sub) => `(tactic| fp_sub [])
  | `(tactic| fp_sub [$ts,*]) => `(tactic| first
      | exact le_rfl
      | (intro b i h; simp only [fpNF, $ts,*] at h ⊢; idx)
      | fail "fp_sub: the footprint is not shown to be included")

/-- **`frame`**: a goal `s.EqOff F s'` where `s'` is a chain of updates (`upd`, `updBlock`,
`updBlocks`, `push`/`pop`) over `s` or over a store `s₁` with a frame `hfr : s.EqOff G s₁` in the
context. Peels the updates (`Store.EqOff.upd`, `Store.EqOff.updBlock_of_le`), closes the
base by `Store.EqOff.refl` or by a frame hypothesis and an inclusion, and proves every membership
and inclusion with `fp_mem` (and `idx`). Fails naming the first write that is not in the
footprint. -/
syntax "frame" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| frame) => `(tactic| frame [])
  | `(tactic| frame [$ts,*]) => `(tactic|
      (try simp only [Mem.store_upd, Mem.store_updBlock, Mem.store_advance]
       repeat' (first
         | exact Store.EqOff.refl _ _
         | refine Store.EqOff.updBlock_of_le ?_ ?_
         | refine Store.EqOff.upd ?_ ?_ _
         | exact Store.EqOff.mono (by assumption) (by fp_sub [$ts,*])
         | fp_mem [$ts,*]
         | (simp only [List.length_cons, List.length_nil, List.length_append, Nat.reduceAdd,
             $ts,*]; fp_sub [$ts,*])
         | fp_sub [$ts,*])
       all_goals fail "frame: a write is not shown to be in the footprint"))

/-- **`step h [facts] as m₁ with x hx`**: the call step in named form. See the module docstring.
Phase B. -/
syntax "step " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? (&" as " ident)?
  (" with" (ppSpace colGt ident)+)? : tactic

macro_rules
  | `(tactic| step $_h $[[$_ts,*]]? $[as $_m]? $[with $_ids*]?) =>
    `(tactic| fail "step: phase B")

/-- **`checkpoint m₁`**: generalise the current memory (a chain of updates) into the fresh name
`m₁`, with the running frame (by `frame`), the lengths and the reads of the context restated
(`NLAlib.Ops.Wp.named`). Phase B. -/
syntax "checkpoint " ident : tactic

macro_rules
  | `(tactic| checkpoint $_m) => `(tactic| fail "checkpoint: phase B")

/-- **`alloc as t₁ … tₖ`**: the allocation rule (`NLAlib.Ops.writes_alloc`,
`NLAlib.Ops.writes_allocs`) with the handles named, their lengths and the facts of the store
below them introduced, and their footprints added. Phase B. -/
syntax "alloc " &"as" (ppSpace colGt ident)+ : tactic

macro_rules
  | `(tactic| alloc as $_ids*) => `(tactic| fail "alloc: phase B")

/-- **`loop_inv F P with i m' hfr hP`**: the loop rule of the goal's loop (`writes_loop`,
`writes_loop₂`, `writes_fill`, `writes_fill₂`, `writes_whileFuel`) at the footprint family `F`
and the invariant `P`; proves the monotonicity of `F` by `fp_sub`, leaves the start `P 0 m` and
the round. Phase B. -/
syntax "loop_inv " term:max ppSpace term:max (" with" (ppSpace colGt ident)+)? : tactic

macro_rules
  | `(tactic| loop_inv $_F $_P $[with $_ids*]?) => `(tactic| fail "loop_inv: phase B")

/-- **`keep`**: after a step from `m` to `m₁` with the frame `hfr₁`, restate for `m₁` every
hypothesis `s.readBlock b o n = some xs`, `s.get b i = some v`, `HoldsVec`, `HoldsMat` about `m`
whose cells are off the footprint (`Store.EqOff.keep`, side condition by `disjoint`); the others
are left as they are. Phase B. -/
macro "keep" : tactic => `(tactic| fail "keep: phase B")

/-- **`cert_intro [n, k] (Q, w) → (w', R) reads (qs, ws)`**: a goal
`R.Meets I .total (B.spec adm)`. Applies `NLAlib.Ops.Impl.meets_of_writes`, splits the dimensions
and the operands by the header (the same header as the builder's), unfolds the admitted operands
(`admNF`) and the blocks read, and leaves the body as a `Writes` with the named facts. Phase B. -/
syntax "cert_intro " "[" ident,* "]" " (" ident,* ")" " → " "(" ident,* ")"
  (&" reads " "(" ident,* ")")? : tactic

macro_rules
  | `(tactic| cert_intro [$_ds,*] ($_ins,*) → ($_outs,*) $[reads ($_xs,*)]?) =>
    `(tactic| fail "cert_intro: phase B")

/-- **`decode`**: rewrite the stored blocks in a goal to the vectors and matrices of layer 1
(`decodeNF`: `vec` of a slice, `decVec`, `decMat`), with the index side conditions by `idx`.
Phase B; provisional implementation. -/
macro "decode" : tactic => `(tactic| first
  | (simp (disch := idx) only [decodeNF]; done)
  | (simp (disch := idx) only [decodeNF])
  | fail "decode: nothing to decode")

end NLAlib.Ops
