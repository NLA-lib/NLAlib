/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Cert
public import NLAlib.Ops.StoreSimp

/-!
# The call step

`wp_call h` is one step of a program proof at a call: `h` says that the operation called meets
its contract (`h : I.Meets md o (R.spec adm)`, or `h : I.IsFn .total o f adm` for a functional
operation). The tactic

* applies the sequence rule if the call is followed by something;
* applies the call rule for the shape of the outputs (`NLAlib.Ops.wp_call_rel` and its
  corollaries for one cell, one block, two blocks): one rule for relational and functional
  contracts and for contracts with a window;
* evaluates the dimensions and the operands in the environment;
* finds the blocks and cells that the call reads from the facts in the context;
* discharges the side goals (the operands are admitted, their handles are buffers of the store,
  the inputs are in the domain, there is room for the outputs) with `store_simp` and
  `store_side`;
* introduces the outputs and their relation to the inputs, in reduced form.

What is left is the continuation, with the mathematical content of the contract as a hypothesis.

`wp_call h [facts] with v hv` passes `facts` to the side goals (typically `hH.eq_iff` for an
injective family of handles `H`) and names what the continuation receives: a cell and its
relation for an output of one cell; a block, its length and its relation for an output of one
block; two blocks, their lengths and the relation for two blocks. Without `with`, a call under a
functional contract with one output cell introduces nothing: the value is computed, and the
memory after the call is `m.upd z (g a b)`.

A side goal that the tactic cannot discharge is left, after the continuation, under its name
(`hadm`: admitted operands; `hlive`: live handles; `hr`: the blocks read; `hdom`: the domain;
`hz`: room for the output), to be closed by `case hadm => …`.

## Main results

* `wp_call`: the call step.
* `wp_adm`, `wp_side`, `wp_read`, `wp_shape`, `wp_dom`: the kinds of side goals, usable on
  their own.
-/

@[expose] public section

namespace NLAlib.Ops

/-- The memory after a call that writes one cell and reads no window, as `wp_call` leaves it. -/
@[storeNF] theorem Mem.advance_zero_updBlocks_cell {K : Type} (m : Mem K) (z : ℕ × ℕ) (v : K) :
    (m.updBlocks [z] [[v]]).advance 0 = m.upd z v := rfl

/-- A side goal of the call rule that is a fact about the store or about the operands: the
operands are admitted, live, in the domain, there is room. -/
syntax "wp_side" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wp_side) => `(tactic| wp_side [])
  | `(tactic| wp_side [$ts,*]) => `(tactic| first
      | trivial
      | assumption
      | omega
      | (store_simp [and_true, $ts,*]; done)
      | (simp (disch := store_side [and_true, $ts,*]) [admNF, *, $ts,*]; done)
      | (simp (disch := store_side [and_true, $ts,*]) [admNF, *, $ts,*] <;> omega)
          | fail "wp_side: this side goal of the call rule is not discharged")

/-- The side goal of the call rule that the operands are admitted: the predicate of the catalog
is unfolded (`admNF`) and what is left (a length is covered, handles are different) is closed
from the hypotheses, the given facts and linear arithmetic. -/
syntax "wp_adm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wp_adm) => `(tactic| wp_adm [])
  | `(tactic| wp_adm [$ts,*]) => `(tactic| first
      | trivial
      | assumption
      | (simp [admNF, *, $ts,*]; done)
      | (simp [admNF, *, $ts,*] <;> first | omega | store_side [and_true, $ts,*])
      | fail "wp_adm: the operands of the call are not shown to be admitted")

/-- A side goal of the call rule of the form `read = some ?x`: the blocks or cells that the call
reads, found from the facts in the context. -/
syntax "wp_read" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wp_read) => `(tactic| wp_read [])
  | `(tactic| wp_read [$ts,*]) => `(tactic| first
      | assumption
      | exact rfl
      | (store_simp [and_true, BlockFn.readBlock_one, $ts,*]; exact rfl)
      | fail "wp_read: the blocks that the call reads are not found in the context")

/-- A side goal of the call rule of the form `shape = ?x`: the length of the window or of the
output blocks of a contract at the dimensions of the call, computed. -/
macro "wp_shape" : tactic => `(tactic| first
  | (simp only [storeNF, List.headD_cons]; exact rfl)
  | exact rfl)

/-- The side goal of the call rule that the inputs are in the domain of the contract: nothing
for a relational contract; for a functional contract, the function is defined on the inputs,
by computation. -/
syntax "wp_dom" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| wp_dom) => `(tactic| wp_dom [])
  | `(tactic| wp_dom [$ts,*]) => `(tactic| first
      | trivial
      | exact ⟨_, rfl, rfl⟩
      | assumption
      | (simp [storeNF, *, $ts,*]; done)
      | fail "wp_dom: the inputs of the call are not shown to be in the domain of the contract")

/-- Introduce and reduce what the continuation of a call receives. With no name, for a call
under a functional contract with one output cell: the value is computed and substituted. -/
syntax "wp_intro" (ppSpace colGt ident)* : tactic

macro_rules
  | `(tactic| wp_intro) => `(tactic|
      first
        | (intro v hv
           cases Option.some.inj hv
           clear hv
           try simp only [storeNF, Mem.advance_zero, Mem.updBlock_singleton])
        | (try simp only [Mem.advance_zero]))
  | `(tactic| wp_intro $ids*) => `(tactic|
      (intro $ids*
       try simp only [storeNF, List.headD_cons, Mem.advance_zero, Mem.pos_advance,
         Mem.pos_updBlock, Mem.pos_upd] at $ids* ⊢))

/-- **The call step.** See the module docstring. -/
syntax "wp_call " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (" with" (ppSpace colGt ident)+)? : tactic

macro_rules
  | `(tactic| wp_call $h) => `(tactic| (wp_call $h []; wp_intro))
  | `(tactic| wp_call $h with $ids*) => `(tactic| (wp_call $h []; wp_intro $ids*))
  | `(tactic| wp_call $h [$ts,*] with $ids*) => `(tactic| (wp_call $h [$ts,*]; wp_intro $ids*))
  | `(tactic| wp_call $h [$ts,*]) => `(tactic|
      ((first | refine wp_seq ?_ | skip)
       first
        | refine wp_call_rel_cell $h rfl rfl rfl rfl (k := ?_) (xs := ?_) ?hk rfl ?hadm ?hlive
            ?hr ?hdom ?hz ?hQ
        | refine wp_call_rel1 $h rfl rfl rfl rfl (k := ?_) (l := ?_) (xs := ?_) ?hk ?hls ?hadm
            ?hlive ?hr ?hdom ?hz ?hQ
        | refine wp_call_rel2 $h rfl rfl rfl rfl (k := ?_) (l₁ := ?_) (l₂ := ?_) (xs := ?_) ?hk
            ?hls ?hadm ?hlive ?hr ?hdom ?hz₁ ?hz₂ ?hQ
        | refine wp_call_rel $h rfl rfl rfl rfl (k := ?_) (ls := ?_) (xs := ?_) ?hk ?hls ?hadm
            ?hlive ?hr ?hdom ?hz ?hQ
        | fail "wp_call: the call rule does not apply to this goal with this contract"
       try (case' hk => first | wp_shape | skip)
       try (case' hls => first | wp_shape | skip)
       try (case' hr => first | wp_read [$ts,*] | skip)
       try (case' hadm => first | wp_adm [$ts,*] | skip)
       try (case' hlive => first | wp_side [$ts,*] | skip)
       try (case' hdom => first | wp_dom [$ts,*] | skip)
       try (case' hz => first | wp_side [$ts,*] | skip)
       try (case' hz₁ => first | wp_side [$ts,*] | skip)
       try (case' hz₂ => first | wp_side [$ts,*] | skip)
       case' hQ => skip))

end NLAlib.Ops
