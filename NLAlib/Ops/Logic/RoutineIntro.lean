/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.RoutineLink
public import NLAlib.Ops.Logic.Tactic
public meta import Lean.Elab.Tactic.Basic

/-!
# Proving and using the judgment of a routine

Tactics for `NLAlib.Ops.Routine.Meets` and `NLAlib.Ops.Routine.Implements`.

* `routine_intro [n, k] (b, x, r, p) reads (bs, xs)` opens a goal `R.Meets I S`: it names the
  dimensions, the operands and the blocks read, and puts in the context the hypotheses of the
  judgment in the form the rules of the logic use.
* `call h [n] (x, z) as ν hfr hpos (zs) hpost` uses the judgment `h` of a routine at a frame of
  its tree: it proves the side conditions from the context and names the memory after the call,
  its frame, its tape position, the blocks written and the postcondition.
* `routine_exit` closes the proof at the final memory, leaving the postcondition at the blocks
  found in the context.
* `implements [n] (x) → (z) with hadm` proves that a routine implements an operation contract,
  separation included when the admission states it buffer by buffer.
* `shaped_intro h [n] (x) → (z) with hadm` names the dimensions and operands of an operation
  contract at which a call can succeed.
* `routine_sep` proves that named operands are separated as a routine requires, from the
  inequalities of buffers in the context.
* `routine_nf` rewrites the operands, lengths and layout of a routine at named operands to list
  literals.

`split_reads h as (xs, ys)` splits `h : m.readBlocks [x, y] [n, k] = some X` into named blocks;
`read_outputs hys as (xs, ys)` does it for the reported buffers of a certificate.

## Main results

The tactics `routine_intro`, `call`, `routine_exit`, `implements`, `shaped_intro`, `routine_sep`,
`routine_nf`, `name_list`, `split_reads` and `read_outputs`.
-/

@[expose] public section

namespace NLAlib.Ops

attribute [routineNF] Routine.sel Routine.lens Routine.outs Routine.operands Routine.env
  Routine.readArgs Routine.readLens Routine.writeArgs Routine.writeLens Routine.outArgs
  Routine.outLens Routine.roArgs Routine.roLens Routine.arity Routine.Advances
  Routine.impl Routine.nin Routine.nout Routine.regions Routine.SeparatedBlocks
  Port.read Port.write Port.update Port.isolated Port.continuing Port.unreported
  Port.place Port.placeFrom Port.regions Port.regionsFrom
  Access.readable Access.writable Access.readOnly Access.isIsolated Access.join
  List.zip_cons_cons List.zip_nil_left List.zip_nil_right List.filter_cons List.filter_nil
  List.map_cons List.map_nil List.filterMap_cons List.filterMap_nil List.getElem?_cons_zero
  List.getElem?_cons_succ List.getD_cons_zero List.getD_cons_succ List.headD_cons
  List.length_cons List.length_nil Bool.and_true Bool.true_and Bool.and_false Bool.false_and
  Bool.or_true Bool.true_or Bool.or_false Bool.false_or Bool.not_true Bool.not_false
  Bool.false_eq_true Nat.add_zero Nat.zero_add

/-- A block of one cell that is read is the cell. After a call that reports a cell `zs`,
`obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hzs` names it. -/
theorem Store.readBlock_one_eq_some {K : Type} {s : Store K} {b off : ℕ} {xs : List K} :
    s.readBlock b off 1 = some xs ↔ ∃ v, s.get b off = some v ∧ xs = [v] := by
  rw [BlockFn.readBlock_one]
  cases s.get b off <;> simp [eq_comm]

/-- **`split_reads h as (xs, ys)`**: split `h : m.readBlocks [x, y] [n, k] = some X` into the
named blocks with their facts `hxs`, `hys`, and substitute `X`. -/
syntax "split_reads " ident &" as " "(" ident,* ")" : tactic

open Lean in
macro_rules
  | `(tactic| split_reads $h:ident as ($xs,*)) => do
    let xs := xs.getElems
    let mut tacs : Array (TSyntax `tactic) := #[]
    tacs := tacs.push (← `(tactic| have $(mkIdent `hr_0) := $h))
    let mut i := 0
    for x in xs do
      let hx := mkIdent (x.getId.appendBefore "h")
      let hri := mkIdent (Name.mkSimple s!"hr_{i}")
      let hrj := mkIdent (Name.mkSimple s!"hr_{i+1}")
      let Xj := mkIdent (Name.mkSimple s!"X_{i+1}")
      tacs := tacs.push (← `(tactic|
        obtain ⟨$x:ident, $Xj:ident, $hx:ident, $hrj:ident, $(mkIdent `rfl):ident⟩ :=
          Mem.readBlocks_cons_eq_some.mp $hri:ident))
      i := i + 1
    let hrn := mkIdent (Name.mkSimple s!"hr_{i}")
    tacs := tacs.push (← `(tactic| obtain $(mkIdent `rfl):ident := Option.some.inj $hrn:ident))
    for j in [0:i+1] do
      let hrj := mkIdent (Name.mkSimple s!"hr_{j}")
      tacs := tacs.push (← `(tactic| try clear $hrj:ident))
    let mut r := tacs[0]!
    for t in tacs.extract 1 tacs.size do
      r ← `(tactic| ($r:tactic; $t:tactic))
    return r

/-- **`routine_nf`** (`at h₁ h₂ ⊢`): rewrite the operands, the lengths, the layout and the
draws of the routines of the goal, at named dimensions and operands, to list literals and
numbers. The definitions of the routines that occur are unfolded. Fails if nothing changes. -/
syntax (name := routineNf) "routine_nf" (Lean.Parser.Tactic.location)? : tactic

open Lean Meta Elab Tactic in
/-- The constants of an expression that are routines, with the routines their definitions
mention (a routine named by an abbreviation, or built from another). -/
private meta def routineConsts (e : Expr) (acc : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let isRoutine (c : Name) : Option Expr := do
    let info ← env.find? c
    let v ← info.value?
    if info.type.getForallBody.getAppFn.isConstOf ``Routine then some v else none
  let mut out := acc
  let mut todo := e.getUsedConstants.toList
  let mut fuel := 256
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if out.contains c then continue
      if let some v := isRoutine c then
        out := out.push c
        todo := v.getUsedConstants.toList ++ todo
  return out

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| routine_nf $[$loc]?) => withMainContext do
    let mut cs : Array Name := #[]
    for d in ← getLCtx do
      cs ← routineConsts (← instantiateMVars d.type) cs
    cs ← routineConsts (← instantiateMVars (← getMainTarget)) cs
    let ids : Array Term := cs.map fun c => mkCIdent c
    evalTactic (← `(tactic| simp only [$[$ids:term],*, routineNF, ↓reduceIte] $[$loc]?))

open Lean Elab Tactic in
/-- Remove the name of the main goal, so that the goals a later `refine` names are found by
their own names. -/
elab (name := unnameGoal) "unname_goal" : tactic => do (← getMainGoal).setTag .anonymous

/-- **`routine_sep`**: a goal `R.SeparatedAt d [x, y, z]` at named operands of a routine.

* Separated by buffer: reduces the goal to the inequalities of buffers that the interface
  requires (on regions, for a routine with an operand that continues another) and proves each
  from the context, in either direction.
* Separated by block: reduces the goal to the disjointness of the blocks that the interface
  requires, at the named operands and lengths, and proves each from a hypothesis
  `Fp.Disj (Store.inBlock …) (Store.inBlock …)` of the context, in either direction, or by
  `disjoint`. -/
macro (name := routineSep) "routine_sep" : tactic => `(tactic|
  first
  | (refine Routine.separatedAt_of_apartAll ?_
     repeat' constructor
     all_goals first
       | assumption
       | exact Ne.symm (by assumption)
       | fail "routine_sep: an inequality of buffers is not in the context")
  | (refine Routine.separatedAt_of_regions ?_
     try routine_nf
     repeat' constructor
     all_goals first
       | assumption
       | exact Ne.symm (by assumption)
       | fail "routine_sep: an inequality of buffers is not in the context")
  | (refine Routine.separatedAt_of_blocks rfl ?_
     try routine_nf
     try simp only [routineNF, List.cons_append, List.nil_append, ↓reduceIte,
       Routine.SeparatedBlocks, Fp.Apart, Fp.blocks_cons, Fp.blocks_nil,
       Fp.disj_sup_left, Fp.disj_sup_right, Fp.disj_bot_left, Fp.disj_bot_right, and_true,
       true_and]
     repeat' constructor
     all_goals first
       | assumption
       | exact Fp.Disj.symm (by assumption)
       | disjoint
       | fail "routine_sep: a disjointness of blocks is not in the context"))

/-- **`split_ands h`**: split the conjunctions and existential statements of `h` into separate
hypotheses, recursively. Only `∧` and `∃` are taken apart; operands and numbers are not. -/
syntax "split_ands " ident : tactic

macro_rules
  | `(tactic| split_ands $h) => `(tactic|
      first
        | (obtain ⟨h₁, h₂⟩ : _ ∧ _ := $h:ident
           split_ands h₁
           split_ands h₂)
        | (obtain ⟨_, h₂⟩ : ∃ _, _ := $h:ident
           split_ands h₂)
        | skip)

/-- **`name_list l h as [x, y]`**: with `h : l.length = 2` (up to computation), replace the list
`l` by `[x, y]`. -/
syntax "name_list " ident ident &" as " "[" ident,* "]" : tactic

open Lean in
macro_rules
  | `(tactic| name_list $v:ident $h:ident as [$xs,*]) => do
    let xs := xs.getElems
    if xs.isEmpty then
      `(tactic| obtain $(mkIdent `rfl):ident : $v = [] := by
          match $v:ident, $h:ident with
          | [], _ => rfl)
    else
      let rflPat ← `(Lean.Parser.Tactic.rcasesPatLo| $(mkIdent `rfl):ident)
      let pats : Array (TSyntax `Lean.Parser.Tactic.rcasesPatLo) :=
        (← xs.mapM fun x => `(Lean.Parser.Tactic.rcasesPatLo| $x:ident)).push rflPat
      let rflTerm : Term := mkCIdent ``rfl
      let elems : Array Term := (xs.map fun x => (⟨x.raw⟩ : Term)).push rflTerm
      let ty ← xs.foldrM (init := ← `($v = [$xs,*])) fun x body => `(∃ $x:ident, $body)
      `(tactic| obtain ⟨$pats,*⟩ : $ty := by
          match $v:ident, $h:ident with
          | [$xs,*], _ => exact ⟨$elems,*⟩)

/-- **`routine_intro [n, k] (b, x, r, p) reads (bs, xs)`**: open a goal `R.Meets I S`. Names
the dimensions `n`, `k`, the supplied operands `b`, `x`, `r`, `p` and the blocks read `bs`,
`xs` (with `hbs`, `hxs`), and leaves in the context:

* `τ`, `m`: the tape and the memory of the call (`memory μ` names the memory `μ` instead,
  for a routine with a dimension called `m`);
* `hlive : m.Live [b, x, r, p]` and `hl`, the same fact as a conjunction, one operand each;
* `hsep`: the separation of the operands. For a routine separated by buffer, each pair that
  the interface requires in different buffers gives the fact named by the two operands
  (`hxr : x.1 ≠ r.1`); the operands are the regions, so an operand that continues another has
  no name of its own. For a routine separated by block, `hblocks` is the disjointness of the
  blocks at the named operands and lengths;
* `hpre`: the precondition at the named dimensions and blocks;
* `hrooms : m.Room [x, r, p] [n, n, n]`, room for the written blocks, and `hroom`, the same
  fact as a conjunction.

The goal is the `Writes` statement of the tree at the named operands. Without `reads`, the
blocks read stay in `hr`. -/
syntax "routine_intro " "[" ident,* "]" " (" ident,* ")" (&" reads " "(" ident,* ")")?
    (&" memory " ident)? : tactic

open Lean in
macro_rules
  | `(tactic| routine_intro [$ds,*] ($opnds,*) $[reads ($xs,*)]? $[memory $mem]?) => do
    let mem : Ident := mem.getD (mkIdent `m)
    let ds := ds.getElems
    let opnds := opnds.getElems
    let d := mkIdent `routine_dims
    let args := mkIdent `routine_args
    let hnd := mkIdent `routine_hnd
    let hlen := mkIdent `routine_hlen
    let hsep := mkIdent `hsep
    let hr := mkIdent `hr
    let mut tacs : Array (TSyntax `tactic) := #[]
    tacs := tacs.push (← `(tactic| intro $d:ident $args:ident $(mkIdent `τ):ident
      $mem:ident $(mkIdent `X):ident $hnd:ident $hlen:ident $(mkIdent `hl):ident
      $hsep:ident $hr:ident $(mkIdent `hpre):ident $(mkIdent `hroom):ident))
    tacs := tacs.push (← `(tactic| name_list $d:ident $hnd:ident as [$ds,*]))
    tacs := tacs.push (← `(tactic| name_list $args:ident $hlen:ident as [$opnds,*]))
    tacs := tacs.push (← `(tactic| try clear $hnd $hlen))
    tacs := tacs.push (← `(tactic| try routine_nf at $hr:ident $(mkIdent `hroom):ident ⊢))
    tacs := tacs.push (← `(tactic| have $(mkIdent `hlive):ident := $(mkIdent `hl):ident))
    tacs := tacs.push (← `(tactic| have $(mkIdent `hrooms):ident := $(mkIdent `hroom):ident))
    tacs := tacs.push (← `(tactic|
      try simp only [Mem.live_cons, Mem.live_nil, and_true] at $(mkIdent `hl):ident))
    tacs := tacs.push (← `(tactic|
      try simp only [Mem.room_cons, Mem.room_nil, and_true] at $(mkIdent `hroom):ident))
    -- the pairs of operands that the interface requires in different buffers
    let hbuf := mkIdent `hsep_buffers
    let mut pairs : Array (TSyntax `tactic) := #[]
    for i in [:opnds.size] do
      for j in [i+1:opnds.size] do
        let x := opnds[i]!
        let y := opnds[j]!
        let h := mkIdent (Name.mkSimple s!"h{x.getId}{y.getId}")
        let ni := Syntax.mkNumLit (toString i)
        let nj := Syntax.mkNumLit (toString j)
        pairs := pairs.push (← `(tactic|
          try have $h:ident : ($x).1 ≠ ($y).1 := Routine.Separated.ne $hbuf (i := $ni) (j := $nj)
                (by omega) rfl rfl rfl))
    let pairSeq ← pairs.foldlM (init := ← `(tactic| skip)) fun acc t => `(tactic| ($acc; $t))
    tacs := tacs.push (← `(tactic| try (
      have $hbuf:ident := Routine.SeparatedAt.regions $hsep
      $pairSeq:tactic
      clear $hbuf)))
    -- a routine separated by block: the disjointness of the blocks, at the named operands
    tacs := tacs.push (← `(tactic| try (
      have $(mkIdent `hblocks):ident := Routine.SeparatedAt.regionBlocks $hsep
      routine_nf at $(mkIdent `hblocks):ident)))
    if let some xs := xs then
      tacs := tacs.push (← `(tactic| split_reads $hr:ident as ($xs,*)))
    tacs := tacs.push (← `(tactic| strip_notes))
    let mut r := tacs[0]!
    for t in tacs.extract 1 tacs.size do
      r ← `(tactic| ($r:tactic; $t:tactic))
    return r

/-- **`call h [n] (x, z) as ν hfr hpos (zs) hpost`**: use the judgment `h : R.Meets I S` of a
routine at a frame of its tree. The goal is a `Writes` or a `Wp` of `.frame ds ops R.body`, or
of that followed by more. `[n]` are the dimensions of the call and `(x, z)` its operands, one
per region of the interface.

The tactic proves the side conditions of the judgment: liveness and room by `room`, separation
by `routine_sep`, the blocks read by `reads`, the footprint by `fp_sub`, the precondition by
`trivial` or `assumption`. A condition it does not prove is left as a goal named `hlive`, `hsep`,
`hr`, `hpre`, `hroom` or `hle`; `(pre := t)` and `(sep := t)` supply a proof of the
precondition or of the separation.

It then introduces the memory `ν` after the call, the frame `hfr` of the call, the claim `hpos`
on the tape position, the blocks reported `zs` with their facts (`hzs`), and the postcondition
`hpost` at the named blocks. -/
syntax &"call " term:max " [" term,* "]" " (" term,* ")" (" (" &"pre" " := " term ")")?
  (" (" &"sep" " := " term ")")? &" as " ident ident ident " (" ident,* ")" ident : tactic

macro_rules
  | `(tactic| call $h [$ds,*] ($opnds,*) $[(pre := $pre)]? $[(sep := $sep)]? as $m $hfr $hpos
      ($zs,*) $hpost) => do
    let preTac ← match pre with
      | some t => `(tactic| exact $t)
      | none => `(tactic| first | trivial | assumption | skip)
    let sepTac ← match sep with
      | some t => `(tactic| exact $t)
      | none => `(tactic| first | routine_sep | skip)
    `(tactic|
      (unname_goal
       strip_notes
       -- the shape of the goal picks the rule; the judgment is then elaborated once
       (first
         | apply Writes.seq_le ?hcall ?hle fun $m $hfr hpost_call => ?hQ
         | apply Writes.then_ ?hcall fun $m $hfr hpost_call => ?hQ
         | apply Writes.mono ?hcall ?hle fun $m $hfr hpost_call => ?hQ
         | apply Writes.wp ?hcall fun $m $hfr hpost_call => ?hQ
         | fail "call: the goal is not a statement about a tree")
       (case' hcall =>
         first
           | refine Routine.Meets.call $h (d := [$ds,*]) (args := [$opnds,*])
               (xs := ?_) rfl rfl rfl rfl ?hlive ?hsep ?hr ?hpre ?hroom
           | fail "call: the goal is not a frame of the tree of this routine at these operands")
       all_goals try frame_facts
       try (case' hlive => first | room | wp_side | skip)
       try (case' hsep => ($sepTac:tactic))
       try (case' hr => first | reads | ((try routine_nf); reads) | skip)
       try (case' hroom => first | ((try routine_nf); room) | ((try routine_nf); wp_side) | skip)
       try (case' hle => first | ((try routine_nf); fp_sub) | fp_sub | skip)
       try (case' hpre => ($preTac:tactic))
       case' hQ =>
         obtain ⟨$hpos, ys_call, hys_call, $hpost⟩ := hpost_call
         try routine_nf at $hpos:ident
         try routine_nf at hys_call
         try routine_nf at $hfr:ident
         split_reads hys_call as ($zs,*)
       unname_goal))

/-- **`read_outputs hys as (xs, rs)`**: in the output obligation of a certificate
(`hgood` of `NLAlib.Ops.Routine.algorithm`), with
`hys : m'.readBlocks (R.outArgs (slots b)) (R.outLens (List.ofFn d)) = some ys`, name the
reported blocks, one per reported operand of the routine at the supplied buffers, with their
facts `hxs`, `hrs`, and substitute `ys`, so that the postcondition is at the named blocks. -/
syntax "read_outputs " ident &" as " "(" ident,* ")" : tactic

macro_rules
  | `(tactic| read_outputs $h:ident as ($xs,*)) => `(tactic|
      ((try simp only [slots, List.range, List.range.loop, List.map_cons, List.map_nil,
          List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at $h:ident)
       (try routine_nf at $h:ident)
       split_reads $h:ident as ($xs,*)))

/-- **`routine_exit`**: the last goal of a proof of `R.Meets I S`, at the final memory: the
claim on the tape position and the reported blocks with their postcondition. Proves the position
from the positions in the context (by `omega`), finds the reported blocks in the context (by
`reads`), and leaves the postcondition at those blocks. A part it does not prove is left as a
goal named `hpos` or `hreads`. -/
macro (name := routineExit) "routine_exit" : tactic => `(tactic|
  (unname_goal
   refine ⟨?hpos, ?_, ?hreads, ?hpost⟩
   case' hreads => first | reads | skip
   case' hpos => first | assumption | omega | (dsimp only; omega) | trivial | skip
   case' hpost => unname_goal))

/-- **`shaped_intro h [n] (x, y) → (z) with hadm`**: with `h : B.Shaped adm d ins outs`, the
operands of an operation contract at which a call can succeed, name the dimensions, the inputs
and the outputs, and keep the admission `hadm : adm [n] [x, y] [z]`. -/
syntax "shaped_intro " ident " [" ident,* "]" " (" ident,* ")" " → " "(" ident,* ")" " with "
  ident : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| shaped_intro $h:ident [$ds,*] ($ins,*) → ($outs,*) with $hadm) => withMainContext do
    let hdecl ← getLocalDeclFromUserName h.getId
    let t ← whnfR (← instantiateMVars hdecl.type)
    let args := t.getAppArgs
    unless t.isAppOf ``BlockRel.Shaped && args.size ≥ 3 do
      throwError "shaped_intro: not the shape of the operands of a contract"
    let names := #[`d_shaped, `ins_shaped, `outs_shaped]
    let mut g ← getMainGoal
    for i in [0:3] do
      let v := args[args.size - 3 + i]!
      unless v.isFVar do
        throwError "shaped_intro: the dimensions and the operands must be variables"
      g ← g.rename v.fvarId! names[i]!
    replaceMainGoal [g]
    let d := mkIdent names[0]!
    let i := mkIdent names[1]!
    let o := mkIdent names[2]!
    let hd := mkIdent `hd_shaped
    let hin := mkIdent `hin_shaped
    let hout := mkIdent `hout_shaped
    evalTactic (← `(tactic|
      (obtain ⟨$hd, $hadm, $hin, $hout⟩ := $h
       name_list $d:ident $hd:ident as [$ds,*]
       name_list $i:ident $hin:ident as [$ins,*]
       name_list $o:ident $hout:ident as [$outs,*])))

/-- **`implements [n] (x, y) → (z) with hadm`**: a goal `R.Implements B adm port`. Names the
dimensions, the input operands and the output operands of the contract, proves by computation
that the numbers, the layout, the operands read and written and their lengths are those of the
routine, and proves the separation `R.SeparatedAt [n] (port [x, y] [z])` by `routine_sep` from
the inequalities of buffers that the admission `hadm : adm [n] [x, y] [z]` gives. An admission
that names an output as an input (an operation updating an operand in place) is substituted
first, so the in-place output may be named again: `implements [n] (α, x, y) → (y) with hadm`. A
fact that does not hold by computation, or a separation that the admission does not give
literally, is left as a goal. -/
syntax &"implements " "[" ident,* "]" " (" ident,* ")" " → " "(" ident,* ")" " with " ident :
  tactic

open Lean in
macro_rules
  | `(tactic| implements [$ds,*] ($ins,*) → ($outs,*) with $hadm) => do
    let hs := mkIdent `hshaped
    `(tactic|
      (unname_goal
       refine Routine.Implements.of_shaped rfl
         (fun d => by first | rfl | (rcases d with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl))
         fun _ _ _ $hs:ident => ?_
       shaped_intro $hs:ident [$ds,*] ($ins,*) → ($outs,*) with $hadm
       have hsplit := $hadm:ident
       try simp only [admNF, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
         false_or, forall_eq_or_imp, forall_eq, imp_false, List.dropLast_cons_cons,
         List.dropLast_singleton, List.dropLast_nil, List.getLast?_cons_cons,
         List.getLast?_singleton, Option.toList_some, List.cons.injEq, and_true] at hsplit
       split_ands hsplit
       try subst_vars
       refine ⟨⟨rfl, rfl⟩, rfl, ?hmem, ?hsep, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
       case' hmem => first
         | exact fun _ hz => hz
         | (intro z hz; simpa using hz)
         | (intro z hz
            simp only [List.take, List.drop, List.mem_append, List.mem_cons, List.mem_singleton,
              List.not_mem_nil, or_false] at hz ⊢
            tauto)
         | skip
       case' hsep => first | routine_sep | unname_goal))

end NLAlib.Ops
