/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.Step

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
* `alloc as t₁ … tₖ`: goal `Writes … (.allocAs …)` or `Writes … (Stmt.allocs …)`. Leaves the body
  at a fresh store, with the handles `tᵢ` and their lengths.
* `loop_inv F P with …`: goal `Writes … (.loop …)`, alone or at the start of a sequence.
  Leaves the initial invariant, round and continuation when they need proofs.
* `keep`: after a step. Restates for the new memory every read fact of the context that is off
  the step's footprint.
* `cert_intro [n, k] (Q, w) → (w', R) reads (qs, ws)`: goal `R.Triple I .total (B.spec adm)`.
  Leaves the body as a `Writes`, with named dimensions, operands and inputs.
* `decode`: layer-1 vectors and matrices of stored blocks. Leaves the mathematical goal.
* `count_eval`: `stmtCost s idx = C`. Leaves nothing.

`step` is the call step of `NLAlib.Ops.Tactic` (`wp_call`) on the footprint rules
(`NLAlib.Ops.writes_call` and its shapes): it applies `Writes.then_` (or `Writes.seq`), picks the
rule by the shape of the outputs, discharges the side goals with `store_simp`, `store_side`,
`idx`, `disjoint` and the facts, unifies the inputs read with the reads in the context, and
introduces the fresh memory and the outputs. The running frame `hfr : m₀.store.EqOff F m.store`
of the block is replaced by `hfr.trans' hfr₁`, the lengths `hlen : ∀ b, m₁.store.len b = …` are
restated, and `keep` restates the reads. A side goal it cannot discharge makes it fail, naming
the goal (`step!` leaves it instead, under its name: `hadm`, `hpre`, `hap`).

The allocation, counted-loop, call and certificate tactics use the proved footprint rules.
`decode` is provisional.

## Main results

The tactics `step`, `frame`, `fp_sub`, `checkpoint`, `alloc`, `loop_inv`, `keep`, `cert_intro`,
`decode` (and `fp_mem`, `disjoint`, `idx`, `count_eval` in their files).
-/

@[expose] public section

namespace NLAlib.Ops

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

/-- **`checkpoint m₁`**: generalise the current `Writes` or `Wp` memory into the fresh name
`m₁`, carrying the context's facts about it. Before generalizing, `keep` restates preserved
reads and lengths. Existing frames are carried; a frame must already be proved in the context.
No equality to the original update chain is retained. -/
syntax "checkpoint " ident : tactic

open Lean Meta Elab Tactic in
/-- **`alloc as t₁ … tₖ`**: the allocation rule (`NLAlib.Ops.writes_alloc`,
`NLAlib.Ops.writes_allocs`) with the handles named, their lengths and the facts of the store
below them introduced, and their footprints added. Names the fresh store `s_t₁`, its length
`hlen_t₁`, agreement with the caller `hbelow_t₁`, and each buffer length `htᵢ`; generated
names gain suffixes when needed. The buffer names must be fresh and match a nonempty prefix of
consecutive allocations, preserving each explicit storage format. -/
elab "alloc " &"as" ids:(ppSpace colGt ident)+ : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``Writes do throwError "alloc: expected a Writes goal"
  let args := target.getAppArgs
  let m := args.back!
  let mut body := args[args.size - 5]!
  let mut allocations : Array Expr := #[]
  let mut names : Array Name := #[]
  for id in ids do
    if names.contains id.getId || ((← getLCtx).findFromUserName? id.getId).isSome then
      throwErrorAt id "alloc: buffer name is already in scope"
    names := names.push id.getId
    let stmt ← whnfD body
    let (``Stmt.allocAs, #[_, _, format, len, rest]) := stmt.getAppFnArgs
      | throwErrorAt id "alloc: expected another consecutive allocation"
    allocations := allocations.push (← mkAppM ``Prod.mk #[format, len])
    body := rest
  let allocationType ← mkAppM ``Prod #[mkConst ``StorageFormat, mkConst ``IExp]
  let allocationTerm ← Term.exprToSyntax (← mkListLit allocationType allocations.toList)
  let start ← mkAppM ``List.length #[← mkAppM ``Mem.store #[m]]
  for i in [:ids.size] do
    let id := ids[i]!
    let val ← mkAppM ``Nat.add #[start, mkNatLit i]
    let valTerm ← Term.exprToSyntax val
    evalTactic (← `(tactic| let $id : ℕ := $valTerm))
  withMainContext do
    let store ← mkIdent <$> getUnusedUserName (ids[0]!.getId.appendBefore "s_")
    let hlen ← mkIdent <$> getUnusedUserName (ids[0]!.getId.appendBefore "hlen_")
    let hsizes ← mkIdent <$> getUnusedUserName (ids[0]!.getId.appendBefore "hsizes_")
    let hbelow ← mkIdent <$> getUnusedUserName (ids[0]!.getId.appendBefore "hbelow_")
    evalTactic (← `(tactic| refine writes_allocsAs (allocations := $allocationTerm) (by rfl) ?_))
    evalTactic (← `(tactic| intro $store $hlen $hsizes $hbelow))
    for i in [:ids.size] do
      withMainContext do
        let id := ids[i]!
        let hsize ← mkIdent <$> getUnusedUserName (id.getId.appendBefore "h")
        let idx := quote i
        evalTactic (← `(tactic| have $hsize := $hsizes $idx (by simp)))
        evalTactic (← `(tactic| change ($store:ident).len $id = _ at $hsize:ident))
        evalTactic (← `(tactic| simp only [List.getElem_cons_zero, List.getElem_cons_succ,
          $id:ident, Nat.add_zero]
          at $hsize:ident))
  evalTactic (← `(tactic| frame_facts))

/-- **`loop_inv F P with i hi m' hfr hP`** applies `writes_loop` at footprint family `F` and
invariant `P`, also when the loop begins a sequence. The bound is evaluated or found in the
context; footprint monotonicity and inclusion are proved by `fp_sub`. Leaves `initial` when the
initial invariant needs a proof, `round` for the body, and `exit` when the final invariant needs
to be weakened or more statements follow. The optional five names introduce the round index,
its bound, the fresh memory, its frame and the invariant. Nested loops use repeated
`loop_inv`; fill and early-exit rules are applied directly. -/
syntax "loop_inv " term:max ppSpace term:max (" with" (ppSpace colGt ident)+)? : tactic

open Lean in
macro_rules
  | `(tactic| loop_inv $F $P $[with $ids*]?) => do
    let introduce ← match ids with
      | none => `(tactic| skip)
      | some names =>
        unless names.size == 5 do
          Macro.throwError "loop_inv: expected five names for the round"
        `(tactic| intro $names*)
    `(tactic|
      ((first
        | refine Writes.seq_le
            (writes_loop (N := ?_) (F := $F) (P := $P)
              ?bound ?mono ?initial ?round) ?footprint ?exit
        | refine Writes.mono
            (writes_loop (N := ?_) (F := $F) (P := $P)
              ?bound ?mono ?initial ?round) ?footprint ?exit)
       case' bound =>
         first | rfl | assumption | fail "loop_inv: the loop bound could not be evaluated"
       case' mono => intro i hi; fp_sub
       case' footprint => fp_sub
       try (case' initial => first | assumption | rfl | trivial)
       try (case' exit => intro m' hfr hP; exact hP)
       case' round => $introduce:tactic))

open Lean Meta Elab Tactic in
/-- **`keep`**: after a step from `m` to `m₁` with the frame `hfr₁`, restate for `m₁` every
hypothesis `s.readBlock b o n = some xs`, `s.get b i = some v`, `HoldsVec`, `HoldsMat` about `m`
whose cells are off the footprint (`Store.EqOff.keep`, side condition by `disjoint`); the others
are left as they are. New facts use the old name followed by `_kept`, with a suffix when
needed. Also closes a goal expressing such a kept fact. -/
elab "keep" : tactic => withMainContext do
  let solve : TacticM Unit := withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    if goal.isAppOf ``Store.HoldsVec || goal.isAppOf ``Store.HoldsMat then
      let args := goal.getAppArgs
      let predicate ← withLocalDeclD `s (← inferType args[1]!) fun s =>
        mkLambdaFVars #[s] (mkAppN goal.getAppFn (args.set! 1 s))
      let predicate ← Term.exprToSyntax predicate
      evalTactic (← `(tactic| first
        | exact Store.EqOff.keep (P := $predicate) (by assumption)
            (by first | exact Store.readsOnly_holdsVec _ _ _ _ | exact Store.readsOnly_holdsMat _ _)
            (by disjoint) (by assumption)
        | exact Store.Below.keep (P := $predicate) (by assumption)
            (by first | exact Store.readsOnly_holdsVec _ _ _ _ | exact Store.readsOnly_holdsMat _ _)
            (by intro b i h; simp only [fpNF] at h; obtain ⟨rfl, -⟩ := h; idx) (by assumption)))
    else evalTactic (← `(tactic| kept))
  let target ← instantiateMVars (← getMainTarget)
  let isProgram := target.isAppOf ``Writes || target.isAppOf ``Wp
  if !isProgram && (← observing? do
      let goals ← Tactic.run (← getMainGoal) solve
      unless goals.isEmpty do throwError "keep: the fact was not proved").isSome then
    replaceMainGoal []
    return
  unless isProgram do return
  let store ← mkAppM ``Mem.store #[target.getAppArgs.back!]
  let storeType ← inferType store
  let lctx ← getLCtx
  let mut known ← (lctx.foldl (init := #[]) fun acc d => acc.push d.type).mapM instantiateMVars
  for d in lctx do
    if d.isImplementationDetail then continue
    let result ← withMainContext do
      let ty ← instantiateMVars d.type
      let atom := match ty.eq? with | some (_, lhs, _) => lhs | none => ty
      unless atom.isAppOf ``Store.get || atom.isAppOf ``Store.readBlock ||
          atom.isAppOf ``Store.HoldsVec || atom.isAppOf ``Store.HoldsMat do return none
      unless ← isDefEq (← inferType atom.getAppArgs[1]!) storeType do return none
      let candidate ← match ty.eq? with
        | some (_, lhs, rhs) =>
          if lhs.isAppOf ``Store.get || lhs.isAppOf ``Store.readBlock then
            pure (some (← mkEq (mkAppN lhs.getAppFn (lhs.getAppArgs.set! 1 store)) rhs))
          else pure none
        | none =>
          if ty.isAppOf ``Store.HoldsVec || ty.isAppOf ``Store.HoldsMat then
            pure (some (mkAppN ty.getAppFn (ty.getAppArgs.set! 1 store)))
          else pure none
      let some candidate := candidate | return none
      if known.contains candidate then return none
      let some proof ← observing? do
          let hole ← mkFreshExprMVar candidate
          let goals ← Tactic.run hole.mvarId! solve
          unless goals.isEmpty do throwError "keep: the fact was not proved"
          instantiateMVars hole
        | return none
      let name ← getUnusedUserName (d.userName.appendAfter "_kept")
      return some (name, candidate, proof)
    if let some (name, candidate, proof) := result then
      let (_, goal) ← (← (← getMainGoal).assert name candidate proof).intro1
      replaceMainGoal [goal]
      known := known.push candidate
  evalTactic (← `(tactic| frame_facts))

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| checkpoint $name:ident) => withMainContext do
    if ((← getLCtx).findFromUserName? name.getId).isSome then
      throwErrorAt name "checkpoint: memory name is already in scope"
    let target ← instantiateMVars (← getMainTarget)
    unless target.isAppOf ``Writes || target.isAppOf ``Wp do
      throwError "checkpoint: expected a Writes or Wp goal"
    evalTactic (← `(tactic| keep))
    withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let memory := target.getAppArgs.back!
      let hyps := (← getLCtx).foldl (init := #[]) fun acc d => acc.push d.fvarId
      let (_, _, goal) ← (← getMainGoal).generalizeHyp
        #[{ expr := memory, xName? := some name.getId }] hyps
      replaceMainGoal [goal]

open Lean in
/-- The lemma that splits a list of the given length into named elements. -/
meta def certLenLemma (k : Nat) : MacroM (TSyntax `term) :=
  match k with
  | 0 => `(List.length_eq_zero_iff)
  | 1 => `(List.length_eq_one_iff)
  | 2 => `(List.length_eq_two)
  | 3 => `(List.length_eq_three)
  | 4 => `(List.length_eq_four)
  | _ => Macro.throwError "cert_intro: at most four dimensions, inputs or outputs"

open Lean in
/-- The pattern `⟨x₁, …, xₖ, rfl⟩` (or `rfl` for no element). -/
meta def certPat (xs : Array Lean.Ident) : MacroM (TSyntax ``Lean.Parser.Tactic.rcasesPatMed) := do
  let mut ps : Array (TSyntax ``Lean.Parser.Tactic.rcasesPatLo) := #[]
  for x in xs do
    let p ← `(rcasesPat| $x:ident)
    ps := ps.push (← `(Lean.Parser.Tactic.rcasesPatLo| $p:rcasesPat))
  let r ← `(rcasesPat| $(mkIdent `rfl):ident)
  ps := ps.push (← `(Lean.Parser.Tactic.rcasesPatLo| $r:rcasesPat))
  `(Lean.Parser.Tactic.rcasesPatMed| ⟨$ps,*⟩)

/-- The blocks read are as many as the lengths asked. -/
theorem Mem.length_of_readBlocks {K : Type} {m : Mem K} {as : List (ℕ × ℕ)} {ns : List ℕ}
    {X : List (List K)} (h : m.readBlocks as ns = some X) : as.length = ns.length := by
  induction as generalizing ns X with
  | nil => cases ns with
    | nil => rfl
    | cons n ns => simp [Mem.readBlocks] at h
  | cons a as ih => cases ns with
    | nil => simp [Mem.readBlocks] at h
    | cons n ns =>
      obtain ⟨x, xs, -, h', -⟩ := Mem.readBlocks_cons_eq_some.mp h
      simp [ih h']

/-- **`cert_intro [n, k] (Q, w) → (w', R) reads (qs, ws)`**: a goal
`R.Triple I .total (B.spec adm)`. Applies `NLAlib.Ops.Impl.meets_of_writes`, names the tape `τ`
and the memory `μ`, splits the dimensions and the operands by the header (the same header as the
builder's), the input blocks read into `qs`, `ws`, … with their facts `hqs`, `hws`, …, and
unfolds the admitted operands into `hadm`, the live handles into `hl` and the room for the
outputs into `hz` (conjunctions, which the side-goal tactics use as they are). Leaves `Fits`
proved and the body as a `Writes` goal. -/
syntax "cert_intro " "[" ident,* "]" " (" ident,* ")" " → " "(" ident,* ")"
  (&" reads " "(" ident,* ")")? : tactic

open Lean in
macro_rules
  | `(tactic| cert_intro [$ds,*] ($ins,*) → ($outs,*) reads ($xs,*)) => do
    let ds := ds.getElems; let ins := ins.getElems; let outs := outs.getElems
    let xs := xs.getElems
    unless xs.size == ins.size do Macro.throwError "cert_intro: one name per input block"
    let μ := mkIdent `μ
    let τ := mkIdent `τ
    let hl := mkIdent `hl
    let hz := mkIdent `hz
    let hadm := mkIdent `hadm
    let hdom := mkIdent `hdom
    let mut tacs : Array (TSyntax `tactic) := #[]
    tacs := tacs.push (← `(tactic|
      refine Impl.meets_of_writes
        fun d ins outs $τ $μ X hnd $hadm $hl $(mkIdent `hr_0) $hdom $hz => ?_))
    let pd ← certPat ds
    let pi ← certPat ins
    let po ← certPat outs
    tacs := tacs.push (← `(tactic| obtain $pd := $(← certLenLemma ds.size).mp hnd))
    tacs := tacs.push (← `(tactic|
      obtain $pi := $(← certLenLemma ins.size).mp
        ((Mem.length_of_readBlocks $(mkIdent `hr_0)).trans rfl)))
    tacs := tacs.push (← `(tactic|
      obtain $po := $(← certLenLemma outs.size).mp ((Mem.Room.length_eq $hz).trans rfl)))
    tacs := tacs.push (← `(tactic|
      try simp only [storeNF, List.headD_cons, List.getD_cons_zero, List.getD_cons_succ]
        at $(mkIdent `hr_0):ident $hz:ident))
    tacs := tacs.push (← `(tactic|
      try simp only [admNF, AnyOperands, List.headD_cons, List.getD_cons_zero, List.getD_cons_succ,
        List.mem_cons,
        List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq, List.cons.injEq, and_true,
        and_assoc, exists_and_left, exists_eq_left', exists_eq_left, exists_eq_right,
        exists_eq_right_right, ne_eq] at $hadm:ident))
    tacs := tacs.push (← `(tactic|
      try simp only [Mem.room_cons, Mem.room_nil, and_true] at $hz:ident))
    tacs := tacs.push (← `(tactic|
      try simp only [List.cons_append, List.nil_append, Mem.live_cons, Mem.live_nil, and_true]
        at $hl:ident))
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
    tacs := tacs.push (← `(tactic| refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩))
    let mut r := tacs[0]!
    for t in tacs.extract 1 tacs.size do
      r ← `(tactic| ($r:tactic; $t:tactic))
    return r
  | `(tactic| cert_intro [$_ds,*] ($_ins,*) → ($_outs,*)) => Macro.throwError
      "cert_intro: name the input blocks with `reads (…)`"

/-- **`decode`**: rewrite the stored blocks in a goal to the vectors and matrices of layer 1
(`decodeNF`: `vec` of a slice, `decVec`, `decMat`), with the index side conditions by `idx`.
Phase B; provisional implementation. -/
macro "decode" : tactic => `(tactic| first
  | (simp (disch := idx) only [decodeNF]; done)
  | (simp (disch := idx) only [decodeNF])
  | fail "decode: nothing to decode")

end NLAlib.Ops
