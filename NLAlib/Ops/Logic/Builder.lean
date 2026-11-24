/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Link
public meta import Lean.Elab.Term

/-!
# The program builder: named variables, elaborated to plain trees

`ops% [n, k] (Q, w) → (w, R) { … }` is a **term** whose value is a plain
`NLAlib.Ops.Stmt Op Tst`: the names are resolved to positions of the environment when the term is
elaborated, by a macro, and nothing of the notation survives in the tree. So the evaluator, the
static count, linking and every rule see exactly the tree that would be written by hand, and a
tree built with the notation is `rfl`-equal to the positional one (the examples are in
`NLAlib.Ops.Examples.Built`). There is no compile function in the kernel and no kernel `rfl` of a
compiled tree.

The names are kept beside the tree. A declaration `foo` whose value is written with `ops%` or
`routine%` gets a second definition `foo._noted`, the noted copy: the same tree with the names of
the source as notes (`NLAlib.Ops.Stmt.note`), namely the names of the header, of each loop
variable, scratch buffer and index binding, and of the routine or tree that each `run` frames.
`noted_of% foo` is that copy, `NLAlib.Ops.Stmt.pretty` reads it as pseudocode, and erasing its
notes (`NLAlib.Ops.Stmt.erase`) gives the tree of `foo`. The value of `foo` has no note, so no
rule, count or certificate sees one. `noted% t` puts the notes in the value itself; the library
does not use it.

## The header

`[n, k]` are the dimensions, `(Q, w)` the input operands, `(w, R)` the output operands, in the
order of `NLAlib.Ops.Env.frame`: the index variables are the dimensions and then the offsets of the
operands, the buffer variables are the operands. A name repeated in the header is one operand
updated in place (it is passed twice by the caller, `[Q, w, w, R]`); it denotes its first
occurrence.

## Statements

```
call op [dims] (ins) → (outs)          -- Stmt.call
run R [dims] (operands)               -- a routine, by its interface (one operand per operand)
run body [dims] (args)                -- a tree, by its buffer variables (Stmt.frame)
let t ← allocAs fmt len                -- explicit StorageFormat, scoped over the rest
let t ← alloc len                      -- one-byte StorageFormat.cell, scoped over the rest
let v ← index q (ins) ≤ bound          -- Stmt.bindIdx, scoped over the rest of the block
for i < n { … }                        -- Stmt.loop
if q [dims] (ins) { … } else { … }     -- Stmt.ite
while i < fuel, q [dims] (ins) { … } then { … }   -- Stmt.whileFuel; `i` is the round index,
                                       -- and in the `then` block the number of rounds done
ifPos e { … }   ifZero e { … }         -- Stmt.ifPos, Stmt.ifZero
skip   abort   { … }
```

`run` takes either a routine or a tree. A routine (`NLAlib.Ops.Routine`) is run by its interface:
one operand per operand of the routine, and the frame is laid out by the routine's layout, so an
operand updated in place is named once. This is the frame `call` expects. A tree (`Stmt`, for
instance a fragment of a routine) is run by its buffer variables, which the caller lists in the
tree's own order. A routine with an operand that continues another has no frame of its own
operands (the continued position is computed from lengths, which are not index expressions) and
is not run by `run`.

Statements are separated by `;`; a sequence is nested to the right. An operand is `X` or `X[e]`:
for an operand of the header, the offset is the offset variable of `X` plus the summands of `e`,
added from the left (`R[j * p + i]` is `.var oR + .var j * .var p + .var i`; a parenthesised
summand stays one: `C[(i * p + j)]` is `.var oC + (.var i * .var p + .var j)`); for a scratch
buffer it is `e` (and `X` alone is offset `0`). Index expressions are names, numerals, `+`, `-`
(truncated), `*`, `/` and parentheses. Operation and query names are Lean terms
(`(Has.inj Blas1Op.dot)`); sizes are never Lean terms, so a tree is one tree for all sizes.

The keywords `call`, `alloc`, `index`, `abort`, `ifPos`, `ifZero` are not reserved: they stay
usable as identifiers elsewhere.

An unknown name, a buffer used as an index or an index used as a buffer is an error at the name;
so is a dimension declared twice or also an operand, and a binder (`for`, `let`, `while`) that
shadows a name of the header. The offset variable of an operand `X` is named `X_off` and may be
used in index expressions.

**The offset convention is frozen** (it is part of the identity of every registered tree): `X[e]`
for an operand is `.var X_off` plus the top-level `+`-summands of `e`, added from the left; a
parenthesised summand, a `-`, `*` or `/` stays one summand; `X` alone is `.var X_off`. For
scratch, `X[e]` is `e` and `X` is `.const 0`. Numerals are `.const n`; `+ - * /` are the `IExp`
instances.

## Main results

* `ops%`: a program with named variables, elaborated to a plain `Stmt`.
-/

@[expose] public section

namespace NLAlib.Ops

/-! ### Running a routine or a tree -/

/-- `ops_run% R ds [ops]`: the frame of `run` (internal to the builder). For a routine `R`, the
frame of its tree at the operands of its interface: the layout of `R` is applied when the term is
elaborated, so the result is the literal `Stmt.frame ds ops' R.body`. For a tree, `Stmt.frame ds
ops t`. -/
syntax (name := opsRun) "ops_run% " term:max term:max " [" term,* "]" : term

open Lean Elab Term Meta in
/-- The literal list of natural numbers of an expression, if it reduces to one. -/
private meta def natListLit? (e : Expr) : MetaM (Option (Array Nat)) := do
  let mut e ← whnfD e
  let mut out : Array Nat := #[]
  for _ in [0:4096] do
    if e.isAppOfArity ``List.nil 1 then return some out
    unless e.isAppOfArity ``List.cons 3 do return none
    let some h ← (evalNat (← whnfD e.appFn!.appArg!)).run | return none
    out := out.push h
    e ← whnfD e.appArg!
  return none

open Lean Elab Term Meta in
/-- Elaborate `ops_run%`. -/
@[term_elab opsRun] meta def elabOpsRun : TermElab := fun stx expected? => do
  match stx with
  | `(ops_run% $body $ds [$ops,*]) =>
    let ops := ops.getElems
    let (o, t) ← do
      match expected? with
      | some e =>
        let e ← whnfR (← instantiateMVars e)
        if e.isAppOfArity `NLAlib.Ops.Stmt 2 then pure (e.appFn!.appArg!, e.appArg!)
        else pure (← mkFreshTypeMVar, ← mkFreshTypeMVar)
      | none => pure (← mkFreshTypeMVar, ← mkFreshTypeMVar)
    let rty := mkApp2 (mkConst `NLAlib.Ops.Routine) o t
    let saved ← saveState
    let routine? ← try
        let r ← withoutErrToSorry (elabTermEnsuringType body rty)
        synthesizeSyntheticMVarsNoPostponing
        pure (some r)
      catch _ => saved.restore; pure none
    match routine? with
    | none => elabTerm (← `(Stmt.frame $ds [$ops,*] $body)) expected?
    | some r =>
      let flat ← whnfD (mkApp3 (mkConst `NLAlib.Ops.Routine.flat) o t r)
      unless flat.isConstOf ``Bool.true do
        throwErrorAt body "run: a routine with an operand that continues another is called by an \
          explicit frame of its tree"
      let binds ← whnfD (mkApp3 (mkConst `NLAlib.Ops.Routine.binds) o t r)
      let ops' ← if binds.isAppOfArity ``Option.none 1 then pure ops
        else if binds.isAppOfArity ``Option.some 2 then
          match ← natListLit? binds.appArg! with
          | some l => l.mapM fun i => do
              let some a := ops[i]? | throwErrorAt body "run: too few operands for the routine"
              pure a
          | none => throwErrorAt body "run: the layout of the routine is not a literal list"
        else throwErrorAt body "run: the layout of the routine does not reduce"
      let bodyFn := mkCIdent `NLAlib.Ops.Routine.body
      elabTerm (← `(Stmt.frame $ds [$ops',*] ($bodyFn $body))) expected?
  | _ => throwUnsupportedSyntax

/-! ### Syntax -/

/-- Index expressions of the builder. -/
declare_syntax_cat opsIdx
/-- Operands of the builder: `X` or `X[e]`. -/
declare_syntax_cat opsArg
/-- Statements of the builder. -/
declare_syntax_cat opsStmt (behavior := both)

/-- An index variable. -/
syntax ident : opsIdx
/-- A numeral. -/
syntax num : opsIdx
/-- A sum. -/
syntax:65 opsIdx:65 " + " opsIdx:66 : opsIdx
/-- A truncated difference. -/
syntax:65 opsIdx:65 " - " opsIdx:66 : opsIdx
/-- A product. -/
syntax:70 opsIdx:70 " * " opsIdx:71 : opsIdx
/-- A quotient, rounded down. -/
syntax:70 opsIdx:70 " / " opsIdx:71 : opsIdx
/-- Parentheses; a parenthesised summand of an offset stays one summand. -/
syntax "(" opsIdx ")" : opsIdx

/-- A buffer at its offset (offset `0` for scratch). -/
syntax ident : opsArg
/-- A buffer at its offset plus an index expression. -/
syntax ident noWs "[" opsIdx "]" : opsArg

/-- A block of statements. -/
syntax opsBlock := "{" sepBy(opsStmt, "; ", "; ", allowTrailingSep) "}"

/-- Do nothing. -/
syntax "skip" : opsStmt
/-- Fail. -/
syntax &"abort" : opsStmt
/-- `call op [dims] (ins) → (outs)`: a call. -/
syntax &"call " term:max " [" opsIdx,* "]" " (" opsArg,* ")" " → " "(" opsArg,* ")" : opsStmt
/-- `run R [dims] (operands)`: run a routine by its interface, or a tree by its buffer
variables, in a frame. -/
syntax &"run " term:max " [" opsIdx,* "]" " (" opsArg,* ")" : opsStmt
/-- `let t ← alloc len`: one-byte-cell scratch for the rest of the block.
Use `allocAs` when the resource model requires an explicit storage format. -/
syntax "let " ident " ← " &"alloc " opsIdx : opsStmt
/-- `let t ← allocAs fmt len`: explicitly formatted scratch for the rest of the block. -/
syntax "let " ident " ← " &"allocAs " term:max opsIdx : opsStmt
/-- `let v ← index q (ins) ≤ bound`: an index read from the store, for the rest of the
block. -/
syntax "let " ident " ← " &"index " term:max " (" opsArg,* ")" " ≤ " opsIdx : opsStmt
/-- `for i < n { … }`: a counted loop. -/
syntax "for " ident " < " opsIdx ppSpace opsBlock : opsStmt
/-- `if q [dims] (ins) { … } else { … }`: a branch on a test. -/
syntax "if " term:max " [" opsIdx,* "]" " (" opsArg,* ")" ppSpace opsBlock " else " opsBlock :
  opsStmt
/-- `while i < fuel, q [dims] (ins) { … } then { … }`: the loop with early exit; `i` is the
round index, and in the `then` block the number of rounds done. -/
syntax "while " ident " < " opsIdx ", " term:max " [" opsIdx,* "]" " (" opsArg,* ")" ppSpace
  opsBlock " then " opsBlock : opsStmt
/-- `ifPos e { … }`: run the block if the size `e` is positive. -/
syntax &"ifPos " opsIdx ppSpace opsBlock : opsStmt
/-- `ifZero e { … }`: run the block if the size `e` is zero. -/
syntax &"ifZero " opsIdx ppSpace opsBlock : opsStmt
/-- A nested block. -/
syntax opsBlock : opsStmt

/-- **A program with named variables**, elaborated to a plain `Stmt`. See the module docstring. -/
syntax (name := opsProg) "ops% " "[" ident,* "]" " (" ident,* ")" " → " "(" ident,* ")" ppSpace
  opsBlock : term

/-! ### The translation -/

namespace Builder

open Lean

/-- The scope of the translation: the names of the index and buffer variables by position, the
offset variable of each buffer of the header, and the number of variables of the header (which
are looked up from the left, so that an operand updated in place denotes its first occurrence;
the binders of the body are looked up from the right, so that an inner binder shadows). -/
structure Scope where
  /-- Names of the index variables, by position. -/
  idx : Array Name
  /-- Names of the buffer variables and their offset variables (`none` for scratch). -/
  buf : Array (Name × Option Nat)
  /-- Number of index variables of the header. -/
  nIdx : Nat
  /-- Number of buffer variables of the header. -/
  nBuf : Nat

/-- Find a name: the binders of the body from the right, then the header from the left. -/
meta def findName {α : Type} (xs : Array α) (n0 : Nat) (key : α → Name) (x : Name) :
    Option Nat :=
  let hit := fun (j : Nat) => (xs[j]?).map key == some x
  match (List.range (xs.size - n0)).reverse.find? fun j => hit (n0 + j) with
  | some j => some (n0 + j)
  | none => (List.range (min n0 xs.size)).find? hit

/-- The position of an index variable. -/
meta def Scope.findIdx (sc : Scope) (x : Name) : Option Nat := findName sc.idx sc.nIdx id x

/-- The position and offset variable of a buffer variable. -/
meta def Scope.findBuf (sc : Scope) (x : Name) : Option (Nat × Option Nat) :=
  (findName sc.buf sc.nBuf Prod.fst x).map fun p => (p, ((sc.buf[p]?).map Prod.snd).join)

/-- Bind a new index variable. -/
meta def Scope.pushIdx (sc : Scope) (x : Name) : Scope := { sc with idx := sc.idx.push x }

/-- Bind a new buffer variable (scratch). -/
meta def Scope.pushBuf (sc : Scope) (x : Name) : Scope := { sc with buf := sc.buf.push (x, none) }

/-- A binder of the body may not shadow a name of the header (a dimension, an operand or the
offset variable `X_off` of an operand). -/
meta def Scope.fresh (sc : Scope) (x : TSyntax `ident) : MacroM Unit := do
  let n := x.getId
  if (sc.idx.extract 0 sc.nIdx).contains n || ((sc.buf.extract 0 sc.nBuf).map Prod.fst).contains n
  then Macro.throwErrorAt x s!"ops%: `{n}` shadows a name of the header"

/-- A natural number literal. -/
meta def lit (n : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩

/-- The bound on the nesting depth of a program and of an index expression. -/
meta def depth : Nat := 10000

/-- Translate an index expression. -/
meta def idxE (sc : Scope) : Nat → TSyntax `opsIdx → MacroM (TSyntax `term)
  | 0, stx => Macro.throwErrorAt stx "ops%: index expression nested too deeply"
  | f + 1, stx => match stx with
    | `(opsIdx| $x:ident) => match sc.findIdx x.getId with
      | some p => `(IExp.var $(lit p))
      | none =>
        if (sc.findBuf x.getId).isSome then
          Macro.throwErrorAt x s!"ops%: `{x.getId}` is a buffer, not an index variable"
        else Macro.throwErrorAt x s!"ops%: unknown index variable `{x.getId}`"
    | `(opsIdx| $n:num) => `(IExp.const $n)
    | `(opsIdx| $a + $b) => do `($(← idxE sc f a) + $(← idxE sc f b))
    | `(opsIdx| $a - $b) => do `($(← idxE sc f a) - $(← idxE sc f b))
    | `(opsIdx| $a * $b) => do `($(← idxE sc f a) * $(← idxE sc f b))
    | `(opsIdx| $a / $b) => do `($(← idxE sc f a) / $(← idxE sc f b))
    | `(opsIdx| ($a)) => idxE sc f a
    | _ => Macro.throwErrorAt stx "ops%: not an index expression"

/-- The summands of an index expression, from the left; a parenthesised summand stays one. -/
meta def summands : Nat → TSyntax `opsIdx → Array (TSyntax `opsIdx)
  | 0, e => #[e]
  | f + 1, e => match e with
    | `(opsIdx| $a + $b) => summands f a ++ summands f b
    | _ => #[e]

/-- Translate an operand. -/
meta def argE (sc : Scope) (stx : TSyntax `opsArg) : MacroM (TSyntax `term) := do
  let (x, e?) ← match stx with
    | `(opsArg| $x:ident) => pure (x, none)
    | `(opsArg| $x:ident[$e]) => pure (x, some e)
    | _ => Macro.throwErrorAt stx "ops%: not an operand"
  let some (b, off?) := sc.findBuf x.getId
    | if (sc.findIdx x.getId).isSome then
        Macro.throwErrorAt x s!"ops%: `{x.getId}` is an index variable, not a buffer"
      else Macro.throwErrorAt x s!"ops%: unknown buffer `{x.getId}`"
  let off ← match off?, e? with
    | some o, none => `(IExp.var $(lit o))
    | some o, some e =>
      (summands depth e).foldlM (init := ← `(IExp.var $(lit o))) fun acc t => do
        `($acc + $(← idxE sc depth t))
    | none, none => `(IExp.const 0)
    | none, some e => idxE sc depth e
  `(Operand.mk $(lit b) $off)

/-- Translate a list of index expressions. -/
meta def idxL (sc : Scope) (es : Array (TSyntax `opsIdx)) : MacroM (TSyntax `term) := do
  let ts ← es.mapM (idxE sc depth)
  `([$ts,*])

/-- Translate a list of operands. -/
meta def argL (sc : Scope) (as : Array (TSyntax `opsArg)) : MacroM (TSyntax `term) := do
  let ts ← as.mapM (argE sc)
  `([$ts,*])

/-- **`noted% t`** elaborates the term `t` with notes in the value: the trees that `ops%` and
`routine%` build inside `t` carry the names of their header, of each bound variable and of the
routine each `run` frames, as `NLAlib.Ops.Stmt.note`. Without `noted%` the value has no note and
the names are in the noted copy (`ops_named%`). The library's trees are written without `noted%`;
`NLAlib.Ops.Examples.Notes` uses it to show that proofs on a noted tree are the same. -/
syntax (name := opsNoted) "noted% " term : term

open Lean Elab Term in
/-- Elaborate `noted%`: the flag `ops.notes` is set while the term is elaborated. -/
@[term_elab opsNoted] meta def elabOpsNoted : TermElab := fun stx expected? => do
  match stx with
  | `(noted% $t) => withOptions (·.setBool `ops.notes true) (elabTerm t expected?)
  | _ => throwUnsupportedSyntax

/-- `ops_note% n s` is `Stmt.note n s` when notes are on (under `noted%`, and in the noted copy
that `ops_named%` elaborates), and `s` otherwise. -/
syntax (name := opsNote) "ops_note% " term:max term:max : term

open Lean Elab Term in
/-- Elaborate `ops_note%`. -/
@[term_elab opsNote] meta def elabOpsNote : TermElab := fun stx expected? => do
  match stx with
  | `(ops_note% $n $s) =>
    if (← getOptions).getBool `ops.notes false then elabTerm (← `(Stmt.note $n $s)) expected?
    else elabTerm s expected?
  | _ => throwUnsupportedSyntax

/-- `ops_note_run% body dims operands s` is `s`, the frame of a `run`, with the note naming the
routine or tree `body` under `noted%`. -/
syntax (name := opsNoteRun) "ops_note_run% " term:max term:max term:max term:max : term

open Lean Elab Term Meta in
/-- Elaborate `ops_note_run%`: the name is that of the constant at the head of `body`. -/
@[term_elab opsNoteRun] meta def elabOpsNoteRun : TermElab := fun stx expected? => do
  match stx with
  | `(ops_note_run% $body $ds $as $s) =>
    unless (← getOptions).getBool `ops.notes false do return ← elabTerm s expected?
    let saved ← saveState
    let name? ← try
        let b ← instantiateMVars (← withoutErrToSorry (elabTerm body none))
        let b := if b.isAppOf `NLAlib.Ops.Routine.body then b.appArg! else b
        saved.restore
        pure b.getAppFn.constName?
      catch _ => saved.restore; pure none
    match name? with
    | some name =>
      let lit : TSyntax `term := ⟨Syntax.mkStrLit (toString name)⟩
      elabTerm (← `(Stmt.note (Note.routine $lit $ds $as) $s)) expected?
    | none => elabTerm s expected?
  | _ => throwUnsupportedSyntax

/-- `ops_named% t` is `t`. When `t` is elaborated without `noted%` inside a declaration `foo`, the
same term is elaborated once more with notes and stored as the definition `foo._noted` (then
`foo._noted1`, … for further trees of the declaration), with the parameters of `foo` that the
tree uses. The value of `foo` has no note; `foo._noted` is the same tree with the names of its
source, for `NLAlib.Ops.Stmt.pretty` and for tools. When the second elaboration fails or leaves
a metavariable nothing is stored, and an information message names the declaration and the
reason: the declaration is unchanged, and `noted_of% foo` is then `foo`, without names. -/
syntax (name := opsNamed) "ops_named% " term:max : term

open Lean Elab Term Meta in
/-- Elaborate `ops_named%`. The state of the elaborator after the term is restored, apart from
the environment, so the noted copy cannot influence the declaration being elaborated. -/
@[term_elab opsNamed] meta def elabOpsNamed : TermElab := fun stx expected? => do
  match stx with
  | `(ops_named% $t) =>
    let e ← elabTerm t expected?
    if (← getOptions).getBool `ops.notes false then return e
    let some decl ← getDeclName? | return e
    let saved ← saveState
    try
      let eN ← withoutErrToSorry <| withEnableInfoTree false <|
        withSynthesize (postpone := .no) <|
          withOptions (·.setBool `ops.notes true) (elabTermEnsuringType t expected?)
      let eN ← instantiateMVars eN
      if eN.hasMVar then throwError "ops_named%: the noted tree has a metavariable"
      let mut name := decl ++ `_noted
      let mut k := 1
      while (← getEnv).contains name do
        name := decl ++ Name.mkSimple s!"_noted{k}"
        k := k + 1
      discard <| mkAuxDefinitionFor name eN
      let env ← getEnv
      saved.restore
      setEnv env
    catch ex =>
      saved.restore
      logInfo (m!"ops%: no named copy `{decl}._noted` is stored, the elaboration with the " ++
        m!"names failed:{indentD ex.toMessageData}")
    return e
  | _ => throwUnsupportedSyntax

/-- `ops_tree% t` is `t`, a tree defined elsewhere. Under notes, when `t` is a constant `foo`
(possibly applied) that has a noted copy `foo._noted`, it is that copy at the same arguments. -/
syntax (name := opsTree) "ops_tree% " term:max : term

open Lean Elab Term Meta in
/-- Elaborate `ops_tree%`. -/
@[term_elab opsTree] meta def elabOpsTree : TermElab := fun stx expected? => do
  match stx with
  | `(ops_tree% $t) =>
    unless (← getOptions).getBool `ops.notes false do return ← elabTerm t expected?
    let head : Syntax := match t.raw with
      | `(($f:ident $_*)) => f
      | `(($f:ident)) => f
      | `($f:ident $_*) => f
      | `($f:ident) => f
      | _ => Syntax.missing
    if head.isIdent then
      let noted := mkIdentFrom head (head.getId ++ `_noted)
      let t' : Syntax := t.raw.replaceM (m := Id) fun s => if s == head then some noted else none
      let saved ← saveState
      try
        return ← withoutErrToSorry (elabTermEnsuringType t' expected?)
      catch _ => saved.restore
    elabTerm t expected?
  | _ => throwUnsupportedSyntax

/-- `noted_of% foo` is the noted copy `foo._noted` of the tree or routine `foo`, when there is
one, and `foo` otherwise. Every declaration of the library written with `ops%` or `routine%`
has a copy, except:

* a declaration written with `noted%`, which carries its notes itself and gets no copy
  (`NLAlib.Ops.Examples.Integrator.myStep`, `NLAlib.Ops.Examples.Integrator.myIntegrate` and
  `NLAlib.Ops.Examples.Routines.sum2`): `noted_of% foo` is `foo`, with its notes;
* a tree in an `example` or outside a declaration: there is no name to store a copy under;
* a declaration whose elaboration with the names fails: `ops_named%` reports it with an
  information message when the declaration is compiled (none in the library). -/
syntax:max (name := opsNotedOf) "noted_of% " ident : term

open Lean Elab Term in
/-- Elaborate `noted_of%`. -/
@[term_elab opsNotedOf] meta def elabOpsNotedOf : TermElab := fun stx expected? => do
  match stx with
  | `(noted_of% $f:ident) =>
    let saved ← saveState
    try
      return ← withoutErrToSorry (elabTerm (mkIdentFrom f (f.getId ++ `_noted)) expected?)
    catch _ => saved.restore
    elabTerm f expected?
  | _ => throwUnsupportedSyntax

/-- A list of names as a term: the strings of a note. -/
meta def strL (xs : Array String) : MacroM (TSyntax `term) := do
  let ts : Array (TSyntax `term) := xs.map fun x => ⟨Syntax.mkStrLit x⟩
  `([$ts,*])

/-- The source text of a piece of syntax, for a note. -/
meta def srcText (stx : Syntax) : String := (stx.reprint.getD "").trimAscii.toString

mutual

/-- Translate a sequence of statements: nested to the right; a `let` scopes over the rest. -/
meta def seqE (sc : Scope) : Nat → List (TSyntax `opsStmt) → MacroM (TSyntax `term)
  | 0, _ => Macro.throwError "ops%: program nested too deeply"
  | _ + 1, [] => `(Stmt.skip)
  | f + 1, s :: rest => do
    match s with
    | `(opsStmt| let $t:ident ← allocAs $fmt $len) =>
      sc.fresh t
      `(ops_note% (Note.var $(⟨Syntax.mkStrLit (toString t.getId)⟩))
        (Stmt.allocAs $fmt $(← idxE sc depth len) $(← seqE (sc.pushBuf t.getId) f rest)))
    | `(opsStmt| let $t:ident ← alloc $len) =>
      sc.fresh t
      `(ops_note% (Note.var $(⟨Syntax.mkStrLit (toString t.getId)⟩))
        (Stmt.alloc $(← idxE sc depth len) $(← seqE (sc.pushBuf t.getId) f rest)))
    | `(opsStmt| let $v:ident ← index $q ($as,*) ≤ $bd) =>
      sc.fresh v
      `(ops_note% (Note.var $(⟨Syntax.mkStrLit (toString v.getId)⟩))
        (Stmt.bindIdx $q $(← argL sc as.getElems) $(← idxE sc depth bd)
          $(← seqE (sc.pushIdx v.getId) f rest)))
    | _ =>
      if rest.isEmpty then stmtE sc f s
      else `(Stmt.seq $(← stmtE sc f s) $(← seqE sc f rest))

/-- Translate a block. -/
meta def blockE (sc : Scope) : Nat → TSyntax ``opsBlock → MacroM (TSyntax `term)
  | 0, b => Macro.throwErrorAt b "ops%: program nested too deeply"
  | f + 1, b => match b with
    | `(opsBlock| { $ss;* }) => seqE sc f ss.getElems.toList
    | _ => Macro.throwErrorAt b "ops%: not a block"

/-- Translate one statement. -/
meta def stmtE (sc : Scope) : Nat → TSyntax `opsStmt → MacroM (TSyntax `term)
  | 0, s => Macro.throwErrorAt s "ops%: program nested too deeply"
  | f + 1, s => do match s with
    | `(opsStmt| skip) => `(Stmt.skip)
    | `(opsStmt| abort) => `(Stmt.abort)
    | `(opsStmt| call $o [$ds,*] ($as,*) → ($zs,*)) =>
      `(Stmt.call $o $(← idxL sc ds.getElems) $(← argL sc as.getElems) $(← argL sc zs.getElems))
    | `(opsStmt| run $body [$ds,*] ($as,*)) => do
      let ops ← as.getElems.mapM (argE sc)
      `(ops_note_run% $body $(← strL (ds.getElems.map (srcText ·.raw)))
        $(← strL (as.getElems.map (srcText ·.raw)))
        (ops_run% $body $(← idxL sc ds.getElems) [$ops,*]))
    | `(opsStmt| for $i:ident < $n $b:opsBlock) =>
      sc.fresh i
      `(ops_note% (Note.var $(⟨Syntax.mkStrLit (toString i.getId)⟩))
        (Stmt.loop $(← idxE sc depth n) $(← blockE (sc.pushIdx i.getId) f b)))
    | `(opsStmt| if $q [$ds,*] ($as,*) $t:opsBlock else $e:opsBlock) =>
      `(Stmt.ite $q $(← idxL sc ds.getElems) $(← argL sc as.getElems) $(← blockE sc f t)
        $(← blockE sc f e))
    | `(opsStmt| while $i:ident < $fu, $q [$ds,*] ($as,*) $b:opsBlock then $k:opsBlock) =>
      sc.fresh i
      let sc' := sc.pushIdx i.getId
      `(ops_note% (Note.var $(⟨Syntax.mkStrLit (toString i.getId)⟩))
        (Stmt.whileFuel $(← idxE sc depth fu) $q $(← idxL sc' ds.getElems)
          $(← argL sc' as.getElems)
          $(← blockE sc' f b) $(← blockE sc' f k)))
    | `(opsStmt| ifPos $e $b:opsBlock) =>
      `(Stmt.ifPos $(← idxE sc depth e) $(← blockE (sc.pushIdx Name.anonymous) f b))
    | `(opsStmt| ifZero $e $b:opsBlock) =>
      `(Stmt.ifZero $(← idxE sc depth e) $(← blockE (sc.pushIdx Name.anonymous) f b))
    | `(opsStmt| $b:opsBlock) => blockE sc f b
    | `(opsStmt| let $_t:ident ← allocAs $_ $_) => seqE sc f [s]
    | `(opsStmt| let $_t:ident ← alloc $_) => seqE sc f [s]
    | `(opsStmt| let $_v:ident ← index $_ ($_,*) ≤ $_) => seqE sc f [s]
    | _ => Macro.throwErrorAt s "ops%: not a statement"

end

/-- The scope of a header: dimensions, then the offsets and the handles of the operands. The
names of the dimensions are distinct and differ from the operands and their offset variables;
an operand name may repeat (an operand updated in place, which denotes its first occurrence). -/
meta def header (ds ins outs : Array Ident) : MacroM Scope := do
  let ops := ins ++ outs
  let offs := ops.map (·.getId.appendAfter "_off")
  for h : k in [0:ds.size] do
    let x := ds[k]
    if (ds.extract 0 k).any (·.getId == x.getId) then
      Macro.throwErrorAt x s!"ops%: the dimension `{x.getId}` is declared twice"
    if ops.any (·.getId == x.getId) || offs.contains x.getId then
      Macro.throwErrorAt x s!"ops%: the dimension `{x.getId}` is also an operand"
  let idx := ds.map (·.getId) ++ offs
  let buf := (ops.zipIdx).map fun (x, j) => (x.getId, some (ds.size + j))
  return { idx, buf, nIdx := idx.size, nBuf := buf.size }

end Builder

open Lean in
macro_rules
  | `(ops% [$ds,*] ($ins,*) → ($outs,*) $b:opsBlock) =>
    do
      let names (xs : Array Ident) := xs.map fun x => toString x.getId
      let tree ← Builder.blockE (← Builder.header ds.getElems ins.getElems outs.getElems)
        Builder.depth b
      `(ops_named% (ops_note% (Note.header $(← Builder.strL (names ds.getElems))
        $(← Builder.strL (names (ins.getElems ++ outs.getElems)))) $tree))

end NLAlib.Ops
