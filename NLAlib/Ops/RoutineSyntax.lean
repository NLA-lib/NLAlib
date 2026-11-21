/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Routine
public import NLAlib.Ops.Logic.Builder

/-!
# Writing a routine and its specification

`routine% [n, k] (b : n, x : n) → (x, r : n, p : n) { … }` is a **term** whose value is a plain
`NLAlib.Ops.Routine`: the header is the interface, and the body is a program of the builder
(`NLAlib/Ops/Logic/Builder.lean`) in which the dimensions and the operands are named. Nothing of
the notation survives in the value, unless the term is written under `noted%`, which records the
names in the tree as notes (`NLAlib.Ops.Stmt.note`).

## The header

`[n, k]` are the dimensions. Each operand is declared once, with its length, an index expression
of the builder in the dimensions (`b : n`, `A : n * n`); a length that is not an index expression
is a Lean term in which the dimensions are natural numbers, written `↑(…)`
(`data : ↑(dataLength n n)`).

* An operand named only on the left of `→` is read (`NLAlib.Ops.Port.read`).
* An operand named only on the right is written (`NLAlib.Ops.Port.write`).
* An operand named on both sides is updated in place (`NLAlib.Ops.Port.update`). It is declared
  on the left and named again, without its length, on the right.

The operands of the interface are those of the left and then the new ones of the right. The
buffer variables of the tree are the left operands and then the right operands, the convention
of the contract of an operation and of `ops%`; so an operand updated in place is two buffer
variables, and the layout of the routine (`NLAlib.Ops.Routine.binds`) is generated.

An operand may be named again on the left, without its length: the tree then has one more buffer
variable on the same operand, as when a tree written for distinct operands is used with two of
them equal (`(a : 1, x : n, x) → (x)` runs `axpy` with `x` as both vectors and the output).

The block of an operand need not be contiguous. `x : n every inc` is `n` cells, one every `inc`
cells from the position of the operand (a vector with an increment, a row of a matrix stored by
columns); `A : m × n every lda` is `n` runs of `m` cells, one run every `lda` cells (a submatrix
of a matrix with leading dimension `lda`). The block is the cells in order, run after run
(`NLAlib.Ops.Port.stride`). The tree addresses the cells by index arithmetic on the operand
(`x[inc * i]`); the blocks of an operation contract are contiguous.

An operand may be marked: `isolated A : n * n` (read, and apart from every other operand),
`unreported w : n` (written, with final contents that the judgment does not report). An operand
whose block continues another's (`NLAlib.Ops.Port.continuing`) is not written in a header: it
comes directly after the operand it continues in the interface, which is not the order of a
header, so such a routine gives its operands as a list
(`NLAlib.Ops.extendRoutine`).

## Clauses

Between the header and the body:

* `draws e` (an index expression or `↑(…)`): the tape positions the routine consumes;
  `draws unspecified`: their number depends on the data. Without the clause the routine draws
  nothing.
* `by blocks`: operands are separated by block (`NLAlib.Ops.Separation.blocks`). Without the
  clause they are separated by buffer.
* `one variable`: the tree has one buffer variable for each operand, in the order of the
  interface, so an operand updated in place is one variable and no layout is generated. The
  operands of a block are then numbered that way. A routine without a layout is its own program:
  `NLAlib.Ops.Routine.close` adds no frame, so a top-level routine that updates an operand in
  place is written with this clause when the frame is not to be part of the certified tree.

## The body

A block `{ … }` of the builder, or `:= t` for a tree `t : Stmt Op Tst` defined elsewhere with the
variables in the order above.

## Specifications

`spec% [n, k] (bs, xs) → (xs', rs, ps) requires P ensures Q` is a `NLAlib.Ops.Routine.Spec`: the
dimensions, the blocks read and the blocks reported are named (any patterns), `P` is the
precondition and `Q` the postcondition. At dimensions or blocks of another shape the
postcondition is `False`, and so is a stated precondition; with `requires P` omitted the
precondition is `True` at every shape. `tape ω` before the blocks names the draws, the tape seen
from the position of the call.

## Main results

* `routine%`: a routine with a named interface, elaborated to a plain `Routine`.
* `spec%`: a specification on named dimensions and blocks, elaborated to a plain `Routine.Spec`.
-/

@[expose] public section

namespace NLAlib.Ops

/-- A length of the interface of a routine. -/
declare_syntax_cat routineLen
/-- An index expression in the dimensions. -/
syntax opsIdx : routineLen
/-- A Lean term in which the dimensions are natural numbers. -/
syntax "↑" term:max : routineLen

/-- An operand of the interface of a routine. -/
declare_syntax_cat routinePort (behavior := both)
/-- An operand, with its marks and, where it is declared, its length: `x : n` (`n` cells),
`x : n every p` (`n` cells, one every `p`), `A : m × n every p` (`n` runs of `m` cells, one run
every `p` cells). -/
syntax (&"isolated " <|> &"unreported ")* ident
  (" : " routineLen (" × " routineLen)? (&" every " routineLen)?)? : routinePort

/-- A clause of the interface of a routine. -/
declare_syntax_cat routineClause (behavior := both)
/-- The tape positions the routine consumes. -/
syntax &"draws " routineLen : routineClause
/-- The number of tape positions the routine consumes depends on the data. -/
syntax &"draws " &"unspecified" : routineClause
/-- Operands are separated by block. -/
syntax "by " &"blocks" : routineClause
/-- The tree has one buffer variable for each operand, in the order of the interface: an
operand updated in place is one variable, and the routine has no layout. Its program
(`NLAlib.Ops.Routine.close`) is then the tree itself, with no frame around it. -/
syntax &"one " &"variable" : routineClause

/-- **A routine with a named interface**, elaborated to a plain `Routine`. See the module
docstring. -/
syntax (name := routineProg) "routine% " "[" ident,* "]" " (" routinePort,* ")" " → "
  "(" routinePort,* ")" (ppSpace routineClause)* ppSpace (opsBlock <|> (":= " term)) : term

/-- **A specification on named dimensions and blocks**, elaborated to a plain `Routine.Spec`.
See the module docstring. -/
syntax (name := routineSpec) "spec% " "[" term,* "]" (&" tape " ident)? " (" term,* ")" " → "
  "(" term,* ")" (" requires " term)? " ensures " term : term

namespace Builder

open Lean

/-- A length as a natural number in the entries of the list `d` of the dimensions. -/
meta def natE (ds : Array Ident) (d : Ident) : Nat → TSyntax `opsIdx → MacroM (TSyntax `term)
  | 0, stx => Macro.throwErrorAt stx "routine%: length nested too deeply"
  | f + 1, stx => match stx with
    | `(opsIdx| $x:ident) => match ds.findIdx? (·.getId == x.getId) with
      | some i => `(List.getD $d $(lit i) 0)
      | none => Macro.throwErrorAt x s!"routine%: `{x.getId}` is not a dimension"
    | `(opsIdx| $n:num) => `(($n : ℕ))
    | `(opsIdx| $a + $b) => do `($(← natE ds d f a) + $(← natE ds d f b))
    | `(opsIdx| $a - $b) => do `($(← natE ds d f a) - $(← natE ds d f b))
    | `(opsIdx| $a * $b) => do `($(← natE ds d f a) * $(← natE ds d f b))
    | `(opsIdx| $a / $b) => do `($(← natE ds d f a) / $(← natE ds d f b))
    | `(opsIdx| ($a)) => natE ds d f a
    | _ => Macro.throwErrorAt stx "routine%: not an index expression"

/-- Remove the source positions of a syntax tree, so that a binder it introduces is not
reported as unused. -/
meta def stripInfo (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun s => s.setInfo .none

/-- A length of the interface as a function of the list of the dimensions. -/
meta def lenE (ds : Array Ident) (stx : TSyntax `routineLen) : MacroM (TSyntax `term) := do
  let d := mkIdent `d
  match stx with
  | `(routineLen| $e:opsIdx) => do `(fun $d:ident => $(← natE ds d depth e))
  | `(routineLen| ↑$t) =>
    let args ← (List.range ds.size).toArray.mapM fun i => `(List.getD $d $(lit i) 0)
    -- the binders carry no source position, so a dimension the term does not use is not
    -- reported as an unused variable
    let bs : Array Ident := ds.map fun x => ⟨stripInfo x⟩
    if ds.isEmpty then `(fun _ => $t) else `(fun $d:ident => (fun $bs* => $t) $args*)
  | _ => Macro.throwErrorAt stx "routine%: not a length"

/-- An operand of a header: its name, its marks and its length where declared. -/
structure PortDecl where
  /-- The name. -/
  name : Ident
  /-- Marked `isolated`. -/
  isolated : Bool
  /-- Marked `unreported`. -/
  unreported : Bool
  /-- The declared length. -/
  len : Option (TSyntax `routineLen)
  /-- The number of runs, after `×`. -/
  runs : Option (TSyntax `routineLen)
  /-- The period, after `every`. -/
  period : Option (TSyntax `routineLen)

/-- Read an operand of a header. -/
meta def portDecl (stx : TSyntax `routinePort) : MacroM PortDecl := do
  let marks := stx.raw[0].getArgs.map fun m => ((m.reprint.getD "").trimAscii).toString
  let name : Ident := ⟨stx.raw[1]⟩
  let decl := stx.raw[2]
  let len : Option (TSyntax `routineLen) :=
    if decl.getNumArgs == 0 then none else some ⟨decl[1]⟩
  let runs : Option (TSyntax `routineLen) :=
    if decl.getNumArgs == 0 || decl[2].getNumArgs == 0 then none else some ⟨decl[2][1]⟩
  let period : Option (TSyntax `routineLen) :=
    if decl.getNumArgs == 0 || decl[3].getNumArgs == 0 then none else some ⟨decl[3][1]⟩
  return { name, isolated := marks.contains "isolated",
           unreported := marks.contains "unreported", len, runs, period }

/-- The length of a run of an operand, and its runs when it is not contiguous: `x : n` is one
run of `n` cells; `x : n every p` is `n` runs of one cell every `p`; `A : m × n every p` is `n`
runs of `m` cells every `p`. -/
meta def shapeE (ds : Array Ident) (p : PortDecl) (len : TSyntax `routineLen) :
    MacroM (TSyntax `term × Option (TSyntax `term × TSyntax `term)) := do
  match p.period, p.runs with
  | none, none => return (← lenE ds len, none)
  | none, some r => Macro.throwErrorAt r "routine%: `×` needs a period: `m × n every p`"
  | some per, none => return (← `(fun _ => 1), some (← lenE ds len, ← lenE ds per))
  | some per, some r => return (← lenE ds len, some (← lenE ds r, ← lenE ds per))

/-- Give an operand its runs, when it has some. -/
meta def everyE (base : TSyntax `term) :
    Option (TSyntax `term × TSyntax `term) → MacroM (TSyntax `term)
  | none => pure base
  | some (c, per) => `(Port.every $base $c $per)

open Lean in
/-- Translate a routine from its header, its clauses and its tree, given as a function of the
names of the buffer variables: the left and the right operands, or, with `one variable`, the
operands of the interface. -/
meta def routineE (ds : Array Ident) (ins outs : Array (TSyntax `routinePort))
    (cs : Array (TSyntax `routineClause))
    (tree : Array Ident → Array Ident → MacroM (TSyntax `term)) : MacroM (TSyntax `term) := do
    let ins ← ins.mapM portDecl
    let outs ← outs.mapM portDecl
    -- the operands of the interface: the left ones, then the new right ones
    let mut ports : Array (TSyntax `term) := #[]
    let mut names : Array Name := #[]
    let mut operands : Array Ident := #[]
    for p in ins do
      if names.contains p.name.getId then
        -- named again: one more buffer variable of the tree on the same operand
        if p.len.isSome || p.isolated || p.unreported then
          Macro.throwErrorAt p.name
            s!"routine%: `{p.name.getId}` is declared on the left; name it again without a length"
        continue
      let some len := p.len
        | Macro.throwErrorAt p.name s!"routine%: `{p.name.getId}` needs a length"
      let updated := outs.any (·.name.getId == p.name.getId)
      if updated && p.isolated then
        Macro.throwErrorAt p.name s!"routine%: `{p.name.getId}` is isolated and written"
      let (l, st) ← shapeE ds p len
      let base ← if updated then `(Port.update $l) else if p.isolated then `(Port.isolated $l)
        else `(Port.read $l)
      let base ← everyE base st
      let unrep := p.unreported || outs.any fun q => q.name.getId == p.name.getId && q.unreported
      let base ← if unrep then `(Port.unreported $base) else pure base
      ports := ports.push base
      names := names.push p.name.getId
      operands := operands.push p.name
    let nIn := names.size
    let mut outNames : Array Name := #[]
    for q in outs do
      if outNames.contains q.name.getId then
        Macro.throwErrorAt q.name s!"routine%: `{q.name.getId}` is named twice on the right"
      outNames := outNames.push q.name.getId
      if (names.extract 0 nIn).contains q.name.getId then
        if q.len.isSome then
          Macro.throwErrorAt q.name
            s!"routine%: `{q.name.getId}` is declared on the left; name it without a length"
      else
        let some len := q.len
          | Macro.throwErrorAt q.name s!"routine%: `{q.name.getId}` needs a length"
        if q.isolated then
          Macro.throwErrorAt q.name s!"routine%: `{q.name.getId}` is isolated and written"
        let (l, st) ← shapeE ds q len
        let base ← `(Port.write $l)
        let base ← everyE base st
        let base ← if q.unreported then `(Port.unreported $base) else pure base
        ports := ports.push base
        names := names.push q.name.getId
        operands := operands.push q.name
    -- the layout: the buffer variables are the left operands, then the right operands
    let vars := ins.map (·.name.getId) ++ outNames
    let layout := vars.map fun v => lit ((names.idxOf? v).getD 0)
    let oneVar := cs.any fun c => match c with
      | `(routineClause| one variable) => true
      | _ => false
    let binds ← if oneVar || vars == names then `(none) else `(some [$layout,*])
    -- the clauses
    let mut draws ← `(fun _ => some 0)
    let mut sep ← `(Separation.buffers)
    for c in cs do
      match c with
      | `(routineClause| draws unspecified) => draws ← `(fun _ => none)
      | `(routineClause| draws $e:routineLen) =>
        let l ← lenE ds e
        draws ← `(fun d => some ($l d))
      | `(routineClause| by blocks) => sep ← `(Separation.blocks)
      | `(routineClause| one variable) => pure ()
      | _ => Macro.throwErrorAt c "routine%: not a clause"
    -- with `one variable` the buffer variables of a block are the operands, one each
    let tree ← if oneVar then tree operands #[] else tree (ins.map (·.name)) (outs.map (·.name))
    -- the note of the header: the dimensions and the buffer variables, by name
    let varNames := if oneVar then operands.map (toString ·.getId) else vars.map toString
    let noted ← `(ops_note% (Note.header $(← strL (ds.map (toString ·.getId)))
      $(← strL varNames)) $tree)
    `({ nd := $(lit ds.size), ports := [$ports,*], draws := $draws, body := $noted,
        binds := $binds, sep := $sep })

end Builder

open Lean Builder in
macro_rules
  | `(routine% [$ds,*] ($ins,*) → ($outs,*) $cs:routineClause* $b:opsBlock) =>
    routineE ds.getElems ins.getElems outs.getElems cs fun ins outs => do
      blockE (← header ds.getElems ins outs) depth b
  | `(routine% [$ds,*] ($ins,*) → ($outs,*) $cs:routineClause* := $t:term) =>
    routineE ds.getElems ins.getElems outs.getElems cs fun _ _ => pure t

open Lean Builder in
macro_rules
  | `(spec% [$ds,*] $[tape $ω]? ($xs,*) → ($ys,*) $[requires $P]? ensures $Q) => do
    let ω : Ident := ω.getD (mkIdent `_ω)
    let dp : Array Term := ds.getElems.map fun t => ⟨stripInfo t⟩
    let xp : Array Term := xs.getElems.map fun t => ⟨stripInfo t⟩
    let yp : Array Term := ys.getElems.map fun t => ⟨stripInfo t⟩
    let ω' : Ident := ⟨stripInfo ω⟩
    let pre ← match P with
      | some P => `(fun d $ω':ident X => match d, X with
          | [$dp,*], [$xp,*] => $P
          | _, _ => False)
      | none => `(fun _ _ _ => True)
    `({ pre := $pre
        post := fun d $ω':ident X Y => match d, X, Y with
          | [$dp,*], [$xp,*], [$yp,*] => $Q
          | _, _, _ => False })

end NLAlib.Ops
