/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Link

/-!
# The program builder: named variables, elaborated to plain trees

`ops% [n, k] (Q, w) → (w, R) { … }` is a **term** whose value is a plain
`NLAlib.Ops.Stmt Op Tst`: the names are resolved to positions of the environment when the term is
elaborated, by a macro, and nothing of the notation survives in the tree. So the evaluator, the
static count, linking and every rule see exactly the tree that would be written by hand, and a
tree built with the notation is `rfl`-equal to the positional one (the examples are in
`NLAlib.Ops.Examples.Built`). There is no compile function in the kernel and no kernel `rfl` of a
compiled tree.

`opsImpl% …` is the same with the numbers of dimensions and operands: an `NLAlib.Ops.Impl`.

## The header

`[n, k]` are the dimensions, `(Q, w)` the input operands, `(w, R)` the output operands, in the
order of `NLAlib.Ops.Env.frame`: the index variables are the dimensions and then the offsets of the
operands, the buffer variables are the operands. A name repeated in the header is one operand
updated in place (it is passed twice by the caller, `[Q, w, w, R]`); it denotes its first
occurrence.

## Statements

```
call op [dims] (ins) → (outs)          -- Stmt.call
let t ← alloc len                      -- Stmt.alloc, scoped over the rest of the block
let v ← index q (ins) ≤ bound          -- Stmt.bindIdx, scoped over the rest of the block
for i < n { … }                        -- Stmt.loop
if q [dims] (ins) { … } else { … }     -- Stmt.ite
while i < fuel, q [dims] (ins) { … } then { … }   -- Stmt.whileFuel; `i` is the round index,
                                       -- and in the `then` block the number of rounds done
ifPos e { … }   ifZero e { … }         -- Stmt.ifPos, Stmt.ifZero
skip   abort   { … }
```

Statements are separated by `;`; a sequence is nested to the right. An operand is `X` or `X[e]`:
for an operand of the header, the offset is the offset variable of `X` plus the summands of `e`,
added from the left (`R[j * p + i]` is `.var oR + .var j * .var p + .var i`; a parenthesised
summand stays one: `C[(i * p + j)]` is `.var oC + (.var i * .var p + .var j)`); for a scratch
buffer it is `e` (and `X` alone is offset `0`). Index expressions are names, numerals, `+`, `-`
(truncated), `*`, `/` and parentheses. Operation and query names are Lean terms
(`(Has.inj Blas1Op.dot)`); sizes are never Lean terms, so a tree is one tree for all sizes.

The keywords `call`, `alloc`, `index`, `abort`, `ifPos`, `ifZero` are not reserved: they stay
usable as identifiers elsewhere.

An unknown name, a buffer used as an index or an index used as a buffer is an error at the name.

## Main results

* `ops%`: a program with named variables, elaborated to a plain `Stmt`.
* `opsImpl%`: an implementation with named variables, elaborated to a plain `Impl`.
-/

@[expose] public section

namespace NLAlib.Ops

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
/-- `let t ← alloc len`: a scratch buffer for the rest of the block. -/
syntax "let " ident " ← " &"alloc " opsIdx : opsStmt
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

/-- **An implementation with named variables**: `Impl.mk nd nin nout tree`. -/
syntax (name := opsImpl) "opsImpl% " "[" ident,* "]" " (" ident,* ")" " → " "(" ident,* ")"
  ppSpace opsBlock : term

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

mutual

/-- Translate a sequence of statements: nested to the right; a `let` scopes over the rest. -/
meta def seqE (sc : Scope) : Nat → List (TSyntax `opsStmt) → MacroM (TSyntax `term)
  | 0, _ => Macro.throwError "ops%: program nested too deeply"
  | _ + 1, [] => `(Stmt.skip)
  | f + 1, s :: rest => do
    match s with
    | `(opsStmt| let $t:ident ← alloc $len) =>
      `(Stmt.alloc $(← idxE sc depth len) $(← seqE (sc.pushBuf t.getId) f rest))
    | `(opsStmt| let $v:ident ← index $q ($as,*) ≤ $bd) =>
      `(Stmt.bindIdx $q $(← argL sc as.getElems) $(← idxE sc depth bd)
        $(← seqE (sc.pushIdx v.getId) f rest))
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
    | `(opsStmt| for $i:ident < $n $b:opsBlock) =>
      `(Stmt.loop $(← idxE sc depth n) $(← blockE (sc.pushIdx i.getId) f b))
    | `(opsStmt| if $q [$ds,*] ($as,*) $t:opsBlock else $e:opsBlock) =>
      `(Stmt.ite $q $(← idxL sc ds.getElems) $(← argL sc as.getElems) $(← blockE sc f t)
        $(← blockE sc f e))
    | `(opsStmt| while $i:ident < $fu, $q [$ds,*] ($as,*) $b:opsBlock then $k:opsBlock) =>
      let sc' := sc.pushIdx i.getId
      `(Stmt.whileFuel $(← idxE sc depth fu) $q $(← idxL sc' ds.getElems)
        $(← argL sc' as.getElems)
        $(← blockE sc' f b) $(← blockE sc' f k))
    | `(opsStmt| ifPos $e $b:opsBlock) =>
      `(Stmt.ifPos $(← idxE sc depth e) $(← blockE (sc.pushIdx Name.anonymous) f b))
    | `(opsStmt| ifZero $e $b:opsBlock) =>
      `(Stmt.ifZero $(← idxE sc depth e) $(← blockE (sc.pushIdx Name.anonymous) f b))
    | `(opsStmt| $b:opsBlock) => blockE sc f b
    | `(opsStmt| let $_t:ident ← alloc $_) => seqE sc f [s]
    | `(opsStmt| let $_v:ident ← index $_ ($_,*) ≤ $_) => seqE sc f [s]
    | _ => Macro.throwErrorAt s "ops%: not a statement"

end

/-- The scope of a header: dimensions, then the offsets and the handles of the operands. -/
meta def header (ds ins outs : Array Ident) : Scope :=
  let ops := ins ++ outs
  let idx := ds.map (·.getId) ++ ops.map (·.getId.appendAfter "_off")
  let buf := (ops.zipIdx).map fun (x, j) => (x.getId, some (ds.size + j))
  { idx, buf, nIdx := idx.size, nBuf := buf.size }

end Builder

open Lean in
macro_rules
  | `(ops% [$ds,*] ($ins,*) → ($outs,*) $b:opsBlock) =>
    Builder.blockE (Builder.header ds.getElems ins.getElems outs.getElems) Builder.depth b

open Lean in
macro_rules
  | `(opsImpl% [$ds,*] ($ins,*) → ($outs,*) $b:opsBlock) => do
    let body ← Builder.blockE (Builder.header ds.getElems ins.getElems outs.getElems)
      Builder.depth b
    `(Impl.mk $(Builder.lit ds.getElems.size) $(Builder.lit ins.getElems.size)
      $(Builder.lit outs.getElems.size) $body)

end NLAlib.Ops
