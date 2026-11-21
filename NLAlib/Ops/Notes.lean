/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Static

/-!
# Notes: metadata that a tree carries and no judgment reads

`NLAlib.Ops.Stmt.note n s` is the tree `s` with the metadata `n` (`NLAlib.Ops.Note`): the name
of the routine a frame runs, the source name of a bound variable, the header of a fragment. The
evaluator, the counted evaluator, the static count and scratch, the storage check, linking and
instrumentation treat a note as the tree it annotates; the instrumented tree has no notes, so a
note adds no instruction. `NLAlib.Ops.Stmt.erase` removes every note, and the erased tree has
the same run, count and scratch.

`NLAlib.Ops.Stmt.pretty` renders a tree as indented pseudocode with the names the notes give.
It is a reading aid for people and tools; it is not a code emitter and nothing is proved about
its output.

## Main definitions

* `NLAlib.Ops.Stmt.erase`: the tree without its notes.
* `NLAlib.Ops.Stmt.pretty`: the tree as pseudocode.

## Main results

* `NLAlib.Ops.eval_erase`, `NLAlib.Ops.stmtCost_erase`, `NLAlib.Ops.stmtPeak_erase`,
  `NLAlib.Ops.Stmt.instrument_erase`: erasing notes changes no run, count or scratch.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- The tree without its notes. -/
def Stmt.erase : Stmt Op Tst → Stmt Op Tst
  | .skip => .skip
  | .abort => .abort
  | .seq s t => .seq s.erase t.erase
  | .call o ds ins outs => .call o ds ins outs
  | .ite q ds ins t e => .ite q ds ins t.erase e.erase
  | .whileFuel fuel q ds ins body k => .whileFuel fuel q ds ins body.erase k.erase
  | .bindIdx q ins bound body => .bindIdx q ins bound body.erase
  | .allocAs fmt len body => .allocAs fmt len body.erase
  | .loop n body => .loop n body.erase
  | .frame ds args body => .frame ds args body.erase
  | .note _ s => s.erase

/-- The instrumented tree does not depend on the notes. -/
theorem Stmt.instrument_erase (s : Stmt Op Tst) : s.erase.instrument = s.instrument := by
  induction s with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => simp only [Stmt.erase, Stmt.instrument, ihs, iht]
  | call o ds ins outs => rfl
  | ite q ds ins t e iht ihe => simp only [Stmt.erase, Stmt.instrument, iht, ihe]
  | whileFuel fuel q ds ins body k ih ihk => simp only [Stmt.erase, Stmt.instrument, ih, ihk]
  | bindIdx q ins bound body ih => simp only [Stmt.erase, Stmt.instrument, ih]
  | allocAs fmt len body ih => simp only [Stmt.erase, Stmt.instrument, ih]
  | loop n body ih => simp only [Stmt.erase, Stmt.instrument, ih]
  | frame ds args body ih => simp only [Stmt.erase, Stmt.instrument, ih]
  | note _ _ ih => simpa only [Stmt.erase, Stmt.instrument] using ih

/-- Erasing the notes changes no run. -/
theorem eval_erase (I : Interp Op Tst K) (τ : Tape K) (s : Stmt Op Tst) :
    eval I τ s.erase = eval I τ s := by
  induction s with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => funext ρ m; simp only [Stmt.erase, eval, ihs, iht]
  | call o ds ins outs => rfl
  | ite q ds ins t e iht ihe => funext ρ m; simp only [Stmt.erase, eval, iht, ihe]
  | whileFuel fuel q ds ins body k ih ihk => funext ρ m; simp only [Stmt.erase, eval, ih, ihk]
  | bindIdx q ins bound body ih => funext ρ m; simp only [Stmt.erase, eval, ih]
  | allocAs fmt len body ih => funext ρ m; simp only [Stmt.erase, eval, ih]
  | loop n body ih => funext ρ m; simp only [Stmt.erase, eval, ih]
  | frame ds args body ih => funext ρ m; simp only [Stmt.erase, eval, ih]
  | note _ _ ih => funext ρ m; simpa only [Stmt.erase, eval] using congrFun (congrFun ih ρ) m

/-- Erasing the notes changes no static count. -/
theorem stmtCost_erase (s : Stmt Op Tst) : stmtCost s.erase = stmtCost s := by
  induction s with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => funext idx; simp only [Stmt.erase, stmtCost, ihs, iht]
  | call o ds ins outs => rfl
  | ite q ds ins t e iht ihe => funext idx; simp only [Stmt.erase, stmtCost, iht, ihe]
  | whileFuel fuel q ds ins body k ih ihk =>
    funext idx; simp only [Stmt.erase, stmtCost, ih, ihk]
  | bindIdx q ins bound body ih => funext idx; simp only [Stmt.erase, stmtCost, ih]
  | allocAs fmt len body ih => funext idx; simp only [Stmt.erase, stmtCost, ih]
  | loop n body ih => funext idx; simp only [Stmt.erase, stmtCost, ih]
  | frame ds args body ih => funext idx; simp only [Stmt.erase, stmtCost, ih]
  | note _ _ ih => funext idx; simpa only [Stmt.erase, stmtCost] using congrFun ih idx

/-- Erasing the notes changes no static scratch. -/
theorem stmtPeak_erase (W : Op → List ℕ → ℕ) (s : Stmt Op Tst) :
    stmtPeak W s.erase = stmtPeak W s := by
  induction s with
  | skip => rfl
  | abort => rfl
  | seq s t ihs iht => funext idx; simp only [Stmt.erase, stmtPeak, ihs, iht]
  | call o ds ins outs => rfl
  | ite q ds ins t e iht ihe => funext idx; simp only [Stmt.erase, stmtPeak, iht, ihe]
  | whileFuel fuel q ds ins body k ih ihk =>
    funext idx; simp only [Stmt.erase, stmtPeak, ih, ihk]
  | bindIdx q ins bound body ih => funext idx; simp only [Stmt.erase, stmtPeak, ih]
  | allocAs fmt len body ih => funext idx; simp only [Stmt.erase, stmtPeak, ih]
  | loop n body ih => funext idx; simp only [Stmt.erase, stmtPeak, ih]
  | frame ds args body ih => funext idx; simp only [Stmt.erase, stmtPeak, ih]
  | note _ _ ih => funext idx; simpa only [Stmt.erase, stmtPeak] using congrFun ih idx

/-! ### Pseudocode -/

namespace Pretty

/-- The name of the index variable at a position: the source name, or `i` and the position. -/
def idxName (idx : List String) (i : ℕ) : String := idx.getD i s!"i{i}"

/-- The name of the buffer variable at a position: the source name, or `b` and the position. -/
def bufName (buf : List String) (b : ℕ) : String := buf.getD b s!"b{b}"

/-- An index expression, with sums and differences in parentheses when `tight`. -/
def iexp (idx : List String) : Bool → IExp → String
  | _, .var i => idxName idx i
  | _, .const n => toString n
  | tight, .add a b =>
      let r := s!"{iexp idx false a} + {iexp idx false b}"
      if tight then s!"({r})" else r
  | tight, .sub a b =>
      let r := s!"{iexp idx false a} - {iexp idx true b}"
      if tight then s!"({r})" else r
  | _, .mul a b => s!"{iexp idx true a} * {iexp idx true b}"
  | _, .div a b => s!"{iexp idx true a} / {iexp idx true b}"

/-- The printed form of an operation or a test without the namespace of its constructor:
`NLAlib.Ops.ScalarOp.add` is shown as `add`. -/
def opName {α : Type} [Repr α] (o : α) : String :=
  let cs := (reprStr o).toList
  let head := cs.takeWhile (· != ' ')
  let rest := cs.dropWhile (· != ' ')
  String.ofList ((head.reverse.takeWhile (· != '.')).reverse ++ rest)

/-- A list of index expressions. -/
def iexps (idx : List String) (es : List IExp) : String :=
  ", ".intercalate (es.map (iexp idx false))

/-- An operand: the name of its buffer variable, with the offset inside it when there is one. -/
def operand (idx buf : List String) (a : Operand) : String :=
  let x := bufName buf a.buf
  match a.off with
  | .const 0 => x
  | .var k => if idxName idx k = x ++ ".off" then x else s!"{x}@{idxName idx k}"
  | .add (.var k) e =>
      if idxName idx k = x ++ ".off" then s!"{x}[{iexp idx false e}]"
      else s!"{x}@({iexp idx false (.add (.var k) e)})"
  | e => s!"{x}@({iexp idx false e})"

/-- A list of operands. -/
def operands (idx buf : List String) (as : List Operand) : String :=
  ", ".intercalate (as.map (operand idx buf))

/-- The lines of a tree. `idx` and `buf` are the names in scope, `pending` the source name of
the variable the next binder introduces, `ind` the indentation. -/
def lines [Repr Op] [Repr Tst] (idx buf : List String) (pending : Option String)
    (ind : String) : Stmt Op Tst → List String
  | .skip => [ind ++ "skip"]
  | .abort => [ind ++ "abort"]
  | .seq s t => lines idx buf none ind s ++ lines idx buf none ind t
  | .call o ds ins outs =>
      [s!"{ind}call {opName o} [{iexps idx ds}] ({operands idx buf ins}) → {""
        }({operands idx buf outs})"]
  | .ite q ds ins t e =>
      [s!"{ind}if {opName q} [{iexps idx ds}] ({operands idx buf ins}) \{"] ++
        lines idx buf none (ind ++ "  ") t ++ [ind ++ "} else {"] ++
        lines idx buf none (ind ++ "  ") e ++ [ind ++ "}"]
  | .whileFuel fuel q ds ins body k =>
      let i := pending.getD s!"i{idx.length}"
      [s!"{ind}while {i} < {iexp idx false fuel}, {opName q} [{iexps (idx ++ [i]) ds}] {""
        }({operands (idx ++ [i]) buf ins}) \{"] ++
        lines (idx ++ [i]) buf none (ind ++ "  ") body ++ [ind ++ "} then {"] ++
        lines (idx ++ [i]) buf none (ind ++ "  ") k ++ [ind ++ "}"]
  | .bindIdx q ins bound body =>
      let v := pending.getD s!"i{idx.length}"
      [s!"{ind}let {v} ← index {opName q} ({operands idx buf ins}) ≤ {""
        }{iexp idx false bound}"] ++ lines (idx ++ [v]) buf none ind body
  | .allocAs _ len body =>
      let t := pending.getD s!"b{buf.length}"
      [s!"{ind}let {t} ← alloc {iexp idx false len}"] ++ lines idx (buf ++ [t]) none ind body
  | .loop n body =>
      let i := pending.getD s!"i{idx.length}"
      [s!"{ind}for {i} < {iexp idx false n} \{"] ++
        lines (idx ++ [i]) buf none (ind ++ "  ") body ++ [ind ++ "}"]
  | .frame ds args body =>
      let bs := (List.range args.length).map fun j => s!"a{j}"
      let is := (List.range ds.length).map (fun j => s!"d{j}") ++ bs.map (· ++ ".off")
      [s!"{ind}frame [{iexps idx ds}] ({operands idx buf args}) \{"] ++
        lines is bs none (ind ++ "  ") body ++ [ind ++ "}"]
  | .note (.var x) s => lines idx buf (some x) ind s
  | .note (.routine name ds as) _ =>
      [s!"{ind}run {name} [{", ".intercalate ds}] ({", ".intercalate as})"]
  | .note (.header ds as) s => lines (ds ++ as.map (· ++ ".off")) as none ind s
  | .note (.label text) s => [s!"{ind}-- {text}"] ++ lines idx buf pending ind s
  | .note (.tag _ _) s => lines idx buf pending ind s

end Pretty

/-- **The tree as pseudocode**, with the names its notes give: source names of variables, and
`run name [dims] (operands)` for a frame noted as the run of a routine, in place of the tree of
that routine. A variable without a note is shown by its position. This is a reading aid; it is
not a code emitter and nothing is proved about its output. -/
def Stmt.pretty [Repr Op] [Repr Tst] (s : Stmt Op Tst) : String :=
  "\n".intercalate (Pretty.lines [] [] none "" s)

end NLAlib.Ops
