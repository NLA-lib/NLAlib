/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Store

/-!
# Programs over operations

A program `NLAlib.Ops.Stmt Op` is a first-order tree over the operation names `Op`. Its only
effects are calls of operations. An operation is used in one of three ways: `call` (it writes
cells), a test (`ite`, `whileFuel`: it returns a Boolean) or an index (`bindIdx`: it returns a
number, and the run fails if the conversion fails or the number exceeds the bound).

`whileFuel` is the loop of an iteration with a stopping test: it binds the round index in the
test and in the body, stops at the cap without failing, and hands the number of rounds done to
its continuation. The strict loop, which fails if the test still holds at the cap, is
`NLAlib.Ops.Stmt.whileStrict`. There is no Lean function in a tree:
index variables and buffer variables are positions in the environment (`NLAlib.Ops.Env`), a
binder appends to it, and sizes are index expressions `NLAlib.Ops.IExp`. So one tree serves all
sizes.

`frame` runs a body in a new environment made of the dimensions and operands it is given: it is
the instance of a procedure, and linking (`NLAlib.Ops.Stmt.link`) turns a call into the frame of
its implementation.
## Main results

* `NLAlib.Ops.Operand.evalList_append`, `NLAlib.Ops.Operand.evalList_off_of_evalList`: the
  evaluation of operand lists.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Index expressions: variables are positions in the environment. -/
inductive IExp where
  /-- The index variable at position `i` of the environment. -/
  | var (i : ℕ)
  /-- A number. -/
  | const (n : ℕ)
  /-- A sum. -/
  | add (a b : IExp)
  /-- A product. -/
  | mul (a b : IExp)
  /-- A truncated difference. -/
  | sub (a b : IExp)
  /-- A quotient, rounded down (zero when the divisor is zero). -/
  | div (a b : IExp)
  deriving DecidableEq, Repr

namespace IExp

instance : Add IExp := ⟨.add⟩
instance : Mul IExp := ⟨.mul⟩
instance : Sub IExp := ⟨.sub⟩
instance : Div IExp := ⟨.div⟩

/-- The value of an index expression; `none` at an unbound variable. -/
def eval (idx : List ℕ) : IExp → Option ℕ
  | .var i => idx[i]?
  | .const n => some n
  | .add a b => match a.eval idx, b.eval idx with
    | some x, some y => some (x + y)
    | _, _ => none
  | .mul a b => match a.eval idx, b.eval idx with
    | some x, some y => some (x * y)
    | _, _ => none
  | .sub a b => match a.eval idx, b.eval idx with
    | some x, some y => some (x - y)
    | _, _ => none
  | .div a b => match a.eval idx, b.eval idx with
    | some x, some y => some (x / y)
    | _, _ => none

@[simp] theorem eval_var (idx : List ℕ) (i : ℕ) : (var i).eval idx = idx[i]? := rfl
@[simp] theorem eval_const (idx : List ℕ) (n : ℕ) : (const n).eval idx = some n := rfl
@[simp] theorem eval_add (idx : List ℕ) (a b : IExp) :
    (a + b).eval idx = (a.eval idx).bind fun x => (b.eval idx).map fun y => x + y := by
  change (IExp.add a b).eval idx = _
  simp only [eval]
  cases a.eval idx <;> cases b.eval idx <;> rfl
@[simp] theorem eval_mul (idx : List ℕ) (a b : IExp) :
    (a * b).eval idx = (a.eval idx).bind fun x => (b.eval idx).map fun y => x * y := by
  change (IExp.mul a b).eval idx = _
  simp only [eval]
  cases a.eval idx <;> cases b.eval idx <;> rfl

@[simp] theorem eval_sub (idx : List ℕ) (a b : IExp) :
    (a - b).eval idx = (a.eval idx).bind fun x => (b.eval idx).map fun y => x - y := by
  change (IExp.sub a b).eval idx = _
  simp only [eval]
  cases a.eval idx <;> cases b.eval idx <;> rfl
@[simp] theorem eval_div (idx : List ℕ) (a b : IExp) :
    (a / b).eval idx = (a.eval idx).bind fun x => (b.eval idx).map fun y => x / y := by
  change (IExp.div a b).eval idx = _
  simp only [eval]
  cases a.eval idx <;> cases b.eval idx <;> rfl

/-- The values of a list of index expressions. -/
def evalList (idx : List ℕ) : List IExp → Option (List ℕ)
  | [] => some []
  | e :: es => match e.eval idx, evalList idx es with
    | some x, some xs => some (x :: xs)
    | _, _ => none

@[simp] theorem evalList_nil (idx : List ℕ) : evalList idx [] = some [] := rfl
@[simp] theorem evalList_cons (idx : List ℕ) (e : IExp) (es : List IExp) :
    evalList idx (e :: es) =
      (e.eval idx).bind fun x => (evalList idx es).map fun xs => x :: xs := by
  simp only [evalList]
  cases e.eval idx <;> cases evalList idx es <;> rfl

theorem length_of_evalList {idx : List ℕ} {es : List IExp} {xs : List ℕ}
    (h : evalList idx es = some xs) : xs.length = es.length := by
  induction es generalizing xs with
  | nil => cases h; rfl
  | cons e es ih =>
    rw [evalList_cons] at h
    obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [ih hys]

end IExp

/-- An operand of a call: a buffer variable and an offset. The length is the operation's shape. -/
structure Operand where
  /-- The buffer variable: a position in the environment. -/
  buf : ℕ
  /-- The offset in the buffer. -/
  off : IExp
  deriving DecidableEq, Repr

/-- The environment of a run: the values of the index variables and the handles of the buffer
variables. Binders append. -/
structure Env where
  /-- The values of the index variables. -/
  idx : List ℕ
  /-- The handles of the buffer variables. -/
  buf : List ℕ

namespace Env

/-- Bind a new index variable. -/
def pushIdx (ρ : Env) (i : ℕ) : Env := ⟨ρ.idx ++ [i], ρ.buf⟩

/-- Bind a new buffer variable. -/
def pushBuf (ρ : Env) (b : ℕ) : Env := ⟨ρ.idx, ρ.buf ++ [b]⟩

/-- The environment of a procedure instance: the index variables are the dimensions followed by
the offsets of the operands, the buffer variables are the handles of the operands. -/
def frame (d : List ℕ) (a : List (ℕ × ℕ)) : Env := ⟨d ++ a.map Prod.snd, a.map Prod.fst⟩

@[simp] theorem idx_pushIdx (ρ : Env) (i : ℕ) : (ρ.pushIdx i).idx = ρ.idx ++ [i] := rfl
@[simp] theorem buf_pushIdx (ρ : Env) (i : ℕ) : (ρ.pushIdx i).buf = ρ.buf := rfl
@[simp] theorem idx_pushBuf (ρ : Env) (b : ℕ) : (ρ.pushBuf b).idx = ρ.idx := rfl
@[simp] theorem buf_pushBuf (ρ : Env) (b : ℕ) : (ρ.pushBuf b).buf = ρ.buf ++ [b] := rfl
@[simp] theorem idx_frame (d : List ℕ) (a : List (ℕ × ℕ)) :
    (frame d a).idx = d ++ a.map Prod.snd := rfl
@[simp] theorem buf_frame (d : List ℕ) (a : List (ℕ × ℕ)) : (frame d a).buf = a.map Prod.fst := rfl

end Env

namespace Operand

/-- The handle and the offset of an operand. -/
def eval (ρ : Env) (a : Operand) : Option (ℕ × ℕ) :=
  match ρ.buf[a.buf]?, a.off.eval ρ.idx with
  | some b, some o => some (b, o)
  | _, _ => none

/-- The handles and offsets of a list of operands. -/
def evalList (ρ : Env) : List Operand → Option (List (ℕ × ℕ))
  | [] => some []
  | a :: as => match a.eval ρ, evalList ρ as with
    | some x, some xs => some (x :: xs)
    | _, _ => none

theorem eval_eq (ρ : Env) (a : Operand) :
    a.eval ρ = (ρ.buf[a.buf]?).bind fun b => (a.off.eval ρ.idx).map fun o => (b, o) := by
  simp only [eval]
  cases ρ.buf[a.buf]? <;> cases a.off.eval ρ.idx <;> rfl

@[simp] theorem evalList_nil (ρ : Env) : evalList ρ [] = some [] := rfl
@[simp] theorem evalList_cons (ρ : Env) (a : Operand) (as : List Operand) :
    evalList ρ (a :: as) = (a.eval ρ).bind fun x => (evalList ρ as).map fun xs => x :: xs := by
  simp only [evalList]
  cases a.eval ρ <;> cases evalList ρ as <;> rfl

theorem length_of_evalList {ρ : Env} {as : List Operand} {xs : List (ℕ × ℕ)}
    (h : evalList ρ as = some xs) : xs.length = as.length := by
  induction as generalizing xs with
  | nil => cases h; rfl
  | cons a as ih =>
    rw [evalList_cons] at h
    obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [ih hys]

theorem evalList_append (ρ : Env) (as bs : List Operand) :
    evalList ρ (as ++ bs) =
      (evalList ρ as).bind fun xs => (evalList ρ bs).map fun ys => xs ++ ys := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.cons_append, evalList_cons, ih]
    cases a.eval ρ <;> cases evalList ρ as <;> cases evalList ρ bs <;> rfl

/-- The offsets of evaluated operands are the values of their offset expressions. -/
theorem evalList_off_of_evalList {ρ : Env} {as : List Operand} {xs : List (ℕ × ℕ)}
    (h : evalList ρ as = some xs) :
    IExp.evalList ρ.idx (as.map Operand.off) = some (xs.map Prod.snd) := by
  induction as generalizing xs with
  | nil => cases h; rfl
  | cons a as ih =>
    rw [evalList_cons] at h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ys, hys, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [eval_eq] at hx
    obtain ⟨b, -, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hx
    simp [ho, ih hys]

end Operand

/-- **Programs** over the operations `Op` and the queries `Tst`: first-order trees whose only
effects are calls of operations. A query is a name used as a test or as an index; it is a
primitive of the access model and is never implemented, so linking leaves it alone. -/
inductive Stmt (Op Tst : Type) where
  /-- Do nothing. -/
  | skip
  /-- Fail. An implementation called outside its shape fails; it never skips. -/
  | abort
  /-- Sequence. -/
  | seq (s t : Stmt Op Tst)
  /-- Call the operation `o` at the dimensions `dims` on the operands `ins` and `outs`. The run
  fails if an operand handle is not a buffer of the store. -/
  | call (o : Op) (dims : List IExp) (ins outs : List Operand)
  /-- Branch on the Boolean returned by the test `q`. -/
  | ite (q : Tst) (dims : List IExp) (ins : List Operand) (t e : Stmt Op Tst)
  /-- A counted loop with a test that exits early. Round `i` (a new index variable, in the
  dimensions and operands of the test and in `body`) evaluates the test `q` and runs `body` if it
  returns true; the loop ends at the first round whose test returns false, or after `fuel`
  rounds, without a further test. Then `k` runs with the new index variable bound to the number
  of rounds done. -/
  | whileFuel (fuel : IExp) (q : Tst) (dims : List IExp) (ins : List Operand)
      (body k : Stmt Op Tst)
  /-- Bind a new index variable to the number returned by the index query `q`; the run fails
  if the number exceeds `bound`. -/
  | bindIdx (q : Tst) (ins : List Operand) (bound : IExp) (body : Stmt Op Tst)
  /-- Bind a new buffer variable to a scratch buffer of `len` uninitialised cells, freed after
  `body`. -/
  | alloc (len : IExp) (body : Stmt Op Tst)
  /-- Run `body` for the values `0, …, n - 1` of a new index variable. -/
  | loop (n : IExp) (body : Stmt Op Tst)
  /-- A procedure instance: run `body` in the environment `Env.frame` of the dimensions and
  operands. The run fails if an operand handle is not a buffer of the store. -/
  | frame (dims : List IExp) (args : List Operand) (body : Stmt Op Tst)

namespace Stmt

variable {Op Tst : Type}

/-- Run `body` if the size `e` is zero: a loop of `1 - e` rounds. Its index variable is not
used. -/
def ifZero (e : IExp) (body : Stmt Op Tst) : Stmt Op Tst := .loop (.const 1 - e) body

/-- Run `body` if the size `e` is positive: a loop of `1 - (1 - e)` rounds. -/
def ifPos (e : IExp) (body : Stmt Op Tst) : Stmt Op Tst := .loop (.const 1 - (.const 1 - e)) body

/-- **The strict loop**: run `body` while the test `q` returns true, and fail if it still holds
after `fuel` rounds. The fuel is a bound, never a truncation. `nidx` is the number of index
variables in scope: the round index is the variable `nidx` in the test and in `body`. The loop
is given one more round than the fuel and fails if that round is reached. -/
def whileStrict (nidx : ℕ) (fuel : IExp) (q : Tst) (dims : List IExp) (ins : List Operand)
    (body : Stmt Op Tst) : Stmt Op Tst :=
  .whileFuel (fuel + .const 1) q dims ins (.seq (ifZero (fuel - .var nidx) .abort) body) .skip

end Stmt

end NLAlib.Ops
