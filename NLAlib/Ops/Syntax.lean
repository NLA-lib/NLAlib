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
  /-- Bind a new buffer variable to `len` uninitialized elements of the declared storage format,
  freed after `body`; payload charge is `format.bytes * len`. -/
  | allocAs (format : StorageFormat) (len : IExp) (body : Stmt Op Tst)
  /-- Run `body` for the values `0, …, n - 1` of a new index variable. -/
  | loop (n : IExp) (body : Stmt Op Tst)
  /-- A procedure instance: run `body` in the environment `Env.frame` of the dimensions and
  operands. The run fails if an operand handle is not a buffer of the store. -/
  | frame (dims : List IExp) (args : List Operand) (body : Stmt Op Tst)

namespace Stmt

variable {Op Tst : Type}

/-- Allocate one-byte cells. Format-aware programs use `allocAs` explicitly. -/
@[simp] def alloc (len : IExp) (body : Stmt Op Tst) : Stmt Op Tst :=
  .allocAs .cell len body

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


/-- Structural instructions recorded in addition to the specified operations and queries. -/
inductive Bookkeeping where
  /-- Read an index variable. -/
  | indexVar
  /-- Read an index constant. -/
  | indexConst
  /-- Add indices. -/
  | indexAdd
  /-- Multiply indices. -/
  | indexMul
  /-- Subtract indices. -/
  | indexSub
  /-- Divide indices. -/
  | indexDiv
  /-- Resolve an operand's buffer and offset. -/
  | operand
  /-- A skipped statement. -/
  | skip
  /-- Sequence two statements. -/
  | sequence
  /-- Select a branch. -/
  | branch
  /-- Enter or leave a counted loop. -/
  | loop
  /-- Enter a loop round. -/
  | round
  /-- Finish a loop with early exit, including its final index-evaluation allowance. -/
  | exit
  /-- Check and bind an index returned by a query. -/
  | bindIdx
  /-- Allocate a buffer; the dimension is its length. -/
  | allocate
  /-- Release a buffer; the dimension is its length. -/
  | release
  /-- Enter a procedure frame. -/
  | frame
  deriving DecidableEq, Repr

variable {Op Tst K : Type}

/-- The structural operations needed to evaluate an index expression. -/
def IExp.bookkeeping : IExp → List Bookkeeping
  | .var _ => [.indexVar]
  | .const _ => [.indexConst]
  | .add a b => a.bookkeeping ++ b.bookkeeping ++ [.indexAdd]
  | .mul a b => a.bookkeeping ++ b.bookkeeping ++ [.indexMul]
  | .sub a b => a.bookkeeping ++ b.bookkeeping ++ [.indexSub]
  | .div a b => a.bookkeeping ++ b.bookkeeping ++ [.indexDiv]

/-- Structural operations for evaluating dimensions. -/
def indexBookkeeping (ds : List IExp) : List Bookkeeping := ds.flatMap IExp.bookkeeping

/-- Structural operations for resolving operands, including their offsets. -/
def operandBookkeeping (as : List Operand) : List Bookkeeping :=
  as.flatMap fun a => a.off.bookkeeping ++ [.operand]

/-- A list of explicit structural instructions, each an identity operation on memory. -/
def tally : List Bookkeeping → Stmt (Op ⊕ Bookkeeping) Tst
  | [] => .skip
  | k :: ks => .seq (.call (.inr k) [] [] []) (tally ks)

/-- Instrument one fixed symbolic tree. No concrete sizes, inputs, interpretation or tape are
arguments of this transformation. Every dimension expression and operand offset is accounted
for, together with control and allocations. -/
def Stmt.instrument : Stmt Op Tst → Stmt (Op ⊕ Bookkeeping) Tst
  | .skip => tally [.skip]
  | .abort => .abort
  | .seq s t => .seq (tally [.sequence]) (.seq s.instrument t.instrument)
  | .call o ds ins outs =>
      .seq (tally (indexBookkeeping ds ++ operandBookkeeping (ins ++ outs)))
        (.call (.inl o) ds ins outs)
  | .ite q ds ins t e =>
      .seq (tally (indexBookkeeping ds ++ operandBookkeeping ins ++ [.branch]))
        (.ite q ds ins t.instrument e.instrument)
  | .whileFuel fuel q ds ins body k =>
      let testWork := indexBookkeeping ds ++ operandBookkeeping ins
      .seq (tally (fuel.bookkeeping ++ [.loop]))
        (.whileFuel fuel q ds ins
          (.seq (tally (testWork ++ [.round])) body.instrument)
          (.seq (tally (testWork ++ [.exit])) k.instrument))
  | .bindIdx q ins bound body =>
      .seq (tally (operandBookkeeping ins ++ bound.bookkeeping ++ [.bindIdx]))
        (.bindIdx q ins bound body.instrument)
  | .allocAs fmt len body =>
      .seq (tally len.bookkeeping)
        (.seq (.call (.inr .allocate) [.const fmt.bytes, len] [] [])
          (.seq (.allocAs fmt len body.instrument)
            (.call (.inr .release) [.const fmt.bytes, len] [] [])))
  | .loop n body =>
      .seq (tally (n.bookkeeping ++ [.loop]))
        (.loop n (.seq (tally [.round]) body.instrument))
  | .frame ds args body =>
      .seq (tally (indexBookkeeping ds ++ operandBookkeeping args ++ [.frame]))
        (.frame ds args body.instrument)


/-- One fixed first-order tree for every size and input: `r` sizes and `b` initial buffers.
There are no functions or callbacks in this structure. Operation identities and literals are
fixed in the tree. Scope and liveness obligations are discharged by total correctness. -/
structure Program (Op Tst : Type) (r b : ℕ) where
  /-- The one tree executed at every size. -/
  body : Stmt Op Tst

namespace Program

variable {Op Lo Tst K : Type} {r b : ℕ}

/-- The only initial environment: sizes followed by the `b` zero offsets, and handles in order.
The program does not supply an environment-building function. -/
def environment (d : Fin r → ℕ) : Env :=
  ⟨List.ofFn d ++ List.replicate b 0, List.range b⟩


end Program

/-- Storage formats of an operation's input and output operands. Storage and arithmetic
precision are independent: a mixed dot may consume fp16 and produce fp32. -/
structure OperandSignature where
  /-- Storage representation of every input operand, in order. -/
  inputs : List StorageFormat
  /-- Storage representation of every output operand, in order. -/
  outputs : List StorageFormat

/-- One fixed execution configuration: storage signatures, workspace bytes and work/span costs.
Work measures total work; span permits internal primitive parallelism. Source calls are
sequential, so their spans add. This is not a scheduler or elapsed-time guarantee. -/
structure ResourceModel (Op Tst : Type) where
  /-- The permitted representations. Equality includes both identity and byte width. -/
  formats : List StorageFormat
  /-- Required operand storage formats for each primitive. -/
  operation : Op → OperandSignature
  /-- Required inputs for Boolean queries. -/
  testInputs : Tst → List StorageFormat
  /-- Required inputs for index queries. -/
  indexInputs : Tst → List StorageFormat
  /-- Additional temporary payload bytes of each primitive. -/
  workspace : Op → List ℕ → ℕ
  /-- Additional temporary payload bytes of either use of a query. -/
  queryWorkspace : Tst → List ℕ → ℕ
  /-- Total work of each primitive. -/
  operationWork : Op → List ℕ → ℕ
  /-- Internal critical path of each primitive in this configuration. -/
  operationSpan : Op → List ℕ → ℕ
  /-- Total work of queries. -/
  queryWork : Tst → List ℕ → ℕ
  /-- Internal critical path of queries. -/
  querySpan : Tst → List ℕ → ℕ
  /-- Work of structural instructions. -/
  coreWork : Bookkeeping → List ℕ → ℕ
  /-- Span of structural instructions. -/
  coreSpan : Bookkeeping → List ℕ → ℕ
  /-- A primitive's critical path cannot exceed its total work. -/
  operation_span_le : ∀ o d, operationSpan o d ≤ operationWork o d
  /-- A query's critical path cannot exceed its total work. -/
  query_span_le : ∀ q d, querySpan q d ≤ queryWork q d
  /-- A structural instruction's critical path cannot exceed its total work. -/
  core_span_le : ∀ k d, coreSpan k d ≤ coreWork k d

/-- Resolve operand storage representations in a lexical buffer context. Offsets do not
change the backing buffer's representation. -/
def Operand.formatList (ctx : List StorageFormat) : List Operand → Option (List StorageFormat)
  | [] => some []
  | a :: as => (ctx[a.buf]?).bind fun f => (formatList ctx as).map (f :: ·)

/-- The buffer format discipline, checked independently of runtime sizes, values and tests.
Frames inherit actual operand formats, including aliases; no construct retypes a buffer. -/
def Stmt.wellTyped {Op Tst : Type} (R : ResourceModel Op Tst) :
    Stmt Op Tst → List StorageFormat → Bool
  | .skip, _ => true
  | .abort, _ => true
  | .seq s t, ctx => s.wellTyped R ctx && t.wellTyped R ctx
  | .call o _ ins outs, ctx =>
      decide (Operand.formatList ctx ins = some (R.operation o).inputs) &&
        decide (Operand.formatList ctx outs = some (R.operation o).outputs)
  | .ite q _ ins t e, ctx =>
      decide (Operand.formatList ctx ins = some (R.testInputs q)) &&
        t.wellTyped R ctx && e.wellTyped R ctx
  | .whileFuel _ q _ ins body k, ctx =>
      decide (Operand.formatList ctx ins = some (R.testInputs q)) &&
        body.wellTyped R ctx && k.wellTyped R ctx
  | .bindIdx q ins _ body, ctx =>
      decide (Operand.formatList ctx ins = some (R.indexInputs q)) && body.wellTyped R ctx
  | .allocAs f _ body, ctx => decide (f ∈ R.formats) && body.wellTyped R (ctx ++ [f])
  | .loop _ body, ctx => body.wellTyped R ctx
  | .frame _ args body, ctx =>
      match Operand.formatList ctx args with
      | some fs => body.wellTyped R fs
      | none => false

/-- A fixed program uses only declared formats and matches all primitive/query signatures. -/
def Program.wellTyped {Op Tst : Type} {r b : ℕ} (p : Program Op Tst r b)
    (R : ResourceModel Op Tst) (formats : Fin b → StorageFormat) : Bool :=
  (List.ofFn formats).all (fun f => decide (f ∈ R.formats)) &&
    p.body.wellTyped R (List.ofFn formats)

end NLAlib.Ops
