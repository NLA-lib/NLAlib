/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Rat.Sqrt
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Catalog.Random

/-!
# Tools: concrete machines and interpretations

Diagnostic and compute support; formal guarantees are independent of this output.
Concrete carriers (`ℚ`, exact; `Float`) and the interpretations of the
catalog groups over them, so that a program can be run by `#eval`. None of these is a model
primitive. They are sample interpretations, chosen to meet the exact
contracts on `ℚ` (except `sqrt`, see below) and to be a plain sequential reference on `Float`.

## Main results

* `NLAlib.Ops.Tools.Concrete K`: a machine (`NLAlib.Ops.Machine K`), comparisons and the
  conversion to an index, for `ℚ` and `Float`. On `ℚ` the square root is `Rat.sqrt`, exact on
  squares of rationals and a truncation otherwise.
* `NLAlib.Ops.Tools.blas1Fn`: the level-1 operations as sequential loops of the machine.
* `NLAlib.Ops.Tools.randFn`: the operations of `NLAlib.Ops.ROp` for a given matrix (by rows).
* `NLAlib.Ops.Tools.withQueries`: the comparisons `CmpTst` and the conversion `IdxTst` added to an
  interpretation given by block functions.
* `NLAlib.Ops.Tools.cmpOpFn`, `NLAlib.Ops.Tools.withFlagTest`: comparisons that write a flag and
  the query that reads it.
* `NLAlib.Ops.Tools.signTape`, `NLAlib.Ops.Tools.constTape`: fixed concrete tapes.
* `NLAlib.Ops.Tools.ShowKey`: names of operations for the reports.
-/

@[expose] public section

namespace NLAlib.Ops.Tools

open NLAlib.Ops

/-- A concrete carrier: its machine, comparisons, the conversion to an index, and printing. -/
class Concrete (K : Type) extends Inhabited K, ToString K where
  /-- The functions of the scalar operations. -/
  machine : Machine K
  /-- `a < b`. -/
  lt : K → K → Bool
  /-- `a ≤ b`. -/
  le : K → K → Bool
  /-- `a = b`. -/
  eq : K → K → Bool
  /-- The floor of a nonnegative value; nothing for a negative one. -/
  toNat? : K → Option ℕ

/-- Exact rational arithmetic; the square root is `Rat.sqrt` (exact on squares). -/
def ratMachine : Machine ℚ where
  lit q := q
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  div a b := a / b
  neg a := -a
  sqrt a := Rat.sqrt a

instance : Concrete ℚ where
  default := 0
  toString q := toString q
  machine := ratMachine
  lt a b := decide (a < b)
  le a b := decide (a ≤ b)
  eq a b := decide (a = b)
  toNat? a := if 0 ≤ a then some ⌊a⌋₊ else none

/-- The rational `q` as a `Float`. -/
def ratToFloat (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- Binary64 arithmetic of the host. -/
def floatMachine : Machine Float where
  lit q := ratToFloat q
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  div a b := a / b
  neg a := -a
  sqrt a := a.sqrt

instance : Concrete Float where
  default := 0
  toString x := toString x
  machine := floatMachine
  lt a b := a < b
  le a b := a ≤ b
  eq a b := a == b
  toNat? a := if 0 ≤ a then some a.floor.toUInt64.toNat else none

variable {K : Type} [Concrete K]

/-- The machine of the carrier. -/
abbrev mach (K : Type) [Concrete K] : Machine K := Concrete.machine

/-- The sequential sum of the machine, from the literal zero. -/
def sumL (xs : List K) : K := xs.foldl (mach K).add ((mach K).lit 0)

/-- The sequential dot product of the machine. -/
def dotL (xs ys : List K) : K := sumL (List.zipWith (mach K).mul xs ys)

/-- **The level-1 operations as sequential loops of the machine.** -/
def blas1Fn : Blas1Op → BlockFn K
  | .sum => .of1 1 (·.headD 0) (fun _ => 1) fun _ x => some [sumL x]
  | .dot => .of2 1 (·.headD 0) (·.headD 0) (fun _ => 1) fun _ x y => some [dotL x y]
  | .nrm2 => .of1 1 (·.headD 0) (fun _ => 1) fun _ x => some [(mach K).sqrt (dotL x x)]
  | .axpy => .of3 1 (fun _ => 1) (·.headD 0) (·.headD 0) (·.headD 0) fun _ a x y =>
      some (List.zipWith (fun xi yi => (mach K).add yi ((mach K).mul (a.headD default) xi)) x y)
  | .scal => .of2 1 (fun _ => 1) (·.headD 0) (·.headD 0) fun _ a x =>
      some (x.map fun xi => (mach K).div xi (a.headD default))
  | .copy => .of1 1 (·.headD 0) (·.headD 0) fun _ x => some x

/-- The product of a matrix given by rows with a vector. -/
def matvecL (A : List (List K)) (x : List K) : List K := A.map fun row => dotL row x

/-- The matrix-vector operation on a matrix given by rows, with its dimensions checked. -/
def operatorFn (A : List (List K)) : OperatorOp → BlockFn K
  | .matvec => .of1 2 (·.getD 1 0) (·.headD 0) fun d x =>
      if A.length == d.headD 0 && A.all (fun row => row.length == d.getD 1 0) then
        some (matvecL A x)
      else none

/-- **The operations of `ROp`** for the matrix `A` (by rows): the draws read the Gaussian stream
of the tape, the rest is the machine. -/
def randFn (A : List (List K)) : ROp → BlockFn K
  | .draw => .draw Stream.gauss
  | .gauss => .drawVec Stream.gauss
  | .operator o => operatorFn A o
  | .dot => blas1Fn .dot
  | .add => .bin fun a b => some ((mach K).add a b)
  | .nrm2 => blas1Fn .nrm2
  | .mulc q => .un fun a => some ((mach K).mul ((mach K).lit q) a)
  | .axpy => blas1Fn .axpy

/-- **The level-1 and the scalar operations**, the signature of the BLAS profiles. -/
def blasFn : Blas1Op ⊕ ScalarOp → BlockFn K
  | .inl b => blas1Fn b
  | .inr a => (mach K).fn a

/-- The queries: comparisons of cells and the conversion of a cell to an index. -/
abbrev Qry := CmpTst ⊕ IdxTst

/-- The Boolean of a comparison of cells. -/
def cmpTest : CmpTst → List (List K) → Option Bool
  | .lt, [[a], [b]] => some (Concrete.lt a b)
  | .le, [[a], [b]] => some (Concrete.le a b)
  | .eq, [[a], [b]] => some (Concrete.eq a b)
  | .isZero, [[a]] => some (Concrete.eq a default)
  | .isPos, [[a]] => some (Concrete.lt default a)
  | _, _ => none

/-- Compare the input cells and write the result as a literal zero or one. -/
def cmpOpFn : CmpOp → BlockFn K
  | .cmp c => {
      nd := 0
      inLens _ := c.lens
      outLens _ := [1]
      fn _ _ xs := (cmpTest c xs).map fun b => [[(mach K).lit (if b then 1 else 0)]] }

/-- Read a flag written by `cmpOpFn`, and delegate the remaining queries to `I`. -/
def withFlagTest {Op Tst : Type} [Has FlagTst Tst] (I : Interp Op Tst K) : Interp Op Tst K :=
  { I with test := fun q d a m =>
      match Has.proj (G := FlagTst) q with
      | some .isSet =>
        (m.readBlocks a [1]).map (FlagTst.fn fun x => Concrete.eq x ((mach K).lit 1))
      | none => I.test q d a m }

/-- **An interpretation given by block functions, with the queries.** -/
def withQueries {Op : Type} (F : Op → BlockFn K) : Interp Op Qry K where
  call o d ins outs τ m := (F o).apply d ins outs τ m
  test q _ a m := match q with
    | .inl c => (m.readBlocks a c.lens).bind (cmpTest c)
    | .inr _ => none
  index q a m := match q, a with
    | .inr .toNat, [x] => (m.store.get x.1 x.2).bind Concrete.toNat?
    | _, _ => none

/-- A deterministic tape of signs `±1`, from a linear congruential generator seeded by `seed`. -/
def signTape (seed : ℕ) : Tape K := fun p s =>
  let h := (seed * 6364136223846793005 + (p * 31 + s) * 1442695040888963407) % 2 ^ 64
  if (h / 2 ^ 33) % 2 = 0 then (mach K).lit 1 else (mach K).lit (-1)

/-- The tape whose entries in every stream are given by a list (zero after its end). -/
def listTape (xs : List K) : Tape K := fun p _ => xs.getD p ((mach K).lit 0)

/-! ### Memories -/

/-- A buffer holding the words `xs`. -/
def vals (xs : List K) : List (Option K) := xs.map some

/-- A buffer of `n` uninitialised cells. -/
def blank (n : ℕ) : List (Option K) := List.replicate n none

/-- The memory with the given buffers, at tape position zero. -/
def memOf (bufs : List (List (Option K))) : Mem K := ⟨bufs, 0⟩

/-- The environment of a procedure instance over whole buffers: the dimensions, then each
buffer variable bound to the buffer `b` at offset zero. -/
def frameOf (dims : List ℕ) (bufs : List ℕ) : Env := Env.frame dims (bufs.map fun b => (b, 0))

/-! ### Names of operations -/

/-- The name of an operation or a query in a report. -/
class ShowKey (α : Type) where
  /-- The name. -/
  showKey : α → String

instance (priority := low) {α : Type} [Repr α] : ShowKey α := ⟨fun a => reprStr a⟩

instance {α β : Type} [ShowKey α] [ShowKey β] : ShowKey (α ⊕ β) :=
  ⟨fun | .inl a => ShowKey.showKey a | .inr b => ShowKey.showKey b⟩

instance : ShowKey Empty := ⟨fun e => nomatch e⟩

instance : ShowKey ScalarOp := ⟨fun
  | .lit q => s!"lit {q}" | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div"
  | .neg => "neg" | .sqrt => "sqrt" | .copy => "copy"⟩

instance : ShowKey Blas1Op := ⟨fun
  | .sum => "sum" | .dot => "dot" | .axpy => "axpy" | .nrm2 => "nrm2" | .scal => "scal"
  | .copy => "vcopy"⟩

instance : ShowKey OperatorOp := ⟨fun | .matvec => "matvec"⟩

instance : ShowKey ROp := ⟨fun
  | .draw => "draw" | .gauss => "gauss" | .operator o => ShowKey.showKey o
  | .dot => "dot" | .add => "add"
  | .nrm2 => "nrm2" | .mulc q => s!"mulc {q}" | .axpy => "axpy"⟩

instance : ShowKey CmpTst := ⟨fun
  | .lt => "lt?" | .le => "le?" | .eq => "eq?" | .isZero => "isZero?" | .isPos => "isPos?"⟩

instance : ShowKey CmpOp := ⟨fun | .cmp c => s!"cmp {ShowKey.showKey c}"⟩

instance : ShowKey FlagTst := ⟨fun | .isSet => "isSet?"⟩

instance : ShowKey IdxTst := ⟨fun | .toNat => "toNat"⟩

end NLAlib.Ops.Tools
