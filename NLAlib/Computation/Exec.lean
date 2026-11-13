/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import NLAlib.Computation.Store
public import NLAlib.Computation.Syntax

/-!
# Running a program

The run `NLAlib.Computation.exec I s st` of a statement `s` (at `VB := ℕ`, `VI := ℕ`) from a
state `st` under an interpretation `I` is a deterministic function into `Option`: `none` marks a
failure (an operation outside its domain, an uninitialised read, an index out of bounds, a tag
mismatch, an invalid or aliased oracle call, running out of fuel). The interpretation holds the
value semantics of the scalar operations (`NLAlib.Computation.ScalarSem`), the charge of each
operation kind, the random tape of each distribution, the oracles, the read-only data and its
size, the width in bits of a cell of each tag, and the black-box kernels and their block shapes.
The state holds the store
(`NLAlib.Computation.Store`, a stack of tagged buffers of possibly uninitialised cells), the tape
positions, the counts, and the current and peak memory in cells per tag and in bits.

The run lemmas unfold `exec` one constructor at a time, and run a loop by an invariant and a
sequence of draws from the tape. The invariants of the run are the semantic facts the guarantees
of the access models rest on (`docs/design/Computation.md`, "Guarantees"). Design:
`docs/design/Computation.md` (D3, D8, D11, D12, D17).

## Main definitions

* `NLAlib.Computation.OpKind`, `NLAlib.Computation.OpCount`: operation kinds and counts.
* `NLAlib.Computation.OpKind.kernelWeight`: the weight of a kernel call by its largest
  dimension, for weighted kernel counts.
* `NLAlib.Computation.ScalarSem`: a value semantics; `NLAlib.Computation.Interp`: an
  interpretation.
* `NLAlib.Computation.St`: the state; `NLAlib.Computation.St.usage`: its tape positions, counts
  and memory.
* `NLAlib.Computation.Interp.kcallStore`: a black-box kernel call on contiguous blocks;
  `NLAlib.Computation.Interp.withKernel`: an interpretation with one kernel replaced.
* `NLAlib.Computation.toNatStep`: one conversion of a stored value to an index.
* `NLAlib.Computation.exec`: the run.
* `NLAlib.Computation.Stmt.StraightLine`: no `ite`, no `whileFuel` and no `bindIdx`.

## Main results

* `NLAlib.Computation.exec_seq`, `NLAlib.Computation.exec_loop`,
  `NLAlib.Computation.exec_alloc`: the run of a sequence, a loop (a fold) and an allocation.
* `NLAlib.Computation.exists_exec_loop_eq_some_of_forall`: a loop run by an invariant.
* `NLAlib.Computation.exec_forRange_draw`: a loop of draws writes consecutive tape values.
* `NLAlib.Computation.cnt_le_of_exec_eq_some`, `NLAlib.Computation.cur_eq_of_exec_eq_some`,
  `NLAlib.Computation.shape_eq_of_exec_eq_some`, `NLAlib.Computation.peak_le_of_exec_eq_some`:
  the counts and peaks of a run only grow, and it frees exactly what it allocates.
* `NLAlib.Computation.store_eq_of_exec_eq_some_of_cnt_le`,
  `NLAlib.Computation.pos_eq_of_exec_eq_some_of_cnt_le`: a run that charges nothing writes and
  draws nothing.
* `NLAlib.Computation.exec_eq_of_exec_eq_some_of_cnt_load_le`: a run that makes no oracle call is
  the same under any oracle.
* `NLAlib.Computation.usage_eq_of_exec_eq_some_of_straightLine`: two successful runs of a
  straight-line statement, under interpretations with the same charge and widths, from states
  with the same usage and store shape, end with the same usage.
-/

@[expose] public section

namespace NLAlib.Computation

/-! ### Counts and semantics -/

/-- The kinds of operations a run counts: binary and unary operations, literals, comparisons,
copies and conversions per tag, draws per tag and distribution, read-only reads per tag, the
loads and matrix-vector products of each oracle per tag, the calls of each kernel per tag and
dimensions, and the conversions of stored values to indices per tag. -/
inductive OpKind (P ι : Type) where
  /-- A binary operation at a tag. -/
  | bin (p : P) (b : BinOp)
  /-- A unary operation at a tag. -/
  | un (p : P) (u : UnOp)
  /-- A literal at a tag. -/
  | lit (p : P)
  /-- A comparison at a tag. -/
  | cmp (p : P)
  /-- A copy at a tag. -/
  | copy (p : P)
  /-- A draw at a tag from a distribution. -/
  | draw (p : P) (d : Dist)
  /-- A conversion from one tag to another. -/
  | convert (p q : P)
  /-- A read of the read-only data at a tag. -/
  | rom (p : P)
  /-- One oracle call at a tag (a load of the matrix). -/
  | load (p : P) (o : ι)
  /-- One matrix-vector product of an oracle call at a tag. -/
  | matvec (p : P) (o : ι)
  /-- One call of kernel `o` at a tag, at the dimensions `dims`: calls of different dimensions
  are different kinds, so a weighted total (flops) is `Finsupp.weight` of a function of the
  dimensions. -/
  | kcall (p : P) (o : ι) (dims : List ℕ)
  /-- One conversion of a stored value to a natural number (an index binder) at a tag. -/
  | toNat (p : P)

/-- Counts of operations: finitely supported functions on the kinds. A weighted total (flops, bit
operations) is Mathlib's `Finsupp.weight`. -/
abbrev OpCount (P ι : Type) := OpKind P ι →₀ ℕ

/-- **The kernel weight of an operation kind**: for a cost $T$ of a kernel call by its largest
dimension, a call of a kernel at the dimensions `ds` weighs $T(\max ds)$ (the largest dimension,
$0$ for no dimension), and every other kind weighs $0$. The weighted kernel count of a run is
`Finsupp.weight (OpKind.kernelWeight T)` of its count. -/
def OpKind.kernelWeight {P ι : Type} (T : ℕ → ℕ) : OpKind P ι → ℕ
  | .kcall _ _ ds => T (ds.foldr max 0)
  | _ => 0

/-- A value semantics over the carrier `K`: each scalar operation at a tag, partial (`none` marks
an operation outside its domain, such as a division by zero), and the conversion of a stored value
to a natural number that an index binder applies. -/
structure ScalarSem (P K : Type) where
  /-- The value of a rational literal. -/
  lit : P → ℚ → Option K
  /-- A binary operation. -/
  bin : P → BinOp → K → K → Option K
  /-- A unary operation. -/
  un : P → UnOp → K → Option K
  /-- A comparison. -/
  cmp : P → CmpOp → K → K → Option Bool
  /-- A conversion from one tag to another. -/
  convert : P → P → K → Option K
  /-- The conversion of a stored value to a natural number, for an index binder (by default
  none: every binder fails). The semantics of the library fail on a negative value (no clamping
  at $0$); the exactness of the conversion is the separate contract
  `NLAlib.Computation.IsExactToNat`. -/
  toNat : P → K → Option ℕ := fun _ _ => none

/-- The value of a closed index expression. -/
def IExp.eval : IExp ℕ → ℕ
  | .var v => v
  | .const n => n
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .mod a b => a.eval % b.eval

/-- The value of a variable. -/
@[simp] theorem IExp.eval_var (v : ℕ) : (IExp.var v).eval = v := rfl

/-- The value of a constant. -/
@[simp] theorem IExp.eval_const (n : ℕ) : (IExp.const n).eval = n := rfl

/-- The value of the numeral `0` (a case of `NLAlib.Computation.IExp.eval_ofNat`). -/
theorem IExp.eval_zero : (0 : IExp ℕ).eval = 0 := rfl

/-- The value of the numeral `1` (a case of `NLAlib.Computation.IExp.eval_ofNat`). -/
theorem IExp.eval_one : (1 : IExp ℕ).eval = 1 := rfl

/-- The value of a numeral; every numeral, $0$ and $1$ included, is a constant. -/
@[simp] theorem IExp.eval_ofNat (n : ℕ) :
    (no_index (OfNat.ofNat n : IExp ℕ)).eval = OfNat.ofNat n := rfl

/-- The value of a sum. -/
@[simp] theorem IExp.eval_add (a b : IExp ℕ) : (a + b).eval = a.eval + b.eval := rfl

/-- The value of a truncated difference. -/
@[simp] theorem IExp.eval_sub (a b : IExp ℕ) : (a - b).eval = a.eval - b.eval := rfl

/-- The value of a product. -/
@[simp] theorem IExp.eval_mul (a b : IExp ℕ) : (a * b).eval = a.eval * b.eval := rfl

/-- The value of a remainder. -/
@[simp] theorem IExp.eval_mod (a b : IExp ℕ) : (a % b).eval = a.eval % b.eval := rfl

/-- The value of a substituted index expression is its value in the environment of the values
of the substituted expressions. -/
theorem IExp.eval_subst {α : Type} (σ : α → IExp ℕ) (e : IExp α) :
    (e.subst σ).eval = e.evalIn fun v => (σ v).eval := by
  induction e <;> simp only [IExp.subst, IExp.evalIn, IExp.eval, *]

/-! ### States and interpretations -/

/-- The state of a run: the store, the tape position of each distribution, the counts, and the
current and peak memory, in cells per tag and in bits over all tags. -/
structure St (P K C : Type) where
  /-- The store. -/
  store : Store P K
  /-- The next tape position of each distribution. -/
  pos : Dist → ℕ
  /-- The counts. -/
  cnt : C
  /-- Current memory in cells, per tag. -/
  cur : P → ℕ
  /-- Peak memory in cells, per tag. -/
  peak : P → ℕ
  /-- Current memory in bits, over all tags. -/
  curW : ℕ
  /-- Peak memory in bits, over all tags. -/
  peakW : ℕ

/-- An interpretation: the value semantics, the charge of each kind, the tapes, the oracles
(partial: `none` marks an invalid query), their heights, the read-only data, its size per tag, the
width in bits of a cell of each tag, and the black-box kernels with their block shapes (by default
none: every kernel call fails). -/
structure Interp (P ι K C : Type) where
  /-- The value semantics. -/
  sem : ScalarSem P K
  /-- The charge of one operation of each kind. -/
  charge : OpKind P ι → C
  /-- The tape of each distribution. -/
  tape : Dist → ℕ → K
  /-- The oracles: a block of `cols` columns, stored column-major, to its product. -/
  oracle : ι → ℕ → Array K → Option (Array K)
  /-- The number of rows of the matrix of each oracle. -/
  height : ι → ℕ
  /-- The read-only data. -/
  rom : ℕ → Option K
  /-- The size of the read-only data per tag: constant memory. -/
  romSize : P → ℕ
  /-- Bits per cell at each tag (for memory in bits). -/
  width : P → ℕ
  /-- The kernels: at the dimensions, the input blocks to the output blocks (partial: `none`
  marks an invalid call). -/
  kernel : ι → List ℕ → List (Array K) → Option (List (Array K)) := fun _ _ _ => none
  /-- The shape of each kernel at the dimensions: the lengths of its input blocks and of its
  output blocks. -/
  kshape : ι → List ℕ → List ℕ × List ℕ := fun _ _ => ([], [])

/-- An interpretation charges one occurrence of each operation kind to that kind's own
counter. Scalar semantics, word representation and oracle behavior are independent of this
accounting interface. It is exactly the pointwise equation used by the standard charge.
No printed source. -/
def IsUnitCharge {P ι K : Type} (I : Interp P ι K (OpCount P ι)) : Prop :=
  ∀ k, I.charge k = Finsupp.single k 1

/-- The unit-charge interface gives the function equality used to instantiate a static count
summary. No assumption about scalar exactness or execution success is needed. -/
theorem IsUnitCharge.charge_eq {P ι K : Type} {I : Interp P ι K (OpCount P ι)}
    (h : IsUnitCharge I) : I.charge = fun k => Finsupp.single k 1 :=
  funext h

section Exec

variable {P ι K C : Type} [DecidableEq P]

/-- The kind of an instruction, independent of the interpretation. -/
def Instr.kind {ι : Type} : Instr P ℕ ℕ → OpKind P ι
  | .lit p _ _ => .lit p
  | .litIdx p _ _ => .lit p
  | .bin p b _ _ _ => .bin p b
  | .un p u _ _ => .un p u
  | .copy p _ _ => .copy p
  | .draw p d _ => .draw p d
  | .convert p q _ _ => .convert p q

/-- One instruction on the store and the tape positions. -/
def Instr.run (sem : ScalarSem P K) (tape : Dist → ℕ → K) (s : Store P K) (pos : Dist → ℕ) :
    Instr P ℕ ℕ → Option (Store P K × (Dist → ℕ))
  | .lit p dst q => (sem.lit p q).bind fun v =>
      (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .litIdx p dst e => (sem.lit p (e.eval : ℚ)).bind fun v =>
      (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .bin p b dst x y => (s.read p x.buf x.idx.eval).bind fun a =>
      (s.read p y.buf y.idx.eval).bind fun c => (sem.bin p b a c).bind fun v =>
        (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .un p u dst x => (s.read p x.buf x.idx.eval).bind fun a => (sem.un p u a).bind fun v =>
      (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .copy p dst src => (s.read p src.buf src.idx.eval).bind fun v =>
      (s.write p dst.buf dst.idx.eval v).map fun s' => (s', pos)
  | .draw p d dst => (s.write p dst.buf dst.idx.eval (tape d (pos d))).map fun s' =>
      (s', Function.update pos d (pos d + 1))
  | .convert p q dst src => (s.read p src.buf src.idx.eval).bind fun a =>
      (sem.convert p q a).bind fun v =>
        (s.write q dst.buf dst.idx.eval v).map fun s' => (s', pos)

/-- Two blocks `(handle, offset, length)` are disjoint: they lie in different buffers or their
ranges of cells do not overlap. An empty block is disjoint from every block. -/
def blockDisjoint (x y : ℕ × ℕ × ℕ) : Bool :=
  x.1 != y.1 || decide (x.2.2 = 0) || decide (y.2.2 = 0) ||
    decide (x.2.1 + x.2.2 ≤ y.2.1) || decide (y.2.1 + y.2.2 ≤ x.2.1)

/-- The block-disjointness test is exact: it returns true precisely when no cell index belongs
to both blocks in the same buffer. This includes blocks of length zero at any offset. -/
theorem blockDisjoint_eq_true_iff (x y : ℕ × ℕ × ℕ) :
    blockDisjoint x y = true ↔
      ∀ i : ℕ, ¬ (x.1 = y.1 ∧ x.2.1 ≤ i ∧ i < x.2.1 + x.2.2 ∧
        y.2.1 ≤ i ∧ i < y.2.1 + y.2.2) := by
  simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h i
    omega
  · intro h
    have hx := h x.2.1
    have hy := h y.2.1
    omega

/-- Distinct handles or separated endpoints suffice for two blocks to be disjoint, at any
length. -/
theorem blockDisjoint_of_ne_or_le {x y : ℕ × ℕ × ℕ}
    (h : x.1 ≠ y.1 ∨ x.2.1 + x.2.2 ≤ y.2.1 ∨ y.2.1 + y.2.2 ≤ x.2.1) :
    blockDisjoint x y = true := by
  apply (blockDisjoint_eq_true_iff x y).2
  intro i
  omega

/-- The blocks of the operands `(handle, offset)` of a kernel call with the lengths `lens`. -/
def kcallBlocks (bs : List (ℕ × ℕ)) (lens : List ℕ) : List (ℕ × ℕ × ℕ) :=
  List.zipWith (fun b l => (b.1, b.2, l)) bs lens

/-- **A kernel call on the store**: kernel `o` of `I` at the dimensions `ds` reads the input
blocks at the operands `ins` and writes its output blocks at the operands `outs`, each operand a
`(handle, offset)` and each block as long as the shape `I.kshape o ds` says, all at tag `p`. It
fails if the numbers of operands are not those of the shape, if two output blocks overlap or an
output block overlaps an input block (an aliased call), if a read or a write fails, if the kernel
fails, or if it returns blocks of other lengths. -/
def Interp.kcallStore (I : Interp P ι K C) (o : ι) (p : P) (ds : List ℕ)
    (ins outs : List (ℕ × ℕ)) (s : Store P K) : Option (Store P K) :=
  if ins.length = (I.kshape o ds).1.length ∧ outs.length = (I.kshape o ds).2.length ∧
      (kcallBlocks outs (I.kshape o ds).2).Pairwise (fun x y => blockDisjoint x y = true) ∧
      ∀ x ∈ kcallBlocks outs (I.kshape o ds).2, ∀ y ∈ kcallBlocks ins (I.kshape o ds).1,
        blockDisjoint x y = true then
    (s.readBlocks p (kcallBlocks ins (I.kshape o ds).1)).bind fun xs =>
      (I.kernel o ds xs).bind fun ys => s.writeBlocks p (kcallBlocks outs (I.kshape o ds).2) ys
  else none

omit [DecidableEq P] in
/-- The interpretation `I` with kernel `o` replaced by `k`, of block shape `sh`; every other field
of `I` and every other kernel kept. -/
def Interp.withKernel [DecidableEq ι] (I : Interp P ι K C) (o : ι)
    (k : List ℕ → List (Array K) → Option (List (Array K))) (sh : List ℕ → List ℕ × List ℕ) :
    Interp P ι K C :=
  { I with kernel := Function.update I.kernel o k, kshape := Function.update I.kshape o sh }

variable [AddMonoid C] (I : Interp P ι K C)

/-- One comparison: the outcome and the charged state. -/
def cmpStep (p : P) (c : CmpOp) (x y : Cell ℕ ℕ) (st : St P K C) : Option (Bool × St P K C) :=
  (st.store.read p x.buf x.idx.eval).bind fun a => (st.store.read p y.buf y.idx.eval).bind
    fun b => (I.sem.cmp p c a b).map fun r => (r, { st with cnt := st.cnt + I.charge (.cmp p) })

/-- One conversion of a stored value to an index: the cell `x` read at tag `p` and converted by the
semantics, with the charged state. -/
def toNatStep (p : P) (x : Cell ℕ ℕ) (st : St P K C) : Option (ℕ × St P K C) :=
  (st.store.read p x.buf x.idx.eval).bind fun v => (I.sem.toNat p v).map fun k =>
    (k, { st with cnt := st.cnt + I.charge (.toNat p) })

/-- **The run** of a statement under an interpretation. An allocation pushes a fresh buffer of
uninitialised cells, raises the current and peak memory, runs the body with the new buffer's
handle (its position in the stack) and pops the buffer. An oracle call reads the source block,
charges one load and one matrix-vector product per column, and writes the product; it fails if
the source and destination blocks overlap (an aliased call, which no implementation with bounded
scratch can serve). A kernel call runs `NLAlib.Computation.Interp.kcallStore` and charges one call
of its kind at its dimensions. An index binder converts the value of its cell
(`NLAlib.Computation.toNatStep`, one charged conversion) and runs its body at that value; it fails
if the value exceeds its bound (no clamping: a corrupt size is a failure of the run). -/
def exec : Stmt P ι ℕ ℕ → St P K C → Option (St P K C)
  | .skip, st => some st
  | .seq s t, st => (exec s st).bind (exec t)
  | .instr i, st => (i.run I.sem I.tape st.store st.pos).map fun r =>
      { st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i.kind }
  | .apply o p dst dOff src sOff cols, st =>
      if dst ≠ src ∨ dOff.eval + I.height o * cols.eval ≤ sOff.eval ∨
          sOff.eval + I.height o * cols.eval ≤ dOff.eval then
        (st.store.readBlock p src sOff.eval (I.height o * cols.eval)).bind fun X =>
          (I.oracle o cols.eval X).bind fun Y => (st.store.writeBlock p dst dOff.eval Y).map
            fun s => { st with
              store := s
              cnt := st.cnt + (I.charge (.load p o) + cols.eval • I.charge (.matvec p o)) }
      else none
  | .rom p dst i, st => (I.rom i.eval).bind fun v =>
      (st.store.write p dst.buf dst.idx.eval v).map fun s =>
        { st with
          store := s
          cnt := st.cnt + I.charge (.rom p) }
  | .alloc p len body, st =>
      (exec (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) }).map
        fun st₂ => { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p }
  | .loop n body, st => (List.range n.eval).foldlM (fun st i => exec (body i) st) st
  | .whileFuel fuel p c x y body, st =>
      ((List.range fuel.eval).foldlM (fun (s : St P K C × Bool) _ =>
        if s.2 then (cmpStep I p c x y s.1).bind fun r =>
          if r.1 then (exec body r.2).map fun st' => (st', true) else some (r.2, false)
        else some s) (st, true)).bind fun r => if r.2 then none else some r.1
  | .ite p c x y t e, st => (cmpStep I p c x y st).bind fun r =>
      if r.1 then exec t r.2 else exec e r.2
  | .named _ _ body, st => exec body st
  | .kcall o p dims ins outs, st =>
      (I.kcallStore o p (dims.map IExp.eval) (ins.map fun x => (x.1, x.2.eval))
        (outs.map fun x => (x.1, x.2.eval)) st.store).map fun s =>
          { st with store := s, cnt := st.cnt + I.charge (.kcall p o (dims.map IExp.eval)) }
  | .bindIdx p x bound body, st => (toNatStep I p x st).bind fun r =>
      if r.1 ≤ bound.eval then exec (body r.1) r.2 else none

/-! ### Run lemmas -/

/-- The run of a sequence. -/
theorem exec_seq (s t : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.seq s t) st = (exec I s st).bind (exec I t) := by
  rw [exec]

/-- The run of a loop is a fold over the indices. -/
theorem exec_loop (n : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.loop n body) st = (List.range n.eval).foldlM (fun st i => exec I (body i) st) st := by
  rw [exec]

/-- The run of an index binder: the converted value of its cell is bound for the body if it is at
most the bound, and the run fails otherwise. -/
theorem exec_bindIdx (p : P) (x : Cell ℕ ℕ) (bound : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ)
    (st : St P K C) :
    exec I (.bindIdx p x bound body) st =
      (toNatStep I p x st).bind fun r =>
        if r.1 ≤ bound.eval then exec I (body r.1) r.2 else none := by
  rw [exec]

/-- The run of a named kernel is the run of its body. -/
theorem exec_named (name : String) (args : List (Arg ℕ ℕ)) (body : Stmt P ι ℕ ℕ)
    (st : St P K C) : exec I (.named name args body) st = exec I body st := by
  rw [exec]

/-- The run of an allocation: push a fresh buffer, run the body on its handle, pop it. -/
theorem exec_alloc (p : P) (len : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.alloc p len body) st =
      (exec I (body st.store.size) { st with
          store := st.store.push (p, Array.replicate len.eval none),
          cur := Function.update st.cur p (st.cur p + len.eval),
          peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval)),
          curW := st.curW + len.eval * I.width p,
          peakW := max st.peakW (st.curW + len.eval * I.width p) }).map
        fun st₂ => { st₂ with
          store := Array.pop st₂.store
          cur := Function.update st₂.cur p (st₂.cur p - len.eval)
          curW := st₂.curW - len.eval * I.width p } := by
  rw [exec]

/-- The run of a conditional. -/
theorem exec_ite (p : P) (c : CmpOp) (x y : Cell ℕ ℕ) (t e : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.ite p c x y t e) st =
      (cmpStep I p c x y st).bind fun r => if r.1 then exec I t r.2 else exec I e r.2 := by
  rw [exec]

/-- The run of a scalar instruction. -/
theorem exec_instr (i : Instr P ℕ ℕ) (st : St P K C) :
    exec I (.instr i) st = (i.run I.sem I.tape st.store st.pos).map fun r =>
      { st with store := r.1, pos := r.2, cnt := st.cnt + I.charge i.kind } := by
  rw [exec]

/-- The run of a statement followed by `skip` is the run of the statement. -/
theorem exec_seq_skip (s : Stmt P ι ℕ ℕ) (st : St P K C) :
    exec I (.seq s .skip) st = exec I s st := by
  rw [exec_seq]
  rcases exec I s st with _ | st'
  · rfl
  · change exec I .skip st' = some st'
    rw [exec]

/-- The run of a sequence whose first part succeeds: the run of the second part from there. -/
theorem exec_seq_of_exec_eq_some {s t : Stmt P ι ℕ ℕ} {st st₁ : St P K C}
    (h : exec I s st = some st₁) : exec I (.seq s t) st = exec I t st₁ := by
  rw [exec_seq, h, Option.bind_some]

/-- The run of a builder that emits one statement before its continuation (a kernel, a loop, a
conditional, a block), followed by `f`: the run of the first, then the run of `f`. -/
theorem exec_run_bind {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    (hb : ∀ k, ContT.run b k = .seq X (k ())) (f : Unit → Builder P ι ℕ ℕ Unit)
    (st : St P K C) : exec I (b >>= f).run st = (exec I b.run st).bind (exec I (f ()).run) := by
  have h1 : (b >>= f).run = .seq X (f ()).run := hb _
  have h2 : b.run = .seq X .skip := hb _
  rw [h1, h2, exec_seq, exec_seq_skip]

/-- A loop invariant: if `R 0` holds at the start and, for each index `i` below the bound,
the body run from a state satisfying `R i` succeeds in a state satisfying `R (i + 1)`, the loop
succeeds in a state satisfying `R n`. -/
theorem exists_exec_loop_eq_some_of_forall {n : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ}
    {st : St P K C} (R : ℕ → St P K C → Prop) (h0 : R 0 st)
    (hstep : ∀ i < n.eval, ∀ st, R i st → ∃ st', exec I (body i) st = some st' ∧ R (i + 1) st') :
    ∃ st', exec I (.loop n body) st = some st' ∧ R n.eval st' := by
  rw [exec_loop]
  generalize n.eval = m at hstep ⊢
  induction m with
  | zero => exact ⟨st, rfl, h0⟩
  | succ m ih =>
    obtain ⟨st₁, h₁, hR₁⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    obtain ⟨st₂, h₂, hR₂⟩ := hstep m (Nat.lt_succ_self m) st₁ hR₁
    refine ⟨st₂, ?_, hR₂⟩
    rw [List.range_succ, List.foldlM_append, h₁]
    simpa using h₂

/-- The run of `skip`. -/
theorem exec_skip (st : St P K C) : exec I .skip st = some st := by
  rw [exec]

/-- The run of a literal, then the rest. -/
theorem exec_seq_instr_lit {p : P} {dst : Cell ℕ ℕ} {q : ℚ} {t : Stmt P ι ℕ ℕ} {st : St P K C}
    {v : K} {s : Store P K} (hv : I.sem.lit p q = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.lit p dst q)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.lit p) } := by
  simp [exec_seq, exec_instr, Instr.run, hv, hw, Instr.kind]

/-- The run of an index literal, then the rest. -/
theorem exec_seq_instr_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {st : St P K C} {v : K} {s : Store P K} (hv : I.sem.lit p (e.eval : ℚ) = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.litIdx p dst e)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.lit p) } := by
  simp [exec_seq, exec_instr, Instr.run, hv, hw, Instr.kind]

/-- The run of a binary operation, then the rest. -/
theorem exec_seq_instr_bin {p : P} {b : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {st : St P K C} {a c v : K} {s : Store P K}
    (hx : st.store.read p x.buf x.idx.eval = some a)
    (hy : st.store.read p y.buf y.idx.eval = some c) (hv : I.sem.bin p b a c = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.bin p b dst x y)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.bin p b) } := by
  simp [exec_seq, exec_instr, Instr.run, hx, hy, hv, hw, Instr.kind]

/-- The run of a unary operation, then the rest. -/
theorem exec_seq_instr_un {p : P} {u : UnOp} {dst x : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {st : St P K C} {a v : K} {s : Store P K} (hx : st.store.read p x.buf x.idx.eval = some a)
    (hv : I.sem.un p u a = some v) (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.un p u dst x)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.un p u) } := by
  simp [exec_seq, exec_instr, Instr.run, hx, hv, hw, Instr.kind]

/-- The run of a copy, then the rest. -/
theorem exec_seq_instr_copy {p : P} {dst src : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ} {st : St P K C}
    {v : K} {s : Store P K} (hx : st.store.read p src.buf src.idx.eval = some v)
    (hw : st.store.write p dst.buf dst.idx.eval v = some s) :
    exec I (.seq (.instr (.copy p dst src)) t) st =
      exec I t { st with store := s, cnt := st.cnt + I.charge (.copy p) } := by
  simp [exec_seq, exec_instr, Instr.run, hx, hw, Instr.kind]

/-- The run of a draw, then the rest: the next tape value, and the tape position advances. -/
theorem exec_seq_instr_draw {p : P} {d : Dist} {dst : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {st : St P K C} {s : Store P K}
    (hw : st.store.write p dst.buf dst.idx.eval (I.tape d (st.pos d)) = some s) :
    exec I (.seq (.instr (.draw p d dst)) t) st =
      exec I t { st with
        store := s
        pos := Function.update st.pos d (st.pos d + 1)
        cnt := st.cnt + I.charge (.draw p d) } := by
  simp [exec_seq, exec_instr, Instr.run, hw, Instr.kind]

/-- A loop of draws writes consecutive tape values: the loop that draws cell `idx i` of
buffer `X` from the tape of `d`, where `idx i` evaluates to $\mathit{off} + i$, for $i < n$,
succeeds from a state in which each of these cells can be written; cell $\mathit{off} + i$ then
holds the tape value at position $\mathit{pos}(d) + i$, every other cell, the shape and the
memory are kept, the tape position of `d` advances by $n$, and the run counts $n$ draws. -/
theorem exec_forRange_draw (p : P) (d : Dist) (X off : ℕ) (n : IExp ℕ) (idx : ℕ → IExp ℕ)
    (hidx : ∀ i, (idx i).eval = off + i) (st : St P K C)
    (hw : ∀ i < n.eval, ∃ v s, st.store.write p X (off + i) v = some s) :
    ∃ st', exec I (Builder.forRange n fun i => Builder.ins (.draw p d ⟨X, idx i⟩)).run st =
        some st' ∧
      (∀ i < n.eval, st'.store.read p X (off + i) = some (I.tape d (st.pos d + i))) ∧
      (∀ q b j, (b = X → j < off ∨ off + n.eval ≤ j) →
        st'.store.read q b j = st.store.read q b j) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos d (st.pos d + n.eval) ∧
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW ∧
      st'.cnt = st.cnt + n.eval • I.charge (.draw p d) := by
  rw [show (Builder.forRange (ι := ι) n fun i => Builder.ins (.draw p d ⟨X, idx i⟩)).run =
    .seq (.loop n fun i => (Builder.ins (.draw p d ⟨X, idx i⟩)).run) .skip from rfl,
    exec_seq_skip]
  refine exists_exec_loop_eq_some_of_forall I (fun i st' =>
      (∀ i' < i, st'.store.read p X (off + i') = some (I.tape d (st.pos d + i'))) ∧
      (∀ q b j, (b = X → j < off ∨ off + i ≤ j) → st'.store.read q b j = st.store.read q b j) ∧
      st'.store.shape = st.store.shape ∧
      st'.pos = Function.update st.pos d (st.pos d + i) ∧
      st'.cur = st.cur ∧ st'.peak = st.peak ∧ st'.curW = st.curW ∧ st'.peakW = st.peakW ∧
      st'.cnt = st.cnt + i • I.charge (.draw p d))
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl, rfl, by simp, rfl, rfl, rfl,
      rfl, by simp⟩ ?_
  intro i hi st' ⟨hrd, hfr, hsh, hpos, hcur, hpeak, hcurW, hpeakW, hcnt⟩
  obtain ⟨v₀, s₀, hs₀⟩ := hw i hi
  obtain ⟨s, hs⟩ := Store.exists_write_eq_some_of_shape_eq hsh hs₀ (I.tape d (st'.pos d))
  have hpd : st'.pos d = st.pos d + i := by rw [hpos]; simp
  refine ⟨_, (exec_seq_instr_draw I (by rw [hidx]; exact hs)).trans (exec_skip I _),
    fun i' hi' => ?_, fun q b j hb => ?_, ?_, ?_, hcur, hpeak, hcurW, hpeakW, ?_⟩
  · change s.read p X (off + i') = _
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h | rfl
    · rw [Store.read_of_write_eq_some_of_ne hs (Or.inr (by omega)), hrd i' h]
    · rw [Store.read_of_write_eq_some hs, hpd]
  · change s.read q b j = _
    rw [Store.read_of_write_eq_some_of_ne hs ?_, hfr q b j ?_]
    · intro h; rcases hb h with h' | h' <;> omega
    · by_cases h : b = X
      · exact Or.inr (by rcases hb h with h' | h' <;> omega)
      · exact Or.inl h
  · exact (Store.shape_of_write_eq_some hs).trans hsh
  · change Function.update st'.pos d (st'.pos d + 1) = _
    rw [hpd, hpos, Function.update_idem, Nat.add_assoc]
  · change st'.cnt + I.charge (.draw p d) = _
    rw [hcnt, succ_nsmul, add_assoc]

end Exec

/-! ### Invariants of the run

What every successful run keeps or raises, whatever the statement: the counts only grow, the
current memory (in cells and in bits) and the shape of the store come back to their values at the
start (every allocation is freed, and nothing else is), and the peaks only grow. With every charge
nonzero, a run that charges nothing changes neither the store nor the tape positions: every write
and every draw is charged. With the standard charge, a run that makes no oracle call is the same
for every oracle. -/

section Invariants

variable {P ι K : Type} [DecidableEq P]

/-- A scalar instruction keeps the shape of the store. -/
theorem Instr.shape_of_run_eq_some {sem : ScalarSem P K} {tape : Dist → ℕ → K} {s : Store P K}
    {pos : Dist → ℕ} {i : Instr P ℕ ℕ} {r : Store P K × (Dist → ℕ)}
    (h : i.run sem tape s pos = some r) : r.1.shape = s.shape := by
  cases i <;> simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  · obtain ⟨_, -, s', hw, rfl⟩ := h; exact Store.shape_of_write_eq_some hw
  · obtain ⟨_, -, s', hw, rfl⟩ := h; exact Store.shape_of_write_eq_some hw
  · obtain ⟨_, -, _, -, _, -, s', hw, rfl⟩ := h; exact Store.shape_of_write_eq_some hw
  · obtain ⟨_, -, _, -, s', hw, rfl⟩ := h; exact Store.shape_of_write_eq_some hw
  · obtain ⟨_, -, s', hw, rfl⟩ := h; exact Store.shape_of_write_eq_some hw
  · obtain ⟨s', hw, rfl⟩ := h; exact Store.shape_of_write_eq_some hw
  · obtain ⟨_, -, _, -, s', hw, rfl⟩ := h; exact Store.shape_of_write_eq_some hw

/-- A comparison step charges one comparison and changes nothing else. -/
theorem snd_of_cmpStep_eq_some {C : Type} [AddMonoid C] {I : Interp P ι K C} {p : P} {c : CmpOp}
    {x y : Cell ℕ ℕ} {st : St P K C} {r : Bool × St P K C} (h : cmpStep I p c x y st = some r) :
    r.2 = { st with cnt := st.cnt + I.charge (.cmp p) } := by
  simp only [cmpStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, rfl⟩ := h
  rfl

/-- A conversion step charges one conversion and changes nothing else. -/
theorem snd_of_toNatStep_eq_some {C : Type} [AddMonoid C] {I : Interp P ι K C} {p : P}
    {x : Cell ℕ ℕ} {st : St P K C} {r : ℕ × St P K C} (h : toNatStep I p x st = some r) :
    r.2 = { st with cnt := st.cnt + I.charge (.toNat p) } := by
  simp only [toNatStep, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, rfl⟩ := h
  rfl

/-- A kernel call keeps the shape of the store. -/
theorem Interp.shape_of_kcallStore_eq_some {C : Type} {I : Interp P ι K C} {o : ι} {p : P}
    {ds : List ℕ} {ins outs : List (ℕ × ℕ)} {s s' : Store P K}
    (h : I.kcallStore o p ds ins outs s = some s') : s'.shape = s.shape := by
  unfold Interp.kcallStore at h
  split_ifs at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  exact Store.shape_of_writeBlocks_eq_some h

variable (I : Interp P ι K (OpCount P ι))

/-- What a run keeps or raises (the proof of the invariants). -/
private structure RunInv (st st' : St P K (OpCount P ι)) : Prop where
  cnt : st.cnt ≤ st'.cnt
  cur : st'.cur = st.cur
  curW : st'.curW = st.curW
  shape : st'.store.shape = st.store.shape
  peak : st.peak ≤ st'.peak
  peakW : st.peakW ≤ st'.peakW
  idle : (∀ k, I.charge k ≠ 0) → st'.cnt ≤ st.cnt → st'.store = st.store ∧ st'.pos = st.pos

omit [DecidableEq P] in
private theorem RunInv.refl (st : St P K (OpCount P ι)) : RunInv I st st :=
  ⟨le_rfl, rfl, rfl, rfl, le_rfl, le_rfl, fun _ _ => ⟨rfl, rfl⟩⟩

omit [DecidableEq P] in
private theorem RunInv.trans {a b c : St P K (OpCount P ι)} (hab : RunInv I a b)
    (hbc : RunInv I b c) : RunInv I a c where
  cnt := hab.cnt.trans hbc.cnt
  cur := hbc.cur.trans hab.cur
  curW := hbc.curW.trans hab.curW
  shape := hbc.shape.trans hab.shape
  peak := hab.peak.trans hbc.peak
  peakW := hab.peakW.trans hbc.peakW
  idle hc h := by
    obtain ⟨h1, h2⟩ := hab.idle hc (hbc.cnt.trans h)
    obtain ⟨h3, h4⟩ := hbc.idle hc (h.trans hab.cnt)
    exact ⟨h3.trans h1, h4.trans h2⟩

omit [DecidableEq P] in
/-- One charged step that writes a store of the same shape. -/
private theorem RunInv.step {st : St P K (OpCount P ι)} {s : Store P K} {pos : Dist → ℕ}
    {c : OpCount P ι} (hs : s.shape = st.store.shape) (hc : (∀ k, I.charge k ≠ 0) → c ≠ 0) :
    RunInv I st { st with store := s, pos := pos, cnt := st.cnt + c } where
  cnt := le_self_add
  cur := rfl
  curW := rfl
  shape := hs
  peak := le_rfl
  peakW := le_rfl
  idle h hle := absurd (le_antisymm ((add_le_iff_nonpos_right _).mp hle) zero_le) (hc h)

omit [DecidableEq P] in
/-- A fold of steps that each keep the invariant keeps it. -/
private theorem RunInv.foldlM {σ α : Type} (π : σ → St P K (OpCount P ι))
    {f : σ → α → Option σ} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ a b, f a x = some b → RunInv I (π a) (π b)) →
    ∀ {a b : σ}, l.foldlM f a = some b → RunInv I (π a) (π b)
  | [], _, a, b, h => by cases h; exact RunInv.refl I _
  | x :: l, hf, a, b, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨a', h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (hf x List.mem_cons_self a a' h1).trans I
      (RunInv.foldlM π (fun y hy => hf y (List.mem_cons_of_mem x hy)) h2)

private theorem runInv_kcall (o : ι) (p : P) (dims : List (IExp ℕ))
    (ins outs : List (ℕ × IExp ℕ)) {st st' : St P K (OpCount P ι)}
    (h : exec I (.kcall o p dims ins outs) st = some st') :
    RunInv I st st' := by
  rw [exec] at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact RunInv.step I (Interp.shape_of_kcallStore_eq_some hs) fun hc => hc _

private theorem runInv_bindIdx (p : P) (x : Cell ℕ ℕ) (bound : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ)
    (ih : ∀ v {st st' : St P K (OpCount P ι)}, exec I (body v) st = some st' → RunInv I st st')
    {st st' : St P K (OpCount P ι)} (h : exec I (.bindIdx p x bound body) st = some st') :
    RunInv I st st' := by
  rw [exec_bindIdx] at h
  obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
  have hstep : RunInv I st r.2 := by
    rw [snd_of_toNatStep_eq_some hr]
    exact RunInv.step I (pos := st.pos) rfl fun hc => hc _
  split_ifs at h2
  exact hstep.trans I (ih _ h2)

private theorem runInv_of_exec_eq_some : ∀ (s : Stmt P ι ℕ ℕ) {st st' : St P K (OpCount P ι)},
    exec I s st = some st' → RunInv I st st'
  | .skip, st, st', h => by rw [exec_skip] at h; cases h; exact RunInv.refl I _
  | .seq s t, st, st', h => by
    rw [exec_seq] at h
    obtain ⟨st₁, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (runInv_of_exec_eq_some s h1).trans I (runInv_of_exec_eq_some t h2)
  | .instr i, st, st', h => by
    rw [exec_instr] at h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    exact RunInv.step I (Instr.shape_of_run_eq_some hr) fun hc => hc _
  | .apply o p dst dOff src sOff cols, st, st', h => by
    rw [exec] at h
    split_ifs at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, -, _, -, s, hs, rfl⟩ := h
    exact RunInv.step I (Store.shape_of_writeBlock_eq_some hs) fun hc h0 =>
      hc (.load p o) (add_eq_zero.mp h0).1
  | .rom p dst i, st, st', h => by
    rw [exec] at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, -, s, hs, rfl⟩ := h
    exact RunInv.step I (Store.shape_of_write_eq_some hs) fun hc => hc _
  | .alloc p len body, st, st', h => by
    rw [exec_alloc] at h
    obtain ⟨st₂, h2, rfl⟩ := Option.map_eq_some_iff.mp h
    have hi := runInv_of_exec_eq_some (body st.store.size) h2
    have hcur := hi.cur
    have hcurW := hi.curW
    simp only at hcur hcurW
    refine ⟨hi.cnt, ?_, ?_, ?_, ?_, ?_, fun hc hle => ?_⟩
    · change Function.update st₂.cur p (st₂.cur p - len.eval) = st.cur
      rw [hcur, Function.update_self, Nat.add_sub_cancel, Function.update_idem,
        Function.update_eq_self]
    · change st₂.curW - len.eval * I.width p = st.curW
      rw [hcurW, Nat.add_sub_cancel]
    · change Store.shape (Array.pop st₂.store) = st.store.shape
      rw [Store.shape_pop, hi.shape]
      simp [Store.shape]
    · refine le_trans (fun q => ?_) hi.peak
      by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq]
    · exact le_trans (le_max_left _ _) hi.peakW
    · obtain ⟨hs, hp⟩ := hi.idle hc hle
      refine ⟨?_, hp⟩
      change Array.pop st₂.store = st.store
      rw [hs]
      exact Array.pop_push
  | .loop n body, st, st', h => by
    rw [exec_loop] at h
    exact RunInv.foldlM I id (fun i _ a b hb => runInv_of_exec_eq_some (body i) hb) h
  | .whileFuel fuel p c x y body, st, st', h => by
    rw [exec] at h
    obtain ⟨r, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h2
    cases h2
    refine RunInv.foldlM I Prod.fst (fun _ _ a b hb => ?_) h1
    split_ifs at hb
    · obtain ⟨r', hr', hb⟩ := Option.bind_eq_some_iff.mp hb
      have hstep : RunInv I a.1 r'.2 := by
        rw [snd_of_cmpStep_eq_some hr']
        exact RunInv.step I (pos := a.1.pos) rfl fun hc => hc _
      split_ifs at hb
      · obtain ⟨st₁, h3, rfl⟩ := Option.map_eq_some_iff.mp hb
        exact hstep.trans I (runInv_of_exec_eq_some body h3)
      · cases hb; exact hstep
    · cases hb; exact RunInv.refl I _
  | .ite p c x y t e, st, st', h => by
    rw [exec_ite] at h
    obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
    have hstep : RunInv I st r.2 := by
      rw [snd_of_cmpStep_eq_some hr]
      exact RunInv.step I (pos := st.pos) rfl fun hc => hc _
    split_ifs at h2
    · exact hstep.trans I (runInv_of_exec_eq_some t h2)
    · exact hstep.trans I (runInv_of_exec_eq_some e h2)
  | .named _ _ body, st, st', h => by
    rw [exec_named] at h
    exact runInv_of_exec_eq_some body h
  | .kcall o p dims ins outs, st, st', h => runInv_kcall I o p dims ins outs h
  | .bindIdx p x bound body, st, st', h =>
    runInv_bindIdx I p x bound body (fun v _ _ hv => runInv_of_exec_eq_some (body v) hv) h

variable {I} {s : Stmt P ι ℕ ℕ} {st st' : St P K (OpCount P ι)}

/-- The counts of a run only grow. -/
theorem cnt_le_of_exec_eq_some (h : exec I s st = some st') : st.cnt ≤ st'.cnt :=
  (runInv_of_exec_eq_some I s h).cnt

/-- Every allocation is freed: a run ends with the current memory in cells, at every tag, of
its start. -/
theorem cur_eq_of_exec_eq_some (h : exec I s st = some st') : st'.cur = st.cur :=
  (runInv_of_exec_eq_some I s h).cur

/-- A run ends with the current memory in bits of its start. -/
theorem curW_eq_of_exec_eq_some (h : exec I s st = some st') : st'.curW = st.curW :=
  (runInv_of_exec_eq_some I s h).curW

/-- A run frees exactly what it allocates: it ends with the shape of the store (the tag and
length of every buffer) of its start. -/
theorem shape_eq_of_exec_eq_some (h : exec I s st = some st') :
    st'.store.shape = st.store.shape :=
  (runInv_of_exec_eq_some I s h).shape

/-- The peak memory in cells of a run only grows. -/
theorem peak_le_of_exec_eq_some (h : exec I s st = some st') : st.peak ≤ st'.peak :=
  (runInv_of_exec_eq_some I s h).peak

/-- The peak memory in bits of a run only grows. -/
theorem peakW_le_of_exec_eq_some (h : exec I s st = some st') : st.peakW ≤ st'.peakW :=
  (runInv_of_exec_eq_some I s h).peakW

/-- Every write is charged: if no operation kind is free, a run whose counts do not grow
leaves the store unchanged. -/
theorem store_eq_of_exec_eq_some_of_cnt_le (hc : ∀ k, I.charge k ≠ 0)
    (h : exec I s st = some st') (hcnt : st'.cnt ≤ st.cnt) : st'.store = st.store :=
  ((runInv_of_exec_eq_some I s h).idle hc hcnt).1

/-- Every draw is charged: if no operation kind is free, a run whose counts do not grow
leaves the tape positions unchanged. -/
theorem pos_eq_of_exec_eq_some_of_cnt_le (hc : ∀ k, I.charge k ≠ 0)
    (h : exec I s st = some st') (hcnt : st'.cnt ≤ st.cnt) : st'.pos = st.pos :=
  ((runInv_of_exec_eq_some I s h).idle hc hcnt).2

omit [DecidableEq P] in
/-- A fold of steps whose counts grow has growing counts. -/
private theorem foldlM_cnt_le {σ α : Type} (μ : σ → OpCount P ι) {f : σ → α → Option σ}
    (hmono : ∀ x a b, f a x = some b → μ a ≤ μ b) :
    ∀ {l : List α} {a b : σ}, l.foldlM f a = some b → μ a ≤ μ b
  | [], a, b, h => by cases h; exact le_rfl
  | x :: l, a, b, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨a', h1, h2⟩ := Option.bind_eq_some_iff.mp h
    exact (hmono x a a' h1).trans (foldlM_cnt_le μ hmono h2)

omit [DecidableEq P] in
/-- Two folds agree when each step of the first, making no oracle call, is a step of the
second. -/
private theorem foldlM_eq_of_cnt_load_le {σ α : Type} (μ : σ → OpCount P ι)
    {f g : σ → α → Option σ} (hmono : ∀ x a b, f a x = some b → μ a ≤ μ b)
    (hfg : ∀ x a b, f a x = some b → (∀ p o, μ b (.load p o) ≤ μ a (.load p o)) →
      g a x = some b) :
    ∀ {l : List α} {a b : σ}, l.foldlM f a = some b →
      (∀ p o, μ b (.load p o) ≤ μ a (.load p o)) → l.foldlM g a = some b
  | [], a, b, h, _ => h
  | x :: l, a, b, h, hl => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨a', h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have hab := Finsupp.le_def.mp (hmono x a a' h1)
    have hb := Finsupp.le_def.mp (foldlM_cnt_le μ hmono h2)
    rw [hfg x a a' h1 (fun p o => (hb _).trans (hl p o))]
    exact foldlM_eq_of_cnt_load_le μ hmono hfg h2 fun p o => (hl p o).trans (hab _)

/-- The index-binder case of `NLAlib.Computation.exec_eq_of_exec_eq_some_of_cnt_load_le`. -/
private theorem exec_bindIdx_eq_of_cnt_load_le (O : ι → ℕ → Array K → Option (Array K)) (p : P)
    (x : Cell ℕ ℕ) (bound : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ)
    (ih : ∀ v {st st' : St P K (OpCount P ι)}, exec I (body v) st = some st' →
      (∀ p o, st'.cnt (.load p o) ≤ st.cnt (.load p o)) →
      exec { I with oracle := O } (body v) st = some st')
    {st st' : St P K (OpCount P ι)} (h : exec I (.bindIdx p x bound body) st = some st')
    (hl : ∀ p o, st'.cnt (.load p o) ≤ st.cnt (.load p o)) :
    exec { I with oracle := O } (.bindIdx p x bound body) st = some st' := by
  rw [exec_bindIdx] at h ⊢
  obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
  have hm : st.cnt ≤ r.2.cnt := by rw [snd_of_toNatStep_eq_some hr]; exact le_self_add
  change (toNatStep I p x st).bind _ = _
  rw [hr, Option.bind_some]
  split_ifs at h2 ⊢
  exact ih _ h2 fun p o => (hl p o).trans (Finsupp.le_def.mp hm _)

/-- The oracle is used only by oracle calls: under the standard charge, a run that makes no
oracle call (its load counts do not grow) is the same run under any other oracle. -/
theorem exec_eq_of_exec_eq_some_of_cnt_load_le (hc : IsUnitCharge I)
    (O : ι → ℕ → Array K → Option (Array K)) :
    ∀ (s : Stmt P ι ℕ ℕ) {st st' : St P K (OpCount P ι)}, exec I s st = some st' →
      (∀ p o, st'.cnt (.load p o) ≤ st.cnt (.load p o)) →
      exec { I with oracle := O } s st = some st'
  | .skip, st, st', h, _ => h
  | .seq s t, st, st', h, hl => by
    rw [exec_seq] at h ⊢
    obtain ⟨st₁, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have m1 := Finsupp.le_def.mp (cnt_le_of_exec_eq_some h1)
    have m2 := Finsupp.le_def.mp (cnt_le_of_exec_eq_some h2)
    rw [exec_eq_of_exec_eq_some_of_cnt_load_le hc O s h1 fun p o => (m2 _).trans (hl p o),
      Option.bind_some]
    exact exec_eq_of_exec_eq_some_of_cnt_load_le hc O t h2 fun p o => (hl p o).trans (m1 _)
  | .instr i, st, st', h, _ => h
  | .apply o p dst dOff src sOff cols, st, st', h, hl => by
    rw [exec] at h
    split_ifs at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, -, _, -, s, -, rfl⟩ := h
    have := hl p o
    simp [hc.charge_eq] at this
  | .rom p dst i, st, st', h, _ => h
  | .alloc p len body, st, st', h, hl => by
    rw [exec_alloc] at h ⊢
    obtain ⟨st₂, h2, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [exec_eq_of_exec_eq_some_of_cnt_load_le hc O (body _) h2 hl, Option.map_some]
  | .loop n body, st, st', h, hl => by
    rw [exec_loop] at h ⊢
    exact foldlM_eq_of_cnt_load_le St.cnt (fun i a b hb => cnt_le_of_exec_eq_some hb)
      (fun i a b hb hl' => exec_eq_of_exec_eq_some_of_cnt_load_le hc O (body i) hb hl') h hl
  | .whileFuel fuel p c x y body, st, st', h, hl => by
    rw [exec] at h ⊢
    obtain ⟨r, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    have hcmp : ∀ {a : St P K (OpCount P ι)} {r' : Bool × St P K (OpCount P ι)},
        cmpStep I p c x y a = some r' → a.cnt ≤ r'.2.cnt := fun hr' => by
      rw [snd_of_cmpStep_eq_some hr']; exact le_self_add
    have hmono : ∀ (_ : ℕ) (a b : St P K (OpCount P ι) × Bool),
        (if a.2 then (cmpStep I p c x y a.1).bind fun r =>
          if r.1 then (exec I body r.2).map fun st' => (st', true) else some (r.2, false)
        else some a) = some b → a.1.cnt ≤ b.1.cnt := fun _ a b hb => by
      split_ifs at hb
      · obtain ⟨r', hr', hb⟩ := Option.bind_eq_some_iff.mp hb
        split_ifs at hb
        · obtain ⟨st₁, h3, rfl⟩ := Option.map_eq_some_iff.mp hb
          exact (hcmp hr').trans (cnt_le_of_exec_eq_some h3)
        · cases hb; exact hcmp hr'
      · cases hb; exact le_rfl
    rw [foldlM_eq_of_cnt_load_le (fun a => a.1.cnt) hmono (fun _ a b hb hl' => ?_) h1 ?_,
      Option.bind_some]
    · exact h2
    · split_ifs at h2
      cases h2
      exact hl
    · split_ifs at hb ⊢
      · obtain ⟨r', hr', hb⟩ := Option.bind_eq_some_iff.mp hb
        change (cmpStep I p c x y a.1).bind _ = _
        rw [hr', Option.bind_some]
        split_ifs at hb ⊢
        · obtain ⟨st₁, h3, rfl⟩ := Option.map_eq_some_iff.mp hb
          rw [exec_eq_of_exec_eq_some_of_cnt_load_le hc O body h3
            fun p o => (hl' p o).trans (Finsupp.le_def.mp (hcmp hr') _), Option.map_some]
        · exact hb
      · exact hb
  | .ite p c x y t e, st, st', h, hl => by
    rw [exec_ite] at h ⊢
    obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.mp h
    have hm : st.cnt ≤ r.2.cnt := by rw [snd_of_cmpStep_eq_some hr]; exact le_self_add
    change (cmpStep I p c x y st).bind _ = _
    rw [hr, Option.bind_some]
    split_ifs at h2 ⊢
    · exact exec_eq_of_exec_eq_some_of_cnt_load_le hc O t h2
        fun p o => (hl p o).trans (Finsupp.le_def.mp hm _)
    · exact exec_eq_of_exec_eq_some_of_cnt_load_le hc O e h2
        fun p o => (hl p o).trans (Finsupp.le_def.mp hm _)
  | .named _ _ body, st, st', h, hl => by
    rw [exec_named] at h ⊢
    exact exec_eq_of_exec_eq_some_of_cnt_load_le hc O body h hl
  | .kcall .., st, st', h, _ => h
  | .bindIdx p x bound body, st, st', h, hl =>
    exec_bindIdx_eq_of_cnt_load_le O p x bound body
      (fun v _ _ hv hl' => exec_eq_of_exec_eq_some_of_cnt_load_le hc O (body v) hv hl') h hl

end Invariants

/-! ### Straight-line statements

A statement with no conditional and no loop on a comparison has its control flow fixed by its
syntax, so the tape positions, counts and memory of a successful run do not depend on the value
semantics: a floating-point analysis of a straight-line kernel takes them from its exact
specification. -/

section StraightLine

variable {P ι VB VI : Type}

/-- A statement is **straight-line** if it has no conditional (`ite`), no loop on a comparison
(`whileFuel`) and no index binder (`bindIdx`), in any loop or allocation body: which instructions it
runs is fixed by its syntax and its index values, not by the stored values. A kernel call is one
charged step whose kind is fixed by its dimensions, so it is straight-line; an index binder is not
(two runs can bind different values). -/
def Stmt.StraightLine : Stmt P ι VB VI → Prop
  | .skip => True
  | .seq s t => s.StraightLine ∧ t.StraightLine
  | .instr _ => True
  | .apply .. => True
  | .rom .. => True
  | .alloc _ _ body => ∀ b, (body b).StraightLine
  | .loop _ body => ∀ i, (body i).StraightLine
  | .whileFuel .. => False
  | .ite .. => False
  | .named _ _ body => body.StraightLine
  | .kcall .. => True
  | .bindIdx .. => False

/-- The **usage** of a state: the tape positions, the counts, and the current and peak memory,
in cells per tag and in bits; the state without its store. -/
def St.usage {K C : Type} (st : St P K C) : (Dist → ℕ) × C × (P → ℕ) × (P → ℕ) × ℕ × ℕ :=
  (st.pos, st.cnt, st.cur, st.peak, st.curW, st.peakW)

variable [DecidableEq P] {K K' C : Type} [AddMonoid C]

/-- Two runs of one scalar instruction from the same tape positions end at the same tape
positions, whatever the value semantics, the tapes and the stores. -/
private theorem Instr.snd_run_eq {i : Instr P ℕ ℕ} {sem : ScalarSem P K} {sem' : ScalarSem P K'}
    {tape : Dist → ℕ → K} {tape' : Dist → ℕ → K'} {s : Store P K} {s' : Store P K'}
    {pos : Dist → ℕ} {r : Store P K × (Dist → ℕ)} {r' : Store P K' × (Dist → ℕ)}
    (h : i.run sem tape s pos = some r) (h' : i.run sem' tape' s' pos = some r') :
    r.2 = r'.2 := by
  cases i <;> simp only [Instr.run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h' <;>
    grind

/-- Two folds whose steps keep a relation between their states keep it. -/
private theorem foldlM_rel {α σ σ' : Type} (R : σ → σ' → Prop) {f : σ → α → Option σ}
    {g : σ' → α → Option σ'}
    (hfg : ∀ x a a' b b', R a a' → f a x = some b → g a' x = some b' → R b b') :
    ∀ {l : List α} {a b : σ} {a' b' : σ'}, R a a' → l.foldlM f a = some b →
      l.foldlM g a' = some b' → R b b'
  | [], _, _, _, _, hR, h, h' => by cases h; cases h'; exact hR
  | x :: l, _, _, _, _, hR, h, h' => by
    rw [List.foldlM_cons] at h h'
    obtain ⟨c, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c', h1', h2'⟩ := Option.bind_eq_some_iff.mp h'
    exact foldlM_rel R hfg (hfg x _ _ _ _ hR h1 h1') h2 h2'

/-- The kernel-call case of `NLAlib.Computation.usage_eq_of_exec_eq_some_of_straightLine`. -/
private theorem shape_usage_eq_of_exec_kcall (I : Interp P ι K C) (I' : Interp P ι K' C)
    (hc : I.charge = I'.charge) (o : ι) (p : P) (dims : List (IExp ℕ))
    (ins outs : List (ℕ × IExp ℕ)) {st₀ st₁ : St P K C} {st₀' st₁' : St P K' C}
    (hsh : st₀.store.shape = st₀'.store.shape) (hu : st₀.usage = st₀'.usage)
    (h : exec I (.kcall o p dims ins outs) st₀ = some st₁)
    (h' : exec I' (.kcall o p dims ins outs) st₀' = some st₁') :
    st₁.store.shape = st₁'.store.shape ∧ st₁.usage = st₁'.usage := by
  simp only [St.usage, Prod.mk.injEq] at hu
  obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
  rw [exec] at h h'
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h'
  refine ⟨(Interp.shape_of_kcallStore_eq_some hs).trans
    (hsh.trans (Interp.shape_of_kcallStore_eq_some hs').symm), ?_⟩
  simp only [St.usage, Prod.mk.injEq]
  exact ⟨hpos, by rw [hcnt, hc], hcur, hpeak, hcurW, hpeakW⟩

/-- The induction behind `NLAlib.Computation.usage_eq_of_exec_eq_some_of_straightLine`: the
shape of the store and the usage are carried together. -/
private theorem shape_usage_eq_of_exec (I : Interp P ι K C) (I' : Interp P ι K' C)
    (hc : I.charge = I'.charge) (hw : I.width = I'.width) :
    ∀ (s : Stmt P ι ℕ ℕ), s.StraightLine → ∀ {st₀ st₁ : St P K C} {st₀' st₁' : St P K' C},
      st₀.store.shape = st₀'.store.shape → st₀.usage = st₀'.usage →
      exec I s st₀ = some st₁ → exec I' s st₀' = some st₁' →
      st₁.store.shape = st₁'.store.shape ∧ st₁.usage = st₁'.usage
  | .skip, _, _, _, _, _, hsh, hu, h, h' => by
    rw [exec_skip] at h h'; cases h; cases h'; exact ⟨hsh, hu⟩
  | .seq s t, hst, _, _, _, _, hsh, hu, h, h' => by
    rw [exec_seq] at h h'
    obtain ⟨st₂, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st₂', h1', h2'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨hsh₂, hu₂⟩ := shape_usage_eq_of_exec I I' hc hw s hst.1 hsh hu h1 h1'
    exact shape_usage_eq_of_exec I I' hc hw t hst.2 hsh₂ hu₂ h2 h2'
  | .instr i, _, st₀, _, st₀', _, hsh, hu, h, h' => by
    simp only [St.usage, Prod.mk.injEq] at hu
    obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
    rw [exec_instr] at h h'
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h'
    rw [hpos] at hr
    refine ⟨(Instr.shape_of_run_eq_some hr).trans
      (hsh.trans (Instr.shape_of_run_eq_some hr').symm), ?_⟩
    simp only [St.usage, Prod.mk.injEq]
    exact ⟨Instr.snd_run_eq hr hr', by rw [hcnt, hc], hcur, hpeak, hcurW, hpeakW⟩
  | .apply o p dst dOff src sOff cols, _, st₀, _, st₀', _, hsh, hu, h, h' => by
    simp only [St.usage, Prod.mk.injEq] at hu
    obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
    rw [exec] at h h'
    split_ifs at h h'
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨_, -, _, -, s, hs, rfl⟩ := h
    obtain ⟨_, -, _, -, s', hs', rfl⟩ := h'
    refine ⟨(Store.shape_of_writeBlock_eq_some hs).trans
      (hsh.trans (Store.shape_of_writeBlock_eq_some hs').symm), ?_⟩
    simp only [St.usage, Prod.mk.injEq]
    exact ⟨hpos, by rw [hcnt, hc], hcur, hpeak, hcurW, hpeakW⟩
  | .rom p dst i, _, st₀, _, st₀', _, hsh, hu, h, h' => by
    simp only [St.usage, Prod.mk.injEq] at hu
    obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
    rw [exec] at h h'
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h h'
    obtain ⟨_, -, s, hs, rfl⟩ := h
    obtain ⟨_, -, s', hs', rfl⟩ := h'
    refine ⟨(Store.shape_of_write_eq_some hs).trans
      (hsh.trans (Store.shape_of_write_eq_some hs').symm), ?_⟩
    simp only [St.usage, Prod.mk.injEq]
    exact ⟨hpos, by rw [hcnt, hc], hcur, hpeak, hcurW, hpeakW⟩
  | .alloc p len body, hst, st₀, _, st₀', _, hsh, hu, h, h' => by
    simp only [St.usage, Prod.mk.injEq] at hu
    obtain ⟨hpos, hcnt, hcur, hpeak, hcurW, hpeakW⟩ := hu
    rw [exec_alloc] at h h'
    obtain ⟨st₂, h2, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨st₂', h2', rfl⟩ := Option.map_eq_some_iff.mp h'
    have hsize : st₀.store.size = st₀'.store.size := by
      simpa [Store.shape] using congrArg Array.size hsh
    rw [hsize] at h2
    obtain ⟨hsh₂, hu₂⟩ := shape_usage_eq_of_exec I I' hc hw (body st₀'.store.size)
      (hst _) (by simp only [Store.shape, Array.map_push, Array.size_replicate] at hsh ⊢; rw [hsh])
      (by simp only [St.usage, Prod.mk.injEq]
          exact ⟨hpos, hcnt, by rw [hcur], by rw [hpeak, hcur], by rw [hcurW, hw],
            by rw [hpeakW, hcurW, hw]⟩) h2 h2'
    simp only [St.usage, Prod.mk.injEq] at hu₂
    obtain ⟨hpos₂, hcnt₂, hcur₂, hpeak₂, hcurW₂, hpeakW₂⟩ := hu₂
    refine ⟨by simp only [Store.shape_pop, hsh₂], ?_⟩
    simp only [St.usage, Prod.mk.injEq]
    exact ⟨hpos₂, hcnt₂, by rw [hcur₂], hpeak₂, by rw [hcurW₂, hw], hpeakW₂⟩
  | .loop n body, hst, _, _, _, _, hsh, hu, h, h' => by
    rw [exec_loop] at h h'
    exact foldlM_rel (fun (a : St P K C) (a' : St P K' C) =>
        a.store.shape = a'.store.shape ∧ a.usage = a'.usage)
      (fun i _ _ _ _ hR hb hb' => shape_usage_eq_of_exec I I' hc hw (body i) (hst i) hR.1 hR.2
        hb hb') ⟨hsh, hu⟩ h h'
  | .whileFuel .., hst, _, _, _, _, _, _, _, _ => hst.elim
  | .ite .., hst, _, _, _, _, _, _, _, _ => hst.elim
  | .named _ _ body, hst, _, _, _, _, hsh, hu, h, h' => by
    rw [exec_named] at h h'
    exact shape_usage_eq_of_exec I I' hc hw body hst hsh hu h h'
  | .kcall o p dims ins outs, _, _, _, _, _, hsh, hu, h, h' =>
    shape_usage_eq_of_exec_kcall I I' hc o p dims ins outs hsh hu h h'
  | .bindIdx .., hst, _, _, _, _, _, _, _, _ => hst.elim

/-- The costs of a straight-line run do not depend on the value semantics: for interpretations
`I` and `I'` (over any carriers) with the same charge and the same widths, and a straight-line
statement $s$, if the runs of $s$ under `I` from $\mathit{st}_0$ and under `I'` from
$\mathit{st}'_0$ both succeed, and the two start states have the same usage and the same store
shape, then the two end states have the same usage: the same tape positions, counts, and current
and peak memory. The value semantics, tapes, oracles, read-only data and stored values may
differ. No printed source. -/
theorem usage_eq_of_exec_eq_some_of_straightLine (I : Interp P ι K C) (I' : Interp P ι K' C)
    (hc : I.charge = I'.charge) (hw : I.width = I'.width) {s : Stmt P ι ℕ ℕ}
    (hs : s.StraightLine) {st₀ st₁ : St P K C} {st₀' st₁' : St P K' C}
    (hshape : st₀.store.shape = st₀'.store.shape) (husage : st₀.usage = st₀'.usage)
    (h : exec I s st₀ = some st₁) (h' : exec I' s st₀' = some st₁') :
    st₁.usage = st₁'.usage :=
  (shape_usage_eq_of_exec I I' hc hw s hs hshape husage h h').2

end StraightLine

end NLAlib.Computation
