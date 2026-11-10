/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Writes
public import NLAlib.Ops.Catalog.Scalar

/-!
# Straight-line scalar blocks

A rotation, a norm, a coefficient update: a few dozen scalar instructions without loops or
branches. Under `IsScalar M I` (scalar arithmetic is the machine `M`, a total function on words)
their run is a fold of `M` over the cells, so the whole block is **one** specification: the
cells written, each with its value computed by `NLAlib.Ops.ScalarIns.evalBlock` on the cell
function of the store. The proof of a block is then one application of
`NLAlib.Ops.writes_scalarBlock` and one evaluation per output word (one `simp` over all outputs of
a long block is too slow: evaluate each output by its own lemma).

Success needs only that the cells read hold words when they are read (cells written earlier in
the block need no initialisation: the evaluation reads the updated cell function) and room for
the cells written; division is total in the machine, and its meaning at zero is the business of
the arithmetic contract (`StdModel.div`), not of the block.

**Phase A**: statements only (`sorry`).

## Main results

* `NLAlib.Ops.ScalarIns`, `NLAlib.Ops.Stmt.scalarBlock`, `NLAlib.Ops.ScalarIns.evalBlock`.
* `NLAlib.Ops.writes_scalarBlock`: the block rule, in every mode.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- A scalar instruction: an operation of the scalar catalog on cells. -/
structure ScalarIns where
  /-- The operation. -/
  op : ScalarOp
  /-- The input cells. -/
  ins : List Operand
  /-- The output cell. -/
  out : Operand

/-- The call of one scalar instruction. -/
def ScalarIns.stmt [Has ScalarOp Op] (x : ScalarIns) : Stmt Op Tst :=
  .call (Has.inj x.op) [] x.ins [x.out]

/-- **A straight-line block** of scalar instructions, as a sequence nested to the right (the form
the builder produces). -/
def Stmt.scalarBlock [Has ScalarOp Op] : List ScalarIns → Stmt Op Tst
  | [] => .skip
  | [x] => x.stmt
  | x :: xs => .seq x.stmt (Stmt.scalarBlock xs)

/-- The cells of a store as a function; `none` at a cell that holds no word. -/
def Store.cellFn (s : Store K) : ℕ × ℕ → Option K := fun z => s.get z.1 z.2

/-- The value of a scalar operation of the machine on the values of its inputs. -/
def Machine.eval (M : Machine K) : ScalarOp → List K → Option K
  | .lit q, [] => some (M.lit q)
  | .add, [a, b] => some (M.add a b)
  | .sub, [a, b] => some (M.sub a b)
  | .mul, [a, b] => some (M.mul a b)
  | .div, [a, b] => some (M.div a b)
  | .neg, [a] => some (M.neg a)
  | .sqrt, [a] => some (M.sqrt a)
  | .copy, [a] => some a
  | _, _ => none

/-- **The evaluation of a block** on a cell function: the cells written, in order, with their
values; each instruction reads the cells as updated by the instructions before it. `none` if an
operand does not evaluate, a cell read holds no word or an instruction has the wrong arity. -/
def ScalarIns.evalBlock (M : Machine K) (ρ : Env) :
    List ScalarIns → (ℕ × ℕ → Option K) → Option (List ((ℕ × ℕ) × K))
  | [], _ => some []
  | x :: xs, f =>
    (Operand.evalList ρ x.ins).bind fun a => (a.mapM f).bind fun vs => (x.out.eval ρ).bind
      fun z => (M.eval x.op vs).bind fun v =>
        (ScalarIns.evalBlock M ρ xs (Function.update f z (some v))).map fun ws => (z, v) :: ws

/-- Write the cells `ws`, in order. -/
def Mem.updCells (m : Mem K) : List ((ℕ × ℕ) × K) → Mem K
  | [] => m
  | w :: ws => (m.upd w.1 w.2).updCells ws

/-- The cells of a list, one each. -/
def Fp.cells (zs : List (ℕ × ℕ)) : Fp := fun b i => (b, i) ∈ zs

/-- **The block rule**: a straight-line block of scalar instructions writes its output cells, and
the memory after it is the memory before with the evaluated cells written. Success needs room
for the cells written (the cells read hold words: that is the evaluation succeeding). -/
theorem writes_scalarBlock [Has ScalarOp Op] {md : Mode} {I : Interp Op Tst K} {τ : Tape K}
    {ρ : Env} {m : Mem K} {M : Machine K} (hS : IsScalar M I) {xs : List ScalarIns}
    {ws : List ((ℕ × ℕ) × K)} (hev : ScalarIns.evalBlock M ρ xs m.store.cellFn = some ws)
    (hroom : md.Needs (∀ w ∈ ws, w.1.2 < m.store.len w.1.1)) :
    Writes md I τ (Stmt.scalarBlock xs) ρ (Fp.cells (ws.map Prod.fst))
      (fun m' => m' = m.updCells ws) m := by sorry

/-- The value of a cell after the block: the last value written to it, or its value before. -/
theorem get_updCells {m : Mem K} {ws : List ((ℕ × ℕ) × K)} {z : ℕ × ℕ} {v : K}
    (hz : (ws.reverse.lookup z) = some v) (hl : z.2 < m.store.len z.1) :
    (m.updCells ws).store.get z.1 z.2 = some v := by sorry

/-- A cell not written by the block keeps its value. -/
theorem get_updCells_of_notMem {m : Mem K} {ws : List ((ℕ × ℕ) × K)} {z : ℕ × ℕ}
    (hz : z ∉ ws.map Prod.fst) : (m.updCells ws).store.get z.1 z.2 = m.store.get z.1 z.2 := by
  sorry

end NLAlib.Ops
