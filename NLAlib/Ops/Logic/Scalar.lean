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
* `NLAlib.Ops.ScalarCall`, `NLAlib.Ops.IsScalar.scalarCall`: operations as functions of cells.
* `NLAlib.Ops.writes_scalarBlock`: the block rule, in total mode.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- A scalar instruction: an operation (of any tag) on cells. -/
structure ScalarIns (Op : Type) where
  /-- The operation, as a name of the signature (`Has.inj ScalarOp.add`, or the same at a tag). -/
  op : Op
  /-- The input cells. -/
  ins : List Operand
  /-- The output cell. -/
  out : Operand

/-- The call of one scalar instruction. -/
def ScalarIns.stmt (x : ScalarIns Op) : Stmt Op Tst := .call x.op [] x.ins [x.out]

/-- **A straight-line block** of scalar instructions, as a sequence of calls nested to the right.
The builder writes the calls themselves; they are this block by `rfl` at a literal list, which
the tactic of the rule states (`change`). -/
def Stmt.scalarBlock : List (ScalarIns Op) → Stmt Op Tst
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

/-- **A scalar operation as a function of cells**: a call of `o` with no dimensions on live
input cells holding `vs` and an output cell in bounds writes `g vs` in the output cell, when
`g vs` is defined. A total-mode property (the catalog's contracts are total). -/
def ScalarCall (I : Interp Op Tst K) (o : Op) (g : List K → Option K) : Prop :=
  ∀ (ins : List (ℕ × ℕ)) (z : ℕ × ℕ) (τ : Tape K) (m : Mem K) (vs : List K) (v : K),
    m.Live (ins ++ [z]) → ins.mapM (fun a => m.store.get a.1 a.2) = some vs →
    z.2 < m.store.len z.1 → g vs = some v → I.callS o [] ins [z] τ m = some (m.upd z v)

/-- The scalar contract of the catalog, at any tag, as functions of cells. -/
theorem IsScalar.scalarCall [Has ScalarOp Op] {M : Machine K} {I : Interp Op Tst K}
    (hS : IsScalar M I) (a : ScalarOp) : ScalarCall I (Has.inj a) (M.eval a) := by sorry

/-- **The evaluation of a block** on a cell function, given the function `sem` of each operation:
the cells written, in order, with their values; each instruction reads the cells as updated by
the instructions before it. `none` if an operand does not evaluate, a cell read holds no word or
`sem` is undefined. -/
def ScalarIns.evalBlock (sem : Op → List K → Option K) (ρ : Env) :
    List (ScalarIns Op) → (ℕ × ℕ → Option K) → Option (List ((ℕ × ℕ) × K))
  | [], _ => some []
  | x :: xs, f =>
    (Operand.evalList ρ x.ins).bind fun a => (a.mapM f).bind fun vs => (x.out.eval ρ).bind
      fun z => (sem x.op vs).bind fun v =>
        (ScalarIns.evalBlock sem ρ xs (Function.update f z (some v))).map fun ws => (z, v) :: ws

/-- Write the cells `ws`, in order. -/
def Mem.updCells (m : Mem K) : List ((ℕ × ℕ) × K) → Mem K
  | [] => m
  | w :: ws => (m.upd w.1 w.2).updCells ws

/-- **The block rule** (total mode): a straight-line block of scalar instructions whose
operations are functions of cells (`ScalarCall`, e.g. by `IsScalar.scalarCall`, at any tag or
mixing tags) writes its output cells, and the memory after it is the memory before with the
evaluated cells written. It needs room for the cells written and live input cells (the cells
read hold words: that is the evaluation succeeding).

Only total mode: the catalog's scalar contracts are total, and a total contract says nothing of
a call outside its precondition, so a liberal statement would need the room anyway. A block that
contains catalog calls gets its liberal corollary by `Writes.of_total`, under the same
hypotheses; one proof does not give both modes for free. -/
theorem writes_scalarBlock {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {m : Mem K}
    {sem : Op → List K → Option K} {xs : List (ScalarIns Op)}
    (hS : ∀ x ∈ xs, ScalarCall I x.op (sem x.op)) {ws : List ((ℕ × ℕ) × K)}
    (hev : ScalarIns.evalBlock sem ρ xs m.store.cellFn = some ws)
    (hroom : ∀ w ∈ ws, w.1.2 < m.store.len w.1.1) :
    Writes .total I τ (Stmt.scalarBlock xs) ρ (Fp.cells (ws.map Prod.fst))
      (fun m' => m' = m.updCells ws) m := by sorry

/-- The value of a cell after the block: the last value written to it. -/
theorem get_updCells {m : Mem K} {ws : List ((ℕ × ℕ) × K)} {z : ℕ × ℕ} {v : K}
    (hz : ws.reverse.lookup z = some v) (hl : z.2 < m.store.len z.1) :
    (m.updCells ws).store.get z.1 z.2 = some v := by sorry

/-- A cell not written by the block keeps its value. -/
theorem get_updCells_of_notMem {m : Mem K} {ws : List ((ℕ × ℕ) × K)} {z : ℕ × ℕ}
    (hz : z ∉ ws.map Prod.fst) : (m.updCells ws).store.get z.1 z.2 = m.store.get z.1 z.2 := by
  sorry

end NLAlib.Ops
