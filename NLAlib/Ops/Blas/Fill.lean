/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Tactic
public import NLAlib.Ops.Catalog.Scalar
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# Filling a stored vector

A nullary operation (a literal) written to each entry of a vector is a counted loop. It needs
only room for the output, so a routine can give its output words a value before a computation
that may stop early.

## Main definitions

* `NLAlib.Ops.fillMap`: the loop.
* `NLAlib.Ops.fillRoutine`, `NLAlib.Ops.fillSpec`: the loop as a routine `[n] () → (y : n)`,
  and its specification. The fill with the literal zero initializes the iterate of the
  conjugate gradient solvers and the output tails of Lanczos.

## Main results

* `NLAlib.Ops.fillMap_writes`, `NLAlib.Ops.fillMap_writes_readBlock`: the run, which writes the
  value of the operation to every entry and keeps the tape position.
* `NLAlib.Ops.fillRoutine_meets`: the routine meets its specification.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- Write the value of one nullary operation to each entry of a vector, without scratch
allocations. The operation reads no cell and writes one cell. -/
def fillMap (o : Op) : Stmt Op Tst :=
  .loop (.var 0) (.call o [] [] [⟨0, .var 1 + .var 2⟩])

/-- The fill's complete primitive count is one call per entry. -/
theorem stmtCost_fillMap (o : Op) (n y : ℕ) :
    stmtCost (fillMap (Tst := Tst) o) [n, y] = n • Count.one o [] := by
  simp [fillMap, stmtCost, useCost]

/-- A fill has only the workspace of a primitive call, independently of vector length. -/
theorem stmtPeak_fillMap_le (o : Op) (W : Op → List ℕ → ℕ) (n y : ℕ) :
    stmtPeak W (fillMap (Tst := Tst) o) [n, y] ≤ W o [] := by
  simp only [fillMap, stmtPeak]
  exact Finset.sup_le fun _ _ => le_rfl

/-- The fill writes the value of its operation to every entry: for an operation with the
constant value `v`, from room for the $n$ entries at `y`, on every tape, the fill writes only
those entries, stores `v` in each and keeps the tape position. A step in the proof of
`NLAlib.Ops.fillRoutine_meets`, with the entries stated as a stored vector. -/
theorem fillMap_writes {o : Op} {v : K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.const v) AnyOperands) {τ : Tape K} {m : Mem K} {n : ℕ}
    {y : ℕ × ℕ} (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I τ (fillMap (Tst := Tst) o) (Env.frame [n] [y])
      (Store.inBlock y.1 y.2 n)
      (fun m' => m'.store.HoldsVec y.1 y.2 n (fun _ => v) ∧ m'.pos = m.pos) m := by
  refine writes_fill rfl (fun _ => v) (fun _ => m.pos) rfl fun i hi m' hfr _ hpos => ?_
  have hz : y.2 + i < m'.store.len y.1 := by rw [hfr.len_eq]; omega
  refine wp_call_const hI rfl rfl rfl trivial hz ?_
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _, Store.get_upd_self hz _, hpos⟩

/-- The fill of `NLAlib.Ops.fillMap_writes` read back as a block: the $n$ entries at `y` are
$n$ copies of `v`. A step in the proof of `NLAlib.Ops.fillRoutine_meets`, which is the statement
callers use. -/
theorem fillMap_writes_readBlock {o : Op} {v : K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.const v) AnyOperands) {τ : Tape K} {m : Mem K} {n : ℕ}
    {y : ℕ × ℕ} (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I τ (fillMap (Tst := Tst) o) (Env.frame [n] [y])
      (Store.inBlock y.1 y.2 n)
      (fun m' => m'.store.readBlock y.1 y.2 n = some (List.replicate n v) ∧ m'.pos = m.pos)
      m := by
  refine (fillMap_writes hI hy).mono le_rfl fun m' _ h => ⟨?_, h.2⟩
  rw [Store.holdsVec_iff_readBlock.mp h.1]
  simp

/-- Fill a vector with the value of a nullary operation: `[n] () → (y : n)`. -/
def fillRoutine (o : Op) : Routine Op Tst :=
  routine% [n] () → (y : n) := fillMap o

/-- Every entry of the written block is `v`. -/
def fillSpec (v : K) : Routine.Spec K :=
  spec% [n] () → (ys) ensures ys = List.replicate n v

/-- The fill meets its specification for an operation with the constant value `v`, from room for
the block alone: nothing is read. -/
theorem fillRoutine_meets {o : Op} {v : K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.const v) AnyOperands) :
    (fillRoutine (Tst := Tst) o).Meets I (fillSpec v) := by
  routine_intro [n] (y) reads ()
  refine (fillMap_writes_readBlock hI hroom).mono (by fp_sub) ?_
  rintro m' - ⟨hread, hpos⟩
  exact ⟨hpos.trans (Nat.add_zero _).symm, [List.replicate n v],
    Mem.readBlocks_of_cons hread rfl, rfl⟩

end NLAlib.Ops
