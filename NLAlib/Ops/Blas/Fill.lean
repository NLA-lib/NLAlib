/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Tactic
public import NLAlib.Ops.Catalog.Scalar

/-!
# Filling a stored vector

A nullary operation (a literal) written to each entry of a vector is a counted loop. It needs
only room for the output, so a routine can give its output words a value before a computation
that may stop early.

## Main results

* `NLAlib.Ops.fillMap`: the loop.
* `NLAlib.Ops.writes_fillMap`, `NLAlib.Ops.writes_fillMap_readBlock`: the run, which writes the
  value of the operation to every entry and keeps the tape position.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type}

/-- Write the value of one nullary operation to each entry of a vector, without scratch
allocations. The operation reads no cell and writes one cell. -/
def fillMap (o : Op) : Impl Op Tst where
  nd := 1
  nin := 0
  nout := 1
  body := .loop (.var 0) (.call o [] [] [⟨0, .var 1 + .var 2⟩])

/-- The fill's complete primitive count is one call per entry. -/
theorem stmtCost_fillMap (o : Op) (n y : ℕ) :
    stmtCost (fillMap (Tst := Tst) o).body [n, y] = n • Count.one o [] := by
  simp [fillMap, stmtCost, useCost]

/-- A fill has only the workspace of a primitive call, independently of vector length. -/
theorem stmtPeak_fillMap_le (o : Op) (W : Op → List ℕ → ℕ) (n y : ℕ) :
    stmtPeak W (fillMap (Tst := Tst) o).body [n, y] ≤ W o [] := by
  simp only [fillMap, stmtPeak]
  exact Finset.sup_le fun _ _ => le_rfl

/-- The fill writes the value of its operation to every entry: for an operation with the
constant value `v`, from room for the $n$ entries at `y`, on every tape, the fill writes only
those entries, stores `v` in each and keeps the tape position. -/
theorem writes_fillMap {o : Op} {v : K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.const v) AnyOperands) {τ : Tape K} {m : Mem K} {n : ℕ}
    {y : ℕ × ℕ} (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I τ (fillMap (Tst := Tst) o).body (Env.frame [n] [y])
      (Store.inBlock y.1 y.2 n)
      (fun m' => m'.store.HoldsVec y.1 y.2 n (fun _ => v) ∧ m'.pos = m.pos) m := by
  refine writes_fill rfl (fun _ => v) (fun _ => m.pos) rfl fun i hi m' hfr _ hpos => ?_
  have hz : y.2 + i < m'.store.len y.1 := by rw [hfr.len_eq]; omega
  refine wp_call_const hI rfl rfl rfl trivial hz ?_
  exact ⟨(Store.EqOff.refl _ _).upd ⟨rfl, le_rfl, by omega⟩ _, Store.get_upd_self hz _, hpos⟩

/-- The fill of `NLAlib.Ops.writes_fillMap` read back as a block: the $n$ entries at `y` are
$n$ copies of `v`. -/
theorem writes_fillMap_readBlock {o : Op} {v : K} {I : Interp Op Tst K}
    (hI : I.IsFn .total o (.const v) AnyOperands) {τ : Tape K} {m : Mem K} {n : ℕ}
    {y : ℕ × ℕ} (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I τ (fillMap (Tst := Tst) o).body (Env.frame [n] [y])
      (Store.inBlock y.1 y.2 n)
      (fun m' => m'.store.readBlock y.1 y.2 n = some (List.replicate n v) ∧ m'.pos = m.pos)
      m := by
  refine (writes_fillMap hI hy).mono le_rfl fun m' _ h => ⟨?_, h.2⟩
  rw [Store.holdsVec_iff_readBlock.mp h.1]
  simp

end NLAlib.Ops
