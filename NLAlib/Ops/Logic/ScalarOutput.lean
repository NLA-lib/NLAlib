/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Scalar

/-!
# Contiguous outputs of scalar blocks

A scalar block is evaluated by the existing pure word evaluator. When its evaluated writes
fill a consecutive interval, the ordinary scalar-block rule gives one packed output read.
The adapter introduces no operation or evaluator and retains the original executed calls.

## Main results

* `NLAlib.Ops.Mem.updCells_range`: consecutive scalar updates are a block update.
* `NLAlib.Ops.writes_machineScalarBlock_readBlock`: total packed output of a scalar block.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Reassociate three executed blocks without changing their footprint or postcondition. -/
theorem Writes.seq_assoc_iff {K Op Tst : Type} {md : Mode} {I : Interp Op Tst K}
    {τ : Tape K} {ρ : Env} {m : Mem K} {a b c : Stmt Op Tst} {F : Fp}
    {P : Mem K → Prop} :
    Writes md I τ (.seq (.seq a b) c) ρ F P m ↔
      Writes md I τ (.seq a (.seq b c)) ρ F P m := by
  simp only [Writes, Wp, eval, Option.bind_assoc]

/-- Writing consecutive cells in order is the existing block update. -/
theorem Mem.updCells_range {K : Type} (m : Mem K) (z : ℕ × ℕ) (n : ℕ) (v : ℕ → K) :
    m.updCells ((List.range n).map fun i => ((z.1, z.2 + i), v i)) =
      m.updBlock z ((List.range n).map v) := by
  induction n generalizing m z v with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map]
    change (m.upd (z.1, z.2 + 0) (v 0)).updCells
      ((List.range n).map fun i => ((z.1, z.2 + (i + 1)), v (i + 1))) =
        (m.upd z (v 0)).updBlock (z.1, z.2 + 1)
          ((List.range n).map fun i => v (i + 1))
    simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
      ih (m.upd z (v 0)) (z.1, z.2 + 1) (fun i => v (i + 1))

/-- A machine scalar block that evaluates to consecutive output writes produces their packed
values, with a block footprint and unchanged tape position. Only actual word evaluation and
output capacity are required; initialized inputs are witnessed by that pure evaluation. -/
theorem writes_machineScalarBlock_readBlock {K Op Tst : Type} [Has ScalarOp Op]
    {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {ρ : Env} {m : Mem K} {xs : List (ScalarIns ScalarOp)}
    {z : ℕ × ℕ} {n : ℕ} {v : ℕ → K}
    (hev : ScalarIns.evalBlock M.eval ρ xs m.store.cellFn =
      some ((List.range n).map fun i => ((z.1, z.2 + i), v i)))
    (hroom : z.2 + n ≤ m.store.len z.1) :
    Writes .total I τ (Stmt.scalarBlock (xs.map ScalarIns.lift)) ρ
      (Store.inBlock z.1 z.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 n =
        some ((List.range n).map v)) m := by
  have hmem : ∀ w ∈ (List.range n).map (fun i => ((z.1, z.2 + i), v i)),
      w.1.2 < m.store.len w.1.1 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    dsimp only
    omega
  refine (writes_machineScalarBlock hI hev hmem).mono ?_ ?_
  · intro b j hj
    change (b, j) ∈ _ at hj
    simp only [List.map_map, Function.comp_apply, List.mem_map, List.mem_range] at hj
    obtain ⟨i, hi, he⟩ := hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact ⟨rfl, by omega, by omega⟩
  · intro m' _ he
    subst m'
    rw [Mem.updCells_range]
    refine ⟨rfl, ?_⟩
    simpa only [Mem.store_updBlock, List.length_map, List.length_range] using
      (Store.readBlock_updBlock_self (s := m.store) (b := z.1) (off := z.2)
        (xs := (List.range n).map v) (by simpa using hroom))

end NLAlib.Ops
