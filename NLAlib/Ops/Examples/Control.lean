/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Logic

/-!
# Example: tests and index binders, run on words

A concrete interpretation on natural-number words, with a test (`nz`) and an index conversion
(`toNat`), and the runs of three small programs checked by evaluation:

## Main results

* `whileFuel` runs while the test holds and **fails** when the fuel is exhausted;
* `bindIdx` binds the number returned and **fails** when it exceeds the bound (nothing is
  clamped);
* `ite` branches on the test.

`NLAlib.Ops.Examples.isTest_ctlInterp_nz` and `NLAlib.Ops.Examples.index_ctlInterp_toNat`: the
interpretation meets
the exactness clauses that an access model imposes on tests and index conversions.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

/-- Operations on counters. -/
inductive COp where
  /-- Decrement a cell. -/
  | dec
  /-- Increment a cell. -/
  | inc
  deriving DecidableEq

/-- Queries on counters. -/
inductive CTst where
  /-- Test: the cell is not zero. -/
  | nz
  /-- Index: the number in the cell. -/
  | toNat
  deriving DecidableEq

/-- A concrete interpretation on natural-number words. -/
def ctlInterp : Interp COp CTst ℕ where
  call o d ins outs τ m :=
    match o with
    | .dec => (BlockFn.un fun a => some (a - 1)).apply d ins outs τ m
    | .inc => (BlockFn.un fun a => some (a + 1)).apply d ins outs τ m
  test o _ a m :=
    match o, a with
    | .nz, [x] => (m.store.get x.1 x.2).map fun v => v != 0
    | _, _ => none
  index o a m :=
    match o, a with
    | .toNat, [x] => m.store.get x.1 x.2
    | _, _ => none

/-- The test `nz` is exact. -/
theorem isTest_ctlInterp_nz :
    ctlInterp.IsTest .nz (fun _ => [1]) fun _ xs => xs.flatten.all (· != 0) := by
  intro d a m xs h
  rcases a with _ | ⟨x, _ | ⟨y, a⟩⟩
  · simp [Mem.readBlocks] at h
  · simp only [Mem.readBlocks, BlockFn.readBlock_one] at h
    cases hx : m.store.get x.1 x.2 with
    | none => simp [hx] at h
    | some v =>
      simp only [hx, Option.map_some, Option.bind_some, Option.some.injEq] at h
      subst h
      simp [ctlInterp, hx]
  · simp [Mem.readBlocks] at h

/-- The index conversion `toNat` is exact on one cell. -/
theorem index_ctlInterp_toNat (x : ℕ × ℕ) (m : Mem ℕ) (v : ℕ) (h : m.store.get x.1 x.2 = some v) :
    ctlInterp.index .toNat [x] m = some v := h

/-- Move the counter in cell `0` to cell `1`, one unit at a time, for at most `5` rounds. -/
def countdown : Stmt COp CTst :=
  .whileFuel (.const 5) .nz [] [⟨0, .const 0⟩]
    (.seq (.call .dec [] [⟨0, .const 0⟩] [⟨0, .const 0⟩])
      (.call .inc [] [⟨0, .const 1⟩] [⟨0, .const 1⟩])) .skip

/-- The same loop, strict: the run fails if the counter is not zero after `5` rounds. -/
def countdownStrict : Stmt COp CTst :=
  .whileStrict 0 (.const 5) .nz [] [⟨0, .const 0⟩]
    (.seq (.call .dec [] [⟨0, .const 0⟩] [⟨0, .const 0⟩])
      (.call .inc [] [⟨0, .const 1⟩] [⟨0, .const 1⟩]))

/-- Decrement cell `0` while it is not zero, for at most `5` rounds; then add **the number of
rounds done** to cell `1`: the continuation of the loop is given the round index. -/
def countRounds : Stmt COp CTst :=
  .whileFuel (.const 5) .nz [] [⟨0, .const 0⟩] (.call .dec [] [⟨0, .const 0⟩] [⟨0, .const 0⟩])
    (.loop (.var 0) (.call .inc [] [⟨0, .const 1⟩] [⟨0, .const 1⟩]))

/-- Add the number in cell `0`, at most `4`, to cell `1`. -/
def addIdx : Stmt COp CTst :=
  .bindIdx .toNat [⟨0, .const 0⟩] (.const 4)
    (.loop (.var 0) (.call .inc [] [⟨0, .const 1⟩] [⟨0, .const 1⟩]))

/-- Increment cell `1` if cell `0` is not zero. -/
def incIf : Stmt COp CTst :=
  .ite .nz [] [⟨0, .const 0⟩] (.call .inc [] [⟨0, .const 1⟩] [⟨0, .const 1⟩]) .skip

/-- The memory with one buffer of two cells holding `a` and `b`. -/
def twoCells (a b : ℕ) : Mem ℕ := ⟨[[some a, some b]], 0⟩

example : eval ctlInterp (fun _ => 0) countdown ⟨[], [0]⟩ (twoCells 3 0) = some (twoCells 0 3) := by
  rfl

/-- At the cap the loop stops, with the current state: no failure. -/
example : eval ctlInterp (fun _ => 0) countdown ⟨[], [0]⟩ (twoCells 7 0) = some (twoCells 2 5) := by
  rfl

example : eval ctlInterp (fun _ => 0) countdownStrict ⟨[], [0]⟩ (twoCells 3 0) =
    some (twoCells 0 3) := by rfl

/-- The strict loop: the test still holds after the fuel, the run fails. -/
example : eval ctlInterp (fun _ => 0) countdownStrict ⟨[], [0]⟩ (twoCells 7 0) = none := by rfl

/-- The continuation receives the number of rounds done: `3` when the test ends the loop. -/
example : eval ctlInterp (fun _ => 0) countRounds ⟨[], [0]⟩ (twoCells 3 0) =
    some (twoCells 0 3) := by rfl

/-- The continuation receives the number of rounds done: the cap `5` when it is reached. -/
example : eval ctlInterp (fun _ => 0) countRounds ⟨[], [0]⟩ (twoCells 7 10) =
    some (twoCells 2 15) := by rfl

example : eval ctlInterp (fun _ => 0) addIdx ⟨[], [0]⟩ (twoCells 3 10) = some (twoCells 3 13) := by
  rfl

/-- The index exceeds the bound: the run fails, nothing is clamped. -/
example : eval ctlInterp (fun _ => 0) addIdx ⟨[], [0]⟩ (twoCells 5 10) = none := by rfl

example : eval ctlInterp (fun _ => 0) incIf ⟨[], [0]⟩ (twoCells 2 0) = some (twoCells 2 1) := by rfl

example : eval ctlInterp (fun _ => 0) incIf ⟨[], [0]⟩ (twoCells 0 0) = some (twoCells 0 0) := by rfl

/-- Linking leaves queries alone: no table can implement a test. -/
example (T : Table COp COp CTst) :
    incIf.link T = .ite .nz [] [⟨0, .const 0⟩]
      ((Stmt.call .inc [] [⟨0, .const 1⟩] [⟨0, .const 1⟩]).link T) .skip := rfl

/-- Write the positivity flag of the first cell to the second cell and succeed if it is set. -/
def branchOnPositive : Stmt CmpOp FlagTst :=
  .seq (.call (.cmp .isPos) [] [⟨0, .const 0⟩] [⟨0, .const 1⟩])
    (.ite .isSet [] [⟨0, .const 1⟩] .skip .abort)

-- A substituted comparison supplies the flag for the primitive test.
example {K Lo : Type} {I : Interp Lo FlagTst K} {T : Table CmpOp Lo FlagTst}
    {R : Impl Lo FlagTst} (hT : T (.cmp .isPos) = .inl R)
    {dec : K → ℝ} {readFlag : K → Bool}
    (hcmp : R.Meets I .total ((cmpRel dec readFlag .isPos).spec AnyOperands))
    (hflag : IsFlagTest readFlag I) {τ : Tape K} {m : Mem K} {a : K}
    (hx : m.store.get 0 0 = some a) (hpos : 0 < dec a)
    (hl : m.Live [(0, 0), (0, 1)]) (hz : 1 < m.store.len 0) :
    Wp .total I τ (branchOnPositive.link T) ⟨[], [0]⟩
      (fun m' => ∃ flag, m'.store.get 0 1 = some flag ∧ readFlag flag = true) m := by
  have hrun : Wp .total (I.link T) τ branchOnPositive ⟨[], [0]⟩
      (fun m' => ∃ flag, m'.store.get 0 1 = some flag ∧ readFlag flag = true) m := by
    unfold branchOnPositive
    refine wp_seq (wp_call_rel_cell (Interp.link_meets hT hcmp) rfl rfl rfl rfl rfl rfl trivial
      hl (BlockFn.readBlocks_cells_one.mpr ⟨a, hx, rfl⟩) trivial hz ?_)
    intro flag hf
    have hread : ((m.upd (0, 1) flag).advance 0).store.get 0 1 = some flag :=
      Store.get_upd_self hz flag
    have hbit : readFlag flag = true := by
      change readFlag flag = CmpTst.fn dec .isPos [[a]] at hf
      simpa [CmpTst.fn, hpos] using hf
    have htest : IsFlagTest readFlag (I.link T) := hflag
    refine wp_ite (c := true) rfl rfl ?_ (wp_skip ⟨flag, hread, hbit⟩)
    change (I.link T).test (Has.inj FlagTst.isSet) [] [(0, 1)]
      ((m.upd (0, 1) flag).advance 0) = some true
    rw [htest.test_isSet (x := (0, 1)) hread, hbit]
  simpa only [Wp, run_link] using hrun

end NLAlib.Ops.Examples
