/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import NLAlib.Ops.Catalog.Scalar

/-!
# Catalog: comparisons and the conversion to an index

Queries are the names a program uses in a test (`ite`, `whileFuel`) or as an index (`bindIdx`).
They are primitives of the access model, which imposes their exactness; no table implements
them.

* `NLAlib.Ops.CmpTst`: the comparisons `lt`, `le`, `eq` of two cells and `isZero`, `isPos` of one
  cell. Contract `NLAlib.Ops.IsCmp dec`: each is decided exactly on the decoded values
  (`NLAlib.Ops.Interp.IsTest`).
* `NLAlib.Ops.IdxTst.toNat`: the conversion of a cell to a number. Contract
  `NLAlib.Ops.IsToNat dec`: the number is the floor of the decoded value, and **the conversion
  fails on a negative value** (`NLAlib.Ops.Interp.IsIndex`, whose function is `Option`-valued).
  Nothing is clamped: a program that wants a clamp tests first.

Witness: `NLAlib.Ops.exists_isCmp`, on the real numbers.

## Main results

* `NLAlib.Ops.IsCmp`, `NLAlib.Ops.IsToNat`: the contracts.
* `NLAlib.Ops.IsCmp.test_lt` and its analogues, `NLAlib.Ops.IsToNat.index_eq`,
  `NLAlib.Ops.IsToNat.index_neg`: what a query returns on readable cells.
* `NLAlib.Ops.exists_isCmp`: the contracts can be met.
-/

@[expose] public section

namespace NLAlib.Ops

/-- The comparison queries. -/
inductive CmpTst where
  /-- `lt [] [x, y]`: the cell `x` is less than the cell `y`. -/
  | lt
  /-- `le [] [x, y]`: the cell `x` is at most the cell `y`. -/
  | le
  /-- `eq [] [x, y]`: the cells decode to the same number. -/
  | eq
  /-- `isZero [] [x]`: the cell decodes to zero. -/
  | isZero
  /-- `isPos [] [x]`: the cell decodes to a positive number. -/
  | isPos
  deriving DecidableEq

/-- The conversion of a cell to an index. -/
inductive IdxTst where
  /-- `toNat [x]`: the floor of the cell; fails on a negative value. -/
  | toNat
  deriving DecidableEq

variable {K Op Tst : Type}

/-- The lengths of the blocks a comparison reads. -/
def CmpTst.lens : CmpTst → List ℕ
  | .lt => [1, 1]
  | .le => [1, 1]
  | .eq => [1, 1]
  | .isZero => [1]
  | .isPos => [1]

open Classical in
/-- The Boolean of a comparison, on the decoded values of the cells read. -/
noncomputable def CmpTst.fn (dec : K → ℝ) : CmpTst → List (List K) → Bool
  | .lt, [[a], [b]] => decide (dec a < dec b)
  | .le, [[a], [b]] => decide (dec a ≤ dec b)
  | .eq, [[a], [b]] => decide (dec a = dec b)
  | .isZero, [[a]] => decide (dec a = 0)
  | .isPos, [[a]] => decide (0 < dec a)
  | _, _ => false

/-- **The contract of the comparisons**: each is exact on the decoded values. -/
def IsCmp [Has CmpTst Tst] (dec : K → ℝ) (I : Interp Op Tst K) : Prop :=
  ∀ c : CmpTst, I.IsTest (Has.inj c) (fun _ => c.lens) fun _ xs => c.fn dec xs

/-- The conversion of one cell: the floor of a nonnegative value, nothing otherwise. -/
noncomputable def toNatFn (dec : K → ℝ) : List K → Option ℕ
  | [w] => if 0 ≤ dec w then some ⌊dec w⌋₊ else none
  | _ => none

/-- **The contract of the conversion to an index**: the floor of a nonnegative value; failure on
a negative value. -/
def IsToNat [Has IdxTst Tst] (dec : K → ℝ) (I : Interp Op Tst K) : Prop :=
  I.IsIndex (Has.inj IdxTst.toNat) (toNatFn dec)

section Use

variable [Has CmpTst Tst] {dec : K → ℝ} {I : Interp Op Tst K}

open Classical in
/-- `lt` on two readable cells. -/
theorem IsCmp.test_lt (h : IsCmp dec I) {d : List ℕ} {x y : ℕ × ℕ} {m : Mem K} {a b : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b) :
    I.test (Has.inj CmpTst.lt) d [x, y] m = some (decide (dec a < dec b)) :=
  h .lt d [x, y] m [[a], [b]] (BlockFn.readBlocks_cells_two.mpr ⟨a, b, hx, hy, rfl⟩)

open Classical in
/-- `le` on two readable cells. -/
theorem IsCmp.test_le (h : IsCmp dec I) {d : List ℕ} {x y : ℕ × ℕ} {m : Mem K} {a b : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b) :
    I.test (Has.inj CmpTst.le) d [x, y] m = some (decide (dec a ≤ dec b)) :=
  h .le d [x, y] m [[a], [b]] (BlockFn.readBlocks_cells_two.mpr ⟨a, b, hx, hy, rfl⟩)

open Classical in
/-- `eq` on two readable cells. -/
theorem IsCmp.test_eq (h : IsCmp dec I) {d : List ℕ} {x y : ℕ × ℕ} {m : Mem K} {a b : K}
    (hx : m.store.get x.1 x.2 = some a) (hy : m.store.get y.1 y.2 = some b) :
    I.test (Has.inj CmpTst.eq) d [x, y] m = some (decide (dec a = dec b)) :=
  h .eq d [x, y] m [[a], [b]] (BlockFn.readBlocks_cells_two.mpr ⟨a, b, hx, hy, rfl⟩)

open Classical in
/-- `isZero` on a readable cell. -/
theorem IsCmp.test_isZero (h : IsCmp dec I) {d : List ℕ} {x : ℕ × ℕ} {m : Mem K} {a : K}
    (hx : m.store.get x.1 x.2 = some a) :
    I.test (Has.inj CmpTst.isZero) d [x] m = some (decide (dec a = 0)) :=
  h .isZero d [x] m [[a]] (BlockFn.readBlocks_cells_one.mpr ⟨a, hx, rfl⟩)

open Classical in
/-- `isPos` on a readable cell. -/
theorem IsCmp.test_isPos (h : IsCmp dec I) {d : List ℕ} {x : ℕ × ℕ} {m : Mem K} {a : K}
    (hx : m.store.get x.1 x.2 = some a) :
    I.test (Has.inj CmpTst.isPos) d [x] m = some (decide (0 < dec a)) :=
  h .isPos d [x] m [[a]] (BlockFn.readBlocks_cells_one.mpr ⟨a, hx, rfl⟩)

end Use

section UseIdx

variable [Has IdxTst Tst] {dec : K → ℝ} {I : Interp Op Tst K}

/-- The conversion of a readable cell with a nonnegative value is its floor. -/
theorem IsToNat.index_eq (h : IsToNat dec I) {x : ℕ × ℕ} {m : Mem K} {w : K}
    (hx : m.store.get x.1 x.2 = some w) (hw : 0 ≤ dec w) :
    I.index (Has.inj IdxTst.toNat) [x] m = some ⌊dec w⌋₊ := by
  rw [h [x] m [[w]] (BlockFn.readBlocks_cells_one.mpr ⟨w, hx, rfl⟩)]
  simp [toNatFn, hw]

/-- **The conversion of a negative value fails**: nothing is clamped. -/
theorem IsToNat.index_neg (h : IsToNat dec I) {x : ℕ × ℕ} {m : Mem K} {w : K}
    (hx : m.store.get x.1 x.2 = some w) (hw : dec w < 0) :
    I.index (Has.inj IdxTst.toNat) [x] m = none := by
  rw [h [x] m [[w]] (BlockFn.readBlocks_cells_one.mpr ⟨w, hx, rfl⟩)]
  simp [toNatFn, not_le.mpr hw]

end UseIdx

/-- The interpretation of the queries on real numbers: exact comparisons, and the floor of a
nonnegative cell. It has no operation. -/
noncomputable def cmpInterp : Interp Empty (CmpTst ⊕ IdxTst) ℝ where
  call o := o.elim
  test q _ a m := match q with
    | .inl c => (m.readBlocks a c.lens).map (c.fn id)
    | .inr _ => none
  index q a m := match q with
    | .inr .toNat => (m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn id xs.flatten
    | .inl _ => none

/-- **Witness**: the contracts of the comparisons and of the conversion to an index can be met
together. -/
theorem exists_isCmp : ∃ (K : Type) (dec : K → ℝ) (I : Interp Empty (CmpTst ⊕ IdxTst) K),
    IsCmp dec I ∧ IsToNat dec I :=
  ⟨ℝ, id, cmpInterp, fun c d a m xs h => by
    change (m.readBlocks a c.lens).map (c.fn id) = _
    rw [h]
    rfl, fun a m xs h => by
    change ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn id xs.flatten) = _
    rw [h]
    rfl⟩

end NLAlib.Ops
