/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.BlockRel

/-!
# Functional contracts: block functions

A **functional** contract is a contract in operand form whose relation is the graph of a
function. `NLAlib.Ops.BlockFn` is such a function (of the dimensions, the entries of the tape
window and the input blocks, to the output blocks), `NLAlib.Ops.BlockFn.rel` the relation it
defines, and `NLAlib.Ops.Interp.IsFn` says an operation meets its contract. Under `IsFn` a call
is an equation: it is `NLAlib.Ops.BlockFn.apply`, the effect of the function on the memory
(`NLAlib.Ops.Interp.IsFn.callS_eq`, `NLAlib.Ops.Interp.IsFn.apply_of_callS`).

`NLAlib.Ops.Interp.ofFns` is the interpretation whose operations are given block functions
(model primitives, concrete formats, witnesses).

The common shapes: scalar functions on cells (`NLAlib.Ops.BlockFn.const`, `un`, `bin`, `tern`,
`draw`), a vector draw (`drawVec`) and functions of one, two or three blocks (`of1`, `of2`,
`of3`).

## Main results

* `NLAlib.Ops.BlockFn.apply_eq_some_iff`: the effect of a block function, unfolded.
* `NLAlib.Ops.Interp.IsFn.callS_eq`: under a functional contract a call is an equation.
* `NLAlib.Ops.Interp.ofFns_isFn`: an interpretation given by block functions meets their
  functional contracts.
* `NLAlib.Ops.BlockFn.apply_bin_eq_some_iff` and its analogues: calls of scalar block functions,
  on cells.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- **A block function**: the output blocks as a function of the dimensions, the entries of the
tape window and the input blocks. `nd` is the number of dimensions, `win` the length of the
window (zero for an operation that does not draw) in the stream `stream`, `inLens` and `outLens`
the lengths of the input and output blocks. -/
structure BlockFn (K : Type) where
  /-- The number of dimensions. -/
  nd : ℕ
  /-- The stream of the tape that the window is read from. -/
  stream : ℕ := 0
  /-- The length of the tape window read at the dimensions. -/
  win : List ℕ → ℕ := fun _ => 0
  /-- The lengths of the input blocks at the dimensions. -/
  inLens : List ℕ → List ℕ
  /-- The lengths of the output blocks at the dimensions. -/
  outLens : List ℕ → List ℕ
  /-- The output blocks. -/
  fn : List ℕ → List K → List (List K) → Option (List (List K))

namespace BlockFn

/-- **The contract in operand form of a block function**: the relation is its graph, the domain
is where it is defined with outputs of the declared lengths. -/
@[simps (attr := storeNF)]
def rel (f : BlockFn K) : BlockRel K where
  nd := f.nd
  stream := f.stream
  win := f.win
  inLens := f.inLens
  outLens := f.outLens
  dom d xs w := ∃ ys, f.fn d w xs = some ys ∧ ys.map List.length = f.outLens d
  rel d xs w ys := f.fn d w xs = some ys

/-- The effect of a block function on the memory: read the input blocks and the tape window,
apply the function, write the output blocks at `outs`, advance the tape. It fails if the number
of dimensions is wrong, if an operand handle is not a buffer of the store, if a block cannot be
read, if the outputs do not have the declared lengths or if there is no room for them. -/
def apply (f : BlockFn K) (d : List ℕ) (ins outs : List (ℕ × ℕ)) (τ : Tape K) (m : Mem K) :
    Option (Mem K) :=
  if d.length = f.nd ∧ m.Live (ins ++ outs) then
    (m.readBlocks ins (f.inLens d)).bind fun xs =>
      (f.fn d (τ.window f.stream m.pos (f.win d)) xs).bind fun ys =>
        if ys.map List.length = f.outLens d then
          (m.writes outs ys).map fun m' => m'.advance (f.win d)
        else none
  else none

/-- The effect of a block function, unfolded. -/
theorem apply_eq_some_iff {f : BlockFn K} {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K}
    {m m' : Mem K} :
    f.apply d ins outs τ m = some m' ↔ d.length = f.nd ∧ m.Live (ins ++ outs) ∧
      ∃ xs ys, m.readBlocks ins (f.inLens d) = some xs ∧
      f.fn d (τ.window f.stream m.pos (f.win d)) xs = some ys ∧
      ys.map List.length = f.outLens d ∧ m.Room outs (f.outLens d) ∧
      m' = (m.updBlocks outs ys).advance (f.win d) := by
  unfold apply
  by_cases hl : d.length = f.nd ∧ m.Live (ins ++ outs)
  · simp only [hl, and_self, if_true, true_and, Option.bind_eq_some_iff]
    constructor
    · rintro ⟨xs, hxs, ys, hys, h⟩
      split_ifs at h with hlen
      obtain ⟨m₁, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hroom, rfl⟩ := Mem.writes_eq_some_iff.mp hw
      exact ⟨xs, ys, hxs, hys, hlen, hlen ▸ hroom, rfl⟩
    · rintro ⟨xs, ys, hxs, hys, hlen, hroom, rfl⟩
      refine ⟨xs, hxs, ys, hys, ?_⟩
      rw [if_pos hlen, Mem.writes_eq_some_iff.mpr ⟨hlen ▸ hroom, rfl⟩]
      rfl
  · rw [if_neg hl]
    exact iff_of_false (by simp) fun h => hl ⟨h.1, h.2.1⟩

theorem shape_of_apply {f : BlockFn K} {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K}
    {m m' : Mem K} (h : f.apply d ins outs τ m = some m') : m'.store.shape = m.store.shape := by
  obtain ⟨-, -, xs, ys, -, -, -, -, rfl⟩ := apply_eq_some_iff.mp h
  simp

/-- **A call from the blocks that were read.** -/
theorem apply_of_read {f : BlockFn K} {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K}
    {m : Mem K} {xs ys : List (List K)} (hnd : d.length = f.nd) (hl : m.Live (ins ++ outs))
    (hread : m.readBlocks ins (f.inLens d) = some xs)
    (hfn : f.fn d (τ.window f.stream m.pos (f.win d)) xs = some ys)
    (hlen : ys.map List.length = f.outLens d) (hz : m.Room outs (f.outLens d)) :
    f.apply d ins outs τ m = some ((m.updBlocks outs ys).advance (f.win d)) :=
  apply_eq_some_iff.mpr ⟨hnd, hl, xs, ys, hread, hfn, hlen, hz, rfl⟩

end BlockFn

/-- **The operation `o` of `I` is the block function `f`** on the admitted operands, in the mode
`md`: it meets the contract in operand form of `f`. -/
def Interp.IsFn (I : Interp Op Tst K) (md : Mode) (o : Op) (f : BlockFn K)
    (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop) : Prop :=
  I.Meets md o (f.rel.spec adm)

/-- **A call of a functional operation is an equation.** -/
theorem Interp.IsFn.callS_eq {I : Interp Op Tst K} {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (h : I.IsFn .total o f adm)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m m' : Mem K} (hadm : adm d ins outs)
    (ha : f.apply d ins outs τ m = some m') : I.callS o d ins outs τ m = some m' := by
  obtain ⟨hnd, hl, xs, ys, hxs, hys, hlen, hroom, rfl⟩ := BlockFn.apply_eq_some_iff.mp ha
  obtain ⟨m₁, h₁, xs', hxs', -, ys', -, hys', rfl⟩ :=
    h d ins outs τ m ⟨hnd, hadm, fun _ => ⟨hl, ⟨xs, hxs, ys, hys, hlen⟩, hroom⟩⟩
  have hxs'' : m.readBlocks ins (f.inLens d) = some xs' := hxs'
  rw [hxs] at hxs''
  cases hxs''
  have e : ys' = ys := Option.some.inj (hys'.symm.trans hys)
  rw [h₁, e]
  rfl

/-- In liberal mode: a successful call of a functional operation is `apply`. -/
theorem Interp.IsFn.apply_of_callS {I : Interp Op Tst K} {o : Op} {f : BlockFn K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop} (h : I.IsFn .liberal o f adm)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape K} {m m' : Mem K} (hnd : d.length = f.nd)
    (hadm : adm d ins outs) (hc : I.callS o d ins outs τ m = some m') :
    f.apply d ins outs τ m = some m' := by
  obtain ⟨xs, hxs, hroom, ys, hlen, hys, rfl⟩ := h d ins outs τ m ⟨hnd, hadm, by simp⟩ m' hc
  exact BlockFn.apply_of_read hnd (Interp.live_of_callS hc) hxs hys hlen hroom

/-- **The interpretation whose operations are given block functions** (model primitives, concrete
formats, witnesses): a call is `apply`; nothing is a test or an index. -/
def Interp.ofFns (F : Op → BlockFn K) : Interp Op Tst K where
  call o d ins outs τ m := (F o).apply d ins outs τ m
  test _ _ _ _ := none
  index _ _ _ := none

theorem Interp.ofFns_callS (F : Op → BlockFn K) (o : Op) (d : List ℕ) (ins outs : List (ℕ × ℕ))
    (τ : Tape K) (m : Mem K) :
    (Interp.ofFns F : Interp Op Tst K).callS o d ins outs τ m = (F o).apply d ins outs τ m := by
  by_cases hl : m.Live (ins ++ outs)
  · simp only [Interp.callS, Interp.ofFns, hl, if_true]
    cases h : (F o).apply d ins outs τ m with
    | none => rfl
    | some m' => simp [BlockFn.shape_of_apply h]
  · simp [Interp.callS, BlockFn.apply, hl]

/-- An interpretation given by block functions meets their functional contracts, in both modes
and on all operands. -/
theorem Interp.ofFns_isFn (F : Op → BlockFn K) (md : Mode) (o : Op)
    (adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop) :
    (Interp.ofFns F : Interp Op Tst K).IsFn md o (F o) adm := by
  rintro d ins outs τ m ⟨hnd, -, hn⟩
  rw [Interp.ofFns_callS]
  cases md with
  | total =>
    obtain ⟨hl, ⟨xs, hxs, ys, hys, hlen⟩, hroom⟩ := hn rfl
    exact ⟨_, BlockFn.apply_of_read hnd hl hxs hys hlen hroom, xs, hxs, hroom, ys, hlen, hys, rfl⟩
  | liberal =>
    intro m' hm'
    obtain ⟨-, -, xs, ys, hxs, hys, hlen, hroom, rfl⟩ := BlockFn.apply_eq_some_iff.mp hm'
    exact ⟨xs, hxs, hroom, ys, hlen, hys, rfl⟩

namespace BlockFn

/-! ### Scalar shapes -/

/-- A constant: no input, one cell. -/
@[simps (attr := storeNF)]
def const (v : K) : BlockFn K where
  nd := 0
  inLens _ := []
  outLens _ := [1]
  fn _ _ xs := match xs with
    | [] => some [[v]]
    | _ => none

/-- A function of one cell. -/
@[simps (attr := storeNF)]
def un (g : K → Option K) : BlockFn K where
  nd := 0
  inLens _ := [1]
  outLens _ := [1]
  fn _ _ xs := match xs with
    | [[a]] => (g a).map fun v => [[v]]
    | _ => none

/-- A function of two cells. -/
@[simps (attr := storeNF)]
def bin (g : K → K → Option K) : BlockFn K where
  nd := 0
  inLens _ := [1, 1]
  outLens _ := [1]
  fn _ _ xs := match xs with
    | [[a], [b]] => (g a b).map fun v => [[v]]
    | _ => none

/-- A function of three cells. -/
@[simps (attr := storeNF)]
def tern (g : K → K → K → Option K) : BlockFn K where
  nd := 0
  inLens _ := [1, 1, 1]
  outLens _ := [1]
  fn _ _ xs := match xs with
    | [[a], [b], [c]] => (g a b c).map fun v => [[v]]
    | _ => none

/-- A draw: the next entry of the stream `s` of the tape, in one cell. -/
@[simps (attr := storeNF)]
def draw (s : ℕ) : BlockFn K where
  nd := 0
  stream := s
  win _ := 1
  inLens _ := []
  outLens _ := [1]
  fn _ w xs := match w, xs with
    | [ξ], [] => some [[ξ]]
    | _, _ => none

/-- A vector draw at one dimension `n`: the next `n` entries of the stream `s`, in a block. -/
@[simps (attr := storeNF)]
def drawVec (s : ℕ) : BlockFn K where
  nd := 1
  stream := s
  win d := d.headD 0
  inLens _ := []
  outLens d := [d.headD 0]
  fn _ w xs := match xs with
    | [] => some [w]
    | _ => none

theorem readBlock_one (s : Store K) (b off : ℕ) :
    s.readBlock b off 1 = (s.get b off).map fun a => [a] := by
  rw [Store.readBlock_succ]
  cases s.get b off <;> rfl

/-- Reading a list of cells: a cell after the others. -/
theorem readBlocks_cell_cons (m : Mem K) (x : ℕ × ℕ) (as : List (ℕ × ℕ)) (ns : List ℕ) :
    m.readBlocks (x :: as) (1 :: ns) =
      (m.store.get x.1 x.2).bind fun a => (m.readBlocks as ns).map fun xs => [a] :: xs := by
  rw [Mem.readBlocks_cons, readBlock_one]
  cases m.store.get x.1 x.2 <;> rfl

/-- Reading one cell. -/
theorem readBlocks_cells_one {m : Mem K} {x : ℕ × ℕ} {xs : List (List K)} :
    m.readBlocks [x] [1] = some xs ↔ ∃ a, m.store.get x.1 x.2 = some a ∧ xs = [[a]] := by
  cases hx : m.store.get x.1 x.2 <;> simp [readBlocks_cell_cons, hx, eq_comm]

/-- Reading two cells. -/
theorem readBlocks_cells_two {m : Mem K} {x y : ℕ × ℕ} {xs : List (List K)} :
    m.readBlocks [x, y] [1, 1] = some xs ↔ ∃ a b, m.store.get x.1 x.2 = some a ∧
      m.store.get y.1 y.2 = some b ∧ xs = [[a], [b]] := by
  cases hx : m.store.get x.1 x.2 <;> cases hy : m.store.get y.1 y.2 <;>
    simp [readBlocks_cell_cons, hx, hy, eq_comm]

/-- Reading three cells. -/
theorem readBlocks_cells_three {m : Mem K} {x y w : ℕ × ℕ} {xs : List (List K)} :
    m.readBlocks [x, y, w] [1, 1, 1] = some xs ↔ ∃ a b c, m.store.get x.1 x.2 = some a ∧
      m.store.get y.1 y.2 = some b ∧ m.store.get w.1 w.2 = some c ∧ xs = [[a], [b], [c]] := by
  cases hx : m.store.get x.1 x.2 <;> cases hy : m.store.get y.1 y.2 <;>
    cases hw : m.store.get w.1 w.2 <;> simp [readBlocks_cell_cons, hx, hy, hw, eq_comm]

/-- The updates of one cell. -/
theorem updBlocks_cell (m : Mem K) (z : ℕ × ℕ) (v : K) : m.updBlocks [z] [[v]] = m.upd z v := rfl

/-- A call of a constant, on cells. -/
theorem apply_const_eq_some_iff {v : K} {z : ℕ × ℕ} {τ : Tape K} {m m' : Mem K} :
    (const v).apply [] [] [z] τ m = some m' ↔ z.2 < m.store.len z.1 ∧ m' = m.upd z v := by
  rw [apply_eq_some_iff]
  constructor
  · rintro ⟨-, -, xs, ys, hxs, hys, -, hroom, rfl⟩
    cases hxs
    cases hys
    exact ⟨hroom.1, rfl⟩
  · rintro ⟨hz, rfl⟩
    exact ⟨rfl, by simp [Store.lt_length_of_lt_len hz], [], [[v]], rfl, rfl, rfl, ⟨hz, trivial⟩,
      rfl⟩

/-- A call of a function of one cell, on cells. -/
theorem apply_un_eq_some_iff {g : K → Option K} {x z : ℕ × ℕ} {τ : Tape K} {m m' : Mem K} :
    (un g).apply [] [x] [z] τ m = some m' ↔ ∃ a v, m.store.get x.1 x.2 = some a ∧ g a = some v ∧
      z.2 < m.store.len z.1 ∧ m' = m.upd z v := by
  rw [apply_eq_some_iff]
  constructor
  · rintro ⟨-, -, xs, ys, hxs, hys, -, hroom, rfl⟩
    obtain ⟨a, ha, rfl⟩ := readBlocks_cells_one.mp hxs
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hys
    exact ⟨a, v, ha, hv, hroom.1, rfl⟩
  · rintro ⟨a, v, ha, hv, hz, rfl⟩
    exact ⟨rfl, by simp [Store.lt_length_of_get ha, Store.lt_length_of_lt_len hz], [[a]], [[v]],
      readBlocks_cells_one.mpr ⟨a, ha, rfl⟩, by simp [un, hv], rfl, ⟨hz, trivial⟩, rfl⟩

/-- A call of a function of two cells, on cells. -/
theorem apply_bin_eq_some_iff {g : K → K → Option K} {x y z : ℕ × ℕ} {τ : Tape K}
    {m m' : Mem K} :
    (bin g).apply [] [x, y] [z] τ m = some m' ↔ ∃ a b v, m.store.get x.1 x.2 = some a ∧
      m.store.get y.1 y.2 = some b ∧ g a b = some v ∧ z.2 < m.store.len z.1 ∧
      m' = m.upd z v := by
  rw [apply_eq_some_iff]
  constructor
  · rintro ⟨-, -, xs, ys, hxs, hys, -, hroom, rfl⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := readBlocks_cells_two.mp hxs
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hys
    exact ⟨a, b, v, ha, hb, hv, hroom.1, rfl⟩
  · rintro ⟨a, b, v, ha, hb, hv, hz, rfl⟩
    exact ⟨rfl, by simp [Store.lt_length_of_get ha, Store.lt_length_of_get hb,
      Store.lt_length_of_lt_len hz], [[a], [b]], [[v]],
      readBlocks_cells_two.mpr ⟨a, b, ha, hb, rfl⟩, by simp [bin, hv], rfl, ⟨hz, trivial⟩, rfl⟩

/-- A call of a function of three cells, on cells. -/
theorem apply_tern_eq_some_iff {g : K → K → K → Option K} {x y w z : ℕ × ℕ} {τ : Tape K}
    {m m' : Mem K} :
    (tern g).apply [] [x, y, w] [z] τ m = some m' ↔ ∃ a b c v, m.store.get x.1 x.2 = some a ∧
      m.store.get y.1 y.2 = some b ∧ m.store.get w.1 w.2 = some c ∧ g a b c = some v ∧
      z.2 < m.store.len z.1 ∧ m' = m.upd z v := by
  rw [apply_eq_some_iff]
  constructor
  · rintro ⟨-, -, xs, ys, hxs, hys, -, hroom, rfl⟩
    obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := readBlocks_cells_three.mp hxs
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hys
    exact ⟨a, b, c, v, ha, hb, hc, hv, hroom.1, rfl⟩
  · rintro ⟨a, b, c, v, ha, hb, hc, hv, hz, rfl⟩
    exact ⟨rfl, by simp [Store.lt_length_of_get ha, Store.lt_length_of_get hb,
      Store.lt_length_of_get hc, Store.lt_length_of_lt_len hz], [[a], [b], [c]], [[v]],
      readBlocks_cells_three.mpr ⟨a, b, c, ha, hb, hc, rfl⟩, by simp [tern, hv], rfl, ⟨hz, trivial⟩,
      rfl⟩

/-- A draw, on cells: the cell receives the tape entry at the position, which advances. -/
theorem apply_draw_eq_some_iff {s : ℕ} {z : ℕ × ℕ} {τ : Tape K} {m m' : Mem K} :
    (draw s : BlockFn K).apply [] [] [z] τ m = some m' ↔
      z.2 < m.store.len z.1 ∧ m' = (m.upd z (τ m.pos s)).advance 1 := by
  rw [apply_eq_some_iff]
  constructor
  · rintro ⟨-, -, xs, ys, hxs, hys, -, hroom, rfl⟩
    cases hxs
    simp only [draw, Tape.window_one, Option.some.injEq] at hys
    subst hys
    exact ⟨hroom.1, rfl⟩
  · rintro ⟨hz, rfl⟩
    exact ⟨rfl, by simp [Store.lt_length_of_lt_len hz], [], [[τ m.pos s]], rfl,
      by simp [draw, Tape.window_one], rfl, ⟨hz, trivial⟩, rfl⟩

/-! ### Functions of blocks -/

/-- A function of one block, at `nd` dimensions; `l` is the length of the input block, `lo`
that of the output block. -/
@[simps (attr := storeNF)]
def of1 (nd : ℕ) (l lo : List ℕ → ℕ) (g : List ℕ → List K → Option (List K)) : BlockFn K where
  nd := nd
  inLens d := [l d]
  outLens d := [lo d]
  fn d _ xs := match xs with
    | [x] => (g d x).map fun y => [y]
    | _ => none

/-- A function of two blocks, at `nd` dimensions. -/
@[simps (attr := storeNF)]
def of2 (nd : ℕ) (l₁ l₂ lo : List ℕ → ℕ) (g : List ℕ → List K → List K → Option (List K)) :
    BlockFn K where
  nd := nd
  inLens d := [l₁ d, l₂ d]
  outLens d := [lo d]
  fn d _ xs := match xs with
    | [x, y] => (g d x y).map fun z => [z]
    | _ => none

/-- A function of three blocks, at `nd` dimensions. -/
@[simps (attr := storeNF)]
def of3 (nd : ℕ) (l₁ l₂ l₃ lo : List ℕ → ℕ)
    (g : List ℕ → List K → List K → List K → Option (List K)) : BlockFn K where
  nd := nd
  inLens d := [l₁ d, l₂ d, l₃ d]
  outLens d := [lo d]
  fn d _ xs := match xs with
    | [x, y, w] => (g d x y w).map fun z => [z]
    | _ => none

end BlockFn

/-- A list as a vector, with the default word outside. -/
abbrev vec [Inhabited K] (xs : List K) : ℕ → K := fun k => xs.getD k default

theorem vec_append_left [Inhabited K] {xs : List K} {i : ℕ} (h : i < xs.length) (ys : List K) :
    vec (xs ++ ys) i = vec xs i := by
  simp [vec, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem vec_concat [Inhabited K] (xs : List K) (v : K) : vec (xs ++ [v]) xs.length = v := by
  simp [vec, List.getD_eq_getElem?_getD]

theorem vec_append_right [Inhabited K] (xs ys : List K) (i : ℕ) :
    vec (xs ++ ys) (xs.length + i) = vec ys i := by
  simp [vec, List.getD_eq_getElem?_getD, List.getElem?_append_right]

end NLAlib.Ops
