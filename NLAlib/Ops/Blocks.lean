/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Contract

/-!
# Shapes of block functions and block relations

The common shapes of functional contracts, each with the lemma that unfolds a call, so that no
block function needs its own: scalar functions on cells (`NLAlib.Ops.BlockFn.const`, `un`, `bin`,
`tern`, `draw`) and functions of one, two or three blocks at a fixed number of dimensions
(`NLAlib.Ops.BlockFn.of1`, `of2`, `of3`).

A relational contract in operand form is a `NLAlib.Ops.BlockRel`: the lengths of the input
blocks and of the output block, and a relation between the input blocks and the output block.
Its contract `NLAlib.Ops.BlockRel.spec` reads only the operands, by construction.

## Main results

* `NLAlib.Ops.BlockFn.apply_bin_eq_some_iff` and its analogues: calls of scalar block functions,
  on cells.
* `NLAlib.Ops.BlockFn.apply_of2_eq_some_iff` and its analogues: calls of block functions, on
  blocks.
* `NLAlib.Ops.BlockFn.apply_of_read`: a call from the blocks that were read.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

namespace Mem

/-- Reading one block. -/
theorem readBlocks_one {m : Mem K} {as : List (ℕ × ℕ)} {p : ℕ} {X : List (List K)}
    (h : m.readBlocks as [p] = some X) : ∃ x xs, as = [x] ∧
      m.store.readBlock x.1 x.2 p = some xs ∧ X = [xs] := by
  rcases as with _ | ⟨x, _ | ⟨y, as⟩⟩
  · simp [readBlocks] at h
  · cases hx : m.store.readBlock x.1 x.2 p with
    | none => simp [readBlocks, hx] at h
    | some xs =>
      simp only [readBlocks, hx, Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨x, xs, rfl, hx, h.symm⟩
  · simp [readBlocks] at h

end Mem

namespace BlockFn

/-- The effect of a block function on live operands. -/
def applyL (f : BlockFn K) (d : List ℕ) (ins : List (ℕ × ℕ)) (z : ℕ × ℕ) (τ : ℕ → K)
    (m : Mem K) : Option (Mem K) :=
  (m.readBlocks ins (f.inLens d)).bind fun xs =>
    (f.fn d ((List.range (f.win d)).map fun j => τ (m.pos + j)) xs).bind fun ys =>
      (m.write z ys).map fun m' => m'.advance (f.win d)

theorem apply_of_live {f : BlockFn K} {d : List ℕ} {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K}
    {m : Mem K} (h : m.Live (ins ++ [z])) : f.apply d ins z τ m = f.applyL d ins z τ m :=
  if_pos h

theorem apply_of_not_live {f : BlockFn K} {d : List ℕ} {ins : List (ℕ × ℕ)} {z : ℕ × ℕ}
    {τ : ℕ → K} {m : Mem K} (h : ¬ m.Live (ins ++ [z])) : f.apply d ins z τ m = none :=
  if_neg h

/-- **A call from the blocks that were read.** -/
theorem apply_of_read {f : BlockFn K} {d : List ℕ} {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K}
    {m : Mem K} {xs : List (List K)} {ys : List K} (hl : m.Live (ins ++ [z]))
    (hread : m.readBlocks ins (f.inLens d) = some xs)
    (hfn : f.fn d ((List.range (f.win d)).map fun j => τ (m.pos + j)) xs = some ys)
    (hz : z.2 + ys.length ≤ m.store.len z.1) :
    f.apply d ins z τ m = some ((m.updBlock z ys).advance (f.win d)) :=
  apply_eq_some_iff.mpr ⟨hl, xs, ys, hread, hfn, hz, rfl⟩

/-- A constant: no input, one cell. -/
def const (v : K) : BlockFn K where
  inLens _ := []
  fn _ _ xs := match xs with
    | [] => some [v]
    | _ => none

/-- A function of one cell. -/
def un (g : K → Option K) : BlockFn K where
  inLens _ := [1]
  fn _ _ xs := match xs with
    | [[a]] => (g a).map fun v => [v]
    | _ => none

/-- A function of two cells. -/
def bin (g : K → K → Option K) : BlockFn K where
  inLens _ := [1, 1]
  fn _ _ xs := match xs with
    | [[a], [b]] => (g a b).map fun v => [v]
    | _ => none

/-- A function of three cells. -/
def tern (g : K → K → K → Option K) : BlockFn K where
  inLens _ := [1, 1, 1]
  fn _ _ xs := match xs with
    | [[a], [b], [c]] => (g a b c).map fun v => [v]
    | _ => none

/-- A draw: the next entry of the tape, in one cell. -/
def draw : BlockFn K where
  win _ := 1
  inLens _ := []
  fn _ w xs := match w, xs with
    | [ξ], [] => some [ξ]
    | _, _ => none

theorem readBlock_one (s : Store K) (b off : ℕ) :
    s.readBlock b off 1 = (s.get b off).map fun a => [a] := by
  rw [Store.readBlock_succ]
  cases s.get b off <;> rfl

theorem write_one (m : Mem K) (z : ℕ × ℕ) (v : K) :
    m.write z [v] = if z.2 < m.store.len z.1 then some (m.upd z v) else none := by
  simp only [Mem.write, List.length_singleton, Nat.add_one_le_iff]
  rfl

/-- A call of a constant, on cells. -/
theorem apply_const_eq_some_iff {v : K} {d : List ℕ} {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K} :
    (const v).apply d [] z τ m = some m' ↔ z.2 < m.store.len z.1 ∧ m' = m.upd z v := by
  by_cases hl : m.Live ([] ++ [z])
  swap
  · rw [apply_of_not_live hl]
    refine iff_of_false (by simp) fun h => hl ?_
    obtain ⟨hz, -⟩ := h
    simp [Store.lt_length_of_lt_len hz]
  rw [apply_of_live hl]
  simp only [applyL, const, Mem.readBlocks_nil, Option.bind_some, write_one]
  split_ifs with h <;> simp [h, eq_comm]

/-- A call of a function of one cell, on cells. -/
theorem apply_un_eq_some_iff {g : K → Option K} {d : List ℕ} {x z : ℕ × ℕ} {τ : ℕ → K}
    {m m' : Mem K} :
    (un g).apply d [x] z τ m = some m' ↔ ∃ a v, m.store.get x.1 x.2 = some a ∧ g a = some v ∧
      z.2 < m.store.len z.1 ∧ m' = m.upd z v := by
  by_cases hl : m.Live ([x] ++ [z])
  swap
  · rw [apply_of_not_live hl]
    refine iff_of_false (by simp) fun h => hl ?_
    obtain ⟨a, v, hx, -, hz, -⟩ := h
    simp [Store.lt_length_of_get hx, Store.lt_length_of_lt_len hz]
  rw [apply_of_live hl]
  cases hx : m.store.get x.1 x.2 with
  | none => simp [applyL, un, Mem.readBlocks_cons, readBlock_one, hx]
  | some a =>
    cases hg : g a with
    | none => simp [applyL, un, Mem.readBlocks_cons, readBlock_one, hx, hg]
    | some v =>
      by_cases h : z.2 < m.store.len z.1 <;>
        simp [applyL, un, Mem.readBlocks_cons, readBlock_one, hx, hg, write_one, h, eq_comm]

/-- A call of a function of two cells, on cells. -/
theorem apply_bin_eq_some_iff {g : K → K → Option K} {d : List ℕ} {x y z : ℕ × ℕ} {τ : ℕ → K}
    {m m' : Mem K} :
    (bin g).apply d [x, y] z τ m = some m' ↔ ∃ a b v, m.store.get x.1 x.2 = some a ∧
      m.store.get y.1 y.2 = some b ∧ g a b = some v ∧ z.2 < m.store.len z.1 ∧
      m' = m.upd z v := by
  by_cases hl : m.Live ([x, y] ++ [z])
  swap
  · rw [apply_of_not_live hl]
    refine iff_of_false (by simp) fun h => hl ?_
    obtain ⟨a, b, v, hx, hy, -, hz, -⟩ := h
    simp [Store.lt_length_of_get hx, Store.lt_length_of_get hy, Store.lt_length_of_lt_len hz]
  rw [apply_of_live hl]
  cases hx : m.store.get x.1 x.2 with
  | none => simp [applyL, bin, Mem.readBlocks_cons, readBlock_one, hx]
  | some a =>
    cases hy : m.store.get y.1 y.2 with
    | none => simp [applyL, bin, Mem.readBlocks_cons, readBlock_one, hx, hy]
    | some b =>
      cases hg : g a b with
      | none => simp [applyL, bin, Mem.readBlocks_cons, readBlock_one, hx, hy, hg]
      | some v =>
        by_cases h : z.2 < m.store.len z.1 <;>
          simp [applyL, bin, Mem.readBlocks_cons, readBlock_one, hx, hy, hg, write_one, h, eq_comm]

/-- A call of a function of three cells, on cells. -/
theorem apply_tern_eq_some_iff {g : K → K → K → Option K} {d : List ℕ} {x y w z : ℕ × ℕ}
    {τ : ℕ → K} {m m' : Mem K} :
    (tern g).apply d [x, y, w] z τ m = some m' ↔ ∃ a b c v, m.store.get x.1 x.2 = some a ∧
      m.store.get y.1 y.2 = some b ∧ m.store.get w.1 w.2 = some c ∧ g a b c = some v ∧
      z.2 < m.store.len z.1 ∧ m' = m.upd z v := by
  by_cases hl : m.Live ([x, y, w] ++ [z])
  swap
  · rw [apply_of_not_live hl]
    refine iff_of_false (by simp) fun h => hl ?_
    obtain ⟨a, b, c, v, hx, hy, hw, -, hz, -⟩ := h
    simp [Store.lt_length_of_get hx, Store.lt_length_of_get hy, Store.lt_length_of_get hw,
      Store.lt_length_of_lt_len hz]
  rw [apply_of_live hl]
  cases hx : m.store.get x.1 x.2 with
  | none => simp [applyL, tern, Mem.readBlocks_cons, readBlock_one, hx]
  | some a =>
    cases hy : m.store.get y.1 y.2 with
    | none => simp [applyL, tern, Mem.readBlocks_cons, readBlock_one, hx, hy]
    | some b =>
      cases hw : m.store.get w.1 w.2 with
      | none => simp [applyL, tern, Mem.readBlocks_cons, readBlock_one, hx, hy, hw]
      | some c =>
        cases hg : g a b c with
        | none => simp [applyL, tern, Mem.readBlocks_cons, readBlock_one, hx, hy, hw, hg]
        | some v =>
          by_cases h : z.2 < m.store.len z.1 <;>
            simp [applyL, tern, Mem.readBlocks_cons, readBlock_one, hx, hy, hw, hg, write_one, h,
              eq_comm]

/-- A draw, on cells: the cell receives the tape entry at the position, which advances. -/
theorem apply_draw_eq_some_iff {d : List ℕ} {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K} :
    (draw : BlockFn K).apply d [] z τ m = some m' ↔
      z.2 < m.store.len z.1 ∧ m' = (m.upd z (τ m.pos)).advance 1 := by
  by_cases hl : m.Live ([] ++ [z])
  swap
  · rw [apply_of_not_live hl]
    refine iff_of_false (by simp) fun h => hl ?_
    obtain ⟨hz, -⟩ := h
    simp [Store.lt_length_of_lt_len hz]
  rw [apply_of_live hl]
  simp only [applyL, draw, Mem.readBlocks_nil, Option.bind_some, List.range_one, List.map_cons,
    List.map_nil, Nat.add_zero, write_one]
  split_ifs with h <;> simp [h, eq_comm]


/-! ### Functions of blocks -/

/-- A function of one block, at `nd` dimensions; `l` is the length of the input block. -/
def of1 (nd : ℕ) (l : List ℕ → ℕ) (g : List ℕ → List K → Option (List K)) : BlockFn K where
  inLens d := [l d]
  fn d _ xs := if d.length = nd then
      match xs with
      | [x] => g d x
      | _ => none
    else none

/-- A function of two blocks, at `nd` dimensions. -/
def of2 (nd : ℕ) (l₁ l₂ : List ℕ → ℕ) (g : List ℕ → List K → List K → Option (List K)) :
    BlockFn K where
  inLens d := [l₁ d, l₂ d]
  fn d _ xs := if d.length = nd then
      match xs with
      | [x, y] => g d x y
      | _ => none
    else none

/-- A function of three blocks, at `nd` dimensions. -/
def of3 (nd : ℕ) (l₁ l₂ l₃ : List ℕ → ℕ)
    (g : List ℕ → List K → List K → List K → Option (List K)) : BlockFn K where
  inLens d := [l₁ d, l₂ d, l₃ d]
  fn d _ xs := if d.length = nd then
      match xs with
      | [x, y, w] => g d x y w
      | _ => none
    else none

/-- A call of a function of one block, on blocks. -/
theorem apply_of1_eq_some_iff {nd : ℕ} {l : List ℕ → ℕ} {g : List ℕ → List K → Option (List K)}
    {d : List ℕ} {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K} :
    (of1 nd l g).apply d ins z τ m = some m' ↔ d.length = nd ∧ ∃ x xs v, ins = [x] ∧
      m.Live [x, z] ∧ m.store.readBlock x.1 x.2 (l d) = some xs ∧ g d xs = some v ∧
      z.2 + v.length ≤ m.store.len z.1 ∧ m' = m.updBlock z v := by
  rw [apply_eq_some_iff]
  constructor
  · rintro ⟨hl, X, v, hread, hfn, hz, rfl⟩
    obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hread
    by_cases hd : d.length = nd
    · simp only [of1, hd, if_true] at hfn
      exact ⟨hd, x, xs, v, rfl, hl, hx, hfn, hz, rfl⟩
    · simp [of1, hd] at hfn
  · rintro ⟨hd, x, xs, v, rfl, hl, hx, hg, hz, rfl⟩
    exact ⟨hl, [xs], v, by simp [of1, Mem.readBlocks, hx], by simp [of1, hd, hg], hz, rfl⟩

/-- A call of a function of two blocks, on blocks. -/
theorem apply_of2_eq_some_iff {nd : ℕ} {l₁ l₂ : List ℕ → ℕ}
    {g : List ℕ → List K → List K → Option (List K)} {d : List ℕ} {ins : List (ℕ × ℕ)}
    {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K} :
    (of2 nd l₁ l₂ g).apply d ins z τ m = some m' ↔ d.length = nd ∧ ∃ x y xs ys v,
      ins = [x, y] ∧ m.Live [x, y, z] ∧ m.store.readBlock x.1 x.2 (l₁ d) = some xs ∧
      m.store.readBlock y.1 y.2 (l₂ d) = some ys ∧ g d xs ys = some v ∧
      z.2 + v.length ≤ m.store.len z.1 ∧ m' = m.updBlock z v := by
  rw [apply_eq_some_iff]
  constructor
  · rintro ⟨hl, X, v, hread, hfn, hz, rfl⟩
    obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hread
    by_cases hd : d.length = nd
    · simp only [of2, hd, if_true] at hfn
      exact ⟨hd, x, y, xs, ys, v, rfl, hl, hx, hy, hfn, hz, rfl⟩
    · simp [of2, hd] at hfn
  · rintro ⟨hd, x, y, xs, ys, v, rfl, hl, hx, hy, hg, hz, rfl⟩
    exact ⟨hl, [xs, ys], v, by simp [of2, Mem.readBlocks, hx, hy], by simp [of2, hd, hg], hz,
      rfl⟩

/-- A call of a function of three blocks, on blocks. -/
theorem apply_of3_eq_some_iff {nd : ℕ} {l₁ l₂ l₃ : List ℕ → ℕ}
    {g : List ℕ → List K → List K → List K → Option (List K)} {d : List ℕ}
    {ins : List (ℕ × ℕ)} {z : ℕ × ℕ} {τ : ℕ → K} {m m' : Mem K} :
    (of3 nd l₁ l₂ l₃ g).apply d ins z τ m = some m' ↔ d.length = nd ∧ ∃ x y w xs ys ws v,
      ins = [x, y, w] ∧ m.Live [x, y, w, z] ∧ m.store.readBlock x.1 x.2 (l₁ d) = some xs ∧
      m.store.readBlock y.1 y.2 (l₂ d) = some ys ∧ m.store.readBlock w.1 w.2 (l₃ d) = some ws ∧
      g d xs ys ws = some v ∧ z.2 + v.length ≤ m.store.len z.1 ∧ m' = m.updBlock z v := by
  rw [apply_eq_some_iff]
  constructor
  · rintro ⟨hl, X, v, hread, hfn, hz, rfl⟩
    obtain ⟨x, y, w, xs, ys, ws, rfl, hx, hy, hw, rfl⟩ := Mem.readBlocks_three hread
    by_cases hd : d.length = nd
    · simp only [of3, hd, if_true] at hfn
      exact ⟨hd, x, y, w, xs, ys, ws, v, rfl, hl, hx, hy, hw, hfn, hz, rfl⟩
    · simp [of3, hd] at hfn
  · rintro ⟨hd, x, y, w, xs, ys, ws, v, rfl, hl, hx, hy, hw, hg, hz, rfl⟩
    exact ⟨hl, [xs, ys, ws], v, by simp [of3, Mem.readBlocks, hx, hy, hw],
      by simp [of3, hd, hg], hz, rfl⟩

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

/-! ### Relational contracts in operand form -/

/-- **A block relation**: a relational contract in operand form. At `nd` dimensions `d`, the
call reads input blocks of the lengths `inLens d` and writes one output block `ys` of the length
`outLen d` with `rel d xs ys`. -/
structure BlockRel (K : Type) where
  /-- The number of dimensions. -/
  nd : ℕ
  /-- The lengths of the input blocks. -/
  inLens : List ℕ → List ℕ
  /-- The length of the output block. -/
  outLen : List ℕ → ℕ
  /-- The relation between the input blocks and the output block. -/
  rel : List ℕ → List (List K) → List K → Prop

/-- **The contract of a block relation** on the admitted operands `adm`. Live handles, readable
inputs and room for the output are needed only for success; a successful call has read its
inputs. The contract reads the operand blocks and nothing else. -/
def BlockRel.spec (R : BlockRel K) (adm : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop) : Contract K :=
  fun md d ins outs _ =>
    { pre := fun m => ∃ z, outs = [z] ∧ d.length = R.nd ∧ adm d ins z ∧
        md.Needs (m.Live (ins ++ [z]) ∧ (m.readBlocks ins (R.inLens d)).isSome ∧
          z.2 + R.outLen d ≤ m.store.len z.1)
      post := fun m m' => ∃ z xs ys, outs = [z] ∧ m.readBlocks ins (R.inLens d) = some xs ∧
        ys.length = R.outLen d ∧ R.rel d xs ys ∧ m' = m.updBlock z ys }

end NLAlib.Ops
