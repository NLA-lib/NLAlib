/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import NLAlib.Ops.Logic.Footprint
public import NLAlib.Ops.Logic.Index

/-!
# Layouts: vectors and matrices in the store, and their decoding

A program stores a vector as a block and a matrix as columns (or rows) with a leading dimension.
The predicates here say what the store holds **as a function of the logical indices**, so that
invariants and contracts are stated on `ℕ → K` or `ℕ → ℕ → K` and decoded to the `Fin n → ℝ` and
`Matrix` of layer 1 by one lemma (`decode`), instead of `vec (xs.drop a |>.take n) i` rewritten
by hand in every proof.

* `NLAlib.Ops.Store.HoldsVec s b o n v`: the cells `o, …, o + n - 1` of `b` hold `v 0, …`.
* `NLAlib.Ops.MatLayout`: a matrix of `rows × cols` at `(buf, off)` with leading dimension `ld`,
  stored by columns: entry `(i, j)` is the cell `off + j * ld + i`. A matrix stored by rows is
  the layout of its transpose.
* `NLAlib.Ops.Store.HoldsMat s L A`: the store holds `A` in the layout `L`.
* `NLAlib.Ops.MatLayout.fp`: the cells of the layout (its footprint); `MatLayout.upto`: the cells
  of the columns before `j` and of column `j` before row `i` (the footprint of a fill).

## Main results

* `NLAlib.Ops.Store.holdsVec_iff_readBlock`: a vector is a block read.
* `NLAlib.Ops.Store.HoldsMat.col`: a column of a matrix is a vector.
* `NLAlib.Ops.Store.readsOnly_holdsVec`, `NLAlib.Ops.Store.readsOnly_holdsMat`: kept facts.
* `NLAlib.Ops.MatLayout.disj_of_cols`: two column ranges of one layout are disjoint (block-level
  disjointness in one buffer, for a kernel that reads and writes one arena).
* `NLAlib.Ops.vec_drop_take`, `NLAlib.Ops.decVec`, `NLAlib.Ops.decMat`: decoding.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K : Type}

namespace Store

/-- The cells `o, …, o + n - 1` of the buffer `b` hold `v 0, …, v (n - 1)`. -/
def HoldsVec (s : Store K) (b o n : ℕ) (v : ℕ → K) : Prop :=
  ∀ i < n, s.get b (o + i) = some (v i)

theorem holdsVec_iff_readBlock {s : Store K} {b o n : ℕ} {v : ℕ → K} :
    s.HoldsVec b o n v ↔ s.readBlock b o n = some ((List.range n).map v) := by
  rw [readBlock_eq_some_iff]
  constructor
  · intro h
    exact ⟨by simp, fun j hj => by rw [h j hj]; simp [hj]⟩
  · intro h i hi
    rw [h.2 i hi]
    simp [hi]

/-- A block read holds the vector of its list. -/
theorem holdsVec_of_readBlock [Inhabited K] {s : Store K} {b o n : ℕ} {xs : List K}
    (h : s.readBlock b o n = some xs) : s.HoldsVec b o n (vec xs) :=
  fun _ hi => get_of_readBlock h hi default

theorem readsOnly_holdsVec (b o n : ℕ) (v : ℕ → K) :
    ReadsOnly (inBlock b o n) fun s : Store K => s.HoldsVec b o n v := fun _ _ hg hp i hi =>
  (hg b (o + i) ⟨rfl, by omega, by omega⟩).trans (hp i hi)

/-- A vector extended by one cell. -/
theorem HoldsVec.snoc {s : Store K} {b o n : ℕ} {v : ℕ → K} (h : s.HoldsVec b o n v)
    (hn : s.get b (o + n) = some (v n)) : s.HoldsVec b o (n + 1) v := fun i hi => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h i hi
  · exact hn

end Store

/-- **A matrix layout**: `rows × cols` entries at `(buf, off)`, by columns, with the leading
dimension `ld`: entry `(i, j)` is the cell `off + j * ld + i`. -/
structure MatLayout where
  /-- The buffer. -/
  buf : ℕ
  /-- The offset of entry `(0, 0)`. -/
  off : ℕ
  /-- The number of rows. -/
  rows : ℕ
  /-- The number of columns. -/
  cols : ℕ
  /-- The leading dimension: the distance between two columns. -/
  ld : ℕ

namespace MatLayout

/-- The cell of entry `(i, j)`. -/
@[fpNF] def cell (L : MatLayout) (i j : ℕ) : ℕ := L.off + j * L.ld + i

/-- The columns do not overlap. -/
def Valid (L : MatLayout) : Prop := L.rows ≤ L.ld

/-- The cells of the layout. -/
def fp (L : MatLayout) : Fp := fun b x => b = L.buf ∧ ∃ i < L.rows, ∃ j < L.cols, x = L.cell i j

/-- The cells of the columns before `j` and of column `j` before row `i`: the footprint of a
fill by columns after `j * rows + i` entries. -/
def upto (L : MatLayout) (j i : ℕ) : Fp := fun b x => b = L.buf ∧
  ((∃ i' < L.rows, ∃ j' < j, x = L.cell i' j') ∨ (∃ i' < i, x = L.cell i' j))

@[fpNF] theorem fp_apply (L : MatLayout) (b x : ℕ) :
    L.fp b x ↔ b = L.buf ∧ ∃ i < L.rows, ∃ j < L.cols, x = L.cell i j := Iff.rfl

@[fpNF] theorem upto_apply (L : MatLayout) (j i b x : ℕ) :
    L.upto j i b x ↔ b = L.buf ∧
      ((∃ i' < L.rows, ∃ j' < j, x = L.cell i' j') ∨ (∃ i' < i, x = L.cell i' j)) := Iff.rfl

/-- A valid layout lies in one block. -/
theorem fp_le_inBlock {L : MatLayout} (hL : L.Valid) :
    L.fp ≤ Store.inBlock L.buf L.off (L.cols * L.ld) := by
  rintro b x ⟨rfl, i, hi, j, hj, rfl⟩
  have := Idx.mul_add_le_mul hj L.ld
  unfold Valid at hL
  exact ⟨rfl, by simp only [cell]; omega, by simp only [cell]; omega⟩

/-- Column `j` is a block of the layout. -/
theorem col_fp (L : MatLayout) {j : ℕ} (hj : j < L.cols) :
    Store.inBlock L.buf (L.off + j * L.ld) L.rows ≤ L.fp := by
  rintro b x ⟨rfl, h1, h2⟩
  exact ⟨rfl, x - (L.off + j * L.ld), by omega, j, hj, by simp only [cell]; omega⟩

/-- Two ranges of columns of one valid layout are disjoint: block-level disjointness in one
buffer. -/
theorem disj_of_cols (L : MatLayout) {j₁ n₁ j₂ n₂ : ℕ} (h : j₁ + n₁ ≤ j₂) :
    Fp.Disj (Store.inBlock L.buf (L.off + j₁ * L.ld) (n₁ * L.ld))
      (Store.inBlock L.buf (L.off + j₂ * L.ld) (n₂ * L.ld)) := by
  refine Fp.disj_inBlock_of_le ?_
  have := Nat.mul_le_mul_right L.ld h
  rw [Nat.add_mul] at this
  omega

theorem upto_zero (L : MatLayout) : L.upto 0 0 = ⊥ := by
  funext b x
  apply propext
  simp only [upto]
  constructor
  · rintro ⟨-, ⟨_, _, _, hj, _⟩ | ⟨_, hi, _⟩⟩ <;> omega
  · exact False.elim

/-- The fill footprint after a whole column. -/
theorem upto_col (L : MatLayout) (j : ℕ) : L.upto j L.rows = L.upto (j + 1) 0 := by
  funext b x
  apply propext
  simp only [upto]
  constructor
  · rintro ⟨hb, ⟨i, hi, j', hj, rfl⟩ | ⟨i, hi, rfl⟩⟩
    · exact ⟨hb, Or.inl ⟨i, hi, j', by omega, rfl⟩⟩
    · exact ⟨hb, Or.inl ⟨i, hi, j, by omega, rfl⟩⟩
  · rintro ⟨hb, ⟨i, hi, j', hj, rfl⟩ | ⟨i, hi, -⟩⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ⟨hb, Or.inl ⟨i, hi, j', hj, rfl⟩⟩
      · exact ⟨hb, Or.inr ⟨i, hi, rfl⟩⟩
    · omega

/-- The fill footprint after one more entry. -/
theorem upto_succ (L : MatLayout) (j i : ℕ) :
    L.upto j (i + 1) = L.upto j i ⊔ Store.inBlock L.buf (L.cell i j) 1 := by
  funext b x
  apply propext
  simp only [upto, Pi.sup_apply, sup_Prop_eq, Store.inBlock]
  constructor
  · rintro ⟨hb, h | ⟨i', hi, rfl⟩⟩
    · exact Or.inl ⟨hb, Or.inl h⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨hb, Or.inr ⟨i', hi, rfl⟩⟩
      · exact Or.inr ⟨hb, le_rfl, by omega⟩
  · rintro (⟨hb, h | ⟨i', hi, rfl⟩⟩ | ⟨hb, h1, h2⟩)
    · exact ⟨hb, Or.inl h⟩
    · exact ⟨hb, Or.inr ⟨i', by omega, rfl⟩⟩
    · exact ⟨hb, Or.inr ⟨i, by omega, by omega⟩⟩

theorem upto_cols (L : MatLayout) : L.upto L.cols 0 = L.fp := by
  funext b x
  apply propext
  simp only [upto, fp]
  constructor
  · rintro ⟨hb, h | ⟨_, hi, _⟩⟩
    · exact ⟨hb, h⟩
    · omega
  · rintro ⟨hb, h⟩
    exact ⟨hb, Or.inl h⟩

end MatLayout

namespace Store

/-- The store holds the matrix `A` in the layout `L`. -/
def HoldsMat (s : Store K) (L : MatLayout) (A : ℕ → ℕ → K) : Prop :=
  ∀ i < L.rows, ∀ j < L.cols, s.get L.buf (L.cell i j) = some (A i j)

/-- The store holds the entries of `A` filled so far (columns before `j`, rows before `i` of
column `j`). -/
def HoldsMatUpto (s : Store K) (L : MatLayout) (A : ℕ → ℕ → K) (j i : ℕ) : Prop :=
  (∀ i' < L.rows, ∀ j' < j, s.get L.buf (L.cell i' j') = some (A i' j')) ∧
    ∀ i' < i, s.get L.buf (L.cell i' j) = some (A i' j)

/-- A column of a matrix is a vector. -/
theorem HoldsMat.col {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K} (h : s.HoldsMat L A) {j : ℕ}
    (hj : j < L.cols) : s.HoldsVec L.buf (L.off + j * L.ld) L.rows (fun i => A i j) :=
  fun i hi => h i hi j hj

/-- A matrix from its columns. -/
theorem holdsMat_of_cols {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K}
    (h : ∀ j < L.cols, s.HoldsVec L.buf (L.off + j * L.ld) L.rows (fun i => A i j)) :
    s.HoldsMat L A := fun i hi j hj => h j hj i hi

theorem readsOnly_holdsMat (L : MatLayout) (A : ℕ → ℕ → K) :
    ReadsOnly L.fp fun s : Store K => s.HoldsMat L A := fun _ _ hg hp i hi j hj =>
  (hg _ _ ⟨rfl, i, hi, j, hj, rfl⟩).trans (hp i hi j hj)

/-- **A dense matrix is a flat block** (the bridge to the contracts in operand form, whose
blocks are flat lists): with `rows = ld`, the layout is the block of `cols * rows` cells, entry
`(i, j)` at `j * rows + i`. -/
theorem HoldsMat.readBlock [Inhabited K] {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K}
    (h : s.HoldsMat L A) (hL : L.rows = L.ld) :
    ∃ ys, s.readBlock L.buf L.off (L.cols * L.rows) = some ys ∧ ys.length = L.cols * L.rows ∧
      ∀ i < L.rows, ∀ j < L.cols, vec ys (j * L.rows + i) = A i j := by
  refine ⟨(List.range (L.cols * L.rows)).map fun q => A (q % L.rows) (q / L.rows), ?_, by simp,
    fun i hi j hj => ?_⟩
  · refine holdsVec_iff_readBlock.mp fun q hq => ?_
    have hr : 0 < L.rows := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hq
    have e : L.off + q = L.cell (q % L.rows) (q / L.rows) := by
      simp only [MatLayout.cell, ← hL]
      have := Nat.div_add_mod q L.rows
      rw [Nat.mul_comm] at this
      omega
    rw [e]
    exact h _ (Nat.mod_lt _ hr) _ (by rw [Nat.div_lt_iff_lt_mul hr]; exact hq)
  · have hq : j * L.rows + i < L.cols * L.rows := Idx.add_lt_mul hj hi
    simp [vec, List.getD_eq_getElem?_getD, hq, Idx.div_add hi, Idx.mod_add hi]

/-- The converse: a flat block of `cols * rows` cells holds the matrix of its entries. -/
theorem holdsMat_of_readBlock [Inhabited K] {s : Store K} {L : MatLayout} {ys : List K}
    (hL : L.rows = L.ld) (h : s.readBlock L.buf L.off (L.cols * L.rows) = some ys) :
    s.HoldsMat L (fun i j => vec ys (j * L.rows + i)) := fun i hi j hj => by
  have := get_of_readBlock h (Idx.add_lt_mul hj hi) default
  simpa [MatLayout.cell, ← hL, Nat.add_assoc] using this

theorem holdsMatUpto_cols {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K} :
    s.HoldsMatUpto L A L.cols 0 ↔ s.HoldsMat L A :=
  ⟨fun h i hi j hj => h.1 i hi j hj, fun h => ⟨fun i hi j hj => h i hi j hj, fun _ hi => by omega⟩⟩

end Store

/-! ### Decoding to layer 1 -/

/-- An entry of a slice of a list is an entry of the list. -/
@[decodeNF] theorem vec_drop_take [Inhabited K] {xs : List K} {a n i : ℕ} (h : i < n) :
    vec ((xs.drop a).take n) i = vec xs (a + i) := Store.getD_drop_take xs a n i h default

/-- The decoded vector of length `n`. -/
def decVec (dec : K → ℝ) (n : ℕ) (v : ℕ → K) : Fin n → ℝ := fun i => dec (v i)

/-- The decoded matrix of a layout. -/
def decMat (dec : K → ℝ) (r c : ℕ) (A : ℕ → ℕ → K) : Matrix (Fin r) (Fin c) ℝ :=
  Matrix.of fun i j => dec (A i j)

/-- An entry of a decoded matrix. -/
@[decodeNF] theorem decMat_apply (dec : K → ℝ) (r c : ℕ) (A : ℕ → ℕ → K) (i : Fin r) (j : Fin c) :
    decMat dec r c A i j = dec (A i j) := rfl

/-- An entry of a decoded vector. -/
@[decodeNF] theorem decVec_apply (dec : K → ℝ) (n : ℕ) (v : ℕ → K) (i : Fin n) :
    decVec dec n v i = dec (v i) := rfl

end NLAlib.Ops
