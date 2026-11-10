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

**Phase A**: statements only (`sorry`).

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
    s.HoldsVec b o n v ↔ s.readBlock b o n = some ((List.range n).map v) := by sorry

/-- A block read holds the vector of its list. -/
theorem holdsVec_of_readBlock [Inhabited K] {s : Store K} {b o n : ℕ} {xs : List K}
    (h : s.readBlock b o n = some xs) : s.HoldsVec b o n (vec xs) := by sorry

theorem readsOnly_holdsVec (b o n : ℕ) (v : ℕ → K) :
    ReadsOnly (inBlock b o n) fun s : Store K => s.HoldsVec b o n v := by sorry

/-- A vector extended by one cell. -/
theorem HoldsVec.snoc {s : Store K} {b o n : ℕ} {v : ℕ → K} (h : s.HoldsVec b o n v)
    (hn : s.get b (o + n) = some (v n)) : s.HoldsVec b o (n + 1) v := by sorry

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

/-- A valid layout lies in one block. -/
theorem fp_le_inBlock {L : MatLayout} (hL : L.Valid) :
    L.fp ≤ Store.inBlock L.buf L.off (L.cols * L.ld) := by sorry

/-- Column `j` is a block. -/
theorem col_fp (L : MatLayout) (j : ℕ) :
    Store.inBlock L.buf (L.off + j * L.ld) L.rows ≤ L.fp ⊔ fun _ _ => ¬ j < L.cols := by sorry

/-- Two ranges of columns of one valid layout are disjoint: block-level disjointness in one
buffer. -/
theorem disj_of_cols {L : MatLayout} (hL : L.Valid) {j₁ n₁ j₂ n₂ : ℕ} (h : j₁ + n₁ ≤ j₂) :
    Fp.Disj (Store.inBlock L.buf (L.off + j₁ * L.ld) (n₁ * L.ld))
      (Store.inBlock L.buf (L.off + j₂ * L.ld) (n₂ * L.ld)) := by sorry

theorem upto_zero (L : MatLayout) : L.upto 0 0 = ⊥ := by sorry

/-- The fill footprint after a whole column. -/
theorem upto_col (L : MatLayout) (j : ℕ) : L.upto j L.rows = L.upto (j + 1) 0 := by sorry

/-- The fill footprint after one more entry. -/
theorem upto_succ (L : MatLayout) (j i : ℕ) :
    L.upto j (i + 1) = L.upto j i ⊔ Store.inBlock L.buf (L.cell i j) 1 := by sorry

theorem upto_cols (L : MatLayout) : L.upto L.cols 0 = L.fp := by sorry

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
    (hj : j < L.cols) : s.HoldsVec L.buf (L.off + j * L.ld) L.rows (fun i => A i j) := by sorry

/-- A matrix from its columns. -/
theorem holdsMat_of_cols {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K}
    (h : ∀ j < L.cols, s.HoldsVec L.buf (L.off + j * L.ld) L.rows (fun i => A i j)) :
    s.HoldsMat L A := by sorry

theorem readsOnly_holdsMat (L : MatLayout) (A : ℕ → ℕ → K) :
    ReadsOnly L.fp fun s : Store K => s.HoldsMat L A := by sorry

theorem holdsMatUpto_cols {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K} :
    s.HoldsMatUpto L A L.cols 0 ↔ s.HoldsMat L A := by sorry

end Store

/-! ### Decoding to layer 1 -/

/-- An entry of a slice of a list is an entry of the list. -/
@[decodeNF] theorem vec_drop_take [Inhabited K] {xs : List K} {a n i : ℕ} (h : i < n) :
    vec ((xs.drop a).take n) i = vec xs (a + i) := by sorry

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
