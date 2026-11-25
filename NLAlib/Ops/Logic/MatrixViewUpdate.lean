/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.MatrixView

/-!
# Rectangular updates inside stored scalar matrices

A logical rectangular read supplies exactly its column-major words. The precise view frame
then reconstructs the whole matrix after those words are replaced, retaining every exterior
entry and every padding cell. These storage bridges are shared by panel rank-one updates and
trailing scalar matrix-product corrections.

## Main results

* `NLAlib.Ops.Store.HoldsMat.readView_rectangle`: actual words of a bounded rectangle.
* `NLAlib.Ops.Store.HoldsMat.update_rectangle_of_frame`: reconstruct the changed matrix.
-/

@[expose] public section

namespace NLAlib.Ops.Store

variable {K : Type}

/-- Read a bounded rectangle using the original matrix leading dimension. Zero row or column
counts give an empty view without imposing a positive-shape hypothesis. -/
theorem HoldsMat.readView_rectangle {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K}
    (h : s.HoldsMat L A) (row col rows cols : ℕ)
    (hr : row + rows ≤ L.rows) (hc : col + cols ≤ L.cols) :
    s.readView L.buf (L.off + col * L.ld + row) ⟨rows, some (cols, L.ld)⟩ =
      some ((EntryCodec.scalar K).packMatrix rows cols (fun i j => A (row + i) (col + j))) := by
  have hs : s.HoldsMat ⟨L.buf, L.off + col * L.ld + row, rows, cols, L.ld⟩
      (fun i j => A (row + i) (col + j)) := by
    intro i hi j hj
    change i < rows at hi
    change j < cols at hj
    have hg := h (row + i) (by omega) (col + j) (by omega)
    simpa only [MatLayout.cell, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hg
  exact hs.readView

/-- Replace a bounded rectangle from its actual final logical words. Validity prevents
column aliasing; the precise view frame preserves every matrix entry outside the rectangle. -/
theorem HoldsMat.update_rectangle_of_frame_with_scratch [Inhabited K] {s s' : Store K}
    {L : MatLayout} {A : ℕ → ℕ → K} (h : s.HoldsMat L A) (hL : L.Valid)
    (row col rows cols : ℕ) (hr : row + rows ≤ L.rows) (scratch : Fp)
    (hdis : Fp.Disj scratch (inBlock L.buf L.off (L.cols * L.ld)))
    (hfr : s.EqOff (Fp.inView L.buf (L.off + col * L.ld + row)
      ⟨rows, some (cols, L.ld)⟩ ⊔ scratch) s') {ys : List K}
    (hy : s'.readView L.buf (L.off + col * L.ld + row) ⟨rows, some (cols, L.ld)⟩ =
      some ys) :
    s'.HoldsMat L (fun i j =>
      if row ≤ i ∧ i < row + rows ∧ col ≤ j ∧ j < col + cols then
        vec ys ((j - col) * rows + (i - row)) else A i j) := by
  have hnew := holdsMat_of_readView
    (L := ⟨L.buf, L.off + col * L.ld + row, rows, cols, L.ld⟩) hy
  intro i hi j hj
  change s'.get L.buf (L.cell i j) = some
    (if row ≤ i ∧ i < row + rows ∧ col ≤ j ∧ j < col + cols then
      vec ys ((j - col) * rows + (i - row)) else A i j)
  by_cases hin : row ≤ i ∧ i < row + rows ∧ col ≤ j ∧ j < col + cols
  · rw [if_pos hin]
    have hg := hnew (i - row) (by change i - row < rows; omega)
      (j - col) (by change j - col < cols; omega)
    have he : L.off + col * L.ld + row + (j - col) * L.ld + (i - row) =
        L.cell i j := by
      have hi' : row + (i - row) = i := by omega
      have hj' : col + (j - col) = j := by omega
      calc
        _ = L.off + (col + (j - col)) * L.ld + (row + (i - row)) := by ring
        _ = L.cell i j := by rw [hi', hj']; rfl
    simpa only [MatLayout.cell, he] using hg
  · rw [if_neg hin, hfr.get_eq ?_]
    · exact h i hi j hj
    · rintro (hf | hs)
      · obtain ⟨_, q, hq, he⟩ := Fp.inView_apply.mp hf
        have hq' : q < cols * rows := hq
        have hrows : 0 < rows := by
          by_contra hz
          have hz' : rows = 0 := by omega
          simp only [hz', Nat.mul_zero] at hq'
          omega
        have hqr : q % rows < rows := Nat.mod_lt q hrows
        have hqc : q / rows < cols := (Nat.div_lt_iff_lt_mul hrows).mpr hq'
        have hir : i < L.ld := hi.trans_le hL
        have hrr : row + q % rows < L.ld := (show row + q % rows < L.rows by omega).trans_le hL
        have he' : j * L.ld + i = (col + q / rows) * L.ld + (row + q % rows) := by
          have he0 : L.off + (j * L.ld + i) =
              L.off + ((col + q / rows) * L.ld + (row + q % rows)) := by
            simpa only [MatLayout.cell, View.offset_runs, Nat.add_mul, Nat.mul_add,
              Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he
          exact Nat.add_left_cancel he0
        have hi' : i = row + q % rows := by
          have hm := congrArg (fun t => t % L.ld) he'
          simpa only [Idx.mod_add hir, Idx.mod_add hrr] using hm
        have hj' : j = col + q / rows := by
          have hd := congrArg (fun t => t / L.ld) he'
          simpa only [Idx.div_add hir, Idx.div_add hrr] using hd
        apply hin
        rw [hi', hj']
        exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hqr _,
          Nat.le_add_right _ _, Nat.add_lt_add_left hqc _⟩
      · apply hdis L.buf (L.cell i j) hs
        have haddr := Idx.add_lt_mul hj (hi.trans_le hL)
        exact ⟨rfl, by simp only [MatLayout.cell]; omega,
          by simpa only [MatLayout.cell, Nat.add_assoc] using Nat.add_lt_add_left haddr L.off⟩

/-- A rectangle-only frame is the scratch-free specialization of whole-matrix
reconstruction. The original rectangle API requires no auxiliary footprint. -/
theorem HoldsMat.update_rectangle_of_frame [Inhabited K] {s s' : Store K}
    {L : MatLayout} {A : ℕ → ℕ → K} (h : s.HoldsMat L A) (hL : L.Valid)
    (row col rows cols : ℕ) (hr : row + rows ≤ L.rows)
    (hfr : s.EqOff (Fp.inView L.buf (L.off + col * L.ld + row)
      ⟨rows, some (cols, L.ld)⟩) s') {ys : List K}
    (hy : s'.readView L.buf (L.off + col * L.ld + row) ⟨rows, some (cols, L.ld)⟩ =
      some ys) :
    s'.HoldsMat L (fun i j =>
      if row ≤ i ∧ i < row + rows ∧ col ≤ j ∧ j < col + cols then
        vec ys ((j - col) * rows + (i - row)) else A i j) := by
  apply h.update_rectangle_of_frame_with_scratch hL row col rows cols hr ⊥
    (Fp.disj_bot_left _) (by simpa only [sup_bot_eq] using hfr) hy

end NLAlib.Ops.Store
