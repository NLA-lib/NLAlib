/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryColumn

/-!
# Replacing a stored matrix-column suffix

A contiguous suffix of one column can be replaced while the matrix's other initialized
entries are carried through its precise frame. LU column materialization and right-looking
Cholesky use the same storage argument, independently of the scalar arithmetic.

## Main results

* `NLAlib.Ops.Store.HoldsMat.readBlock_column_suffix`: read an initialized suffix.
* `NLAlib.Ops.Store.HoldsMat.update_column_suffix_of_frame`: replace the actual suffix words.
-/

@[expose] public section

namespace NLAlib.Ops.Store

variable {K : Type} [Inhabited K]

omit [Inhabited K] in
/-- Read the remaining rows of an initialized matrix column as an actual contiguous word
block. Padding and all entries of the other columns are irrelevant. -/
theorem HoldsMat.readBlock_column_suffix {s : Store K} {L : MatLayout}
    {A : ℕ → ℕ → K} (h : s.HoldsMat L A) (c : ℕ) (hc : c < L.cols)
    (r : ℕ) (hr : r ≤ L.rows) :
    s.readBlock L.buf (L.off + c * L.ld + r) (L.rows - r) =
      some ((List.range (L.rows - r)).map fun i => A (r + i) c) := by
  rw [readBlock_eq_some_iff]
  refine ⟨by simp, fun i hi => ?_⟩
  have hrow : r + i < L.rows := by omega
  have hh := h (r + i) hrow c hc
  simpa [MatLayout.cell, Nat.add_assoc, hi] using hh

/-- Replace the rows from `r` onward in column `c` from an actual suffix read, preserving
every other matrix entry through the suffix frame. The layout may include column padding. -/
theorem HoldsMat.update_column_suffix_of_frame {s s' : Store K} {L : MatLayout}
    {A : ℕ → ℕ → K} (h : s.HoldsMat L A) (hL : L.Valid) (c r : ℕ)
    (hr : r ≤ L.rows)
    (hfr : s.EqOff (inBlock L.buf (L.off + c * L.ld + r) (L.rows - r)) s')
    {ys : List K} (hy : s'.readBlock L.buf (L.off + c * L.ld + r) (L.rows - r) = some ys) :
    s'.HoldsMat L (fun i j => if j = c ∧ r ≤ i then vec ys (i - r) else A i j) := by
  intro i hi j hj
  change s'.get L.buf (L.cell i j) =
    some (if j = c ∧ r ≤ i then vec ys (i - r) else A i j)
  by_cases he : j = c ∧ r ≤ i
  · obtain ⟨hjc, hri⟩ := he
    subst j
    have hg := get_of_readBlock hy (by omega : i - r < L.rows - r) default
    have ha : L.off + c * L.ld + r + (i - r) = L.cell i c := by
      simp only [MatLayout.cell]
      omega
    rw [ha] at hg
    simpa [hri, vec] using hg
  · rw [if_neg he, hfr.get_eq ?_]
    · exact h i hi j hj
    · intro hf
      by_cases hjc : j = c
      · subst j
        have hir : i < r := lt_of_not_ge (fun hri => he ⟨rfl, hri⟩)
        obtain ⟨-, hlo, -⟩ := hf
        simp only [MatLayout.cell] at hlo
        omega
      · have hd : Fp.Disj (inBlock L.buf (L.off + c * L.ld) L.rows)
            (inBlock L.buf (L.off + j * L.ld) L.rows) := by
          simpa only [EntryCodec.scalar, Nat.one_mul, Nat.mul_one] using
            (EntryCodec.scalar K).disj_columns hL (Ne.symm hjc)
        apply hd L.buf (L.cell i j)
        · obtain ⟨hb, hlo, hhi⟩ := hf
          exact ⟨hb, by omega, by omega⟩
        · change L.buf = L.buf ∧
            L.off + j * L.ld ≤ L.off + j * L.ld + i ∧
            L.off + j * L.ld + i < L.off + j * L.ld + L.rows
          exact ⟨rfl, by omega, by omega⟩

end NLAlib.Ops.Store
