/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Ring
public import NLAlib.Ops.Logic.EntryLayout

/-!
# Reading and replacing packed matrix columns

A column update changes one contiguous word block. The generic layout rule retains
all other columns and supplies the new mathematical matrix without update-chain
invariants or assumptions that the columns use different buffers.

## Main results

* `NLAlib.Ops.Store.HoldsEntries.readBlock_column` reads a packed column.
* `NLAlib.Ops.Store.HoldsEntries.update_column_of_frame` reconstructs the updated matrix.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K E : Type}

/-- Distinct logical columns occupy disjoint word blocks, including padded layouts. -/
theorem EntryCodec.disj_columns (C : EntryCodec K E) {L : MatLayout}
    (hL : L.Valid) {j c : ℕ} (hne : j ≠ c) :
    Fp.Disj (Store.inBlock L.buf (L.off + C.width * (j * L.ld)) (L.rows * C.width))
      (Store.inBlock L.buf (L.off + C.width * (c * L.ld)) (L.rows * C.width)) := by
  have hsep : ∀ a b : ℕ, a < b →
      L.off + C.width * (a * L.ld) + L.rows * C.width ≤
        L.off + C.width * (b * L.ld) := by
    intro a b hab
    have h₁ := Nat.mul_le_mul_left C.width hL
    have h₂ := Nat.mul_le_mul_left C.width (Nat.mul_le_mul_right L.ld (Nat.succ_le_of_lt hab))
    have he : C.width * ((a + 1) * L.ld) =
        C.width * (a * L.ld) + C.width * L.ld := by ring
    rw [he] at h₂
    simpa only [Nat.mul_comm L.rows C.width, Nat.add_assoc] using Nat.add_le_add_left
      ((Nat.add_le_add_left h₁ (C.width * (a * L.ld))).trans h₂) L.off
  rcases lt_or_gt_of_ne hne with h | h
  · exact Fp.disj_inBlock_of_le (hsep j c h)
  · exact (Fp.disj_inBlock_of_le (hsep c j h)).symm

/-- Width-one packing is the ordinary list of vector entries, without preprocessing. -/
theorem EntryCodec.scalar_pack (n : ℕ) (v : ℕ → K) :
    (EntryCodec.scalar K).pack n v = List.ofFn (fun i : Fin n => v i) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp [EntryCodec.pack, EntryCodec.scalar]

namespace Store

/-- One matrix column is an ordinary packed vector, with the matrix's leading dimension. -/
theorem HoldsEntries.readBlock_column {s : Store K} {C : EntryCodec K E} {L : MatLayout}
    {A : ℕ → ℕ → E} (h : s.HoldsEntries C L A) {j : ℕ} (hj : j < L.cols) :
    s.readBlock L.buf (L.off + C.width * (j * L.ld)) (L.rows * C.width) =
      some (C.pack L.rows fun i => A i j) := by
  rw [readBlock_eq_some_iff]
  refine ⟨C.length_pack _ _, fun q hq => ?_⟩
  have hi : q / C.width < L.rows := (Nat.div_lt_iff_lt_mul C.width_pos).mpr hq
  have hz := Nat.mod_lt q C.width_pos
  have hr := h (q / C.width) hi j hj ⟨q % C.width, hz⟩
  have he : L.off + C.width * (j * L.ld) + q =
      L.off + C.width * (j * L.ld + q / C.width) + q % C.width := by
    have hd := Nat.div_add_mod q C.width
    simp only [Nat.mul_add]
    omega
  rw [he, hr]
  simp [EntryCodec.pack, hq]

/-- Replace one stored column and preserve every other column through its exact frame.
No initialization of padding cells or separate-buffer assumption is required. -/
theorem HoldsEntries.update_column_of_frame [Inhabited K] {s s' : Store K}
    {C : EntryCodec K E} {L : MatLayout} {A : ℕ → ℕ → E}
    (h : s.HoldsEntries C L A) (hL : L.Valid) {j : ℕ}
    {F : Fp} (hF : Fp.Disj F (inBlock L.buf L.off (C.width * (L.cols * L.ld))))
    (hfr : s.EqOff (inBlock L.buf (L.off + C.width * (j * L.ld))
      (L.rows * C.width) ⊔ F) s') (v : ℕ → E)
    (hv : s'.readBlock L.buf (L.off + C.width * (j * L.ld)) (L.rows * C.width) =
      some (C.pack L.rows v)) :
    s'.HoldsEntries C L (fun i c => if c = j then v i else A i c) := by
  intro i hi c hc z
  have hentry : inBlock L.buf (L.off + C.width * (c * L.ld))
      (L.rows * C.width) L.buf (L.off + C.width * (c * L.ld + i) + z) := by
    have hz := Idx.add_lt_mul hi z.isLt
    rw [Nat.mul_add, Nat.mul_comm C.width i]
    exact ⟨rfl, by omega, by omega⟩
  change s'.get L.buf (L.off + C.width * (c * L.ld + i) + z) =
    some (C.words (if c = j then v i else A i c) z)
  by_cases he : c = j
  · subst c
    have hg := get_of_readBlock hv (Idx.add_lt_mul hi z.isLt) default
    have ha : L.off + C.width * (j * L.ld) + (i * C.width + z) =
        L.off + C.width * (j * L.ld + i) + z := by ring
    rw [ha] at hg
    rw [if_pos rfl]
    change _ = some (C.words (v i) z)
    rw [← C.vec_pack v hi z]
    exact hg
  · have hwhole : inBlock L.buf L.off (C.width * (L.cols * L.ld)) L.buf
        (L.off + C.width * (c * L.ld + i) + z) := by
      have hb := Idx.add_lt_mul (Idx.add_lt_mul hc (hi.trans_le hL)) z.isLt
      refine ⟨rfl, by omega, ?_⟩
      simpa only [Nat.mul_comm C.width, Nat.add_assoc] using Nat.add_lt_add_left hb L.off
    rw [if_neg he, hfr.2 L.buf _ (fun hf => ?_)]
    · exact h i hi c hc z
    · rcases hf with hf | hf
      · exact (C.disj_columns hL (Ne.symm he)) _ _ hf hentry
      · exact hF _ _ hf hwhole

/-- A collection of packed column reads supplies the mathematical matrix entries.
No padding words between columns need to be initialized. -/
theorem holdsEntries_of_readBlock_columns [Inhabited K] {s : Store K}
    {C : EntryCodec K E} {L : MatLayout} {A : ℕ → ℕ → E}
    (h : ∀ j < L.cols,
      s.readBlock L.buf (L.off + C.width * (j * L.ld)) (L.rows * C.width) =
        some (C.pack L.rows fun i => A i j)) : s.HoldsEntries C L A := by
  intro i hi j hj z
  have hg := get_of_readBlock (h j hj) (Idx.add_lt_mul hi z.isLt) default
  have he : L.off + C.width * (j * L.ld) + (i * C.width + z) =
      L.off + C.width * (j * L.ld + i) + z := by ring
  rw [he] at hg
  rw [← C.vec_pack (fun i => A i j) hi z]
  exact hg

/-- A packed scalar matrix supplies each actual column as an ordinary vector block. -/
theorem readBlock_scalar_matrix_column [Inhabited K] {s : Store K} {b off rows cols : ℕ}
    {A : Matrix (Fin rows) (Fin cols) K}
    (h : s.readBlock b off (cols * rows) = some ((EntryCodec.scalar K).packFinMatrix A))
    (j : Fin cols) : s.readBlock b (off + j * rows) rows = some (List.ofFn (A.col j)) := by
  rw [readBlock_eq_some_iff]
  refine ⟨by simp, fun i hi => ?_⟩
  have hg := get_of_readBlock h (Idx.add_lt_mul j.isLt hi) default
  have hv : vec ((EntryCodec.scalar K).packFinMatrix A) (j * rows + i) = A ⟨i, hi⟩ j := by
    simpa [EntryCodec.scalar] using
      (EntryCodec.scalar K).vec_packFinMatrix A ⟨i, hi⟩ j ⟨0, Nat.zero_lt_succ 0⟩
  change s.get b (off + (j * rows + i)) =
    some (vec ((EntryCodec.scalar K).packFinMatrix A) (j * rows + i)) at hg
  rw [hv] at hg
  simpa [Nat.add_assoc, List.getD_eq_getElem?_getD, hi] using hg

/-- Actual scalar column reads assemble into the packed finite matrix, including empty
row or column types. This is the inverse storage direction of the column reader. -/
theorem readBlock_scalar_matrix_of_columns [Inhabited K] {s : Store K}
    {b off rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) K)
    (h : ∀ j : Fin cols, s.readBlock b (off + j * rows) rows =
      some (List.ofFn (A.col j))) :
    s.readBlock b off (cols * rows) = some ((EntryCodec.scalar K).packFinMatrix A) := by
  let f : ℕ → ℕ → K := fun i j =>
    if hi : i < rows then if hj : j < cols then A ⟨i, hi⟩ ⟨j, hj⟩ else default else default
  have hs : s.HoldsEntries (EntryCodec.scalar K) ⟨b, off, rows, cols, rows⟩ f := by
    apply holdsEntries_of_readBlock_columns
    intro j hj
    have hh := h ⟨j, hj⟩
    change s.readBlock b (off + j * rows) rows =
      some (List.ofFn fun i : Fin rows => A i ⟨j, hj⟩) at hh
    simpa [EntryCodec.scalar, EntryCodec.scalar_pack, f, hj] using hh
  have he : (Matrix.of fun (i : Fin rows) (j : Fin cols) => f i j) = A := by
    ext i j
    simp [f]
  simpa only [EntryCodec.scalar, Nat.mul_one, he] using hs.readBlock_packFinMatrix rfl

end Store
end NLAlib.Ops
