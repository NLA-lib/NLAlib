/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage

/-!
# Stored complex vectors in the row solve

A row's mathematical coordinates are stored consecutively using the same pair-codec column
layout as matrices. This is an abbreviation of ordinary matrix storage, with no new codec.

## Main results

* `NLAlib.ShiftedQR.HoldsVector`: an ordinary single-column interleaved matrix block.
* `NLAlib.ShiftedQR.HoldsVector.update`: one stored pair updates one vector coordinate.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- A finite vector viewed as the single matrix column of its coordinates. -/
def vectorColumn {n : ℕ} (v : Fin n → ℂ) : Matrix (Fin n) (Fin 1) ℂ := fun i _ => v i

/-- The actual words of a vector in the existing interleaved matrix representation. -/
abbrev HoldsVector {n : ℕ} (a : ℕ × ℕ) (v : Fin n → ℂ) (s : Store ℝ) : Prop :=
  HoldsMatrix a (vectorColumn v) s

/-- A vector's real component is its first stored word. -/
theorem HoldsVector.get_re {n : ℕ} {a : ℕ × ℕ} {v : Fin n → ℂ} {s : Store ℝ}
    (h : HoldsVector a v s) (i : Fin n) : s.get a.1 (a.2 + 2 * i) = some (v i).re := by
  simpa only [Fin.val_zero, zero_mul, zero_add, vectorColumn] using
    HoldsMatrix.get_re h i (0 : Fin 1)

/-- A vector's imaginary component is its second stored word. -/
theorem HoldsVector.get_im {n : ℕ} {a : ℕ × ℕ} {v : Fin n → ℂ} {s : Store ℝ}
    (h : HoldsVector a v s) (i : Fin n) : s.get a.1 (a.2 + 2 * i + 1) = some (v i).im := by
  simpa only [Fin.val_zero, zero_mul, zero_add, vectorColumn] using
    HoldsMatrix.get_im h i (0 : Fin 1)

/-- A complete coordinate pair is an ordinary two-word block read. -/
theorem HoldsVector.read_entry {n : ℕ} {a : ℕ × ℕ} {v : Fin n → ℂ} {s : Store ℝ}
    (h : HoldsVector a v s) (i : Fin n) :
    s.readBlock a.1 (a.2 + 2 * i) 2 = some [(v i).re, (v i).im] := by
  simpa only [Fin.val_zero, zero_mul, zero_add, vectorColumn] using
    HoldsMatrix.read_entry h i (0 : Fin 1)

/-- Actual component reads reconstruct the stored vector. -/
theorem HoldsVector.of_get {n : ℕ} {a : ℕ × ℕ} {v : Fin n → ℂ} {s : Store ℝ}
    (hr : ∀ i : Fin n, s.get a.1 (a.2 + 2 * i) = some (v i).re)
    (hi : ∀ i : Fin n, s.get a.1 (a.2 + 2 * i + 1) = some (v i).im) : HoldsVector a v s := by
  apply HoldsMatrix.of_get
  · intro i j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa only [Fin.val_zero, zero_mul, zero_add, vectorColumn] using hr i
  · intro i j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa only [Fin.val_zero, zero_mul, zero_add, vectorColumn] using hi i

/-- A write to one complete stored pair updates the corresponding vector coordinate. -/
theorem HoldsVector.update {n : ℕ} {a : ℕ × ℕ} {v : Fin n → ℂ} {s s' : Store ℝ}
    (h : HoldsVector a v s) (i : Fin n) (z : ℂ)
    (hfr : s.EqOff (Store.inBlock a.1 (a.2 + 2 * i) 2) s')
    (hr : s'.get a.1 (a.2 + 2 * i) = some z.re)
    (hi : s'.get a.1 (a.2 + 2 * i + 1) = some z.im) :
    HoldsVector a (Function.update v i z) s' := by
  have hh := HoldsMatrix.of_entry_write h i (0 : Fin 1) z
    (by simpa only [Fin.val_zero, zero_mul, zero_add] using hfr)
    (by simpa only [Fin.val_zero, zero_mul, zero_add] using hr)
    (by simpa only [Fin.val_zero, zero_mul, zero_add] using hi)
  have he : (vectorColumn v).updateRow i (Function.update (vectorColumn v i) 0 z) =
      vectorColumn (Function.update v i z) := by
    funext r c
    obtain rfl : c = 0 := Subsingleton.elim _ _
    by_cases hri : r = i <;> simp [Matrix.updateRow_apply, hri, vectorColumn]
  change HoldsMatrix a (vectorColumn (Function.update v i z)) s'
  rw [← he]
  exact hh

/-- Vector storage reads exactly its own two words per coordinate. -/
theorem readsOnly_holdsVector {n : ℕ} (a : ℕ × ℕ) (v : Fin n → ℂ) :
    Store.ReadsOnly (Store.inBlock a.1 a.2 (2 * n)) (HoldsVector a v) := by
  simpa only [one_mul] using readsOnly_holdsMatrix a (vectorColumn v)

/-- Updating one vector entry may also change disjoint arithmetic scratch. -/
theorem HoldsVector.update_scratch {n : ℕ} {a : ℕ × ℕ} {v : Fin n → ℂ}
    {s s' : Store ℝ} {F : Fp} (h : HoldsVector a v s) (i : Fin n) (z : ℂ)
    (hfr : s.EqOff (F ⊔ Store.inBlock a.1 (a.2 + 2 * i) 2) s')
    (hd : Fp.Disj F (Store.inBlock a.1 a.2 (2 * n)))
    (hr : s'.get a.1 (a.2 + 2 * i) = some z.re)
    (hi : s'.get a.1 (a.2 + 2 * i + 1) = some z.im) :
    HoldsVector a (Function.update v i z) s' := by
  have hentry (r : Fin n) (hri : r ≠ i) :
      s'.readBlock a.1 (a.2 + 2 * r) 2 = some [(v r).re, (v r).im] := by
    refine hfr.keep (Store.readsOnly_readBlock _ _ _ _) ?_ (HoldsVector.read_entry h r)
    refine Fp.disj_sup_left.mpr ⟨hd.mono le_rfl
      (Fp.inBlock_le_inBlock (by omega) (by have := r.isLt; omega)), ?_⟩
    have hne : (r, (0 : Fin 1)) ≠ (i, (0 : Fin 1)) := fun h => hri (congrArg Prod.fst h)
    have h := (EntryCodec.pair ℝ).disj_entryBlock_matrix (b := a.1) (off := a.2) hne
    simpa only [EntryCodec.entryBlock, EntryCodec.pair, Fin.val_zero, zero_mul, zero_add,
      Nat.mul_comm 2] using h.symm
  apply HoldsVector.of_get
  · intro r
    by_cases hri : r = i
    · subst r
      simpa only [Function.update_self] using hr
    · simpa [Function.update_of_ne hri] using
        Store.get_of_readBlock (hentry r hri) (j := 0) (by omega) (0 : ℝ)
  · intro r
    by_cases hri : r = i
    · subst r
      simpa only [Function.update_self] using hi
    · simpa [Function.update_of_ne hri] using
        Store.get_of_readBlock (hentry r hri) (j := 1) (by omega) (0 : ℝ)

end NLAlib.ShiftedQR
