/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryPacking
public import NLAlib.Ops.Logic.EntryRows
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Matrix.FinitePrecision.Machine

/-!
# Interleaved complex storage for shifted QR

The representation is the existing pair entry codec, with real and imaginary components in
adjacent words and matrix columns stored consecutively. The predicates below abbreviate the
ordinary packed block reads. They expose component reads and transport through frames and
scoped allocation; no numerical operation or new encoding is introduced.

## Main results

* `NLAlib.ShiftedQR.HoldsMatrix`: a finite complex matrix in a real-word block.
* `NLAlib.ShiftedQR.HoldsMatrix.get_re`, `NLAlib.ShiftedQR.HoldsMatrix.get_im`: its actual words.
* `NLAlib.ShiftedQR.HoldsMatrix.of_eqOff`: preservation under disjoint writes.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The actual real and imaginary components of a mathematical complex matrix, packed by
the existing pair codec in column-major order. -/
def matrixWords {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) ℂ) : List ℝ :=
  (EntryCodec.pair ℝ).packFinMatrix (A.map fun z => (z.re, z.im))

/-- Every complex entry occupies exactly two real words, including an empty matrix. -/
@[simp] theorem length_matrixWords {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) ℂ) :
    (matrixWords A).length = 2 * (cols * rows) := by
  unfold matrixWords
  rw [EntryCodec.length_packFinMatrix]
  change cols * rows * 2 = 2 * (cols * rows)
  omega

/-- The existing matrix codec stores a list of shifts as a one-column complex matrix. -/
def shiftColumn (ss : List ℂ) : Matrix (Fin ss.length) (Fin 1) ℂ := fun i _ => ss[i]

/-- A list is presented as one complex column; each entry occupies two adjacent real words. -/
def listColumn (ss : List ℂ) (k : ℕ) : Matrix (Fin k) (Fin 1) ℂ :=
  fun i _ => ss.getD i 0

/-- At its actual length the padded list column is exactly the stored shift column. -/
@[simp] theorem listColumn_length (ss : List ℂ) : listColumn ss ss.length = shiftColumn ss := by
  ext i j
  simp only [listColumn, shiftColumn, List.getD_eq_getElem _ _ i.isLt, Fin.getElem_fin]

/-- Decode the supplied word block using the existing pair codec and complex decoding. -/
def matrixOfWords (N : ℕ) (xs : List ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  decodeMatrix id ((EntryCodec.pair ℝ).matrix N N xs)

/-- Reading back packed complex storage recovers its mathematical matrix. -/
@[simp] theorem matrixOfWords_matrixWords {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) :
    matrixOfWords N (matrixWords H) = H := by
  simp only [matrixOfWords, matrixWords, EntryCodec.matrix_packFinMatrix]
  ext i j
  apply Complex.ext <;> rfl

/-- Repacking a correctly sized raw matrix block preserves every supplied word. -/
theorem matrixWords_matrixOfWords {N : ℕ} (xs : List ℝ)
    (hlen : xs.length = 2 * (N * N)) :
    matrixWords (matrixOfWords N xs) = xs := by
  have hcomponents : ((matrixOfWords N xs).map fun z => (z.re, z.im)) =
      (EntryCodec.pair ℝ).matrix N N xs := by
    ext i j <;> rfl
  unfold matrixWords
  rw [hcomponents]
  exact (EntryCodec.pair ℝ).packFinMatrix_matrix N N xs (by
    simpa only [EntryCodec.pair, Nat.mul_comm 2] using hlen)

/-- The named matrix is the actual pair-codec block at the supplied view. -/
def HoldsMatrix {rows cols : ℕ} (b : ℕ × ℕ) (A : Matrix (Fin rows) (Fin cols) ℂ)
    (s : Store ℝ) : Prop :=
  s.readBlock b.1 b.2 (2 * (cols * rows)) = some (matrixWords A)

/-- A kernel's declared-length list column is the actual shift column whenever its output
list has that length. This transports the existing codec representation across that equality. -/
theorem HoldsMatrix.shiftColumn {b : ℕ × ℕ} {ss : List ℂ} {k : ℕ} {st : Store ℝ}
    (h : HoldsMatrix b (listColumn ss k) st) (hlen : ss.length = k) :
    HoldsMatrix b (shiftColumn ss) st := by
  subst k
  simpa only [listColumn_length] using h

/-- The real part is the first word of its actual matrix entry. -/
theorem HoldsMatrix.get_re {rows cols : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin rows) (Fin cols) ℂ} {s : Store ℝ} (h : HoldsMatrix b A s)
    (i : Fin rows) (j : Fin cols) :
    s.get b.1 (b.2 + 2 * (j * rows + i)) = some (A i j).re := by
  have hi := Idx.add_lt_mul (Idx.add_lt_mul j.isLt i.isLt) (show 0 < 2 by omega)
  have hg := Store.get_of_readBlock h (j := (j * rows + i) * 2 + 0) (by omega) (0 : ℝ)
  change s.get b.1 (b.2 + ((j * rows + i) * 2 + 0)) =
    some (vec ((EntryCodec.pair ℝ).packFinMatrix
      (A.map fun z => (z.re, z.im))) ((j * rows + i) * 2 + 0)) at hg
  rw [EntryCodec.vec_packFinMatrix (EntryCodec.pair ℝ) _ i j
    ⟨0, by norm_num [EntryCodec.pair]⟩] at hg
  change s.get b.1 (b.2 + ((j * rows + i) * 2 + 0)) = some (A i j).re at hg
  simpa only [Nat.add_zero, Nat.mul_comm 2] using hg

/-- The imaginary part is the second word of its actual matrix entry. -/
theorem HoldsMatrix.get_im {rows cols : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin rows) (Fin cols) ℂ} {s : Store ℝ} (h : HoldsMatrix b A s)
    (i : Fin rows) (j : Fin cols) :
    s.get b.1 (b.2 + 2 * (j * rows + i) + 1) = some (A i j).im := by
  have hi := Idx.add_lt_mul (Idx.add_lt_mul j.isLt i.isLt) (show 1 < 2 by omega)
  have hg := Store.get_of_readBlock h (j := (j * rows + i) * 2 + 1) (by omega) (0 : ℝ)
  change s.get b.1 (b.2 + ((j * rows + i) * 2 + 1)) =
    some (vec ((EntryCodec.pair ℝ).packFinMatrix
      (A.map fun z => (z.re, z.im))) ((j * rows + i) * 2 + 1)) at hg
  rw [EntryCodec.vec_packFinMatrix (EntryCodec.pair ℝ) _ i j
    ⟨1, by norm_num [EntryCodec.pair]⟩] at hg
  change s.get b.1 (b.2 + ((j * rows + i) * 2 + 1)) = some (A i j).im at hg
  simpa only [Nat.add_assoc, Nat.mul_comm 2] using hg

/-- Each entry is readable as its pair of component words. -/
theorem HoldsMatrix.read_entry {rows cols : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin rows) (Fin cols) ℂ} {s : Store ℝ} (h : HoldsMatrix b A s)
    (i : Fin rows) (j : Fin cols) :
    s.readBlock b.1 (b.2 + 2 * (j * rows + i)) 2 = some [(A i j).re, (A i j).im] := by
  rw [Store.readBlock_eq_some_iff]
  refine ⟨rfl, fun k hk => ?_⟩
  have hk' : k < 2 := hk
  interval_cases k
  · simpa using h.get_re i j
  · simpa [Nat.add_assoc] using h.get_im i j

/-- Actual component reads of every finite matrix entry reconstruct its packed block. -/
theorem HoldsMatrix.of_get {rows cols : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin rows) (Fin cols) ℂ} {s : Store ℝ}
    (hr : ∀ (i : Fin rows) (j : Fin cols), s.get b.1 (b.2 + 2 * (j * rows + i)) = some (A i j).re)
    (hi : ∀ (i : Fin rows) (j : Fin cols),
      s.get b.1 (b.2 + 2 * (j * rows + i) + 1) = some (A i j).im) :
    HoldsMatrix b A s := by
  let E : ℕ → ℕ → ℝ × ℝ := fun i j =>
    if hi : i < rows then if hj : j < cols then
      ((A ⟨i, hi⟩ ⟨j, hj⟩).re, (A ⟨i, hi⟩ ⟨j, hj⟩).im) else (0, 0) else (0, 0)
  have hE : s.HoldsEntries (EntryCodec.pair ℝ) ⟨b.1, b.2, rows, cols, rows⟩ E := by
    intro i hir j hjc z
    fin_cases z
    · simpa [E, hir, hjc, Nat.mul_comm] using hr ⟨i, hir⟩ ⟨j, hjc⟩
    · simpa [E, hir, hjc, Nat.mul_comm, Nat.add_assoc] using hi ⟨i, hir⟩ ⟨j, hjc⟩
  have h := hE.readBlock_packFinMatrix rfl
  have hmat : (Matrix.of fun (i : Fin rows) (j : Fin cols) => E i j) =
      (A.map fun z => (z.re, z.im)) := by
    funext i j
    simp [E, Matrix.map_apply]
  simpa only [HoldsMatrix, matrixWords, hmat, Nat.mul_comm 2] using h

/-- Writing one complete complex entry updates the corresponding mathematical matrix entry.
All other entries are retained by the ordinary spatial frame. -/
theorem HoldsMatrix.of_entry_write {rows cols : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin rows) (Fin cols) ℂ} {s s' : Store ℝ}
    (h : HoldsMatrix b A s) (i : Fin rows) (j : Fin cols) (z : ℂ)
    (hfr : s.EqOff (Store.inBlock b.1 (b.2 + 2 * (j * rows + i)) 2) s')
    (hr : s'.get b.1 (b.2 + 2 * (j * rows + i)) = some z.re)
    (hi : s'.get b.1 (b.2 + 2 * (j * rows + i) + 1) = some z.im) :
    HoldsMatrix b (A.updateRow i (Function.update (A i) j z)) s' := by
  have hkeep (r : Fin rows) (c : Fin cols) (hne : (r, c) ≠ (i, j)) :
      s'.readBlock b.1 (b.2 + 2 * (c * rows + r)) 2 =
        some [(A r c).re, (A r c).im] := by
    have hd := (EntryCodec.pair ℝ).disj_entryBlock_matrix (b := b.1) (off := b.2) hne
    exact hfr.keep (Store.readsOnly_readBlock _ _ _ _) (by
      simpa only [EntryCodec.entryBlock, EntryCodec.pair] using hd.symm) (h.read_entry r c)
  have hvalue (r : Fin rows) (c : Fin cols) (hne : (r, c) ≠ (i, j)) :
      A.updateRow i (Function.update (A i) j z) r c = A r c := by
    by_cases hri : r = i
    · subst r
      have hcj : c ≠ j := fun hcj => hne (Prod.ext rfl hcj)
      simp [Matrix.updateRow_apply, hcj]
    · simp [Matrix.updateRow_apply, hri]
  apply HoldsMatrix.of_get
  · intro r c
    by_cases hrc : (r, c) = (i, j)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrc
      simpa using hr
    · have hg := Store.get_of_readBlock (hkeep r c hrc) (j := 0) (by omega) (0 : ℝ)
      simpa [hvalue r c hrc] using hg
  · intro r c
    by_cases hrc : (r, c) = (i, j)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrc
      simpa using hi
    · have hg := Store.get_of_readBlock (hkeep r c hrc) (j := 1) (by omega) (0 : ℝ)
      simpa [hvalue r c hrc, Nat.add_assoc] using hg

/-- Disjoint writes retain the exact packed matrix and its component values. -/
theorem HoldsMatrix.of_eqOff {rows cols : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin rows) (Fin cols) ℂ} {s s' : Store ℝ} {F : Fp}
    (h : HoldsMatrix b A s) (hfr : s.EqOff F s')
    (hd : Fp.Disj F (Store.inBlock b.1 b.2 (2 * (cols * rows)))) : HoldsMatrix b A s' :=
  hfr.keep (Store.readsOnly_readBlock _ _ _ _) hd h

/-- The packed matrix reads only its own declared component words. -/
theorem readsOnly_holdsMatrix {rows cols : ℕ} (b : ℕ × ℕ)
    (A : Matrix (Fin rows) (Fin cols) ℂ) :
    Store.ReadsOnly (Store.inBlock b.1 b.2 (2 * (cols * rows))) (HoldsMatrix b A) :=
  Store.readsOnly_readBlock _ _ _ _

/-- Surviving matrix storage is preserved through scoped scratch cleanup. -/
theorem HoldsMatrix.of_below {rows cols L : ℕ} {b : ℕ × ℕ}
    {A : Matrix (Fin rows) (Fin cols) ℂ} {s s' : Store ℝ}
    (h : HoldsMatrix b A s) (hBelow : Store.Below L s s') (hb : b.1 < L) :
    HoldsMatrix b A s' :=
  hBelow.keep (readsOnly_holdsMatrix b A) (fun _ _ hi => hi.1 ▸ hb) h

end NLAlib.ShiftedQR
