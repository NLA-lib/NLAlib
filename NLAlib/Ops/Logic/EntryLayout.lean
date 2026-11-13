/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import NLAlib.Ops.Logic.Layout

/-!
# Fixed-width entries in matrix buffers

A fixed-width entry is equivalent to a nonempty finite vector of opaque words. Packing is
column-major, with the words of one entry adjacent. The same component-read and frame facts
apply to pairs, complex storage, or any other fixed-width representation.

## Main results

* `NLAlib.Ops.EntryCodec.entry_pack`: packing followed by decoding preserves an entry.
* `NLAlib.Ops.Store.HoldsEntries.readBlock`: dense matrices give ordinary operand blocks.
* `NLAlib.Ops.Store.readsOnly_holdsEntries`: one frame rule for every entry representation.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K E : Type}

/-- A stored entry is exactly a positive, fixed number of words. The equivalence provides
both encoding and decoding, including all possible word vectors. -/
structure EntryCodec (K E : Type) where
  /-- Words per entry. -/
  width : ℕ
  /-- An entry uses at least one word. -/
  width_pos : 0 < width
  /-- Entries and word vectors are mutually inverse representations. -/
  words : E ≃ (Fin width → K)

namespace EntryCodec

/-- A flat list of words for the first `n` entries of a vector. -/
def pack (C : EntryCodec K E) (n : ℕ) (v : ℕ → E) : List K :=
  (List.range (n * C.width)).map fun q =>
    C.words (v (q / C.width)) ⟨q % C.width, Nat.mod_lt _ C.width_pos⟩

/-- Packing uses the declared word width, including an empty vector. -/
@[simp] theorem length_pack (C : EntryCodec K E) (n : ℕ) (v : ℕ → E) :
    (C.pack n v).length = n * C.width := by simp [pack]

/-- The component at a valid packed entry has its original value. -/
theorem vec_pack [Inhabited K] (C : EntryCodec K E) {n i : ℕ} (v : ℕ → E)
    (hi : i < n) (z : Fin C.width) :
    vec (C.pack n v) (i * C.width + z) = C.words (v i) z := by
  have hq := Idx.add_lt_mul hi z.isLt
  simp [pack, vec, List.getD_eq_getElem?_getD, hq, Idx.div_add z.isLt,
    Idx.mod_add z.isLt]

/-- Decode the entry at index `i` of a flat word list. -/
def entry [Inhabited K] (C : EntryCodec K E) (xs : List K) (i : ℕ) : E :=
  C.words.symm fun z => vec xs (i * C.width + z)

/-- Packing followed by decoding preserves each entry in the declared range. -/
@[simp] theorem entry_pack [Inhabited K] (C : EntryCodec K E) {n i : ℕ} (v : ℕ → E)
    (hi : i < n) : C.entry (C.pack n v) i = v i := by
  unfold entry
  have hw : (fun z : Fin C.width => vec (C.pack n v) (i * C.width + z)) = C.words (v i) := by
    funext z
    exact C.vec_pack v hi z
  rw [hw, C.words.symm_apply_apply]

/-- Pack a matrix by columns, with adjacent words inside each entry. -/
def packMatrix (C : EntryCodec K E) (rows cols : ℕ) (A : ℕ → ℕ → E) : List K :=
  C.pack (cols * rows) fun q => A (q % rows) (q / rows)

/-- The packed matrix has one fixed-width word vector per entry. -/
@[simp] theorem length_packMatrix (C : EntryCodec K E) (rows cols : ℕ)
    (A : ℕ → ℕ → E) : (C.packMatrix rows cols A).length = cols * rows * C.width :=
  C.length_pack _ _

/-- An entry of a matrix decoded from a flat column-major word block. -/
def matrix [Inhabited K] (C : EntryCodec K E) (rows cols : ℕ) (xs : List K) :
    Matrix (Fin rows) (Fin cols) E := fun i j => C.entry xs (j * rows + i)

/-- Matrix packing and decoding preserve every entry, with no rank or size assumptions. -/
@[simp] theorem matrix_packMatrix [Inhabited K] (C : EntryCodec K E) (rows cols : ℕ)
    (A : ℕ → ℕ → E) :
    C.matrix rows cols (C.packMatrix rows cols A) = fun (i : Fin rows) (j : Fin cols) => A i j := by
  funext i j
  simp [matrix, packMatrix, C.entry_pack _ (Idx.add_lt_mul j.isLt i.isLt),
    Idx.mod_add i.isLt, Idx.div_add i.isLt]

/-- Pack a finite matrix without supplying any padding entry. Empty matrices are included. -/
def packFinMatrix (C : EntryCodec K E) {rows cols : ℕ}
    (A : Matrix (Fin rows) (Fin cols) E) : List K :=
  List.ofFn fun q : Fin (cols * rows * C.width) =>
    let qz := finProdFinEquiv.symm q
    let ji := finProdFinEquiv.symm qz.1
    C.words (A ji.2 ji.1) qz.2

/-- The finite packing has exactly the declared number of words. -/
@[simp] theorem length_packFinMatrix (C : EntryCodec K E) {rows cols : ℕ}
    (A : Matrix (Fin rows) (Fin cols) E) :
    (C.packFinMatrix A).length = cols * rows * C.width := by simp [packFinMatrix]

/-- Every actual matrix entry supplies its own component words in finite packing. -/
theorem vec_packFinMatrix [Inhabited K] (C : EntryCodec K E) {rows cols : ℕ}
    (A : Matrix (Fin rows) (Fin cols) E) (i : Fin rows) (j : Fin cols)
    (z : Fin C.width) :
    vec (C.packFinMatrix A) ((j * rows + i) * C.width + z) = C.words (A i j) z := by
  have hq := Idx.add_lt_mul (Idx.add_lt_mul j.isLt i.isLt) z.isLt
  simp [packFinMatrix, vec, List.getD_eq_getElem?_getD, hq, finProdFinEquiv,
    Fin.divNat, Fin.modNat, Idx.div_add z.isLt, Idx.mod_add z.isLt,
    Idx.div_add i.isLt, Idx.mod_add i.isLt]

/-- Decoding finite packing gives the original Mathlib matrix. -/
@[simp] theorem matrix_packFinMatrix [Inhabited K] (C : EntryCodec K E) {rows cols : ℕ}
    (A : Matrix (Fin rows) (Fin cols) E) :
    C.matrix rows cols (C.packFinMatrix A) = A := by
  funext i j
  apply C.words.injective
  simp only [matrix, entry, Equiv.apply_symm_apply]
  funext z
  exact C.vec_packFinMatrix A i j z

/-- Decoding and repacking any correctly sized raw word block preserves every word. The
codec is an equivalence on all component vectors, so no representability or padding premise
is hidden in this inverse direction. -/
@[simp] theorem packFinMatrix_matrix [Inhabited K] (C : EntryCodec K E) (rows cols : ℕ)
    (xs : List K) (hlen : xs.length = cols * rows * C.width) :
    C.packFinMatrix (C.matrix rows cols xs) = xs := by
  apply List.ext_getElem
  · simp [hlen]
  · intro q hq hq'
    have hb : q < cols * rows * C.width := by simpa only [length_packFinMatrix] using hq
    have he : q / C.width < cols * rows := (Nat.div_lt_iff_lt_mul C.width_pos).mpr hb
    have hr : 0 < rows := Nat.pos_of_ne_zero fun hz => by simp [hz] at he
    have hi := Nat.mod_lt (q / C.width) hr
    have hj : q / C.width / rows < cols := (Nat.div_lt_iff_lt_mul hr).mpr he
    have hz := Nat.mod_lt q C.width_pos
    have hslot : (q / C.width / rows) * rows + q / C.width % rows = q / C.width := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod (q / C.width) rows
    have hflat : ((q / C.width / rows) * rows + q / C.width % rows) * C.width +
        q % C.width = q := by
      rw [hslot]
      simpa only [Nat.mul_comm] using Nat.div_add_mod q C.width
    have hv := C.vec_packFinMatrix (C.matrix rows cols xs)
      ⟨q / C.width % rows, hi⟩ ⟨q / C.width / rows, hj⟩ ⟨q % C.width, hz⟩
    simp only [matrix, entry, Equiv.apply_symm_apply] at hv
    change vec (C.packFinMatrix (C.matrix rows cols xs))
      (((q / C.width / rows) * rows + q / C.width % rows) * C.width + q % C.width) =
        vec xs (((q / C.width / rows) * rows + q / C.width % rows) * C.width + q % C.width) at hv
    rw [hflat] at hv
    simpa only [vec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq,
      List.getElem?_eq_getElem hq', Option.getD_some] using hv

/-- A predicate holds on every packed word exactly when it holds on every actual component
of every finite matrix entry. This includes matrices with an empty index type. -/
theorem forall_vec_packFinMatrix_iff [Inhabited K] (C : EntryCodec K E)
    {rows cols : ℕ} (A : Matrix (Fin rows) (Fin cols) E) (P : K → Prop) :
    (∀ q < cols * rows * C.width, P (vec (C.packFinMatrix A) q)) ↔
      ∀ i j z, P (C.words (A i j) z) := by
  constructor
  · intro h i j z
    have hq := Idx.add_lt_mul (Idx.add_lt_mul j.isLt i.isLt) z.isLt
    simpa only [vec_packFinMatrix] using h ((j * rows + i) * C.width + z) hq
  · intro h q hq
    let qz : Fin (cols * rows) × Fin C.width := finProdFinEquiv.symm ⟨q, hq⟩
    let ji : Fin cols × Fin rows := finProdFinEquiv.symm qz.1
    simpa [packFinMatrix, vec, List.getD_eq_getElem?_getD, hq, qz, ji] using h ji.2 ji.1 qz.2

/-- Restricting a logical matrix to finite indices gives the same packed word list. -/
theorem packFinMatrix_eq_packMatrix (C : EntryCodec K E) (rows cols : ℕ)
    (A : ℕ → ℕ → E) :
    C.packFinMatrix (Matrix.of fun (i : Fin rows) (j : Fin cols) => A i j) =
      C.packMatrix rows cols A := by
  refine List.ext_getElem (by rw [length_packFinMatrix, length_packMatrix]) fun i hi hi' => ?_
  simp only [packFinMatrix, packMatrix, pack, List.getElem_ofFn, List.getElem_map,
    List.getElem_range]
  rfl

/-- Taking the first columns of packed storage agrees with packing the corresponding
Mathlib column submatrix. No padding entries are introduced. -/
theorem take_packFinMatrix (C : EntryCodec K E) {rows cols count : ℕ}
    (A : Matrix (Fin rows) (Fin cols) E) (hc : count ≤ cols) :
    (C.packFinMatrix A).take (count * rows * C.width) =
      C.packFinMatrix (A.submatrix id (Fin.castLE hc)) := by
  have hlen : count * rows * C.width ≤ cols * rows * C.width :=
    Nat.mul_le_mul_right C.width (Nat.mul_le_mul_right rows hc)
  refine List.ext_getElem (by simp [List.length_take, Nat.min_eq_left hlen]) ?_
  intro i hi hi'
  simp only [List.getElem_take, packFinMatrix, List.getElem_ofFn]
  rfl

/-- One word stores an entry without an encoding conversion. -/
abbrev scalar (K : Type) : EntryCodec K K where
  width := 1
  width_pos := Nat.zero_lt_one
  words := (Equiv.funUnique (Fin 1) K).symm

/-- A scalar entry's only word is the entry itself. -/
theorem scalar_words_zero (v : K) : (scalar K).words v 0 = v := rfl

/-- Decoding a scalar entry reads exactly its stored word. -/
@[simp] theorem scalar_entry [Inhabited K] (xs : List K) (i : ℕ) :
    (scalar K).entry xs i = vec xs i := by
  simp only [entry, scalar, Equiv.symm_symm, Equiv.funUnique_apply, mul_one,
    Fin.default_eq_zero, Fin.val_zero, Nat.add_zero]

/-- Two words store an ordered pair, first component before second. -/
abbrev pair (K : Type) : EntryCodec K (K × K) where
  width := 2
  width_pos := by omega
  words :=
    { toFun := fun v i => if i = 0 then v.1 else v.2
      invFun := fun v => (v 0, v 1)
      left_inv := by intro v; simp
      right_inv := by
        intro v
        funext i
        fin_cases i <;> simp }

/-- A packed pair's first word is its first component. -/
theorem pair_words_zero (v : K × K) :
    (pair K).words v 0 = v.1 := rfl

/-- A packed pair's second word is its second component. -/
theorem pair_words_one (v : K × K) :
    (pair K).words v 1 = v.2 := rfl

/-- Decoding a pair reads its two actual adjacent words. -/
@[simp] theorem pair_entry [Inhabited K] (xs : List K) (i : ℕ) :
    (pair K).entry xs i = (vec xs (i * 2), vec xs (i * 2 + 1)) := by
  rfl

/-- The pair matrix decoder reads real and imaginary words at adjacent column-major cells. -/
@[simp] theorem pair_matrix [Inhabited K] (rows cols : ℕ) (xs : List K) :
    (pair K).matrix rows cols xs = fun (i : Fin rows) (j : Fin cols) =>
      (vec xs ((j * rows + i) * 2), vec xs ((j * rows + i) * 2 + 1)) := rfl

/-- Capacity for a valid matrix layout supplies capacity for every complete entry block.
The leading dimension and entry width are included in the common word bound. -/
theorem room_entry (C : EntryCodec K E) {s : Store K} {L : MatLayout} {i j : ℕ}
    (hL : L.Valid) (hi : i < L.rows) (hj : j < L.cols)
    (hz : L.off + C.width * (L.cols * L.ld) ≤ s.len L.buf) :
    L.off + C.width * (j * L.ld + i) + C.width ≤ s.len L.buf := by
  have hidx := Idx.add_lt_mul hj (hi.trans_le hL)
  have hw := Nat.mul_le_mul_left C.width (show j * L.ld + i + 1 ≤ L.cols * L.ld by omega)
  rw [Nat.mul_succ] at hw
  omega

end EntryCodec

namespace Store

/-- A matrix with fixed-width entries in a logical column-major layout. Offsets are word
offsets; the leading dimension counts entries. -/
def HoldsEntries (s : Store K) (C : EntryCodec K E) (L : MatLayout)
    (A : ℕ → ℕ → E) : Prop :=
  ∀ i < L.rows, ∀ j < L.cols, ∀ z : Fin C.width,
    s.get L.buf (L.off + C.width * (j * L.ld + i) + z) = some (C.words (A i j) z)

/-- One matrix entry is an ordinary block of its component words. -/
theorem HoldsEntries.readBlock_entry {s : Store K} {C : EntryCodec K E} {L : MatLayout}
    {A : ℕ → ℕ → E} (h : s.HoldsEntries C L A) {i j : ℕ}
    (hi : i < L.rows) (hj : j < L.cols) :
    s.readBlock L.buf (L.off + C.width * (j * L.ld + i)) C.width =
      some (List.ofFn (C.words (A i j))) := by
  rw [readBlock_eq_some_iff]
  refine ⟨by simp, fun z hz => ?_⟩
  rw [h i hi j hj ⟨z, hz⟩]
  simp [hz]

/-- Dense component reads are exactly a read of the packed operand block. -/
theorem HoldsEntries.readBlock {s : Store K} {C : EntryCodec K E} {L : MatLayout}
    {A : ℕ → ℕ → E} (h : s.HoldsEntries C L A) (hL : L.rows = L.ld) :
    s.readBlock L.buf L.off (L.cols * L.rows * C.width) =
      some (C.packMatrix L.rows L.cols A) := by
  rw [readBlock_eq_some_iff]
  refine ⟨C.length_packMatrix _ _ _, fun q hq => ?_⟩
  have he : q / C.width < L.cols * L.rows := by
    rw [Nat.div_lt_iff_lt_mul C.width_pos]
    exact hq
  have hr : 0 < L.rows := Nat.pos_of_ne_zero fun hz => by simp [hz] at he
  have hj : q / C.width / L.rows < L.cols := by
    rw [Nat.div_lt_iff_lt_mul hr]
    exact he
  have hi := Nat.mod_lt (q / C.width) hr
  have hz := Nat.mod_lt q C.width_pos
  have hd := Nat.div_add_mod (q / C.width) L.rows
  have hw := Nat.div_add_mod q C.width
  have ha : L.off + q = L.off + C.width *
      (q / C.width / L.rows * L.ld + q / C.width % L.rows) + q % C.width := by
    rw [← hL, Nat.mul_comm (q / C.width / L.rows) L.rows, hd]
    omega
  rw [ha, h _ hi _ hj ⟨q % C.width, hz⟩]
  simp [EntryCodec.packMatrix, EntryCodec.pack, hq]

/-- Dense logical component reads supply the finite mathematical matrix's packed block. -/
theorem HoldsEntries.readBlock_packFinMatrix {s : Store K} {C : EntryCodec K E}
    {L : MatLayout} {A : ℕ → ℕ → E} (h : s.HoldsEntries C L A) (hL : L.rows = L.ld) :
    s.readBlock L.buf L.off (L.cols * L.rows * C.width) =
      some (C.packFinMatrix (Matrix.of fun (i : Fin L.rows) (j : Fin L.cols) => A i j)) := by
  simpa only [EntryCodec.packFinMatrix_eq_packMatrix] using h.readBlock hL

/-- A dense packed block supplies the actual component reads of its decoded matrix. -/
theorem holdsEntries_of_readBlock [Inhabited K] {s : Store K} {C : EntryCodec K E}
    {L : MatLayout} {xs : List K} (hL : L.rows = L.ld)
    (h : s.readBlock L.buf L.off (L.cols * L.rows * C.width) = some xs) :
    s.HoldsEntries C L (fun i j => C.entry xs (j * L.rows + i)) := by
  intro i hi j hj z
  have hq := Idx.add_lt_mul (Idx.add_lt_mul hj hi) z.isLt
  have hg := get_of_readBlock h hq default
  simpa [EntryCodec.entry, ← hL, Nat.mul_comm, Nat.add_assoc] using hg

/-- Reading an explicitly packed dense matrix gives its original logical entries. -/
theorem holdsEntries_of_readBlock_packMatrix [Inhabited K] {s : Store K}
    {C : EntryCodec K E} {L : MatLayout} {A : ℕ → ℕ → E} (hL : L.rows = L.ld)
    (h : s.readBlock L.buf L.off (L.cols * L.rows * C.width) =
      some (C.packMatrix L.rows L.cols A)) : s.HoldsEntries C L A := by
  have hd := holdsEntries_of_readBlock hL h
  intro i hi j hj z
  simpa [EntryCodec.packMatrix, C.entry_pack _ (Idx.add_lt_mul hj hi),
    Idx.mod_add hi, Idx.div_add hi] using hd i hi j hj z

/-- Dense logical entries and ordinary packed operand blocks are equivalent. -/
theorem holdsEntries_iff_readBlock [Inhabited K] {s : Store K} {C : EntryCodec K E}
    {L : MatLayout} {A : ℕ → ℕ → E} (hL : L.rows = L.ld) :
    s.HoldsEntries C L A ↔ s.readBlock L.buf L.off (L.cols * L.rows * C.width) =
      some (C.packMatrix L.rows L.cols A) :=
  ⟨fun h => h.readBlock hL, holdsEntries_of_readBlock_packMatrix hL⟩

/-- A rectangular view preserves the leading dimension and translates only its word offset.
The enclosing matrix supplies its component reads without any copy operation. -/
theorem HoldsEntries.submatrix {s : Store K} {C : EntryCodec K E} {L : MatLayout}
    {A : ℕ → ℕ → E} (h : s.HoldsEntries C L A) {r c rows cols : ℕ}
    (hr : r + rows ≤ L.rows) (hc : c + cols ≤ L.cols) :
    s.HoldsEntries C ⟨L.buf, L.off + C.width * (c * L.ld + r), rows, cols, L.ld⟩
      (fun i j => A (r + i) (c + j)) := by
  intro i hi j hj z
  change i < rows at hi
  change j < cols at hj
  have hh := h (r + i) (by omega) (c + j) (by omega) z
  convert hh using 1
  congr 1
  simp only [Nat.add_mul, Nat.mul_add]
  omega

/-- Fixed-width matrices read only their containing word block. This lets the existing frame
rule preserve them without per-component frame arguments in algorithms. -/
theorem readsOnly_holdsEntries (C : EntryCodec K E) (L : MatLayout)
    (A : ℕ → ℕ → E) (hL : L.Valid) :
    ReadsOnly (inBlock L.buf L.off (C.width * (L.cols * L.ld)))
      (fun s : Store K => s.HoldsEntries C L A) := by
  intro s s' hg h i hi j hj z
  have hl : i < L.ld := hi.trans_le hL
  have hp := Idx.add_lt_mul (Idx.add_lt_mul hj hl) z.isLt
  rw [hg L.buf (L.off + C.width * (j * L.ld + i) + z) ?_]
  · exact h i hi j hj z
  · exact ⟨rfl, by omega, by nlinarith⟩

end Store

end NLAlib.Ops
