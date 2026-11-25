/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.SchurColumn
public import NLAlib.Ops.Logic.EntryColumn
public import NLAlib.Ops.Blas.Dot

/-!
# Scalar rank-one updates of packed matrices

One saved coefficient, column and row update every entry of a packed rectangular matrix.
The tree calls the scalar column routine once per column. All input words are retained;
only the matrix operand is updated. The word-level result is independent of numerical
accuracy assumptions and is shared by LU and Cholesky elimination.

## Main results

* `NLAlib.LU.rankOne_meets`: the actual scalar tree computes its stated word matrix.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- The words of one saved-column/saved-row update, with the scalar multiplication order
of the implementation stated explicitly. -/
def rankOneValues (M : Machine K) (a : K) (x y : ℕ → K) (A : ℕ → ℕ → K) : ℕ → ℕ → K :=
  fun i j => M.add (A i j) (M.mul (M.mul a (y j)) (x i))

/-- Update every matrix column through scalar multiply-add loops. The saved vectors and
coefficient are separate read operands; the matrix is updated in place. -/
def rankOne : Routine Op Tst :=
  routine% [rows, cols] (a : 1, x : rows, y : cols, A : rows * cols) → (A) {
    for j < cols {
      run (schurColumn (Op := Op) (Tst := Tst)) [rows] (a, x, y[j], A[j * rows])
    }
  }

variable [Inhabited K]

/-- The actual machine rank-one update, packed by columns. Its source vectors are supplied
words; neither a correct factorization nor a successful run is a hypothesis. -/
def rankOneSpec (M : Machine K) : Routine.Spec K :=
  spec% [rows, cols] ([a], xs, ys, As) → (Bs) ensures
    Bs = (EntryCodec.scalar K).packMatrix rows cols
      (rankOneValues M a (vec xs) (vec ys) (fun i j => vec As (j * rows + i)))

omit [Has ScalarOp Op] in
/-- The actual multiply-add word list for a packed column equals its entrywise packing. -/
theorem axpyF_column (M : Machine K) (a : K) (x : ℕ → K) (A : ℕ → ℕ → K)
    (rows j : ℕ) :
    axpyF M a x (vec ((EntryCodec.scalar K).pack rows fun i => A i j)) rows =
      (EntryCodec.scalar K).pack rows (fun i => M.add (A i j) (M.mul a (x i))) := by
  apply List.ext_getElem
  · simp [axpyF]
  · intro i hi hi'
    have hir : i < rows := by simpa [axpyF] using hi
    simp [axpyF, EntryCodec.scalar_pack, hir]

/-- The scalar rank-one routine meets its functional word specification on every machine,
including empty matrix dimensions. Only the matrix is changed, and no tape is consumed. -/
theorem rankOne_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (rankOne (Op := Op) (Tst := Tst)).Meets I (rankOneSpec M) := by
  routine_intro [rows, cols] (a, x, y, A) reads (as, xs, ys, As)
  obtain ⟨av, ha, rfl⟩ := Store.readBlock_one_eq_some.mp has
  let C := EntryCodec.scalar K
  let L : MatLayout := ⟨A.1, A.2, rows, cols, rows⟩
  let old := fun i j => vec As (j * rows + i)
  let new := rankOneValues M av (vec xs) (vec ys) old
  have hAs' : m.store.readBlock A.1 A.2 (cols * rows) = some As := by
    simpa only [Nat.mul_comm] using hAs
  have hstart : m.store.HoldsEntries C L old := by
    simpa only [C, L, EntryCodec.scalar_entry, Nat.mul_one] using
      (Store.holdsEntries_of_readBlock (C := C) (L := L) rfl
        (by simpa only [C, L, Nat.mul_one] using hAs'))
  loop_inv (fun _ => Fp.blocks [A] [rows * cols])
    (fun j m' => m'.pos = m.pos ∧ m'.store.HoldsEntries C L
      (fun i c => if c < j then new i c else old i c))
    with j hj m₁ hfr hP
  case round =>
    obtain ⟨hp, hmatrix⟩ := hP
    have ha₁ : m₁.store.readBlock a.1 a.2 1 = some [av] := by keep
    have hx₁ : m₁.store.readBlock x.1 x.2 rows = some xs := by keep
    have hy₁ : m₁.store.readBlock y.1 y.2 cols = some ys := by keep
    have hyj := Store.readBlock_one_of_get (Store.get_of_readBlock hy₁ hj default)
    have hcol : m₁.store.readBlock A.1 (A.2 + j * rows) rows =
        some (C.pack rows fun i => old i j) := by
      simpa only [C, L, Nat.one_mul, Nat.mul_one, if_neg (Nat.lt_irrefl j)] using
        hmatrix.readBlock_column hj
    have hcolroom : A.2 + j * rows + rows ≤ m₁.store.len A.1 := by
      rw [hfr.len_eq]
      have hm := Nat.mul_le_mul_right rows (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at hm
      nlinarith [hroom]
    call (schurColumn_meets hI) [rows] (a, x, (y.1, y.2 + j), (A.1, A.2 + j * rows))
      as m₂ hfr₂ hpos₂ (bs) hpost
    case' hle =>
      routine_nf
      simp only [Fp.blocks, sup_bot_eq]
      simpa only [L, Fp.blocks, sup_bot_eq, Nat.mul_comm] using
        (L.col_fp hj).trans (MatLayout.fp_le_inBlock le_rfl)
    have hwords : bs = C.pack rows (fun i => new i j) := by
      rw [hpost]
      exact axpyF_column M (M.mul av (vec ys j)) (vec xs) old rows j
    have hnew := hmatrix.update_column_of_frame (hL := le_rfl) (j := j) (F := ⊥)
      (by simp) (by simpa only [C, L, Fp.blocks, Nat.one_mul, Nat.mul_one,
        sup_bot_eq] using hfr₂)
      (fun i => new i j) (by simpa only [C, L, Nat.one_mul, Nat.mul_one, hwords] using hbs)
    refine ⟨hpos₂.trans hp, fun i hi c hc z => ?_⟩
    have hh := hnew i hi c hc z
    by_cases hcj : c = j
    · subst c
      simpa only [if_pos rfl, ite_true, if_pos (Nat.lt_succ_self j)] using hh
    · by_cases hlt : c < j
      · simpa only [if_neg hcj, if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)] using hh
      · simpa only [if_neg hcj, if_neg hlt, if_neg (show ¬c < j + 1 by omega)] using hh
  case exit =>
    rintro m₁ _ ⟨hp, hmatrix⟩
    have hm : m₁.store.HoldsEntries C L new := by
      intro i hi c hc z
      have hc' : c < cols := hc
      simpa only [if_pos hc'] using hmatrix i hi c hc z
    refine ⟨hp, [C.packMatrix rows cols new], Mem.readBlocks_of_cons ?_ rfl, rfl⟩
    simpa only [C, L, Nat.mul_one, Nat.mul_comm] using hm.readBlock rfl

end NLAlib.LU
