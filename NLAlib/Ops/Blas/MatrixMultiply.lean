/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.ScalarProductRoutine
public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Logic.EntryColumn
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# Scalar matrix multiplication in column-major storage

Every output entry is the shared streamed scalar product, with one caller-owned temporary
reused across entries. The full product is computed in scoped storage before its final copy
to the caller. No matrix multiplication primitive or numerical accuracy law is assumed.
The word formula records literal zero and every multiplication and addition in their actual
order, including an empty inner dimension.

## Main results

* `NLAlib.Ops.ScalarMatrix.column_meets`: a streamed column has its actual machine-word values.
* `NLAlib.Ops.ScalarMatrix.multiply_meets`: the complete scalar product's word judgment.
* `NLAlib.Ops.ScalarMatrix.multiply_writes`: the same body permits overlapping output operands.
-/

@[expose] public section

namespace NLAlib.Ops.ScalarMatrix

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- One column of a column-major product. The input row is a view of stride `rows`, and the
same unreported temporary is passed to every scalar product. -/
def column : Routine Op Tst :=
  routine% [rows, inner] (a : rows * inner, b : inner) → (c : rows, unreported t : 1) {
    for i < rows {
      run (ScalarProducts.sumRoutine (Op := Op) (Tst := Tst))
        [inner, rows, 1] (a[i], b, c[i], t)
    }
  }

/-- All columns of the product with one caller-supplied scalar temporary. -/
def columns : Routine Op Tst :=
  routine% [rows, inner, cols] (a : rows * inner, b : inner * cols) →
      (c : rows * cols, unreported t : 1) {
    for j < cols {
      run (column (Op := Op) (Tst := Tst)) [rows, inner]
        (a, b[j * inner], c[j * rows], t)
    }
  }

/-- Compute every product entry before writing the caller's output. The same body supports
outputs overlapping either source when read through the alias-aware operand theorem. -/
def multiply : Routine Op Tst :=
  routine% [rows, inner, cols] (a : rows * inner, b : inner * cols) → (c : rows * cols) {
    let product ← alloc (rows * cols);
    let t ← alloc 1;
    run (columns (Op := Op) (Tst := Tst)) [rows, inner, cols] (a, b, product, t);
    run (copyLoopRoutine (Op := Op) (Tst := Tst)) [rows * cols] (product, c)
  }

variable [Inhabited K]

/-- The actual finite row read by the scalar product's strided view. -/
def rowWords (rows inner : ℕ) (as : List K) (i : ℕ) : List K :=
  List.ofFn fun q : Fin inner => vec as (rows * q + i)

/-- The actual scalar recurrence for one product entry and an explicit right-hand column. -/
def columnEntry (M : Machine K) (rows inner : ℕ) (as bs : List K) (i : ℕ) : K :=
  ScalarProducts.sumWord M (vec (rowWords rows inner as i)) (vec bs) inner

/-- The machine words written for one product column, in increasing row order. -/
def columnWords (M : Machine K) (rows inner : ℕ) (as bs : List K) : List K :=
  (List.range rows).map (columnEntry M rows inner as bs)

/-- The complete machine-word product, indexed by its finite row and column. -/
def wordMatrix (M : Machine K) (rows inner cols : ℕ) (as bs : List K) :
    Matrix (Fin rows) (Fin cols) K := fun i j =>
  columnEntry M rows inner as ((bs.drop (j * inner)).take inner) i

/-- The reported column is its actual scalar recurrence, with the temporary unreported. -/
def columnSpec (M : Machine K) : Routine.Spec K :=
  spec% [rows, inner] (as, bs) → (cs) ensures cs = columnWords M rows inner as bs

/-- The reported matrix is packed by the existing column-major scalar codec. -/
def multiplySpec (M : Machine K) : Routine.Spec K :=
  spec% [rows, inner, cols] (as, bs) → (cs) ensures
    cs = (EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs)

/-- Every row is read by the shared strided scalar-product routine. One temporary is reused;
its writes are disjoint from every retained output entry and both source blocks. -/
theorem column_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (column (Op := Op) (Tst := Tst)).Meets I (columnSpec M) := by
  routine_intro [rows, inner] (a, b, c, t) reads (as, bs)
  obtain ⟨hcroom, htroom⟩ := hroom
  refine (writes_fill_scratch rfl (Store.inBlock t.1 t.2 1)
    (Fp.disj_inBlock_of_ne hct.symm) (columnEntry M rows inner as bs)
    (fun _ => m.pos) rfl ?_).mono (by fp_sub) ?_
  · intro i hi μ hfr hprefix hp
    have hA : μ.store.readBlock a.1 a.2 (rows * inner) = some as := by keep
    have hB : μ.store.readBlock b.1 b.2 inner = some bs := by keep
    have hrow : μ.store.readView a.1 (a.2 + i) ⟨1, some (inner, rows)⟩ =
        some (rowWords rows inner as i) := by
      apply Store.readView_eq_some_iff.mpr
      refine ⟨by simp [rowWords, View.cells], ?_⟩
      intro q hq
      have hq' : q < inner := by simpa [View.cells] using hq
      have hbound : rows * q + i < rows * inner := by
        simpa only [Nat.mul_comm] using Idx.add_lt_mul hq' hi
      have hg := Store.get_of_readBlock hA hbound default
      simpa [rowWords, View.offset_runs_one, vec, hq', Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hg
    have hbview : μ.store.readView b.1 b.2 ⟨1, some (inner, 1)⟩ = some bs := by
      simpa using hB
    call (ScalarProducts.sumRoutine_meets hI) [inner, rows, 1]
      ((a.1, a.2 + i), b, (c.1, c.2 + i), t)
      as μ₂ hfr₂ hpos₂ (zs) hpost
    case' hcall => exact [rowWords rows inner as i, bs]
    case' hr =>
      change μ.readViews [(a.1, a.2 + i), b]
        [⟨1, some (inner, rows)⟩, ⟨1, some (inner, 1)⟩] = some _
      exact Mem.readViews_of_cons hrow (Mem.readViews_of_cons hbview rfl)
    obtain ⟨z, hz, rfl⟩ := Store.readBlock_one_eq_some.mp hzs
    have he : z = columnEntry M rows inner as bs i := hpost
    subst z
    exact ⟨hz, by omega⟩
  · intro μ _ ⟨hvec, hpos⟩
    exact ⟨hpos, [columnWords M rows inner as bs],
      Mem.readBlocks_of_cons (Store.holdsVec_iff_readBlock.mp hvec) rfl, rfl⟩

/-- The column loop returns the packed matrix of actual scalar-product words. All columns
share one temporary cell and preserve the read-only matrix operands. -/
theorem columns_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (columns (Op := Op) (Tst := Tst)).Meets I (multiplySpec M) := by
  routine_intro [rows, inner, cols] (a, b, c, t) reads (as, bs)
  let region := fun j => Store.inBlock c.1 (c.2 + j * rows) rows
  let result := fun j (s : Store K) => s.readBlock c.1 (c.2 + j * rows) rows =
    some (columnWords M rows inner as ((bs.drop (j * inner)).take inner))
  let layout : MatLayout := ⟨c.1, c.2, rows, cols, rows⟩
  have hsub (j : ℕ) (hj : j < cols) : region j ≤ Store.inBlock c.1 c.2 (rows * cols) := by
    simpa only [layout, region, Nat.mul_comm] using
      (layout.col_fp hj).trans (MatLayout.fp_le_inBlock le_rfl)
  have hdis (i j : ℕ) (hne : i ≠ j) :
      Fp.Disj (region i) (region j) := by
    rcases lt_or_gt_of_ne hne with h | h
    · simpa only [layout, region, Nat.one_mul] using
        (layout.disj_of_cols (j₁ := i) (n₁ := 1) (j₂ := j) (n₂ := 1) (by omega))
    · have hh : Fp.Disj (region j) (region i) := by
        simpa only [layout, region, Nat.one_mul] using
          (layout.disj_of_cols (j₁ := j) (n₁ := 1) (j₂ := i) (n₂ := 1) (by omega))
      exact hh.symm
  refine (writes_loop_disjoint_prefix_scratch
    (scratch := Store.inBlock t.1 t.2 1)
    (F := Store.inBlock c.1 c.2 (rows * cols) ⊔ Store.inBlock t.1 t.2 1)
    region result rfl (fun j hj => (hsub j hj).trans le_sup_left) le_sup_right
    (fun i _ j _ hne => hdis i j hne)
    (fun _ _ => Fp.disj_inBlock_of_ne hct.symm)
    (fun _ _ => Store.readsOnly_readBlock _ _ _ _)
    ?_).mono (by fp_sub) ?_
  · intro j hj μ hfr
    have hfull : m.store.EqOff
        (Store.inBlock c.1 c.2 (rows * cols) ⊔ Store.inBlock t.1 t.2 1) μ.store :=
      hfr.mono (by
        intro q x h
        rcases h with h | h
        · obtain ⟨i, hi, hx⟩ := h
          exact Or.inl (hsub i (hi.trans hj) q x hx)
        · exact Or.inr h)
    have hA : μ.store.readBlock a.1 a.2 (rows * inner) = some as := by keep
    have hB : μ.store.readBlock b.1 b.2 (inner * cols) = some bs := by keep
    have hbound : j * inner + inner ≤ inner * cols := by
      have h := Nat.mul_le_mul_right inner (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at h
      simpa only [Nat.mul_comm] using h
    have hBj := Store.readBlock_sub hB hbound
    call (column_meets hI) [rows, inner]
      (a, (b.1, b.2 + j * inner), (c.1, c.2 + j * rows), t)
      as μ₂ hfr₂ hpos₂ (cs) hpost
    case' hroom =>
      change μ.Room [(c.1, c.2 + j * rows), t] [rows, 1]
      simp only [Mem.room_cons, Mem.room_nil, and_true]
      rw [hfr.len_eq c.1, hfr.len_eq t.1]
      have hboundC : j * rows + rows ≤ rows * cols := by
        have h := Nat.mul_le_mul_right rows (Nat.succ_le_of_lt hj)
        rw [Nat.succ_mul] at h
        simpa only [Nat.mul_comm] using h
      exact ⟨by have := hroom.1; omega, hroom.2⟩
    have he : cs = columnWords M rows inner as ((bs.drop (j * inner)).take inner) := hpost
    exact ⟨hpos₂, by simpa only [result, he] using hcs⟩
  · intro μ _ ⟨hpos, hcols⟩
    have hc : μ.store.readBlock c.1 c.2 (cols * rows) =
        some ((EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs)) := by
      apply Store.readBlock_scalar_matrix_of_columns
      intro j
      have hj := hcols j j.isLt
      have he : columnWords M rows inner as ((bs.drop (j * inner)).take inner) =
          List.ofFn ((wordMatrix M rows inner cols as bs).col j) := by
        apply List.ext_getElem <;> simp [columnWords, wordMatrix, Matrix.col]
      simpa only [result, he] using hj
    exact ⟨hpos, [(EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs)],
      Mem.readBlocks_of_cons (by simpa only [Nat.mul_comm] using hc) rfl, rfl⟩

/-- The complete scalar product is computed before the caller's output is written. This
operand judgment permits arbitrary overlap of the output with either source: only its room,
actual source reads and live handles are required. It is the alias-aware reading of the same
body used by `multiply_meets`, whose ordinary routine interface separates its output. -/
theorem multiply_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {m : Mem K} {rows inner cols : ℕ} {a b c : ℕ × ℕ} {as bs : List K}
    (hl : m.Live [a, b, c])
    (ha : m.store.readBlock a.1 a.2 (rows * inner) = some as)
    (hb : m.store.readBlock b.1 b.2 (inner * cols) = some bs)
    (hc : c.2 + rows * cols ≤ m.store.len c.1) :
    Writes .total I τ (multiply (Op := Op) (Tst := Tst)).body
      (Env.frame [rows, inner, cols] [a, b, c]) (Store.inBlock c.1 c.2 (rows * cols))
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock c.1 c.2 (rows * cols) =
        some ((EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs))) m := by
  obtain ⟨hla, hlb, hlc⟩ : a.1 < m.store.length ∧ b.1 < m.store.length ∧
      c.1 < m.store.length := by simpa only [Mem.live_cons, Mem.live_nil, and_true] using hl
  change Writes .total I τ (Stmt.allocs [.var 0 * .var 2, .const 1] _)
    (Env.frame [rows, inner, cols] [a, b, c]) _ _ m
  refine writes_allocs rfl ?_
  intro store hlength hlens hbelow
  have hp : store.len m.store.length = rows * cols := by simpa using hlens 0 (by simp)
  have ht : store.len (m.store.length + 1) = 1 := by simpa using hlens 1 (by simp)
  have hA : store.readBlock a.1 a.2 (rows * inner) = some as :=
    Store.Below.readBlock_of hbelow hla ha
  have hB : store.readBlock b.1 b.2 (inner * cols) = some bs :=
    Store.Below.readBlock_of hbelow hlb hb
  have hC : c.2 + rows * cols ≤ store.len c.1 := by rw [(hbelow c.1 hlc).1]; exact hc
  have hap : a.1 ≠ m.store.length := by omega
  have hat : a.1 ≠ m.store.length + 1 := by omega
  have hbp : b.1 ≠ m.store.length := by omega
  have hbt : b.1 ≠ m.store.length + 1 := by omega
  have hpt : m.store.length ≠ m.store.length + 1 := by omega
  have hpc : m.store.length ≠ c.1 := by omega
  call (columns_meets hI) [rows, inner, cols]
    (a, b, (m.store.length, 0), (m.store.length + 1, 0))
    as μ₁ hfr₁ hpos₁ (ps) hpost
  have hproduct : ps =
      (EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs) := hpost
  call (copyLoopRoutine_meets hI (fun _ => True)) [rows * cols]
    ((m.store.length, 0), c) as μ₂ hfr₂ hpos₂ (cs) hcopy
  have he : cs = ps := (List.cons.inj hcopy).1
  have hread : μ₂.store.readBlock c.1 c.2 (rows * cols) =
      some ((EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs)) := by
    simpa only [he, hproduct] using hcs
  intro final hfinal hbelowFinal
  exact ⟨by change μ₂.pos = m.pos; omega,
    Store.Below.readBlock_of hbelowFinal hlc hread⟩

/-- The ordinary separated-operand interface of the same compute-before-write scalar product
meets its actual word specification. The alias-aware operand judgment is `multiply_writes`. -/
theorem multiply_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (multiply (Op := Op) (Tst := Tst)).Meets I (multiplySpec M) := by
  routine_intro [rows, inner, cols] (a, b, c) reads (as, bs)
  refine (multiply_writes hI hlive has hbs hroom).mono (by fp_sub) ?_
  intro μ _ ⟨hpos, hread⟩
  exact ⟨hpos, [(EntryCodec.scalar K).packFinMatrix (wordMatrix M rows inner cols as bs)],
    Mem.readBlocks_of_cons hread rfl, rfl⟩

end NLAlib.Ops.ScalarMatrix
