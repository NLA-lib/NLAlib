/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.ScalarProducts
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.Catalog.StoredOperator
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.AllocationFree
public import NLAlib.Ops.Profiles.StoredRoutine

/-!
# Dense matrix-vector application by streamed scalar arithmetic

The matrix is stored by columns. Each output row streams its products using one temporary
scalar cell. Output separation from the data and input vector is the declared admission of
the stored-operator model, rather than an assumption that an execution succeeds.

## Main results

* `NLAlib.Ops.StoredDense.apply` performs the row loops with caller-owned temporary.
* `NLAlib.Ops.StoredDense.impl` allocates its one temporary cell.
* `NLAlib.Ops.StoredDense.writes_apply_word` returns the supplied machine's actual row words.
* `NLAlib.Ops.StoredDense.writes_apply` specializes this to the exact matrix-vector product.
-/

@[expose] public section

namespace NLAlib.Ops.StoredDense

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Stream each row of a column-major matrix through the shared scalar product loop. -/
def apply : Stmt Op Tst := ops% [m, n] (data, x, t) → (y) {
  for i < m { run ScalarProducts.sum [n, m, 1] (data[i], x, t, y[i]) }
}

/-- One scoped scalar temporary suffices because the output is separate from the two
input spans. The program contains only scalar arithmetic and structural instructions. -/
def impl : Stmt Op Tst := ops% [m, n] (data, x) → (y) {
  let t ← alloc 1;
  run apply [m, n] (data, x, t, y)
}

variable {𝕜 : Type} [RCLike 𝕜]

/-- Row sums of the actual raw stored matrix and vector words, with zero padding used
only to totalize the mathematical decoder. Actual input lengths are checked by execution. -/
def row (m n : ℕ) (data x : List 𝕜) (i : ℕ) : 𝕜 :=
  ∑ j ∈ Finset.range n, data.getD (j * m + i) 0 * x.getD j 0

/-- The actual streamed word recurrence for a supplied scalar machine and a stored row. -/
def rowWord (M : Machine 𝕜) (m n : ℕ) (data x : List 𝕜) (i : ℕ) : 𝕜 :=
  ScalarProducts.sumWord M (fun j => data.getD (j * m + i) 0) (fun j => x.getD j 0) n

/-- Exact arithmetic identifies the word recurrence with the mathematical row sum. -/
theorem rowWord_exact (m n : ℕ) (data x : List 𝕜) (i : ℕ) :
    rowWord RCLikeBlas.machine m n data x i = row m n data x i :=
  ScalarProducts.sumWord_exact _ _ n

/-- The raw row sums are the finite-dimensional dense operator's output blocks. -/
theorem row_eq (m n : ℕ) (data x : List 𝕜) (i : Fin m) :
    row m n data x i = ∑ j : Fin n, StoredOperator.denseMatrix m n data i j * x.getD j 0 := by
  exact (Fin.sum_univ_eq_sum_range
    (fun j => data.getD (j * m + i) 0 * x.getD j 0) n).symm

variable {I : Interp Op Tst 𝕜} {tape : Tape 𝕜} {mem : Mem 𝕜}

/-- The streamed dense body returns all rows with one caller-owned temporary. The input
matrix and vector may overlap each other; both remain separate from output and temporary. -/
theorem writes_apply_word {M : Machine 𝕜} (hS : IsScalar M I)
    {m n : ℕ} {data x t y : ℕ × ℕ} (ds xs : List 𝕜)
    (hl : mem.Live [data, x, t, y])
    (hD : mem.store.readBlock data.1 data.2 (m * n) = some ds)
    (hX : mem.store.readBlock x.1 x.2 n = some xs)
    (hYD : Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock data.1 data.2 (m * n)))
    (hYX : Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock x.1 x.2 n))
    (hTD : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock data.1 data.2 (m * n)))
    (hTX : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock x.1 x.2 n))
    (hTY : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock y.1 y.2 m))
    (ht : t.2 + 1 ≤ mem.store.len t.1) (hy : y.2 + m ≤ mem.store.len y.1) :
    Writes .total I tape apply (Env.frame [m, n] [data, x, t, y])
      (Store.inBlock y.1 y.2 m ⊔ Store.inBlock t.1 t.2 1)
      (fun mem' => mem'.pos = mem.pos ∧ mem'.store.readBlock y.1 y.2 m =
        some ((List.range m).map (rowWord M m n ds xs))) mem := by
  refine (writes_fill_scratch rfl (Store.inBlock t.1 t.2 1) hTY
    (rowWord M m n ds xs) (fun _ => mem.pos) rfl ?_).mono le_rfl ?_
  · intro i hi mem' hf _ hp
    have hWhole : mem.store.EqOff
        (Store.inBlock y.1 y.2 m ⊔ Store.inBlock t.1 t.2 1) mem'.store :=
      hf.mono (sup_le_sup (Fp.inBlock_le_inBlock le_rfl (by omega)) le_rfl)
    have hD' := hWhole.keep (Store.readsOnly_readBlock _ _ _ ds)
      (Fp.disj_sup_left.mpr ⟨hYD, hTD⟩) hD
    have hX' := hWhole.keep (Store.readsOnly_readBlock _ _ _ xs)
      (Fp.disj_sup_left.mpr ⟨hYX, hTX⟩) hX
    have hRow : Store.inBlock y.1 (y.2 + i) 1 ≤ Store.inBlock y.1 y.2 m :=
      Fp.inBlock_le_inBlock (by omega) (by omega)
    have hWrite : Store.inBlock t.1 t.2 1 ⊔ Store.inBlock y.1 (y.2 + i) 1 ≤
        Store.inBlock y.1 y.2 m ⊔ Store.inBlock t.1 t.2 1 :=
      sup_le le_sup_right (hRow.trans le_sup_left)
    have hDataIndex (j : ℕ) (hj : j < n) : j * m + i < m * n := by
      simpa only [Nat.mul_comm m n] using Idx.add_lt_mul hj hi
    have hDataCell (j : ℕ) (hj : j < n) :
        Store.inBlock data.1 (data.2 + i + m * j) 1 ≤
          Store.inBlock data.1 data.2 (m * n) := by
      have hidx := hDataIndex j hj
      rw [Nat.mul_comm m j]
      exact Fp.inBlock_le_inBlock (by omega) (by omega)
    have hXCell (j : ℕ) (hj : j < n) :
        Store.inBlock x.1 (x.2 + 1 * j) 1 ≤ Store.inBlock x.1 x.2 n :=
      Fp.inBlock_le_inBlock (by omega) (by omega)
    have hl' : mem'.Live [(data.1, data.2 + i), x, t, (y.1, y.2 + i)] := by
      simpa only [Mem.live_cons, Mem.live_nil] using hl.congr hWhole.length_eq
    refine ((ScalarProducts.writes_sum_word hS (n := n) (sx := m) (sy := 1)
      (x := (data.1, data.2 + i)) (y := x) (t := t) (out := (y.1, y.2 + i))
      (fun j => ds.getD (j * m + i) 0) (fun j => xs.getD j 0) hl' ?_ ?_ ?_ ?_
      (hTY.mono le_rfl hRow) (by simpa only [hWhole.len_eq] using ht)
      (by change y.2 + i + 1 ≤ mem'.store.len y.1
          rw [hWhole.len_eq]; omega)).in_frame rfl rfl hl').mono
        (by rw [sup_comm]) ?_
    · intro j hj
      have hget := Store.get_of_readBlock hD' (hDataIndex j hj) (0 : 𝕜)
      apply Store.readBlock_one_of_get
      simpa only [Nat.add_assoc, Nat.add_comm i, Nat.mul_comm m] using hget
    · intro j hj
      have hget := Store.get_of_readBlock hX' hj (0 : 𝕜)
      apply Store.readBlock_one_of_get
      simpa only [one_mul] using hget
    · exact fun j hj => (Fp.disj_sup_left.mpr ⟨hYD, hTD⟩).mono hWrite (hDataCell j hj)
    · exact fun j hj => (Fp.disj_sup_left.mpr ⟨hYX, hTX⟩).mono hWrite (hXCell j hj)
    · intro mem'' _ h
      refine ⟨?_, h.1.trans hp⟩
      simpa only [Nat.add_zero, List.getD_cons_zero, rowWord] using
        Store.get_of_readBlock h.2 (j := 0) (by decide) (0 : 𝕜)
  · intro mem' _ h
    exact ⟨h.2, Store.holdsVec_iff_readBlock.mp h.1⟩

/-- The streamed dense body returns all rows with one caller-owned temporary. The input
matrix and vector may overlap each other; both remain separate from output and temporary. -/
theorem writes_apply (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {m n : ℕ} {data x t y : ℕ × ℕ} (ds xs : List 𝕜)
    (hl : mem.Live [data, x, t, y])
    (hD : mem.store.readBlock data.1 data.2 (m * n) = some ds)
    (hX : mem.store.readBlock x.1 x.2 n = some xs)
    (hYD : Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock data.1 data.2 (m * n)))
    (hYX : Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock x.1 x.2 n))
    (hTD : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock data.1 data.2 (m * n)))
    (hTX : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock x.1 x.2 n))
    (hTY : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock y.1 y.2 m))
    (ht : t.2 + 1 ≤ mem.store.len t.1) (hy : y.2 + m ≤ mem.store.len y.1) :
    Writes .total I tape apply (Env.frame [m, n] [data, x, t, y])
      (Store.inBlock y.1 y.2 m ⊔ Store.inBlock t.1 t.2 1)
      (fun mem' => mem'.pos = mem.pos ∧ mem'.store.readBlock y.1 y.2 m =
        some ((List.range m).map (row m n ds xs))) mem  := by
  have hr : rowWord RCLikeBlas.machine m n ds xs = row m n ds xs :=
    funext (rowWord_exact m n ds xs)
  simpa only [hr] using
    (writes_apply_word (tape := tape) (M := RCLikeBlas.machine) hS ds xs hl hD hX
      hYD hYX hTD hTX hTY ht hy)

/-- The allocated dense implementation returns the actual word matrix-vector
product and frees its single scalar temporary. The tree is the body of two table entries: the
routine `implRoutine`, whose judgment is the exact specialisation, and the context-forwarded
`ContextDense.impl`, which runs the same tree with the matrix as forwarded context; this lemma,
for any machine, is their common proof. -/
theorem writes_impl_word {M : Machine 𝕜} (hS : IsScalar M I)
    {m n : ℕ} {data x y : ℕ × ℕ} (ds xs : List 𝕜)
    (hl : mem.Live [data, x, y])
    (hD : mem.store.readBlock data.1 data.2 (m * n) = some ds)
    (hX : mem.store.readBlock x.1 x.2 n = some xs)
    (hYD : Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock data.1 data.2 (m * n)))
    (hYX : Fp.Disj (Store.inBlock y.1 y.2 m) (Store.inBlock x.1 x.2 n))
    (hy : y.2 + m ≤ mem.store.len y.1) :
    Writes .total I tape impl (Env.frame [m, n] [data, x, y])
      (Store.inBlock y.1 y.2 m)
      (fun mem' => mem'.pos = mem.pos ∧ mem'.store.readBlock y.1 y.2 m =
        some ((List.range m).map (rowWord M m n ds xs))) mem := by
  have hdL := hl data (by simp)
  have hxL := hl x (by simp)
  have hyL := hl y (by simp)
  refine writes_allocs_readBlock (lens := [.const 1]) (ns := [1]) rfl hyL
    fun s hs hlen hBelow => ?_
  have ht : s.len mem.store.length = 1 := by simpa using hlen 0 (by simp)
  have hD₀ := (hBelow.readBlock hdL data.2 (m * n)).trans hD
  have hX₀ := (hBelow.readBlock hxL x.2 n).trans hX
  have hy₀ : y.2 + m ≤ s.len y.1 := by rw [(hBelow y.1 hyL).1]; exact hy
  refine (writes_frame rfl rfl (by simp [Mem.Live, hs]; omega)
    (writes_apply_word hS (data := data) (x := x) (t := (mem.store.length, 0)) (y := y)
      ds xs (by simp [Mem.Live, hs]; omega) hD₀ hX₀ hYD hYX
      (Fp.disj_inBlock_of_ne (by dsimp only; omega))
      (Fp.disj_inBlock_of_ne (by dsimp only; omega))
      (Fp.disj_inBlock_of_ne (by dsimp only; omega))
      (by simpa using ht.ge) hy₀)).mono ?_ (fun _ _ h => h)
  exact sup_le le_sup_left (Fp.inBlock_le_sup_above (by dsimp only; omega))

/-- The row-wise raw output list is exactly the declared local dense primitive result. -/
theorem map_row_eq (m n : ℕ) (data x : List 𝕜) :
    (List.range m).map (row m n data x) =
      List.ofFn (fun i : Fin m =>
        ∑ j : Fin n, StoredOperator.denseMatrix m n data i j * x.getD j 0) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
    row_eq m n data x ⟨i, by simpa using hi⟩

/-- The scalar dense leaf as a routine: `[m, n] (data : read m * n, x : read n) → (y : write m)`,
separated by block. -/
def implRoutine : Routine Op Tst :=
  StoredOperator.matvecRoutine (fun m n => m * n) impl

/-- The scalar dense leaf meets the specification read off the exact stored-operator relation.
No matrix-vector primitive appears in its tree. -/
theorem implRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (implRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (StoredOperator.denseFunctions (K := 𝕜) .matvec).rel fun _ => True) := by
  routine_intro [m, n] (data, x, y) reads (ds, xs)
  obtain ⟨hYD, hYX⟩ := StoredOperator.matvecRoutine_disj hsep
  have hr : rowWord RCLikeBlas.machine m n ds xs = row m n ds xs :=
    funext (rowWord_exact m n ds xs)
  refine (writes_impl_word (tape := τ) (M := RCLikeBlas.machine) hS ds xs hlive hds hxs hYD hYX
    hroom).mono le_sup_left fun μ' _ h => ⟨h.1, [(List.range m).map (row m n ds xs)], ?_, ?_⟩
  · rw [← hr]
    exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩
  · change _ = some _
    simp only [StoredOperator.denseFunctions, StoredOperator.functions]
    rw [map_row_eq]
    rfl

/-- The scalar dense leaf meets the exact stored-operator contract under its explicit
output-separation admission: a consequence of the judgment of its routine. No matrix-vector
primitive appears in the implementing tree. -/
theorem satisfies_impl (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (implRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((StoredOperator.denseFunctions .matvec).rel.spec
        (StoredOperator.OutApart (fun m n => m * n))) :=
  (implRoutine_meets hS).satisfies_ofRel
    (StoredOperator.matvecRoutine_implements _ StoredOperator.denseMatrix _)
    fun _ _ _ _ => trivial

/-- Dense application reserves exactly one extra scalar cell when lower primitives require
no additional workspace. The payload does not grow with the matrix dimensions. -/
theorem stmtPeak_impl_zero (m n : ℕ) (offs : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (impl (Op := Op) (Tst := Tst))
      ([m, n] ++ offs) = 1 := by
  simp only [impl, stmtPeak_alloc]
  rw [stmtPeak_zero_of_allocationFree (by rfl)]
  rfl

/-- Each row initializes zero, then executes one multiplication and addition per entry.
Canonical execution additionally charges all indexing, addressing, frames and control. -/
theorem stmtCost_impl (m n dataOff xOff yOff : ℕ) :
    stmtCost (impl (Op := Op) (Tst := Tst)) [m, n, dataOff, xOff, yOff] =
      m • (Count.one (Has.inj (ScalarOp.lit 0)) [] +
        n • (Count.one (Has.inj ScalarOp.mul) [] + Count.one (Has.inj ScalarOp.add) [])) := by
  simp [impl, apply, ScalarProducts.sum, ScalarProducts.step, stmtCost, useCost,
    IExp.evalList, IExp.eval]

section Linking

variable [Has StoredOperatorOp Op]

/-- Replace stored matrix-vector calls by the fixed scalar implementation, preserving all
other operation names. The same table applies at every shape and raw input. -/
def table : Table Op Op Tst := fun o =>
  match Has.proj (G := StoredOperatorOp) o with
  | some .matvec => .inl implRoutine.impl
  | none => .inr o

/-- The linked interpretation realizes the declared local dense primitive by actual
streamed scalar instructions, with no opaque matrix-vector call in its implementation. -/
theorem isExact_link (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    StoredOperator.IsExact (fun m n => m * n) StoredOperator.denseMatrix (I.link table) :=
  Interp.link_satisfies (E := implRoutine.impl) (by simp [table]) (satisfies_impl hS)

end Linking

end NLAlib.Ops.StoredDense
