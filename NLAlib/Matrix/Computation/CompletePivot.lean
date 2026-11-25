/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Fin.Embedding
public import NLAlib.Matrix.Computation.PivotScan
public import NLAlib.Computation.IndexBinder

/-!
# Complete pivot selection

The active square is scanned column by column. Each column suffix is contiguous in packed
column-major storage, so no transpose or packed copy is needed. Strict global improvement
retains the earliest maximum in column-major order, including the first active entry when
the active square is zero.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.Computation.completePivotChoice`: exact stored row and column selection.

## Main results

* `NLAlib.Computation.executionComposable_completePivotChoice`: scoped composition.
* `NLAlib.Computation.IsRelErrSem.exec_completePivotChoice`: stable maximal choice and exact writes.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Update a magnitude incumbent and both exact coordinates on strict improvement. -/
def completePivotUpdate {P ι VB VI : Type} (tag : P)
    (scratch : VB) (rowIndex colIndex : Cell VB VI) (row col : IExp VI) :
    Builder P ι VB VI Unit :=
  ifThenElse tag .lt ⟨scratch, 0⟩ ⟨scratch, 2⟩ (do
    ins (.copy tag ⟨scratch, 0⟩ ⟨scratch, 2⟩)
    ins (.litIdx tag rowIndex row)
    ins (.litIdx tag colIndex col)) (pure ())

/-- Scan one active column suffix and compare its first maximum to the global incumbent. -/
def completePivotColumn {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (A : VB) (off : IExp VI) (scratch : VB) (rowIndex colIndex : Cell VB VI)
    (col : IExp VI) : Builder P ι VB VI Unit := do
  argmaxAbs tag (n - k) A (off + k + n * col) ⟨scratch, 3⟩
  bindIdx tag ⟨scratch, 3⟩ (n - k) fun rel => do
    copyAbs tag ⟨scratch, 2⟩ ⟨A, off + (k + .var rel) + n * col⟩ ⟨scratch, 1⟩
    completePivotUpdate tag scratch rowIndex colIndex (k + .var rel) col

/-- Select the first entry of largest absolute decoded value in the nonempty active square
with row and column indices at least `k`. Each column suffix is scanned directly. Exact
absolute row and column literals are stored separately; the matrix is retained and four
workspace cells are scoped. Ties select the earliest column, then earliest row. -/
def completePivotChoice {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (A : VB) (off : IExp VI) (rowIndex colIndex : Cell VB VI) :
    Builder P ι VB VI Unit := scope do
  let scratch ← alloc tag 4
  ins (.lit tag ⟨scratch, 1⟩ 0)
  copyAbs tag ⟨scratch, 0⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩
  ins (.litIdx tag rowIndex k)
  ins (.litIdx tag colIndex k)
  forRange (n - k) fun j =>
    completePivotColumn tag n k A off scratch rowIndex colIndex (k + IExp.var j)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The complete pivot selector releases its workspace before any following builder. -/
theorem executionComposable_completePivotChoice (I : Interp P ι K C) (tag : P)
    (n k : IExp ℕ) (A : ℕ) (off : IExp ℕ) (rowIndex colIndex : Cell ℕ ℕ) :
    ExecutionComposable I (completePivotChoice tag n k A off rowIndex colIndex) :=
  executionComposable_single I (fun _ => rfl)

namespace CompletePivot

/-- Scan an active column suffix without packing. The selected relative index is stored
exactly, and the first maximal magnitude is retained under ties. This shared execution
lemma is also used by the alternating rook search. -/
theorem exec_columnScan {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k col : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (A : ℕ) (off : IExp ℕ) (index : Cell ℕ ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (htail : n.eval - k.eval ≤ n.eval)
    (hcol : col.eval < n.eval) (hM : HoldsDecoded st.store dec tag A off.eval M)
    (hw : Writable st.store tag index.buf index.idx.eval 1) (hAI : A ≠ index.buf) :
    ∃ (out : St P K C) (w : K) (r : Fin (n.eval - k.eval)),
      exec I (argmaxAbs tag (n - k) A (off + k + n * col) index).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[w] = some out.store ∧
      dec tag w = r.val ∧
      (∀ i : Fin (n.eval - k.eval),
        |M ((Fin.natAdd_castLEEmb (htail)) i) ⟨col.eval, hcol⟩| ≤
          |M ((Fin.natAdd_castLEEmb (htail)) r) ⟨col.eval, hcol⟩|) ∧
      (∀ i : Fin (n.eval - k.eval), i < r →
        |M ((Fin.natAdd_castLEEmb (htail)) i) ⟨col.eval, hcol⟩| <
          |M ((Fin.natAdd_castLEEmb (htail)) r) ⟨col.eval, hcol⟩|) := by
  let x : Fin (n.eval - k.eval) → ℝ := fun i =>
    M ((Fin.natAdd_castLEEmb (htail)) i) ⟨col.eval, hcol⟩
  have hin : ReadsDecoded st.store dec tag A (off + k + n * col).eval x := by
    intro i
    simpa only [x, Fin.val_natAdd_castLEEmb_sub, IExp.eval_add, IExp.eval_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
        hM ((Fin.natAdd_castLEEmb (htail)) i) ⟨col.eval, hcol⟩
  obtain ⟨out, w, r, hr, hs, hd, hmax, hfirst⟩ := h.exec_argmaxAbs I hi.intLit
    (Nat.sub_le _ _) (Nat.sub_pos_of_lt hk) tag st x A (off + k + n * col) index hin hw hAI
  refine ⟨out, w, r, ?_, hs, hd, hmax, hfirst⟩
  exact (exec_eq_of_normIdx_eq I
    (s := (argmaxAbs tag (n - k) A (off + k + n * col) index).run)
    (s' := (argmaxAbs tag (.const (n.eval - k.eval)) A (off + k + n * col) index).run)
    rfl st).trans hr

private theorem exec_update {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    {N : ℕ} (hi : IsIndexExactSem dec N I.sem) (tag : P) (st : St P K C)
    (scratch : ℕ) (rowIndex colIndex : Cell ℕ ℕ) (row col : IExp ℕ)
    (hrow : row.eval ≤ N) (hcol : col.eval ≤ N)
    (b v ri ci : K) (hb : st.store.read tag scratch 0 = some b)
    (hv : st.store.read tag scratch 2 = some v)
    (hr : st.store.read tag rowIndex.buf rowIndex.idx.eval = some ri)
    (hc : st.store.read tag colIndex.buf colIndex.idx.eval = some ci)
    (hsr : scratch ≠ rowIndex.buf) (hsc : scratch ≠ colIndex.buf)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval) :
    ∃ (out : St P K C) (b' r' c' : K),
      exec I (completePivotUpdate tag scratch rowIndex colIndex row col).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag scratch 0 = some b' ∧
      out.store.read tag rowIndex.buf rowIndex.idx.eval = some r' ∧
      out.store.read tag colIndex.buf colIndex.idx.eval = some c' ∧
      dec tag b' = max (dec tag b) (dec tag v) ∧
      dec tag r' = (if dec tag b < dec tag v then (row.eval : ℝ) else dec tag ri) ∧
      dec tag c' = (if dec tag b < dec tag v then (col.eval : ℝ) else dec tag ci) ∧
      ∀ q buf j, (buf ≠ scratch ∨ j ≠ 0) →
        (buf ≠ rowIndex.buf ∨ j ≠ rowIndex.idx.eval) →
        (buf ≠ colIndex.buf ∨ j ≠ colIndex.idx.eval) →
        out.store.read q buf j = st.store.read q buf j := by
  let tested : St P K C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  have ht : cmpStep I tag .lt ⟨scratch, 0⟩ ⟨scratch, 2⟩ st =
      some (decide (dec tag b < dec tag v), tested) := by
    simp only [cmpStep, IExp.eval, hb, hv, Option.bind_some, h.cmp_lt]
    rfl
  have hrun : (completePivotUpdate tag scratch rowIndex colIndex row col :
      Builder P ι ℕ ℕ Unit).run =
      .seq (.ite tag .lt ⟨scratch, 0⟩ ⟨scratch, 2⟩
        (.seq (.instr (.copy tag ⟨scratch, 0⟩ ⟨scratch, 2⟩))
          (.seq (.instr (.litIdx tag rowIndex row))
            (.seq (.instr (.litIdx tag colIndex col)) .skip))) .skip) .skip := rfl
  simp only [hrun, exec_seq_skip, exec_ite, ht, Option.bind_some]
  by_cases hlt : dec tag b < dec tag v
  · obtain ⟨rw, hrw, hdr⟩ := hi.intLit tag row.eval hrow
    obtain ⟨cw, hcw, hdc⟩ := hi.intLit tag col.eval hcol
    obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_read_eq_some (v := v) hb
    have hr₁ := (Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hsr.symm)).trans hr
    obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_read_eq_some (v := rw) hr₁
    have hc₂ : s₂.read tag colIndex.buf colIndex.idx.eval = some ci := by
      rw [Store.read_of_write_eq_some_of_ne hs₂ (hrc.imp Ne.symm Ne.symm),
        Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hsc.symm)]
      exact hc
    obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_read_eq_some (v := cw) hc₂
    let out : St P K C := { tested with store := s₃, cnt :=
      ((tested.cnt + I.charge (.copy tag)) + I.charge (.lit tag)) + I.charge (.lit tag) }
    refine ⟨out, v, rw, cw, ?_, (Store.shape_of_write_eq_some hs₃).trans
      ((Store.shape_of_write_eq_some hs₂).trans (Store.shape_of_write_eq_some hs₁)),
      ?_, ?_, Store.read_of_write_eq_some hs₃, (max_eq_right hlt.le).symm,
      by simpa only [hlt, ↓reduceIte] using hdr,
      by simpa only [hlt, ↓reduceIte] using hdc, ?_⟩
    · simp only [hlt, decide_true, ↓reduceIte]
      rw [exec_seq_instr_copy I (st := tested) hv hs₁,
        exec_seq_instr_litIdx I hrw hs₂, exec_seq_instr_litIdx I hcw hs₃, exec_skip]
    · rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hsc),
        Store.read_of_write_eq_some_of_ne hs₂ (Or.inl hsr)]
      exact Store.read_of_write_eq_some hs₁
    · rw [Store.read_of_write_eq_some_of_ne hs₃ hrc]
      exact Store.read_of_write_eq_some hs₂
    · intro q buf j hb' hr' hc'
      rw [Store.read_of_write_eq_some_of_ne hs₃ hc',
        Store.read_of_write_eq_some_of_ne hs₂ hr',
        Store.read_of_write_eq_some_of_ne hs₁ hb']
  · refine ⟨tested, b, ri, ci, ?_, rfl, hb, hr, hc,
      (max_eq_left (le_of_not_gt hlt)).symm, by simp only [hlt, ↓reduceIte],
      by simp only [hlt, ↓reduceIte], fun _ _ _ _ _ _ => rfl⟩
    simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact exec_skip I tested

private theorem exec_candidate {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P) (st : St P K C)
    (A scratch : ℕ) (off row col : IExp ℕ) (rowIndex colIndex : Cell ℕ ℕ)
    (hrow : row.eval ≤ n.eval) (hcol : col.eval ≤ n.eval)
    (b v z ri ci : K) (hb : st.store.read tag scratch 0 = some b)
    (hv : st.store.read tag A (off + row + n * col).eval = some v)
    (hz : st.store.read tag scratch 1 = some z) (hdz : dec tag z = 0)
    (hr : st.store.read tag rowIndex.buf rowIndex.idx.eval = some ri)
    (hc : st.store.read tag colIndex.buf colIndex.idx.eval = some ci)
    (hsh : st.store.shape[scratch]? = some (tag, 4))
    (hsr : scratch ≠ rowIndex.buf) (hsc : scratch ≠ colIndex.buf)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval) :
    ∃ (out : St P K C) (b' r' c' : K),
      exec I (do
        copyAbs tag ⟨scratch, 2⟩ ⟨A, off + row + n * col⟩ ⟨scratch, 1⟩
        completePivotUpdate tag scratch rowIndex colIndex row col).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag scratch 0 = some b' ∧
      out.store.read tag rowIndex.buf rowIndex.idx.eval = some r' ∧
      out.store.read tag colIndex.buf colIndex.idx.eval = some c' ∧
      out.store.read tag scratch 1 = some z ∧
      dec tag b' = max (dec tag b) |dec tag v| ∧
      dec tag r' = (if dec tag b < |dec tag v| then (row.eval : ℝ) else dec tag ri) ∧
      dec tag c' = (if dec tag b < |dec tag v| then (col.eval : ℝ) else dec tag ci) ∧
      ∀ q buf j, buf ≠ scratch →
        (buf ≠ rowIndex.buf ∨ j ≠ rowIndex.idx.eval) →
        (buf ≠ colIndex.buf ∨ j ≠ colIndex.idx.eval) →
        out.store.read q buf j = st.store.read q buf j := by
  obtain ⟨mid, cw, he, hw, hd⟩ := h.exec_copyAbs I tag st ⟨scratch, 2⟩
    ⟨A, off + row + n * col⟩ ⟨scratch, 1⟩ v z hv hz hdz
    ⟨4, hsh, by norm_num [IExp.eval]⟩
  have hb₁ : mid.store.read tag scratch 0 = some b := by
    rw [Store.read_of_write_eq_some_of_ne hw (Or.inr (by omega : 0 ≠ 2))]; exact hb
  have hr₁ : mid.store.read tag rowIndex.buf rowIndex.idx.eval = some ri := by
    rw [Store.read_of_write_eq_some_of_ne hw (Or.inl hsr.symm)]; exact hr
  have hc₁ : mid.store.read tag colIndex.buf colIndex.idx.eval = some ci := by
    rw [Store.read_of_write_eq_some_of_ne hw (Or.inl hsc.symm)]; exact hc
  obtain ⟨out, b', r', c', he', hshape, hb', hr', hc', hdb', hdr', hdc', hf⟩ :=
    exec_update I h hi tag mid scratch rowIndex colIndex row col hrow hcol b cw ri ci
      hb₁ (Store.read_of_write_eq_some hw) hr₁ hc₁ hsr hsc hrc
  refine ⟨out, b', r', c', ?_, hshape.trans (Store.shape_of_write_eq_some hw),
    hb', hr', hc', ?_, by simpa only [hd] using hdb',
    by simpa only [hd] using hdr', by simpa only [hd] using hdc', ?_⟩
  · rw [exec_run_bind I (b := copyAbs tag ⟨scratch, 2⟩
      ⟨A, off + row + n * col⟩ ⟨scratch, 1⟩) (fun _ => rfl), he, Option.bind_some]
    exact he'
  · rw [hf tag scratch 1 (Or.inr (by omega : 1 ≠ 0)) (Or.inl hsr) (Or.inl hsc),
      Store.read_of_write_eq_some_of_ne hw (Or.inr (by omega : 1 ≠ 2))]
    exact hz
  · intro q buf j hbs hbr hbc
    rw [hf q buf j (Or.inl hbs) hbr hbc,
      Store.read_of_write_eq_some_of_ne hw (Or.inl hbs)]

private theorem exec_column {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k col : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (A scratch : ℕ) (off : IExp ℕ) (rowIndex colIndex : Cell ℕ ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (htail : n.eval - k.eval ≤ n.eval)
    (hcol : col.eval < n.eval) (hM : HoldsDecoded st.store dec tag A off.eval M)
    (b z ri ci : K) (hb : st.store.read tag scratch 0 = some b)
    (hz : st.store.read tag scratch 1 = some z) (hdz : dec tag z = 0)
    (hr : st.store.read tag rowIndex.buf rowIndex.idx.eval = some ri)
    (hc : st.store.read tag colIndex.buf colIndex.idx.eval = some ci)
    (hsh : st.store.shape[scratch]? = some (tag, 4))
    (hAS : A ≠ scratch) (hsr : scratch ≠ rowIndex.buf) (hsc : scratch ≠ colIndex.buf)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval) :
    ∃ (out : St P K C) (r : Fin (n.eval - k.eval)) (b' r' c' : K),
      exec I (completePivotColumn tag n k A off scratch rowIndex colIndex col).run st =
        some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag scratch 0 = some b' ∧
      out.store.read tag rowIndex.buf rowIndex.idx.eval = some r' ∧
      out.store.read tag colIndex.buf colIndex.idx.eval = some c' ∧
      out.store.read tag scratch 1 = some z ∧
      dec tag b' = max (dec tag b)
        |M ((Fin.natAdd_castLEEmb (htail)) r) ⟨col.eval, hcol⟩| ∧
      dec tag r' = (if dec tag b <
        |M ((Fin.natAdd_castLEEmb (htail)) r) ⟨col.eval, hcol⟩|
        then ((k.eval + r.val : ℕ) : ℝ) else dec tag ri) ∧
      dec tag c' = (if dec tag b <
        |M ((Fin.natAdd_castLEEmb (htail)) r) ⟨col.eval, hcol⟩|
        then (col.eval : ℝ) else dec tag ci) ∧
      (∀ i : Fin (n.eval - k.eval),
        |M ((Fin.natAdd_castLEEmb (htail)) i) ⟨col.eval, hcol⟩| ≤
          |M ((Fin.natAdd_castLEEmb (htail)) r) ⟨col.eval, hcol⟩|) ∧
      (∀ i : Fin (n.eval - k.eval), i < r →
        |M ((Fin.natAdd_castLEEmb (htail)) i) ⟨col.eval, hcol⟩| <
          |M ((Fin.natAdd_castLEEmb (htail)) r) ⟨col.eval, hcol⟩|) ∧
      ∀ q buf j, buf ≠ scratch →
        (buf ≠ rowIndex.buf ∨ j ≠ rowIndex.idx.eval) →
        (buf ≠ colIndex.buf ∨ j ≠ colIndex.idx.eval) →
        out.store.read q buf j = st.store.read q buf j := by
  obtain ⟨mid, w, r, he, hw, hd, hmax, hfirst⟩ := exec_columnScan I h n k col hi tag st
    A off ⟨scratch, 3⟩ M hk htail hcol hM (fun j hj => ⟨4, hsh, by simp [IExp.eval]; omega⟩) hAS
  have hto : I.sem.toNat tag w = some r.val := by rw [hi.toNat tag w, hd]; simp
  let ready : St P K C := { mid with cnt := mid.cnt + I.charge (.toNat tag) }
  obtain ⟨v, hv, hdv⟩ := hM ((Fin.natAdd_castLEEmb (htail)) r) ⟨col.eval, hcol⟩
  have hv' : ready.store.read tag A (off + (k + .var r.val) + n * col).eval = some v := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hAS)]
    simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var, Fin.val_natAdd_castLEEmb_sub,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv
  have hb' : ready.store.read tag scratch 0 = some b := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inr (Or.inl (by omega : 0 < 3)))];
    exact hb
  have hz' : ready.store.read tag scratch 1 = some z := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inr (Or.inl (by omega : 1 < 3)))];
    exact hz
  have hr' : ready.store.read tag rowIndex.buf rowIndex.idx.eval = some ri := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hsr.symm)]; exact hr
  have hc' : ready.store.read tag colIndex.buf colIndex.idx.eval = some ci := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hsc.symm)]; exact hc
  obtain ⟨out, bw, rw, cw, he', hshape, hbw, hrw, hcw, hzw, hdb, hdr, hdc, hf⟩ :=
    exec_candidate I h n hi tag ready A scratch off (k + .var r.val) col rowIndex colIndex
      (by have := r.isLt; simp only [IExp.eval_add, IExp.eval_var]; omega) hcol.le
      b v z ri ci hb' hv' hz' hdz hr' hc'
      ((Store.shape_of_writeBlock_eq_some hw).symm ▸ hsh) hsr hsc hrc
  refine ⟨out, r, bw, rw, cw, ?_, hshape.trans (Store.shape_of_writeBlock_eq_some hw),
    hbw, hrw, hcw, hzw, by simpa only [hdv] using hdb,
    by simpa only [hdv, IExp.eval_add, IExp.eval_var] using hdr,
    by simpa only [hdv] using hdc, hmax, hfirst, ?_⟩
  · unfold completePivotColumn
    rw [exec_run_bind I (b := argmaxAbs tag (n - k) A (off + k + n * col)
      ⟨scratch, 3⟩) (fun _ => rfl), he, Option.bind_some]
    change exec I (.seq (.bindIdx tag ⟨scratch, 3⟩ (n - k) _) .skip) mid = _
    rw [exec_seq_skip, exec_bindIdx_of_read I
      (by simpa using Store.read_of_writeBlock_eq_some_of_lt hw (by simp : 0 < #[w].size))
      hto (by change r.val ≤ n.eval - k.eval; omega)]
    exact he'
  · intro q buf j hbs hbr hbc
    rw [hf q buf j hbs hbr hbc,
      Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hbs)]

private theorem column_choice {N k t : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (r c i j : Fin N) (hj : j.val = k + t)
    (hdom : ∀ a b : Fin N, k ≤ a.val → k ≤ b.val → b.val < k + t →
      |M a b| ≤ |M r c|)
    (hfirst : ∀ a b : Fin N, k ≤ a.val → k ≤ b.val →
      b < c ∨ (b = c ∧ a < r) → |M a b| < |M r c|)
    (hcol : ∀ a : Fin N, k ≤ a.val → |M a j| ≤ |M i j|)
    (hcolfirst : ∀ a : Fin N, k ≤ a.val → a < i → |M a j| < |M i j|) :
    let chosen := if |M r c| < |M i j| then (i, j) else (r, c)
    (∀ a b : Fin N, k ≤ a.val → k ≤ b.val → b.val < k + (t + 1) →
      |M a b| ≤ |M chosen.1 chosen.2|) ∧
    (∀ a b : Fin N, k ≤ a.val → k ≤ b.val →
      b < chosen.2 ∨ (b = chosen.2 ∧ a < chosen.1) →
      |M a b| < |M chosen.1 chosen.2|) := by
  dsimp only
  split_ifs with hlt
  · constructor
    · intro a b ha hb hbt
      by_cases hbj : b = j
      · subst b; exact hcol a ha
      · exact (hdom a b ha hb (by have := b.isLt; omega)).trans hlt.le
    · intro a b ha hb hbefore
      rcases hbefore with hbj | ⟨rfl, hai⟩
      · exact (hdom a b ha hb (by simpa only [Fin.lt_def, hj] using hbj)).trans_lt hlt
      · exact hcolfirst a ha hai
  · constructor
    · intro a b ha hb hbt
      by_cases hbj : b = j
      · subst b; exact (hcol a ha).trans (le_of_not_gt hlt)
      · exact hdom a b ha hb (by have := b.isLt; omega)
    · exact hfirst

private structure ScanState {N : ℕ} (dec : P → K → ℝ) (tag : P)
    (M : Matrix (Fin N) (Fin N) ℝ) (k scratch : ℕ) (rowIndex colIndex : Cell ℕ ℕ)
    (z : K) (initial : Store P K) (t : ℕ) (s : Store P K) : Prop where
  shape : s.shape = initial.shape
  frame : ∀ q buf j, buf ≠ scratch →
    (buf ≠ rowIndex.buf ∨ j ≠ rowIndex.idx.eval) →
    (buf ≠ colIndex.buf ∨ j ≠ colIndex.idx.eval) →
    s.read q buf j = initial.read q buf j
  zero : s.read tag scratch 1 = some z
  values : ∃ (b rw cw : K) (r c : Fin N),
    s.read tag scratch 0 = some b ∧
    s.read tag rowIndex.buf rowIndex.idx.eval = some rw ∧
    s.read tag colIndex.buf colIndex.idx.eval = some cw ∧
    dec tag b = |M r c| ∧ dec tag rw = r.val ∧ dec tag cw = c.val ∧
    k ≤ r.val ∧ k ≤ c.val ∧
    (∀ a b : Fin N, k ≤ a.val → k ≤ b.val → b.val < k + t → |M a b| ≤ |M r c|) ∧
    (∀ a b : Fin N, k ≤ a.val → k ≤ b.val →
      b < c ∨ (b = c ∧ a < r) → |M a b| < |M r c|)

private theorem exec_scanColumn {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (initial : Store P K) (A scratch : ℕ) (off : IExp ℕ)
    (rowIndex colIndex : Cell ℕ ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : HoldsDecoded initial dec tag A off.eval M)
    (z : K) (hdz : dec tag z = 0) (hsh : initial.shape[scratch]? = some (tag, 4))
    (hAS : A ≠ scratch) (hAR : A ≠ rowIndex.buf) (hAC : A ≠ colIndex.buf)
    (hsr : scratch ≠ rowIndex.buf) (hsc : scratch ≠ colIndex.buf)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval)
    (t : ℕ) (ht : t < n.eval - k.eval) (st : St P K C)
    (hs : ScanState dec tag M k.eval scratch rowIndex colIndex z initial t st.store) :
    ∃ out, exec I (completePivotColumn tag n k A off scratch rowIndex colIndex
      (k + .var t)).run st = some out ∧
      ScanState dec tag M k.eval scratch rowIndex colIndex z initial (t + 1) out.store := by
  obtain ⟨bw, rw, cw, r, c, hb, hr, hc, hdb, hdr, hdc, hkr, hkc, hdom, hfirst⟩ := hs.values
  have hMst : HoldsDecoded st.store dec tag A off.eval M := by
    intro i j
    obtain ⟨v, hv, hd⟩ := hM i j
    exact ⟨v, (hs.frame tag A _ hAS (Or.inl hAR) (Or.inl hAC)).trans hv, hd⟩
  have hcol : (k + .var t).eval < n.eval := by simp only [IExp.eval_add, IExp.eval_var]; omega
  obtain ⟨out, rel, b', rw', cw', he, hshape, hb', hr', hc', hz', hd', hdr', hdc',
    hmax, hcolfirst, hf⟩ := exec_column I h n k (k + .var t) hi tag st A scratch off
      rowIndex colIndex M hk (Nat.sub_le _ _) hcol hMst bw z rw cw hb hs.zero hdz hr hc
      (hs.shape ▸ hsh)
      hAS hsr hsc hrc
  let i := (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) rel
  have hiVal : i.val = k.eval + rel.val :=
    Fin.val_natAdd_castLEEmb_sub k.eval (Nat.sub_le n.eval k.eval) rel
  let j : Fin n.eval := ⟨(k + .var t).eval, hcol⟩
  let selected := if |M r c| < |M i j| then (i, j) else (r, c)
  have hcolumn : ∀ a : Fin n.eval, k.eval ≤ a.val → |M a j| ≤ |M i j| := by
    intro a ha
    let relA : Fin (n.eval - k.eval) := ⟨a.val - k.eval, by have := a.isLt; omega⟩
    have heq : (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) relA = a := by
      apply Fin.ext
      rw [Fin.val_natAdd_castLEEmb_sub]
      exact Nat.add_sub_of_le ha
    simpa only [heq, i, j] using hmax relA
  have hcolumnfirst : ∀ a : Fin n.eval, k.eval ≤ a.val → a < i → |M a j| < |M i j| := by
    intro a ha hai
    let relA : Fin (n.eval - k.eval) := ⟨a.val - k.eval, by have := a.isLt; omega⟩
    have heq : (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) relA = a := by
      apply Fin.ext
      rw [Fin.val_natAdd_castLEEmb_sub]
      exact Nat.add_sub_of_le ha
    have hrel : relA < rel := by
      change a.val - k.eval < rel.val
      have hai' : a.val < k.eval + rel.val := by
        change a.val < i.val at hai
        simpa only [hiVal] using hai
      omega
    simpa only [heq, i, j] using hcolfirst relA hrel
  obtain ⟨hdom', hfirst'⟩ := column_choice M r c i j rfl hdom hfirst hcolumn hcolumnfirst
  refine ⟨out, he, hshape.trans hs.shape, ?_, hz', b', rw', cw', selected.1, selected.2,
    hb', hr', hc', ?_, ?_, ?_, ?_, ?_, hdom', hfirst'⟩
  · intro q buf a hbs hbr hbc
    exact (hf q buf a hbs hbr hbc).trans (hs.frame q buf a hbs hbr hbc)
  · rw [hd', hdb]
    dsimp only [selected]
    split_ifs with hlt
    · exact max_eq_right hlt.le
    · exact max_eq_left (le_of_not_gt hlt)
  · simpa only [hdr', hdb, hdr, selected, apply_ite, i, j, Fin.val_natAdd_castLEEmb_sub] using hdr'
  · simpa only [hdc', hdb, hdc, selected, apply_ite, i, j] using hdc'
  · dsimp only [selected]; split_ifs
    · simpa only [hiVal] using Nat.le_add_right k.eval rel.val
    · exact hkr
  · dsimp only [selected]; split_ifs
    · simp only [j, IExp.eval_add, IExp.eval_var]; omega
    · exact hkc

private theorem exec_initialize {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (A scratch : ℕ) (off : IExp ℕ) (rowIndex colIndex : Cell ℕ ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded st.store dec tag A off.eval M)
    (hsh : st.store.shape[scratch]? = some (tag, 4))
    (hwR : Writable st.store tag rowIndex.buf rowIndex.idx.eval 1)
    (hwC : Writable st.store tag colIndex.buf colIndex.idx.eval 1)
    (hAS : A ≠ scratch) (hsr : scratch ≠ rowIndex.buf) (hsc : scratch ≠ colIndex.buf)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval) :
    ∃ (out : St P K C) (z : K), exec I (do
      ins (.lit tag ⟨scratch, 1⟩ 0)
      copyAbs tag ⟨scratch, 0⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩
      ins (.litIdx tag rowIndex k)
      ins (.litIdx tag colIndex k)).run st = some out ∧
      dec tag z = 0 ∧ ScanState dec tag M k.eval scratch rowIndex colIndex z st.store 0
        out.store := by
  obtain ⟨z, hz, hdz⟩ := (h.isArithErrSem fun _ => trivial).lit_zero tag
  obtain ⟨iw, hiw, hdi⟩ := hi.intLit tag k.eval hk.le
  obtain ⟨v, hv, hdv⟩ := hM ⟨k.eval, hk⟩ ⟨k.eval, hk⟩
  obtain ⟨s₁, hs₁, -, hshape₁, hread₁, -⟩ := exec_scalar_lit I tag st
    ⟨scratch, 1⟩ 0 z hz ⟨4, hsh, by norm_num [IExp.eval]⟩
  let st₁ : St P K C := { st with store := s₁, cnt := st.cnt + I.charge (.lit tag) }
  have hv₁ : s₁.read tag A (off + k + n * k).eval = some v := by
    rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hAS)]
    simpa only [IExp.eval_add, IExp.eval_mul] using hv
  obtain ⟨st₂, bw, hr₂, hs₂, hdb⟩ := h.exec_copyAbs I tag st₁
    ⟨scratch, 0⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩ v z hv₁ hread₁ hdz
    ⟨4, hshape₁ ▸ hsh, by norm_num [IExp.eval]⟩
  have hshape₂ : st₂.store.shape = st.store.shape :=
    (Store.shape_of_write_eq_some hs₂).trans hshape₁
  obtain ⟨lenR, hlenR, hltR⟩ := hwR 0 (by omega)
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape iw
    (hshape₂ ▸ hlenR) (by simpa using hltR)
  obtain ⟨lenC, hlenC, hltC⟩ := hwC 0 (by omega)
  have hshape₃ := (Store.shape_of_write_eq_some hs₃).trans hshape₂
  obtain ⟨s₄, hs₄⟩ := Store.exists_write_eq_some_of_getElem?_shape iw
    (hshape₃ ▸ hlenC) (by simpa using hltC)
  let out : St P K C := { st₂ with store := s₄, cnt :=
    (st₂.cnt + I.charge (.lit tag)) + I.charge (.lit tag) }
  refine ⟨out, z, ?_, hdz, (Store.shape_of_write_eq_some hs₄).trans hshape₃, ?_, ?_,
    bw, iw, iw, ⟨k.eval, hk⟩, ⟨k.eval, hk⟩, ?_, ?_, Store.read_of_write_eq_some hs₄,
    by simpa only [hdv] using hdb, hdi, hdi, le_rfl, le_rfl, ?_, ?_⟩
  · change exec I (.seq (.instr (.lit tag ⟨scratch, 1⟩ 0)) _) st = some out
    rw [exec_seq_instr_lit I hz hs₁]
    change exec I (copyAbs tag ⟨scratch, 0⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩ >>=
      fun _ => do ins (.litIdx tag rowIndex k); ins (.litIdx tag colIndex k)).run st₁ = some out
    rw [exec_run_bind I (b := copyAbs tag ⟨scratch, 0⟩
      ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩) (fun _ => rfl), hr₂, Option.bind_some]
    change exec I (.seq (.instr (.litIdx tag rowIndex k))
      (.seq (.instr (.litIdx tag colIndex k)) .skip)) st₂ = some out
    rw [exec_seq_instr_litIdx I hiw hs₃, exec_seq_instr_litIdx I hiw hs₄, exec_skip]
  · intro q buf j hbs hbr hbc
    rw [Store.read_of_write_eq_some_of_ne hs₄ hbc,
      Store.read_of_write_eq_some_of_ne hs₃ hbr,
      Store.read_of_write_eq_some_of_ne hs₂ (Or.inl hbs),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hbs)]
  · rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl hsc),
      Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hsr),
      Store.read_of_write_eq_some_of_ne hs₂ (Or.inr (by omega : 1 ≠ 0))]
    exact hread₁
  · rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl hsc),
      Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hsr)]
    exact Store.read_of_write_eq_some hs₂
  · rw [Store.read_of_write_eq_some_of_ne hs₄ hrc]
    exact Store.read_of_write_eq_some hs₃
  · intro a b ha hb hbt; omega
  · intro a b ha hb hbefore
    rcases hbefore with hbefore | ⟨_, hbefore⟩
    · change b.val < k.eval at hbefore
      omega
    · change a.val < k.eval at hbefore
      omega

private theorem write_pair_of_frame (tag : P) (initial final : Store P K)
    (rowIndex colIndex : Cell ℕ ℕ) (rw cw : K)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval)
    (hshape : final.shape = initial.shape)
    (hr : final.read tag rowIndex.buf rowIndex.idx.eval = some rw)
    (hc : final.read tag colIndex.buf colIndex.idx.eval = some cw)
    (hf : ∀ q buf j, (buf ≠ rowIndex.buf ∨ j ≠ rowIndex.idx.eval) →
      (buf ≠ colIndex.buf ∨ j ≠ colIndex.idx.eval) →
      final.read q buf j = initial.read q buf j) :
    ∃ mid, initial.writeBlock tag rowIndex.buf rowIndex.idx.eval #[rw] = some mid ∧
      mid.writeBlock tag colIndex.buf colIndex.idx.eval #[cw] = some final := by
  suffices hw : initial.writeBlocks tag
      [(rowIndex.buf, rowIndex.idx.eval, 1), (colIndex.buf, colIndex.idx.eval, 1)]
      [#[rw], #[cw]] = some final by
    exact (Store.writeBlocks_pair_eq_some_iff.mp hw).2.2
  refine Store.writeBlocks_eq_some_of_read
    (.cons rfl (.cons rfl .nil)) ?_ hshape ?_ ?_
  · have hd : blockDisjoint (rowIndex.buf, rowIndex.idx.eval, 1)
        (colIndex.buf, colIndex.idx.eval, 1) = true :=
      blockDisjoint_of_ne_or_le (by
        change rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval + 1 ≤ colIndex.idx.eval ∨
          colIndex.idx.eval + 1 ≤ rowIndex.idx.eval
        omega)
    simpa [List.pairwise_cons] using hd
  · intro t x y hx hy j hj
    rcases t with _ | t
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst x; subst y
      have : j = 0 := by change j < 1 at hj; omega
      subst j
      simpa using hr
    · rcases t with _ | t
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
          at hx hy
        subst x; subst y
        have : j = 0 := by change j < 1 at hj; omega
        subst j
        simpa using hc
      · simp at hx
  · intro q buf j hj
    apply hf q buf j
    · have h := hj (rowIndex.buf, rowIndex.idx.eval, 1) (by simp)
      change buf ≠ rowIndex.buf ∨ j < rowIndex.idx.eval ∨ rowIndex.idx.eval + 1 ≤ j at h
      omega
    · have h := hj (colIndex.buf, colIndex.idx.eval, 1) (by simp)
      change buf ≠ colIndex.buf ∨ j < colIndex.idx.eval ∨ colIndex.idx.eval + 1 ≤ j at h
      omega

private theorem scan_pop_write {N k : ℕ} {dec : P → K → ℝ} (tag : P)
    (initial final : Store P K) (M : Matrix (Fin N) (Fin N) ℝ)
    (rowIndex colIndex : Cell ℕ ℕ) (z : K)
    (hwR : Writable initial tag rowIndex.buf rowIndex.idx.eval 1)
    (hwC : Writable initial tag colIndex.buf colIndex.idx.eval 1)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval)
    (hs : ScanState dec tag M k initial.size rowIndex colIndex z
      (initial.push (tag, Array.replicate 4 none)) (N - k) final) :
    ∃ (rw cw : K) (r c : Fin N) (mid : Store P K),
      initial.writeBlock tag rowIndex.buf rowIndex.idx.eval #[rw] = some mid ∧
      mid.writeBlock tag colIndex.buf colIndex.idx.eval #[cw] = some final.pop ∧
      dec tag rw = r.val ∧ dec tag cw = c.val ∧ k ≤ r.val ∧ k ≤ c.val ∧
      (∀ a b : Fin N, k ≤ a.val → k ≤ b.val → |M a b| ≤ |M r c|) ∧
      (∀ a b : Fin N, k ≤ a.val → k ≤ b.val →
        b < c ∨ (b = c ∧ a < r) → |M a b| < |M r c|) := by
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hs.shape
  have hR : rowIndex.buf < initial.size := hwR.lt_size (by omega)
  have hC : colIndex.buf < initial.size := hwC.lt_size (by omega)
  obtain ⟨bw, rw, cw, r, c, -, hr, hc, -, hdr, hdc, hkr, hkc, hdom, hfirst⟩ := hs.values
  obtain ⟨mid, hw₁, hw₂⟩ := write_pair_of_frame tag initial final.pop rowIndex colIndex rw cw
    hrc (by rw [Store.shape_pop, hs.shape]; simp only [Store.shape, Array.map_push,
      Array.pop_push])
    (by rw [Store.read_pop_of_lt (by omega), hr])
    (by rw [Store.read_pop_of_lt (by omega), hc]) (by
      intro q buf j hbr hbc
      by_cases hb : buf < initial.size
      · rw [Store.read_pop_of_lt (by omega), hs.frame q buf j (by omega) hbr hbc,
          Store.read_push_of_lt hb]
      · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
          Store.read_eq_none_of_size_le (by omega)])
  exact ⟨rw, cw, r, c, mid, hw₁, hw₂, hdr, hdc, hkr, hkc,
    fun a b ha hb => hdom a b ha hb (by have := b.isLt; omega), hfirst⟩

private def Result {N : ℕ} (dec : P → K → ℝ) (tag : P) (initial : Store P K)
    (M : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) (rowIndex colIndex : Cell ℕ ℕ)
    (final : Store P K) : Prop :=
  ∃ (rw cw : K) (r c : Fin N) (mid : Store P K),
    initial.writeBlock tag rowIndex.buf rowIndex.idx.eval #[rw] = some mid ∧
    mid.writeBlock tag colIndex.buf colIndex.idx.eval #[cw] = some final ∧
    dec tag rw = r.val ∧ dec tag cw = c.val ∧ k ≤ r.val ∧ k ≤ c.val ∧
    (∀ a b : Fin N, k ≤ a.val → k ≤ b.val → |M a b| ≤ |M r c|) ∧
    (∀ a b : Fin N, k ≤ a.val → k ≤ b.val →
      b < c ∨ (b = c ∧ a < r) → |M a b| < |M r c|)

private theorem exec_body {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st σ : St P K C) (A : ℕ) (off : IExp ℕ) (rowIndex colIndex : Cell ℕ ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded st.store dec tag A off.eval M)
    (hwR : Writable st.store tag rowIndex.buf rowIndex.idx.eval 1)
    (hwC : Writable st.store tag colIndex.buf colIndex.idx.eval 1)
    (hAR : A ≠ rowIndex.buf) (hAC : A ≠ colIndex.buf)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval)
    (hσ : σ.store = st.store.push (tag, Array.replicate 4 none)) :
    ∃ out, exec I (do
      ins (.lit tag ⟨st.store.size, 1⟩ 0)
      copyAbs tag ⟨st.store.size, 0⟩ ⟨A, off + k + n * k⟩ ⟨st.store.size, 1⟩
      ins (.litIdx tag rowIndex k)
      ins (.litIdx tag colIndex k)
      forRange (n - k) fun j => completePivotColumn tag n k A off st.store.size
        rowIndex colIndex (k + IExp.var j)).run σ = some out ∧
      Result dec tag st.store M k.eval rowIndex colIndex out.store.pop := by
  obtain ⟨v, hv, -⟩ := hM ⟨k.eval, hk⟩ ⟨k.eval, hk⟩
  have hA : A < st.store.size := Store.lt_size_of_read_eq_some hv
  have hR : rowIndex.buf < st.store.size := hwR.lt_size (by omega)
  have hC : colIndex.buf < st.store.size := hwC.lt_size (by omega)
  have hMσ : HoldsDecoded σ.store dec tag A off.eval M :=
    hσ ▸ hM.push (tag, Array.replicate 4 none)
  have hsh : σ.store.shape[st.store.size]? = some (tag, 4) := by
    rw [hσ]; exact Store.getElem?_shape_push_size _ _ _
  obtain ⟨mid, z, he, hdz, hs⟩ := exec_initialize I h n k hi tag σ A st.store.size off
    rowIndex colIndex M hk hMσ hsh (hσ ▸ hwR.push (tag, Array.replicate 4 none))
    (hσ ▸ hwC.push (tag, Array.replicate 4 none)) (Nat.ne_of_lt hA)
    (Nat.ne_of_gt hR) (Nat.ne_of_gt hC) hrc
  obtain ⟨out, he', hs'⟩ := exists_exec_loop_eq_some_of_forall I (n := n - k)
    (fun t s => ScanState dec tag M k.eval st.store.size rowIndex colIndex z σ.store t s.store)
    hs (fun t ht s hs => exec_scanColumn I h n k hi tag σ.store A st.store.size off
      rowIndex colIndex M hk hMσ z hdz hsh (Nat.ne_of_lt hA) hAR hAC
      (Nat.ne_of_gt hR) (Nat.ne_of_gt hC) hrc t ht s hs)
  refine ⟨out, ?_, ?_⟩
  · change exec I ((do
      ins (.lit tag ⟨st.store.size, 1⟩ 0)
      copyAbs tag ⟨st.store.size, 0⟩ ⟨A, off + k + n * k⟩ ⟨st.store.size, 1⟩
      ins (.litIdx tag rowIndex k)
      ins (.litIdx tag colIndex k)) >>= fun _ => forRange (n - k) fun j =>
        completePivotColumn tag n k A off st.store.size rowIndex colIndex
          (k + IExp.var j)).run σ = _
    have hcomp : ExecutionComposable I (do
        ins (.lit tag ⟨st.store.size, 1⟩ 0)
        copyAbs tag ⟨st.store.size, 0⟩ ⟨A, off + k + n * k⟩ ⟨st.store.size, 1⟩
        ins (.litIdx tag rowIndex k)
        ins (.litIdx tag colIndex k)) := by
      intro f s
      change exec I (.seq (.instr (.lit tag ⟨st.store.size, 1⟩ 0)) (.seq _
        (.seq (.instr (.litIdx tag rowIndex k))
          (.seq (.instr (.litIdx tag colIndex k)) (f ()).run)))) s =
        (exec I (.seq (.instr (.lit tag ⟨st.store.size, 1⟩ 0)) (.seq _
          (.seq (.instr (.litIdx tag rowIndex k))
            (.seq (.instr (.litIdx tag colIndex k)) .skip)))) s).bind
              (fun s' => exec I (f ()).run s')
      simp only [exec_seq, exec_skip, Option.bind_assoc, Option.bind_some]
    rw [hcomp, he, Option.bind_some]
    change exec I (.seq (.loop (n - k) _) .skip) mid = _
    rw [exec_seq_skip]; exact he'
  · exact scan_pop_write tag st.store out.store M rowIndex colIndex z hwR hwC hrc
      (by simpa only [hσ, IExp.eval_sub] using hs')

end CompletePivot
/-- An actual complete pivot search succeeds on every nonempty active square under exact
current-word comparisons, sign/negation and bounded index conversion/literals. It records
absolute active row and column indices attaining the largest absolute decoded value, with
first column-major ties. The source is retained and the exact net footprint is the two
singleton index writes, even when the two output cells share a buffer at distinct offsets.
No nonzero pivot or nonsingularity hypothesis is imposed. -/
theorem IsRelErrSem.exec_completePivotChoice {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (A : ℕ) (off : IExp ℕ) (rowIndex colIndex : Cell ℕ ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : HoldsDecoded st.store dec tag A off.eval M)
    (hwR : Writable st.store tag rowIndex.buf rowIndex.idx.eval 1)
    (hwC : Writable st.store tag colIndex.buf colIndex.idx.eval 1)
    (hAR : A ≠ rowIndex.buf) (hAC : A ≠ colIndex.buf)
    (hrc : rowIndex.buf ≠ colIndex.buf ∨ rowIndex.idx.eval ≠ colIndex.idx.eval) :
    ∃ (out : St P K C) (r c : Fin n.eval) (rw cw : K) (mid : Store P K),
      exec I (completePivotChoice tag n k A off rowIndex colIndex).run st = some out ∧
      st.store.writeBlock tag rowIndex.buf rowIndex.idx.eval #[rw] = some mid ∧
      mid.writeBlock tag colIndex.buf colIndex.idx.eval #[cw] = some out.store ∧
      dec tag rw = r.val ∧ dec tag cw = c.val ∧ k.eval ≤ r.val ∧ k.eval ≤ c.val ∧
      HoldsDecoded out.store dec tag A off.eval M ∧
      (∀ a b : Fin n.eval, k.eval ≤ a.val → k.eval ≤ b.val → |M a b| ≤ |M r c|) ∧
      (∀ a b : Fin n.eval, k.eval ≤ a.val → k.eval ≤ b.val →
        b < c ∨ (b = c ∧ a < r) → |M a b| < |M r c|) := by
  let Q := CompletePivot.Result dec tag st.store M k.eval rowIndex colIndex
  obtain ⟨out, he, rw, cw, r, c, mid, hw₁, hw₂, hdr, hdc, hkr, hkc, hmax, hfirst⟩ :=
    exists_exec_alloc I tag 4 (fun scratch => ((do
      ins (.lit tag ⟨scratch, 1⟩ 0)
      copyAbs tag ⟨scratch, 0⟩ ⟨A, off + k + n * k⟩ ⟨scratch, 1⟩
      ins (.litIdx tag rowIndex k)
      ins (.litIdx tag colIndex k)
      forRange (n - k) fun j => completePivotColumn tag n k A off scratch
        rowIndex colIndex (k + IExp.var j)) : Builder P ι ℕ ℕ Unit).run) st Q
      (fun σ hσ => CompletePivot.exec_body I h n k hi tag st σ A off rowIndex colIndex
        M hk hM hwR hwC hAR hAC hrc hσ)
  refine ⟨out, r, c, rw, cw, mid, ?_, hw₁, hw₂, hdr, hdc, hkr, hkc, ?_, hmax, hfirst⟩
  · change exec I (.seq (.alloc tag 4 _) .skip) st = some out
    rw [exec_seq_skip]; exact he
  · intro i j
    obtain ⟨v, hv, hd⟩ := hM i j
    refine ⟨v, ?_, hd⟩
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hAC),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hAR)]
    exact hv

end NLAlib.Computation
