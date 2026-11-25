/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.StridedPivotScan
public import NLAlib.Matrix.Computation.CompletePivot
public import NLAlib.Matrix.Factorizations.RookPivoting

/-!
# Stored rook search steps

A rook step selects a column maximum and then a row maximum. It moves to the row maximum's
column only on strict magnitude growth; equality finishes the search, even when the stable
row scan prefers a different column. Search indices and the completion flag live in scoped
workspace, leaving the matrix and caller output cells untouched until the final copies.

## Main definitions

* `NLAlib.Computation.rookPivotSearch`: one column/row comparison and strict continuation.
* `NLAlib.Computation.rookPivotStep`: no-op after completion, otherwise one search step.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Compare the current column maximum with the row maximum. Strict improvement records the
next absolute column; equality marks completion. The comparison executes exact sign/negation
magnitude copies, followed by one stored index or completion literal. -/
def rookPivotCompare {P ι VB VI : Type} (tag : P) (scratch : VB)
    (current candidate : Cell VB VI) (next : IExp VI) : Builder P ι VB VI Unit := do
  copyAbs tag ⟨scratch, 5⟩ current ⟨scratch, 0⟩
  copyAbs tag ⟨scratch, 6⟩ candidate ⟨scratch, 0⟩
  ifThenElse tag .lt ⟨scratch, 5⟩ ⟨scratch, 6⟩
    (ins (.litIdx tag ⟨scratch, 3⟩ next)) (ins (.lit tag ⟨scratch, 1⟩ 1))

/-- Select a row maximum and compare it with the current column's selected entry. The row
coordinate is already stored exactly at workspace offset 2. -/
def rookPivotRow {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (A : VB) (off : IExp VI) (scratch : VB) (row col : IExp VI) :
    Builder P ι VB VI Unit := do
  argmaxStridedAbs tag (n - k) A (off + row + n * k) n ⟨scratch, 4⟩
  bindIdx tag ⟨scratch, 4⟩ (n - k) fun c =>
    rookPivotCompare tag scratch ⟨A, off + row + n * col⟩
      ⟨A, off + row + n * (k + .var c)⟩ (k + .var c)

/-- Search the active suffix of a stored column and the selected row. Workspace offsets are
zero at 0, done at 1, row at 2, current column at 3, relative row maximum column at 4 and
magnitudes at 5 and 6. Completion is set on equal magnitudes; only strict growth changes column. -/
def rookPivotSearch {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (A : VB) (off : IExp VI) (scratch : VB) (col : IExp VI) :
    Builder P ι VB VI Unit := do
  argmaxAbs tag (n - k) A (off + k + n * col) ⟨scratch, 2⟩
  bindIdx tag ⟨scratch, 2⟩ (n - k) fun r => do
    ins (.litIdx tag ⟨scratch, 2⟩ (k + .var r))
    rookPivotRow tag n k A off scratch (k + .var r) col

/-- Perform one rook search step unless the exact stored completion flag is already one.
The guard compares the flag with the stored zero, so completed iterations have no store effect. -/
def rookPivotStep {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (A : VB) (off : IExp VI) (scratch : VB) : Builder P ι VB VI Unit :=
  ifThenElse tag .eq ⟨scratch, 1⟩ ⟨scratch, 0⟩
    (bindIdx tag ⟨scratch, 3⟩ n fun c => rookPivotSearch tag n k A off scratch (.var c))
    (pure ())

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

namespace RookPivot

private abbrev ScratchFrame (base : Store P ℝ) (tag : P) (scratch : ℕ)
    (s : Store P ℝ) : Prop := Store.BlockFrame base tag scratch scratch 0 0 s (fun _ => none)

private theorem exec_decide (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch : ℕ) (b v c : ℝ) (next : IExp ℕ)
    (hb : st.store.read tag scratch 5 = some b)
    (hv : st.store.read tag scratch 6 = some v)
    (hc : st.store.read tag scratch 3 = some c)
    (hd : st.store.read tag scratch 1 = some 0)
    (hsh : st.store.shape[scratch]? = some (tag, 7))
    {base : Store P ℝ} (hF : ScratchFrame base tag scratch st.store) :
    ∃ out, exec I (ifThenElse tag .lt ⟨scratch, 5⟩ ⟨scratch, 6⟩
      (ins (.litIdx tag ⟨scratch, 3⟩ next))
      (ins (.lit tag ⟨scratch, 1⟩ 1))).run st = some out ∧
      ScratchFrame base tag scratch out.store ∧
      out.store.read tag scratch 3 = some (if b < v then (next.eval : ℝ) else c) ∧
      out.store.read tag scratch 1 = some (if b < v then (0 : ℝ) else 1) ∧
      (∀ i, i ≠ 1 → i ≠ 3 → out.store.read tag scratch i = st.store.read tag scratch i) := by
  let tested : St P ℝ C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  have hcmp : cmpStep I tag .lt ⟨scratch, 5⟩ ⟨scratch, 6⟩ st =
      some (decide (b < v), tested) := by
    simp only [cmpStep, IExp.eval, hb, hv, Option.bind_some, hI, exactSem,
      RCLike.im_to_real, and_self, ↓reduceIte,
      Option.map_some]
    rfl
  have hrun : (ifThenElse tag .lt ⟨scratch, 5⟩ ⟨scratch, 6⟩
      (ins (.litIdx tag ⟨scratch, 3⟩ next))
      (ins (.lit tag ⟨scratch, 1⟩ 1)) : Builder P ι ℕ ℕ Unit).run =
      .seq (.ite tag .lt ⟨scratch, 5⟩ ⟨scratch, 6⟩
        (ins (.litIdx tag ⟨scratch, 3⟩ next)).run
        (ins (.lit tag ⟨scratch, 1⟩ 1)).run) .skip := rfl
  simp only [hrun, exec_seq_skip, exec_ite, hcmp, Option.bind_some]
  by_cases hlt : b < v
  · obtain ⟨s, hs⟩ := Store.exists_write_eq_some_of_getElem?_shape
      (i := 3) (next.eval : ℝ) hsh (by omega)
    let out : St P ℝ C := { tested with store := s, cnt := tested.cnt + I.charge (.lit tag) }
    refine ⟨out, ?_, hF.write_scratch (by omega) hs, ?_, ?_, ?_⟩
    · simp only [hlt, decide_true, ↓reduceIte]
      exact (exec_seq_instr_litIdx I (by simp [hI, exactSem]) hs).trans (exec_skip I _)
    · simpa only [hlt, ↓reduceIte] using Store.read_of_write_eq_some hs
    · simpa only [hlt, ↓reduceIte] using
        (Store.read_of_write_eq_some_of_ne hs (Or.inr (by omega : 1 ≠ 3))).trans hd
    · intro i _ hi
      exact Store.read_of_write_eq_some_of_ne hs (Or.inr hi)
  · obtain ⟨s, hs⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) (1 : ℝ) hsh (by omega)
    let out : St P ℝ C := { tested with store := s, cnt := tested.cnt + I.charge (.lit tag) }
    refine ⟨out, ?_, hF.write_scratch (by omega) hs, ?_, ?_, ?_⟩
    · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact (exec_seq_instr_lit I (by simp [hI, exactSem]) hs).trans (exec_skip I _)
    · simpa only [hlt, ↓reduceIte] using
        (Store.read_of_write_eq_some_of_ne hs (Or.inr (by omega : 3 ≠ 1))).trans hc
    · simpa only [hlt, ↓reduceIte] using Store.read_of_write_eq_some hs
    · intro i hi _
      exact Store.read_of_write_eq_some_of_ne hs (Or.inr hi)

private theorem exec_compare (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch : ℕ) (current candidate : Cell ℕ ℕ)
    (next : IExp ℕ) (a b c : ℝ)
    (ha : st.store.read tag current.buf current.idx.eval = some a)
    (hb : st.store.read tag candidate.buf candidate.idx.eval = some b)
    (hc : st.store.read tag scratch 3 = some c)
    (hd : st.store.read tag scratch 1 = some 0)
    (hz : st.store.read tag scratch 0 = some 0)
    (hsh : st.store.shape[scratch]? = some (tag, 7))
    (hcand : candidate.buf ≠ scratch)
    {base : Store P ℝ} (hF : ScratchFrame base tag scratch st.store) :
    ∃ out, exec I (rookPivotCompare tag scratch current candidate next).run st = some out ∧
      ScratchFrame base tag scratch out.store ∧
      out.store.read tag scratch 3 = some (if |a| < |b| then (next.eval : ℝ) else c) ∧
      out.store.read tag scratch 1 = some (if |a| < |b| then (0 : ℝ) else 1) ∧
      (∀ i, i ≠ 1 → i ≠ 3 → i ≠ 5 → i ≠ 6 →
        out.store.read tag scratch i = st.store.read tag scratch i) := by
  have h := hI ▸ (isRelErrSem_exactSem (P := P))
  obtain ⟨mid, aw, he₁, hs₁, haw⟩ := h.exec_copyAbs I tag st ⟨scratch, 5⟩ current
    ⟨scratch, 0⟩ a 0 ha hz rfl ⟨7, hsh, by norm_num [IExp.eval]⟩
  have hz₁ : mid.store.read tag scratch 0 = some 0 := by
    rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inr (by norm_num [IExp.eval]))]; exact hz
  obtain ⟨ready, bw, he₂, hs₂, hbw⟩ := h.exec_copyAbs I tag mid ⟨scratch, 6⟩ candidate
    ⟨scratch, 0⟩ b 0
    (by rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hcand)]; exact hb) hz₁ rfl
    ⟨7, (Store.shape_of_write_eq_some hs₁).symm ▸ hsh, by norm_num [IExp.eval]⟩
  have hpres : ∀ i, i ≠ 5 → i ≠ 6 →
      ready.store.read tag scratch i = st.store.read tag scratch i := by
    intro i hi₅ hi₆
    exact (Store.read_of_write_eq_some_of_ne hs₂ (Or.inr hi₆)).trans
      (Store.read_of_write_eq_some_of_ne hs₁ (Or.inr hi₅))
  obtain ⟨out, he₃, hFout, hr, hd', hf⟩ := exec_decide I hI tag ready scratch aw bw c next
    (by rw [Store.read_of_write_eq_some_of_ne hs₂ (Or.inr (by norm_num [IExp.eval]))];
        exact Store.read_of_write_eq_some hs₁)
    (Store.read_of_write_eq_some hs₂) ((hpres 3 (by omega) (by omega)).trans hc)
    ((hpres 1 (by omega) (by omega)).trans hd)
    (by rw [Store.shape_of_write_eq_some hs₂, Store.shape_of_write_eq_some hs₁]; exact hsh)
    ((hF.write_scratch (by omega) hs₁).write_scratch (by omega) hs₂)
  refine ⟨out, ?_, hFout, by simpa only [haw, hbw] using hr,
    by simpa only [haw, hbw] using hd', ?_⟩
  · unfold rookPivotCompare
    rw [exec_run_bind I (b := copyAbs tag ⟨scratch, 5⟩ current ⟨scratch, 0⟩)
      (fun _ => rfl), he₁, Option.bind_some, exec_run_bind I
      (b := copyAbs tag ⟨scratch, 6⟩ candidate ⟨scratch, 0⟩) (fun _ => rfl), he₂, Option.bind_some]
    exact he₃
  · intro i hi₁ hi₃ hi₅ hi₆
    exact (hf i hi₁ hi₃).trans (hpres i hi₅ hi₆)

private theorem exec_row (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch A : ℕ) (n k off row col : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (htail : n.eval - k.eval ≤ n.eval)
    (hr : row.eval < n.eval) (hcol : col.eval < n.eval)
    (hM : Holds st.store tag A off.eval M)
    (hz : st.store.read tag scratch 0 = some 0)
    (hd : st.store.read tag scratch 1 = some 0)
    (hrow : st.store.read tag scratch 2 = some (row.eval : ℝ))
    (hc : st.store.read tag scratch 3 = some (col.eval : ℝ))
    (hsh : st.store.shape[scratch]? = some (tag, 7)) (hAS : A ≠ scratch)
    {base : Store P ℝ} (hF : ScratchFrame base tag scratch st.store) :
    ∃ (out : St P ℝ C) (d : Fin (n.eval - k.eval)),
      exec I (rookPivotRow tag n k A off scratch row col).run st = some out ∧
      ScratchFrame base tag scratch out.store ∧
      out.store.read tag scratch 0 = some 0 ∧
      out.store.read tag scratch 2 = some (row.eval : ℝ) ∧
      out.store.read tag scratch 3 = some (if |M ⟨row.eval, hr⟩ ⟨col.eval, hcol⟩| <
        |M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) d)|
        then ((k.eval + d.val : ℕ) : ℝ) else col.eval) ∧
      out.store.read tag scratch 1 = some (if |M ⟨row.eval, hr⟩ ⟨col.eval, hcol⟩| <
        |M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) d)|
        then (0 : ℝ) else 1) ∧
      (∀ j : Fin (n.eval - k.eval),
        |M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) j)| ≤
          |M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) d)|) := by
  have h := hI ▸ (isRelErrSem_exactSem (P := P))
  obtain ⟨mid, w, d, he₁, hs, hdw, hm, -⟩ := h.exec_argmaxStridedAbs_row I n k row
    (hI ▸ isIndexExactSem_exactSem n.eval) tag st A off ⟨scratch, 4⟩ M hk htail hr
    (fun i j => ⟨M i j, hM i j, rfl⟩) (fun i hi => ⟨7, hsh, by simp [IExp.eval]; omega⟩)
  let ready : St P ℝ C := { mid with cnt := mid.cnt + I.charge (.toNat tag) }
  have hpres : ∀ i, i ≠ 4 → ready.store.read tag scratch i = st.store.read tag scratch i := by
    intro i hi
    exact Store.read_of_writeBlock_eq_some_of_ne hs (by simp; omega)
  have hcur : ready.store.read tag A (off + row + n * col).eval =
      some (M ⟨row.eval, hr⟩ ⟨col.eval, hcol⟩) := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl hAS)]
    simpa only [IExp.eval_add, IExp.eval_mul] using hM ⟨row.eval, hr⟩ ⟨col.eval, hcol⟩
  have hcand : ready.store.read tag A (off + row + n * (k + .var d.val)).eval =
      some (M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) d)) := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl hAS)]
    have hdval := Fin.val_natAdd_castLEEmb_sub k.eval (htail) d
    simpa only [hdval, IExp.eval_add, IExp.eval_mul, IExp.eval_var] using
      hM ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) d)
  obtain ⟨out, he₂, hFout, hc', hd', hf⟩ := exec_compare I hI tag ready scratch
    ⟨A, off + row + n * col⟩ ⟨A, off + row + n * (k + .var d.val)⟩ (k + .var d.val)
    _ _ (col.eval : ℝ) hcur hcand ((hpres 3 (by omega)).trans hc)
    ((hpres 1 (by omega)).trans hd) ((hpres 0 (by omega)).trans hz)
    ((Store.shape_of_writeBlock_eq_some hs).symm ▸ hsh) hAS
    (hF.writeBlock_scratch (by omega) hs)
  refine ⟨out, d, ?_, hFout, ?_, ?_, by simpa only [IExp.eval_add, IExp.eval_var] using hc',
    hd', hm⟩
  · unfold rookPivotRow
    rw [exec_run_bind I (b := argmaxStridedAbs tag (n - k) A (off + row + n * k) n
      ⟨scratch, 4⟩) (fun _ => rfl), he₁, Option.bind_some]
    change exec I (.seq (.bindIdx tag ⟨scratch, 4⟩ (n - k) _) .skip) mid = _
    have hto : I.sem.toNat tag w = some d.val := by simp [hI, exactSem, hdw]
    rw [exec_seq_skip, exec_bindIdx_of_read I
      (by simpa using Store.read_of_writeBlock_eq_some_of_lt hs (by simp : 0 < #[w].size))
      hto (by change d.val ≤ n.eval - k.eval; omega)]
    exact he₂
  · exact (hf 0 (by omega) (by omega) (by omega) (by omega)).trans
      ((hpres 0 (by omega)).trans hz)
  · exact (hf 2 (by omega) (by omega) (by omega) (by omega)).trans
      ((hpres 2 (by omega)).trans hrow)

/-- A stored rook search step really executes both scans and its strict-growth decision.
All changes are confined to the existing workspace. The returned relative row and column
realize their respective active maxima, without a nonzero-pivot assumption. -/
theorem exec_search (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (scratch A : ℕ) (n k off col : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (htail : n.eval - k.eval ≤ n.eval)
    (hcol : col.eval < n.eval) (hM : Holds st.store tag A off.eval M)
    (hz : st.store.read tag scratch 0 = some 0)
    (hd : st.store.read tag scratch 1 = some 0)
    (hc : st.store.read tag scratch 3 = some (col.eval : ℝ))
    (hsh : st.store.shape[scratch]? = some (tag, 7)) (hAS : A ≠ scratch)
    {base : Store P ℝ}
    (hF : Store.BlockFrame base tag scratch scratch 0 0 st.store (fun _ => none)) :
    ∃ (out : St P ℝ C) (r d : Fin (n.eval - k.eval)),
      let emb := Fin.natAdd_castLEEmb (htail)
      let grow := |M (emb r) ⟨col.eval, hcol⟩| < |M (emb r) (emb d)|
      exec I (rookPivotSearch tag n k A off scratch col).run st = some out ∧
      Store.BlockFrame base tag scratch scratch 0 0 out.store (fun _ => none) ∧
      out.store.read tag scratch 0 = some 0 ∧
      out.store.read tag scratch 2 = some ((k.eval + r.val : ℕ) : ℝ) ∧
      out.store.read tag scratch 3 =
        some (if grow then ((k.eval + d.val : ℕ) : ℝ) else col.eval) ∧
      out.store.read tag scratch 1 = some (if grow then (0 : ℝ) else 1) ∧
      (∀ i : Fin (n.eval - k.eval), |M (emb i) ⟨col.eval, hcol⟩| ≤
        |M (emb r) ⟨col.eval, hcol⟩|) ∧
      (∀ j : Fin (n.eval - k.eval), |M (emb r) (emb j)| ≤ |M (emb r) (emb d)|) := by
  have h := hI ▸ (isRelErrSem_exactSem (P := P))
  obtain ⟨mid, w, r, he₁, hs₁, hdw, hm, -⟩ := CompletePivot.exec_columnScan I h n k col
    (hI ▸ isIndexExactSem_exactSem n.eval) tag st A off ⟨scratch, 2⟩ M hk htail hcol
    (fun i j => ⟨M i j, hM i j, rfl⟩) (fun i hi => ⟨7, hsh, by simp [IExp.eval]; omega⟩) hAS
  let bound : St P ℝ C := { mid with cnt := mid.cnt + I.charge (.toNat tag) }
  have hsh₁ : mid.store.shape[scratch]? = some (tag, 7) :=
    (Store.shape_of_writeBlock_eq_some hs₁).symm ▸ hsh
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape
    (i := 2) ((k.eval + r.val : ℕ) : ℝ) hsh₁ (by omega)
  let ready : St P ℝ C := { bound with store := s₂, cnt := bound.cnt + I.charge (.lit tag) }
  have hF₂ := (hF.writeBlock_scratch (by omega) hs₁).write_scratch (by omega) hs₂
  have hpres : ∀ i, i ≠ 2 → ready.store.read tag scratch i = st.store.read tag scratch i := by
    intro i hi
    exact (Store.read_of_write_eq_some_of_ne hs₂ (Or.inr hi)).trans
      (Store.read_of_writeBlock_eq_some_of_ne hs₁ (by simp; omega))
  have hM₂ : Holds ready.store tag A off.eval M := by
    intro i j
    rw [Store.read_of_write_eq_some_of_ne hs₂ (Or.inl hAS),
      Store.read_of_writeBlock_eq_some_of_ne hs₁ (Or.inl hAS)]
    exact hM i j
  have hr : (k + .var r.val).eval < n.eval := by
    simp only [IExp.eval_add, IExp.eval_var]
    have := r.isLt
    omega
  have hri : (⟨(k + .var r.val).eval, hr⟩ : Fin n.eval) =
      (Fin.natAdd_castLEEmb (htail)) r := by
    ext; simp only [IExp.eval_add, IExp.eval_var, Fin.val_natAdd_castLEEmb_sub]
  obtain ⟨out, d, he₂, hFout, hz', hr', hc', hd', hrowmax⟩ := exec_row I hI tag ready
    scratch A n k off (k + .var r.val) col M hk (Nat.sub_le _ _) hr hcol hM₂
    ((hpres 0 (by omega)).trans hz) ((hpres 1 (by omega)).trans hd)
    (by simpa only [IExp.eval_add, IExp.eval_var] using Store.read_of_write_eq_some hs₂)
    ((hpres 3 (by omega)).trans hc)
    ((Store.shape_of_write_eq_some hs₂).symm ▸ hsh₁) hAS hF₂
  refine ⟨out, r, d, ?_, hFout, hz', ?_, ?_, ?_, ?_, ?_⟩
  · unfold rookPivotSearch
    rw [exec_run_bind I (b := argmaxAbs tag (n - k) A (off + k + n * col)
      ⟨scratch, 2⟩) (fun _ => rfl), he₁, Option.bind_some]
    change exec I (.seq (.bindIdx tag ⟨scratch, 2⟩ (n - k) _) .skip) mid = _
    have hto : I.sem.toNat tag w = some r.val := by simp [hI, exactSem, hdw]
    rw [exec_seq_skip, exec_bindIdx_of_read I
      (by simpa using Store.read_of_writeBlock_eq_some_of_lt hs₁ (by simp : 0 < #[w].size))
      hto (by change r.val ≤ n.eval - k.eval; omega)]
    change exec I (.seq (.instr (.litIdx tag ⟨scratch, 2⟩ (k + .var r.val))) _) bound = _
    rw [exec_seq_instr_litIdx I (by simp [hI, exactSem, IExp.eval]) hs₂]
    exact he₂
  · simpa only [IExp.eval_add, IExp.eval_var] using hr'
  · simpa only [hri] using hc'
  · simpa only [hri] using hd'
  · exact hm
  · simpa only [hri] using hrowmax

end RookPivot

end NLAlib.Computation
