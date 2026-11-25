/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PivotScan
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Stored row scales

`rowScales` initializes the fixed scales for scaled partial pivoting from a rectangular stored
matrix. Each scale is the existing supremum norm of its row, including zero for an empty row.
Only copying, exact decoded comparisons, exact negation and a zero literal are needed.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.Computation.rowScales`: initialize one maximum absolute value per matrix row.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_rowScales`: exact decoded row norms and a single output
  block write under the standard scalar model, assuming only that the zero literal is safe.
* `NLAlib.Computation.executionComposable_rowScales`: composition with a following builder.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

private def rowScale {P ι VB VI : Type} (tag : P) (m n row : IExp VI)
    (A : VB) (ao : IExp VI) (scale : Cell VB VI) : Builder P ι VB VI Unit := scope do
  let scratch ← alloc tag 2
  ins (.lit tag ⟨scratch, 0⟩ 0)
  ins (.copy tag scale ⟨scratch, 0⟩)
  forRange n fun j => do
    copyAbs tag ⟨scratch, 1⟩ ⟨A, ao + row + m * IExp.var j⟩ ⟨scratch, 0⟩
    ifThenElse tag .lt scale ⟨scratch, 1⟩
      (ins (.copy tag scale ⟨scratch, 1⟩)) (pure ())

/-- Initialize one fixed scale per row of a column-major rectangular matrix by its maximum
absolute stored entry. Empty rows receive zero. The scales are intended to follow subsequent
row swaps; this initializer does not recompute active-row scales. [Higham2002, §9.3]. -/
def rowScales {P ι VB VI : Type} (tag : P) (m n : IExp VI) (A : VB) (ao : IExp VI)
    (scales : VB) (so : IExp VI) : Builder P ι VB VI Unit :=
  forRange m fun i => scope do
    let scratch ← alloc tag 2
    ins (.lit tag ⟨scratch, 0⟩ 0)
    ins (.copy tag ⟨scales, so + .var i⟩ ⟨scratch, 0⟩)
    forRange n fun j => do
      copyAbs tag ⟨scratch, 1⟩ ⟨A, ao + .var i + m * IExp.var j⟩ ⟨scratch, 0⟩
      ifThenElse tag .lt ⟨scales, so + .var i⟩ ⟨scratch, 1⟩
        (ins (.copy tag ⟨scales, so + .var i⟩ ⟨scratch, 1⟩)) (pure ())

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Row-scale initialization composes with the following builder. -/
theorem executionComposable_rowScales (I : Interp P ι K C) (tag : P) (m n : IExp ℕ)
    (A : ℕ) (ao : IExp ℕ) (scales : ℕ) (so : IExp ℕ) :
    ExecutionComposable I (rowScales tag m n A ao scales so) :=
  executionComposable_single I (fun _ => rfl)

private theorem exec_maxCopy {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    (tag : P) (st : St P K C) (best candidate : Cell ℕ ℕ) (b c : K)
    (hb : st.store.read tag best.buf best.idx.eval = some b)
    (hc : st.store.read tag candidate.buf candidate.idx.eval = some c) :
    ∃ out w, exec I (ifThenElse tag .lt best candidate
      (ins (.copy tag best candidate)) (pure ()) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      out.store.shape = st.store.shape ∧ out.store.read tag best.buf best.idx.eval = some w ∧
      dec tag w = max (dec tag b) (dec tag c) ∧
      ∀ q buf j, (buf ≠ best.buf ∨ j ≠ best.idx.eval) →
        out.store.read q buf j = st.store.read q buf j := by
  let tested : St P K C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  have ht : cmpStep I tag .lt best candidate st =
      some (decide (dec tag b < dec tag c), tested) := by
    simp only [cmpStep, hb, hc, Option.bind_some, h.cmp_lt]
    rfl
  change ∃ out w, exec I (.seq (.ite tag .lt best candidate
    (.seq (.instr (.copy tag best candidate)) .skip) .skip) .skip) st = some out ∧ _
  rw [exec_seq_skip, exec_ite, ht, Option.bind_some]
  by_cases hlt : dec tag b < dec tag c
  · obtain ⟨s, hs⟩ := Store.exists_write_eq_some_of_read_eq_some (v := c) hb
    refine ⟨{ tested with store := s, cnt := tested.cnt + I.charge (.copy tag) }, c,
      ?_, Store.shape_of_write_eq_some hs, Store.read_of_write_eq_some hs,
      (max_eq_right hlt.le).symm, fun q b j hj => Store.read_of_write_eq_some_of_ne hs hj⟩
    simp only [hlt, decide_true, ↓reduceIte]
    rw [exec_seq_instr_copy I (st := tested) hc hs, exec_skip]
  · refine ⟨tested, b, ?_, rfl, hb, (max_eq_left (le_of_not_gt hlt)).symm,
      fun _ _ _ _ => rfl⟩
    simpa only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte] using exec_skip I tested

private structure RowState (dec : P → K → ℝ) (tag : P) {N : ℕ} (x : Fin N → ℝ)
    (scratch : ℕ) (scale : Cell ℕ ℕ) (z : K) (initial : Store P K) (k : ℕ)
    (s : Store P K) : Prop where
  shape : s.shape = initial.shape
  frame : ∀ q b j, b ≠ scratch → (b ≠ scale.buf ∨ j ≠ scale.idx.eval) →
    s.read q b j = initial.read q b j
  zero : s.read tag scratch 0 = some z
  value : ∃ w, s.read tag scale.buf scale.idx.eval = some w ∧
    0 ≤ dec tag w ∧ (∀ j : Fin N, j.val < k → |x j| ≤ dec tag w) ∧
      (dec tag w = 0 ∨ ∃ j : Fin N, j.val < k ∧ dec tag w = |x j|)

private theorem exec_rowScale_step {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    (tag : P) (st : St P K C) (m n row : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (scale : Cell ℕ ℕ) (x : Fin n.eval → ℝ)
    (hin : ∀ j : Fin n.eval, ∃ w, st.store.read tag A
      (ao.eval + row.eval + m.eval * j.val) = some w ∧ dec tag w = x j)
    (hAS : 0 < n.eval → A ≠ scale.buf) (hscale : scale.buf < st.store.size)
    (z : K) (hzero : dec tag z = 0) (σ : St P K C)
    (hσ : σ.store = st.store.push (tag, Array.replicate 2 none))
    (hsh : σ.store.shape[st.store.size]? = some (tag, 2))
    (k : ℕ) (hk : k < n.eval) (s : St P K C)
    (hs : RowState dec tag x st.store.size scale z σ.store k s.store) :
    ∃ out, exec I (do
      copyAbs tag ⟨st.store.size, 1⟩ ⟨A, ao + row + m * IExp.var k⟩ ⟨st.store.size, 0⟩
      ifThenElse tag .lt scale ⟨st.store.size, 1⟩
        (ins (.copy tag scale ⟨st.store.size, 1⟩)) (pure ())).run s = some out ∧
      RowState dec tag x st.store.size scale z σ.store (k + 1) out.store := by
  obtain ⟨bw, hb, hnonneg, hdom, hatt⟩ := hs.value
  obtain ⟨v, hv, hdv⟩ := hin ⟨k, hk⟩
  have hAb : A < st.store.size := Store.lt_size_of_read_eq_some hv
  have hv' : s.store.read tag A (ao.eval + row.eval + m.eval * k) = some v := by
    rw [hs.frame tag A _ (by omega) (Or.inl (hAS (by omega))), hσ,
      Store.read_push_of_lt hAb]
    exact hv
  obtain ⟨mid, cw, hr₁, hw₁, hdc⟩ := h.exec_copyAbs I tag s
    ⟨st.store.size, 1⟩ ⟨A, ao + row + m * IExp.var k⟩ ⟨st.store.size, 0⟩ v z
    hv' hs.zero hzero ⟨2, hs.shape ▸ hsh, by norm_num [IExp.eval]⟩
  have hb' : mid.store.read tag scale.buf scale.idx.eval = some bw := by
    rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inl (Nat.ne_of_lt hscale))]
    exact hb
  obtain ⟨last, w, hr₂, hshape₂, hread₂, hdw, hframe₂⟩ := exec_maxCopy I h tag mid
    scale ⟨st.store.size, 1⟩ bw cw hb' (Store.read_of_write_eq_some hw₁)
  have hc : dec tag cw = |x ⟨k, hk⟩| := by simpa only [hdv] using hdc
  refine ⟨last, ?_, ⟨hshape₂.trans ((Store.shape_of_write_eq_some hw₁).trans hs.shape),
    ?_, ?_, w, hread₂, ?_, ?_, ?_⟩⟩
  · rw [exec_run_bind I (b := copyAbs tag ⟨st.store.size, 1⟩
      ⟨A, ao + row + m * IExp.var k⟩ ⟨st.store.size, 0⟩) (fun _ => rfl),
      hr₁, Option.bind_some]
    exact hr₂
  · intro q b j hb hj
    rw [hframe₂ q b j hj, Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hb)]
    exact hs.frame q b j hb hj
  · rw [hframe₂ tag st.store.size 0 (Or.inl (Nat.ne_of_gt hscale)),
      Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega : 0 ≠ 1))]
    exact hs.zero
  · rw [hdw]; exact hnonneg.trans (le_max_left _ _)
  · intro j hj
    rw [hdw, hc]
    by_cases hjk : j.val < k
    · exact (hdom j hjk).trans (le_max_left _ _)
    · have he : j = ⟨k, hk⟩ := Fin.ext (by change j.val = k; omega)
      subst j; exact le_max_right _ _
  · rw [hdw, hc]
    by_cases hbigger : dec tag bw < |x ⟨k, hk⟩|
    · exact Or.inr ⟨⟨k, hk⟩, by change k < k + 1; omega, max_eq_right hbigger.le⟩
    · rw [max_eq_left (le_of_not_gt hbigger)]
      rcases hatt with h | ⟨j, hj, he⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, he⟩

private theorem exec_rowScale_body {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    (tag : P) (st : St P K C) (m n row : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (scale : Cell ℕ ℕ) (x : Fin n.eval → ℝ)
    (hin : ∀ j : Fin n.eval, ∃ w, st.store.read tag A
      (ao.eval + row.eval + m.eval * j.val) = some w ∧ dec tag w = x j)
    (hw : Writable st.store tag scale.buf scale.idx.eval 1)
    (hAS : 0 < n.eval → A ≠ scale.buf) (hscale : scale.buf < st.store.size)
    (z : K) (hz : I.sem.lit tag 0 = some z) (hzero : dec tag z = 0) :
    ∀ σ : St P K C, σ.store = st.store.push (tag, Array.replicate 2 none) →
      ∃ out, exec I (do
        ins (.lit tag ⟨st.store.size, 0⟩ 0)
        ins (.copy tag scale ⟨st.store.size, 0⟩)
        forRange n fun j => do
          copyAbs tag ⟨st.store.size, 1⟩ ⟨A, ao + row + m * IExp.var j⟩ ⟨st.store.size, 0⟩
          ifThenElse tag .lt scale ⟨st.store.size, 1⟩
            (ins (.copy tag scale ⟨st.store.size, 1⟩)) (pure ())).run σ = some out ∧
        ∃ w, st.store.write tag scale.buf scale.idx.eval w = some out.store.pop ∧
          dec tag w = ‖x‖ := by
  intro σ hσ
  have hsh : σ.store.shape[st.store.size]? = some (tag, 2) := by
    rw [hσ]; exact Store.getElem?_shape_push_size _ _ _
  obtain ⟨s₁, hs₁, -, hshape₁, hread₁, -⟩ := exec_scalar_lit I tag σ
    ⟨st.store.size, 0⟩ 0 z hz ⟨2, hsh, by norm_num [IExp.eval]⟩
  let σ₁ : St P K C := { σ with store := s₁, cnt := σ.cnt + I.charge (.lit tag) }
  obtain ⟨len, hlen, hlt⟩ := hw 0 (by omega)
  have hlen₁ : s₁.shape[scale.buf]? = some (tag, len) := by
    rw [hshape₁, hσ, Store.getElem?_shape_push_of_lt _ hscale]
    exact hlen
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape z hlen₁ (by simpa using hlt)
  let σ₂ : St P K C := { σ₁ with store := s₂, cnt := σ₁.cnt + I.charge (.copy tag) }
  let R := RowState dec tag x st.store.size scale z σ.store
  have h0 : R 0 s₂ := by
    refine ⟨(Store.shape_of_write_eq_some hs₂).trans hshape₁, ?_, ?_, z,
      Store.read_of_write_eq_some hs₂, hzero ▸ le_rfl, ?_, Or.inl hzero⟩
    · intro q b j hb hj
      rw [Store.read_of_write_eq_some_of_ne hs₂ hj,
        Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hb)]
    · rw [Store.read_of_write_eq_some_of_ne hs₂ (Or.inl (Nat.ne_of_gt hscale))]
      exact hread₁
    · intro j hj; omega
  obtain ⟨out, hr, hs⟩ := exists_exec_loop_eq_some_of_forall I (n := n)
    (body := fun j => ((do
      copyAbs tag ⟨st.store.size, 1⟩ ⟨A, ao + row + m * IExp.var j⟩ ⟨st.store.size, 0⟩
      ifThenElse tag .lt scale ⟨st.store.size, 1⟩
        (ins (.copy tag scale ⟨st.store.size, 1⟩)) (pure ())) : Builder P ι ℕ ℕ Unit).run)
    (fun k s => R k s.store) (st := σ₂) h0 (fun k hk s hs => by
      exact exec_rowScale_step I h tag st m n row A ao scale x hin hAS hscale
        z hzero σ hσ hsh k hk s hs)
  obtain ⟨w, hread, hnonneg, hdom, hatt⟩ := hs.value
  have hnorm : dec tag w = ‖x‖ := by
    apply le_antisymm
    · rcases hatt with he | ⟨j, -, he⟩
      · rw [he]; exact norm_nonneg _
      · rw [he, ← Real.norm_eq_abs]; exact norm_le_pi_norm x j
    · apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hdom j j.isLt
  have hsize : out.store.size = st.store.size + 1 := by
    have he := Store.size_eq_of_shape_eq hs.shape
    simpa only [hσ, Array.size_push] using he
  have hwrite : st.store.write tag scale.buf scale.idx.eval w = some out.store.pop := by
    obtain ⟨s', hw'⟩ := Store.exists_write_eq_some_of_getElem?_shape w hlen
      (by simpa using hlt)
    suffices out.store.pop = s' by simpa only [this] using hw'
    apply Store.ext_of_shape_eq
    · rw [Store.shape_of_write_eq_some hw', Store.shape_pop, hs.shape, hσ]
      simp only [Store.shape, Array.map_push, Array.pop_push]
    · intro q b j
      by_cases he : b = scale.buf ∧ j = scale.idx.eval
      · obtain ⟨rfl, rfl⟩ := he
        by_cases hq : q = tag
        · subst q
          rw [Store.read_of_write_eq_some hw', Store.read_pop_of_lt (by omega), hread]
        · obtain ⟨len', hlen', -⟩ := Store.exists_getElem?_shape_of_read_eq_some hread
          rw [Store.read_eq_none_of_getElem?_shape_of_ne
            (by rw [Store.shape_pop, hs.shape, hσ]; simpa [Store.shape] using hlen) hq,
            Store.read_eq_none_of_getElem?_shape_of_ne
              ((Store.shape_of_write_eq_some hw').symm ▸ hlen) hq]
      · have hj : b ≠ scale.buf ∨ j ≠ scale.idx.eval := by tauto
        rw [Store.read_of_write_eq_some_of_ne hw' hj]
        by_cases hb : b < st.store.size
        · rw [Store.read_pop_of_lt (by omega), hs.frame q b j (by omega) hj,
            hσ, Store.read_push_of_lt hb]
        · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
            Store.read_eq_none_of_size_le (by omega)]
  refine ⟨out, ?_, w, hwrite, hnorm⟩
  change exec I (.seq (.instr (.lit tag ⟨st.store.size, 0⟩ 0)) _) σ = some out
  rw [exec_seq_instr_lit I hz hs₁]
  change exec I (.seq (.instr (.copy tag scale ⟨st.store.size, 0⟩)) _) σ₁ = some out
  rw [exec_seq_instr_copy I (st := σ₁) hread₁ hs₂]
  change exec I (.seq (.loop n _) .skip) σ₂ = some out
  rw [exec_seq_skip]; exact hr

private theorem exec_rowScale {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    (tag : P) (hsafe : safe tag 0) (st : St P K C) (m n row : IExp ℕ)
    (A : ℕ) (ao : IExp ℕ) (scale : Cell ℕ ℕ) (x : Fin n.eval → ℝ)
    (hin : ∀ j : Fin n.eval, ∃ w, st.store.read tag A
      (ao.eval + row.eval + m.eval * j.val) = some w ∧ dec tag w = x j)
    (hw : Writable st.store tag scale.buf scale.idx.eval 1)
    (hAS : 0 < n.eval → A ≠ scale.buf) :
    ∃ out w, exec I (rowScale tag m n row A ao scale).run st = some out ∧
      st.store.write tag scale.buf scale.idx.eval w = some out.store ∧ dec tag w = ‖x‖ := by
  obtain ⟨z, hz⟩ := h.lit_ok tag 0 (by simpa using hsafe)
  obtain ⟨δ, -, hdz⟩ := h.lit_err tag 0 z hz
  have hzero : dec tag z = 0 := by simpa using hdz
  have hscale : scale.buf < st.store.size := hw.lt_size (by omega)
  let Q : Store P K → Prop := fun s => ∃ w,
    st.store.write tag scale.buf scale.idx.eval w = some s ∧ dec tag w = ‖x‖
  have hbody := exec_rowScale_body I h tag st m n row A ao scale x hin hw hAS hscale
    z hz hzero
  obtain ⟨out, hr, w, hw', hdw⟩ := exists_exec_alloc I tag 2
    (fun scratch => ((do
      ins (.lit tag ⟨scratch, 0⟩ 0)
      ins (.copy tag scale ⟨scratch, 0⟩)
      forRange n fun j => do
        copyAbs tag ⟨scratch, 1⟩ ⟨A, ao + row + m * IExp.var j⟩ ⟨scratch, 0⟩
        ifThenElse tag .lt scale ⟨scratch, 1⟩
          (ins (.copy tag scale ⟨scratch, 1⟩)) (pure ())) : Builder P ι ℕ ℕ Unit).run)
    st Q hbody
  refine ⟨out, w, ?_, hw', hdw⟩
  change exec I (.seq (.alloc tag 2 _) .skip) st = some out
  rw [exec_seq_skip]; exact hr

/-- A rectangular stored matrix admits successful row-scale initialization under the standard
real scalar model whenever zero is safe. The decoded outputs are exactly the existing row
supremum norms, and one packed output block is the entire net store change. Input/output
separation is needed only for a nonempty input block. No exact-index or small-roundoff
hypothesis is needed. [Higham2002, §9.3]. -/
theorem IsRelErrSem.exec_rowScales {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    (tag : P) (hsafe : safe tag 0) (st : St P K C) (m n : IExp ℕ)
    (A : ℕ) (ao : IExp ℕ) (scales : ℕ) (so : IExp ℕ)
    (M : Matrix (Fin m.eval) (Fin n.eval) ℝ)
    (hM : HoldsDecoded st.store dec tag A ao.eval M)
    (hw : Writable st.store tag scales so.eval m.eval)
    (hAS : 0 < m.eval * n.eval → A ≠ scales) :
    ∃ (out : St P K C) (W : Fin m.eval → K),
      exec I (rowScales tag m n A ao scales so).run st = some out ∧
      st.store.writeBlock tag scales so.eval (Array.ofFn W) = some out.store ∧
      ∀ i, dec tag (W i) = ‖M i‖ := by
  obtain ⟨out, W, hr, hw', hd⟩ := exists_exec_loop_writeBlock I tag scales so.eval
    (fun i w => ∀ hi : i < m.eval, dec tag w = ‖M ⟨i, hi⟩‖)
    (n := m) (body := fun i => (rowScale tag m n (.var i) A ao
      ⟨scales, so + .var i⟩).run) (st := st) (by
      intro i hi ys s hys hQ hwrite
      have hM' : HoldsDecoded s.store dec tag A ao.eval M :=
        hM.of_writeBlock hwrite (fun hmn _ => by
          simp only [blockDisjoint]; simp [hAS hmn])
      have hw' := hw.of_shape_eq (Store.shape_of_writeBlock_eq_some hwrite)
      obtain ⟨last, w, hr, hw'', hd⟩ := exec_rowScale I h tag hsafe s m n (.var i) A ao
        ⟨scales, so + .var i⟩ (M ⟨i, hi⟩)
        (fun j => by simpa only [IExp.eval_var] using hM' ⟨i, hi⟩ j)
        (by intro j hj; have hj0 : j = 0 := by omega
            subst j
            obtain ⟨len, hlen, hlt⟩ := hw' i hi
            exact ⟨len, hlen, by simpa only [IExp.eval_add, IExp.eval_var, Nat.add_zero] using hlt⟩)
        (fun hn => hAS (Nat.mul_pos (by omega) hn))
      exact ⟨last, w, hr, by simpa only [IExp.eval_add, IExp.eval_var] using hw'',
        fun _ => hd⟩)
  refine ⟨out, W, ?_, hw', fun i => hd i i.isLt⟩
  change exec I (.seq (.loop m _) .skip) st = some out
  rw [exec_seq_skip]; exact hr

end NLAlib.Computation
