/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Fin.Embedding
public import NLAlib.Computation.CopyStride
public import NLAlib.Computation.IndexBinder
public import NLAlib.Matrix.Computation.PivotScan

/-!
# Strided magnitude selection

A strided input is packed by word copies before the existing stable magnitude scan. This
provides row selection in column-major matrices without duplicating the scan or its scalar
comparison proof. The packed words are scoped and the sole net write is the selected index.

## Main definitions

* `NLAlib.Computation.argmaxStridedAbs`: first magnitude maximum of a strided vector.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_argmaxStridedAbs`: successful stable selection and frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Pack a strided vector, select its first magnitude maximum and release the packed copy.
The result is an exact relative index in the nonempty source vector. -/
def argmaxStridedAbs {P ι VB VI : Type} (tag : P) (n : IExp VI) (src : VB)
    (so stride : IExp VI) (index : Cell VB VI) : Builder P ι VB VI Unit := scope do
  let packed ← alloc tag n
  copyStride tag n src packed so stride 0
  argmaxAbs tag n packed 0 index

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The strided selector releases its packed vector before a following builder. -/
theorem executionComposable_argmaxStridedAbs (I : Interp P ι K C) (tag : P)
    (n : IExp ℕ) (src : ℕ) (so stride : IExp ℕ) (index : Cell ℕ ℕ) :
    ExecutionComposable I (argmaxStridedAbs tag n src so stride index) :=
  executionComposable_single I (fun _ => rfl)

/-- Packing and the stable scan succeed under exact comparisons and exact natural literals.
Only the output index cell changes; arbitrary strided source words are retained when their
buffer is distinct from the index buffer. No division or magnitude squaring is executed. -/
theorem IsRelErrSem.exec_argmaxStridedAbs {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (hn : 0 < n.eval)
    (tag : P) (st : St P K C) (x : Fin n.eval → ℝ) (src : ℕ)
    (so stride : IExp ℕ) (index : Cell ℕ ℕ)
    (hin : ∀ i : Fin n.eval, ∃ w,
      st.store.read tag src (so.eval + stride.eval * i) = some w ∧ dec tag w = x i)
    (hw : Writable st.store tag index.buf index.idx.eval 1) :
    ∃ (out : St P K C) (w : K) (chosen : Fin n.eval),
      exec I (argmaxStridedAbs tag n src so stride index).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[w] = some out.store ∧
      dec tag w = chosen.val ∧ (∀ j : Fin n.eval, |x j| ≤ |x chosen|) ∧
      (∀ j : Fin n.eval, j < chosen → |x j| < |x chosen|) := by
  choose words hread hdec using hin
  have hsrc : src < st.store.size := Store.lt_size_of_read_eq_some (hread ⟨0, hn⟩)
  have hidx : index.buf < st.store.size := hw.lt_size (by omega)
  let Q : Store P K → Prop := fun s => ∃ w chosen,
    st.store.writeBlock tag index.buf index.idx.eval #[w] = some s ∧
    dec tag w = (chosen : Fin n.eval).val ∧ (∀ j, |x j| ≤ |x chosen|) ∧
    (∀ j, j < chosen → |x j| < |x chosen|)
  have hbody : ∀ σ : St P K C,
      σ.store = st.store.push (tag, Array.replicate n.eval none) →
      ∃ out, exec I (do
        copyStride tag n src st.store.size so stride 0
        argmaxAbs tag n st.store.size 0 index).run σ = some out ∧ Q out.store.pop := by
    intro σ hσ
    have hwpack : Writable σ.store tag st.store.size 0 n.eval := by
      rw [hσ]
      intro i hi
      exact ⟨n.eval, Store.getElem?_shape_push_size _ _ _, by omega⟩
    obtain ⟨mid, hr₁, hs₁⟩ := exec_copyStride I tag σ n src st.store.size so stride 0
      words (by omega) (fun i => by rw [hσ, Store.read_push_of_lt hsrc]; exact hread i)
      hwpack
    have hpacked : ReadsDecoded mid.store dec tag st.store.size 0 x := by
      intro i
      refine ⟨words i, ?_, hdec i⟩
      have hr := Store.read_of_writeBlock_eq_some_of_lt hs₁ (j := i.val)
        (by simp only [Array.size_ofFn]; exact i.isLt)
      rw [Array.getElem?_eq_getElem (by simp only [Array.size_ofFn]; exact i.isLt),
        Array.getElem_ofFn] at hr
      simpa only [IExp.eval, Nat.zero_add] using hr
    have hwMid : Writable mid.store tag index.buf index.idx.eval 1 := by
      exact (hσ ▸ hw.push (tag, Array.replicate n.eval none)).of_shape_eq
        (Store.shape_of_writeBlock_eq_some hs₁)
    obtain ⟨out, w, r, hr₂, hs₂, hd, hm, hf⟩ := h.exec_argmaxAbs I hi.intLit le_rfl hn
      tag mid x st.store.size 0 index hpacked hwMid (by omega)
    have hr₂' : exec I (argmaxAbs tag n st.store.size 0 index).run mid = some out :=
      (exec_eq_of_normIdx_eq I
        (s := (argmaxAbs tag n st.store.size 0 index).run)
        (s' := (argmaxAbs tag (.const n.eval) st.store.size 0 index).run) rfl mid).trans hr₂
    have hpop : mid.store.pop = st.store := by
      rw [Store.pop_of_writeBlock_top hs₁ (by rw [hσ]; simp), hσ]
      exact Array.pop_push
    have hwrite := Store.writeBlock_pop_of_lt hs₂ (by
      intro _
      have := Store.size_eq_of_shape_eq (Store.shape_of_writeBlock_eq_some hs₁)
      rw [hσ] at this
      simp only [Array.size_push] at this
      omega)
    rw [hpop] at hwrite
    refine ⟨out, ?_, w, r, hwrite, hd, hm, hf⟩
    rw [exec_run_bind I (b := copyStride tag n src st.store.size so stride 0)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂'
  obtain ⟨out, hr, w, r, hs, hd, hm, hf⟩ := exists_exec_alloc I tag n
    (fun packed => ((do
      copyStride tag n src packed so stride 0
      argmaxAbs tag n packed 0 index) : Builder P ι ℕ ℕ Unit).run) st Q hbody
  refine ⟨out, w, r, ?_, hs, hd, hm, hf⟩
  change exec I (.seq (.alloc tag n _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- A strided row suffix of a packed column-major square matrix is selected by the same
stable word-packing scan. The output is its relative column index and the sole net write. -/
theorem IsRelErrSem.exec_argmaxStridedAbs_row {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k row : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (st : St P K C) (A : ℕ) (off : IExp ℕ) (index : Cell ℕ ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (htail : n.eval - k.eval ≤ n.eval)
    (hr : row.eval < n.eval) (hM : HoldsDecoded st.store dec tag A off.eval M)
    (hw : Writable st.store tag index.buf index.idx.eval 1) :
    ∃ (out : St P K C) (w : K) (c : Fin (n.eval - k.eval)),
      exec I (argmaxStridedAbs tag (n - k) A (off + row + n * k) n index).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[w] = some out.store ∧
      dec tag w = c.val ∧
      (∀ j : Fin (n.eval - k.eval),
        |M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) j)| ≤
          |M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) c)|) ∧
      (∀ j : Fin (n.eval - k.eval), j < c →
        |M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) j)| <
          |M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) c)|) := by
  let x : Fin (n.eval - k.eval) → ℝ := fun j =>
    M ⟨row.eval, hr⟩ ((Fin.natAdd_castLEEmb (htail)) j)
  apply h.exec_argmaxStridedAbs I (n - k) (hi.mono (Nat.sub_le _ _))
    (Nat.sub_pos_of_lt hk) tag st x A (off + row + n * k) n index ?_ hw
  intro j
  obtain ⟨w, hwj, hdw⟩ := hM ⟨row.eval, hr⟩
    ((Fin.natAdd_castLEEmb (htail)) j)
  refine ⟨w, ?_, hdw⟩
  have hj := Fin.val_natAdd_castLEEmb_sub k.eval (htail) j
  simpa only [hj, IExp.eval_add, IExp.eval_mul, Nat.mul_add, Nat.add_assoc] using hwj

end NLAlib.Computation
