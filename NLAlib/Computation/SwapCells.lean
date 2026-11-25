/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames

/-!
# Stored scalar exchanges

Three exact word copies exchange two readable cells using one caller-owned writable scratch
cell. The exchanged cells may coincide. The scratch is distinct from both cells; callers
reuse it across a loop and release it in their enclosing scope. No scalar arithmetic or
index-decoding contract is needed.

## Main definitions

* `NLAlib.Computation.swapCells`: three copies using caller-owned scratch.

## Main results

* `NLAlib.Computation.exec_swapCells`: actual success and the three exact scalar writes.
* `NLAlib.Computation.exec_swapCells_inBlock`: the corresponding initialized-block frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Exchange two stored words using a caller-owned scratch cell, in the order scratch from
left, left from right, right from scratch. The scratch is reused without allocating; the two
exchanged cells may coincide. -/
def swapCells {P ι VB VI : Type} (tag : P) (tmp left right : Cell VB VI) :
    Builder P ι VB VI Unit := do
  ins (.copy tag tmp left)
  ins (.copy tag left right)
  ins (.copy tag right tmp)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The scalar exchange composes with a following builder under every interpretation. -/
theorem executionComposable_swapCells (I : Interp P ι K C) (tag : P)
    (tmp left right : Cell ℕ ℕ) : ExecutionComposable I (swapCells tag tmp left right) :=
  (executionComposable_single I (b := ins (.copy tag tmp left)) (fun _ => rfl)).bind
    ((executionComposable_single I (b := ins (.copy tag left right)) (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl)))

/-- Two readable words and a writable scratch cell distinct from both suffice for actual
exchange under every interpretation. The ordered three writes expose the exact generic-word
behavior, including coincident exchanged cells. All other reads at every tag and the shape
are retained. -/
theorem exec_swapCells (I : Interp P ι K C) (tag : P) (st : St P K C)
    (tmp left right : Cell ℕ ℕ) (x y : K)
    (hx : st.store.read tag left.buf left.idx.eval = some x)
    (hy : st.store.read tag right.buf right.idx.eval = some y)
    (hw : Writable st.store tag tmp.buf tmp.idx.eval 1)
    (htl : tmp.buf ≠ left.buf ∨ tmp.idx.eval ≠ left.idx.eval)
    (htr : tmp.buf ≠ right.buf ∨ tmp.idx.eval ≠ right.idx.eval) :
    ∃ (out : St P K C) (s₁ s₂ : Store P K),
      exec I (swapCells tag tmp left right).run st = some out ∧
      st.store.write tag tmp.buf tmp.idx.eval x = some s₁ ∧
      s₁.write tag left.buf left.idx.eval y = some s₂ ∧
      s₂.write tag right.buf right.idx.eval x = some out.store ∧
      out.store.shape = st.store.shape ∧
      ∀ q b i, (b ≠ tmp.buf ∨ i ≠ tmp.idx.eval) →
        (b ≠ left.buf ∨ i ≠ left.idx.eval) →
        (b ≠ right.buf ∨ i ≠ right.idx.eval) →
        out.store.read q b i = st.store.read q b i := by
  obtain ⟨len, hlen, hlt⟩ := hw 0 (by omega)
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_getElem?_shape x hlen (by simpa using hlt)
  have hy₁ : s₁.read tag right.buf right.idx.eval = some y := by
    rw [Store.read_of_write_eq_some_of_ne hs₁ (htr.imp Ne.symm Ne.symm)]; exact hy
  obtain ⟨lenL, hlenL, hltL⟩ := Store.exists_getElem?_shape_of_read_eq_some hx
  obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_getElem?_shape y
    ((Store.shape_of_write_eq_some hs₁).symm ▸ hlenL) hltL
  have hx₂ : s₂.read tag tmp.buf tmp.idx.eval = some x := by
    rw [Store.read_of_write_eq_some_of_ne hs₂ htl]; exact Store.read_of_write_eq_some hs₁
  obtain ⟨lenR, hlenR, hltR⟩ := Store.exists_getElem?_shape_of_read_eq_some hy
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape x
    (((Store.shape_of_write_eq_some hs₂).trans
      (Store.shape_of_write_eq_some hs₁)).symm ▸ hlenR) hltR
  let out : St P K C := { st with store := s₃, cnt :=
    ((st.cnt + I.charge (.copy tag)) + I.charge (.copy tag)) + I.charge (.copy tag) }
  refine ⟨out, s₁, s₂, ?_, hs₁, hs₂, hs₃, (Store.shape_of_write_eq_some hs₃).trans
    ((Store.shape_of_write_eq_some hs₂).trans (Store.shape_of_write_eq_some hs₁)), ?_⟩
  · change exec I (.seq (.instr (.copy tag tmp left))
      (.seq (.instr (.copy tag left right)) (.seq (.instr (.copy tag right tmp)) .skip)))
        st = some out
    rw [exec_seq_instr_copy I hx hs₁, exec_seq_instr_copy I hy₁ hs₂,
      exec_seq_instr_copy I hx₂ hs₃, exec_skip]
  · intro q b i ht hl hr
    rw [Store.read_of_write_eq_some_of_ne hs₃ hr,
      Store.read_of_write_eq_some_of_ne hs₂ hl, Store.read_of_write_eq_some_of_ne hs₁ ht]

/-- Within an initialized block, the same three copies preserve its frame and exchange the
specified words. The two block offsets may coincide; the scratch is a distinct buffer and
may be reused by subsequent exchanges. -/
theorem exec_swapCells_inBlock (I : Interp P ι K C) (tag : P) (st : St P K C)
    {base : Store P K} {T A off len a b : ℕ} {g : ℕ → Option K} {x y : K}
    (hF : Store.BlockFrame base tag T A off len st.store g)
    (hT : base.shape[T]? = some (tag, 1)) (hAT : A ≠ T)
    (ha : a < len) (hb : b < len)
    (hx : st.store.read tag A (off + a) = some x)
    (hy : st.store.read tag A (off + b) = some y) :
    ∃ out, exec I (swapCells tag ⟨T, 0⟩ ⟨A, .const (off + a)⟩
      ⟨A, .const (off + b)⟩).run st = some out ∧
      Store.BlockFrame base tag T A off len out.store
        (Function.update (Function.update g a (some y)) b (some x)) ∧
      ∀ idx, out.store.read tag A idx =
        if idx = off + b then some x else if idx = off + a then some y
        else st.store.read tag A idx := by
  obtain ⟨out, s₁, s₂, he, hs₁, hs₂, hs₃, -, -⟩ := exec_swapCells I tag st
    ⟨T, 0⟩ ⟨A, .const (off + a)⟩ ⟨A, .const (off + b)⟩ x y hx hy
    (fun i hi => ⟨1, hF.1 ▸ hT, by simp only [IExp.eval_zero]; omega⟩)
    (Or.inl hAT.symm) (Or.inl hAT.symm)
  change st.store.write tag T 0 x = some s₁ at hs₁
  change s₁.write tag A (off + a) y = some s₂ at hs₂
  change s₂.write tag A (off + b) x = some out.store at hs₃
  refine ⟨out, he, ((hF.write_scratch (fun _ => hAT) hs₁).write_of_lt ha hs₂).write_of_lt
    hb hs₃, fun idx => ?_⟩
  split_ifs with hbi hai
  · subst idx; exact Store.read_of_write_eq_some hs₃
  · subst idx
    rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inr hbi), Store.read_of_write_eq_some hs₂]
  · rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inr hbi),
      Store.read_of_write_eq_some_of_ne hs₂ (Or.inr hai),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hAT)]

end NLAlib.Computation
