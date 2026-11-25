/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.SwapCells
public import NLAlib.Computation.MatrixStorage
public import NLAlib.Computation.IndexBinder
public import Mathlib.LinearAlgebra.Matrix.Swap

/-!
# Stored column exchanges

A rectangular packed column-major matrix exchanges two columns with three exact copies per
row and one scoped scratch word. The common scalar exchange is shared with the row routine.
Coincident columns are valid, and zero rows perform no source reads.

## Main definitions

* `NLAlib.Computation.swapColumns`: one-scratch rectangular column exchange.

## Main results

* `NLAlib.Computation.exec_swapColumns`: exact words and one packed output block.
* `NLAlib.Computation.exec_swapColumns_of_zero_rows`: empty execution without source handles.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Exchange two columns of an $m\times n$ packed column-major matrix. Three exact copies
per row reuse one scoped scratch word. Equal columns preserve their actual words.
[GolubVanLoan2013, §3.4]. -/
def swapColumns {P ι VB VI : Type} (tag : P) (m _n : IExp VI) (A : VB)
    (off c d : IExp VI) : Builder P ι VB VI Unit := scope do
  let tmp ← alloc tag 1
  forRange m fun i =>
    swapCells tag ⟨tmp, 0⟩ ⟨A, off + .var i + m * c⟩ ⟨A, off + .var i + m * d⟩

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The column exchange releases its scratch before any following builder. -/
theorem executionComposable_swapColumns (I : Interp P ι K C) (tag : P)
    (m n : IExp ℕ) (A : ℕ) (off c d : IExp ℕ) :
    ExecutionComposable I (swapColumns tag m n A off c d) :=
  executionComposable_single I (fun _ => rfl)

namespace ColumnSwap

private def exchangedPrefix {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (c d : Fin n) (k : ℕ) : Matrix (Fin m) (Fin n) K :=
  fun i j => if (i : ℕ) < k then A i (Equiv.swap c d j) else A i j

private theorem holds_exchangedPrefix_succ {m n : ℕ} {A : Matrix (Fin m) (Fin n) K}
    (c d : Fin n) {k : ℕ} (hk : k < m) {before after : Store P K} {p : P} {buf off : ℕ}
    (hA : Holds before p buf off (exchangedPrefix A c d k))
    (hread : ∀ idx, after.read p buf idx =
      if idx = off + k + m * d then some (A ⟨k, hk⟩ c)
      else if idx = off + k + m * c then some (A ⟨k, hk⟩ d)
      else before.read p buf idx) :
    Holds after p buf off (exchangedPrefix A c d (k + 1)) := by
  intro i j
  rw [hread]
  have heqd : off + i + m * j = off + k + m * d ↔ i = ⟨k, hk⟩ ∧ j = d := by
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_cancel_iff]
    constructor
    · intro h
      obtain ⟨hi, hj⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i.isLt hk).mp h
      exact ⟨Fin.ext hi, Fin.ext hj⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have heqc : off + i + m * j = off + k + m * c ↔ i = ⟨k, hk⟩ ∧ j = c := by
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_left_cancel_iff]
    constructor
    · intro h
      obtain ⟨hi, hj⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i.isLt hk).mp h
      exact ⟨Fin.ext hi, Fin.ext hj⟩
    · rintro ⟨rfl, rfl⟩; rfl
  by_cases hi : i = ⟨k, hk⟩
  · subst i
    simp only [heqd, heqc, true_and]
    by_cases hjd : j = d
    · subst j
      simp only [exchangedPrefix, Nat.lt_succ_self, if_true, Equiv.swap_apply_right]
    · by_cases hjc : j = c
      · subst j
        simp only [hjd, if_false, exchangedPrefix, Nat.lt_succ_self, if_true,
          Equiv.swap_apply_left]
      · rw [if_neg hjd, if_neg hjc, hA ⟨k, hk⟩ j]
        simp only [exchangedPrefix, lt_self_iff_false, if_false, Nat.lt_succ_self, if_true,
          Equiv.swap_apply_of_ne_of_ne hjc hjd]
  · rw [if_neg (by rw [heqd]; exact fun h => hi h.1),
      if_neg (by rw [heqc]; exact fun h => hi h.1), hA]
    have hik : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
    have hiff : (i : ℕ) < k + 1 ↔ (i : ℕ) < k := by omega
    simp only [exchangedPrefix, hiff]

private theorem exec_body (I : Interp P ι K C) (p : P)
    (m n : IExp ℕ) (buf T : ℕ) (off c d : IExp ℕ) (st : St P K C)
    {base : Store P K} (A : Matrix (Fin m.eval) (Fin n.eval) K)
    (hc : c.eval < n.eval) (hd : d.eval < n.eval) (hT : base.shape[T]? = some (p, 1))
    (hAT : 0 < m.eval → buf ≠ T) (hA : Holds st.store p buf off.eval A)
    (hF : ∃ g, Store.BlockFrame base p T buf off.eval (m.eval * n.eval) st.store g) :
    ∃ out g, exec I (.loop m fun i => (swapCells p ⟨T, 0⟩
      ⟨buf, .const (off.eval + i + m.eval * c.eval)⟩
      ⟨buf, .const (off.eval + i + m.eval * d.eval)⟩).run) st = some out ∧
      Store.BlockFrame base p T buf off.eval (m.eval * n.eval) out.store g ∧
      Holds out.store p buf off.eval
        (A.submatrix id (Equiv.swap ⟨c.eval, hc⟩ ⟨d.eval, hd⟩)) := by
  let R := fun k (σ : St P K C) =>
    (∃ g, Store.BlockFrame base p T buf off.eval (m.eval * n.eval) σ.store g) ∧
    Holds σ.store p buf off.eval (exchangedPrefix A ⟨c.eval, hc⟩ ⟨d.eval, hd⟩ k)
  have h0 : R 0 st := ⟨hF, fun i j => by
    simpa only [exchangedPrefix, Nat.not_lt_zero, if_false] using hA i j⟩
  obtain ⟨out, hrun, ⟨g, hg⟩, hAout⟩ := exists_exec_loop_eq_some_of_forall I R h0
    (fun i hi σ hR => by
      obtain ⟨⟨g, hg⟩, hB⟩ := hR
      have hx := hB ⟨i, hi⟩ ⟨c.eval, hc⟩
      have hy := hB ⟨i, hi⟩ ⟨d.eval, hd⟩
      simp only [exchangedPrefix, lt_self_iff_false, if_false] at hx hy
      obtain ⟨out, hrun, hframe, hreads⟩ := exec_swapCells_inBlock I p σ hg hT
        (hAT (by omega)) (Nat.add_mul_lt_mul_of_lt_of_lt hi hc)
        (Nat.add_mul_lt_mul_of_lt_of_lt hi hd)
        (by simpa only [Nat.add_assoc] using hx) (by simpa only [Nat.add_assoc] using hy)
      refine ⟨out, ?_, ⟨_, hframe⟩,
        holds_exchangedPrefix_succ ⟨c.eval, hc⟩ ⟨d.eval, hd⟩ hi hB ?_⟩
      · simpa only [Nat.add_assoc] using hrun
      · simpa only [Nat.add_assoc] using hreads)
  refine ⟨out, g, ?_, hg, fun i j => by
    simpa only [exchangedPrefix, i.isLt, if_true, Matrix.submatrix_apply, id_eq] using hAout i j⟩
  simpa only [Nat.add_assoc] using hrun

end ColumnSwap

/-- A stored rectangular column exchange succeeds under every interpretation and writes one
complete packed output block. No arithmetic or index conversion accuracy is required. The
column indices are valid even when the row dimension is zero; then no source handle is read.
Coincident columns preserve the actual stored words. -/
theorem exec_swapColumns (I : Interp P ι K C) (p : P) (st : St P K C)
    (m n : IExp ℕ) (buf : ℕ) (off c d : IExp ℕ)
    (A : Matrix (Fin m.eval) (Fin n.eval) K) (hc : c.eval < n.eval) (hd : d.eval < n.eval)
    (hA : Holds st.store p buf off.eval A) :
    ∃ (out : St P K C) (W : Fin (m.eval * n.eval) → K),
      exec I (swapColumns p m n buf off c d).run st = some out ∧
      st.store.writeBlock p buf off.eval (Array.ofFn W) = some out.store ∧
      Holds out.store p buf off.eval
        (A.submatrix id (Equiv.swap ⟨c.eval, hc⟩ ⟨d.eval, hd⟩)) := by
  let B := A.submatrix id (Equiv.swap ⟨c.eval, hc⟩ ⟨d.eval, hd⟩)
  have hbuf : 0 < m.eval → buf < st.store.size := fun hm =>
    Store.lt_size_of_read_eq_some (hA ⟨0, hm⟩ ⟨c.eval, hc⟩)
  obtain ⟨out, hrun, W, hwrite, hB⟩ := exists_exec_alloc I p 1 (fun T =>
      .seq (.loop m fun i => (swapCells p ⟨T, 0⟩ ⟨buf, off + .var i + m * c⟩
        ⟨buf, off + .var i + m * d⟩).run) .skip)
    st (fun store => ∃ W : Fin (m.eval * n.eval) → K,
      st.store.writeBlock p buf off.eval (Array.ofFn W) = some store ∧
      Holds store p buf off.eval B) (by
        intro σ hσ
        have hAp : Holds σ.store p buf off.eval A := fun i j => by
          rw [hσ, Store.read_push_of_lt (hbuf (Nat.zero_lt_of_lt i.isLt))]
          exact hA i j
        have hF : ∃ g, Store.BlockFrame σ.store p st.store.size buf off.eval
            (m.eval * n.eval) σ.store g := ⟨fun t => σ.store.read p buf (off.eval + t),
          rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
        obtain ⟨out, g, hrun, hframe, hB⟩ := ColumnSwap.exec_body I p m n buf st.store.size
          off c d σ A hc hd (hσ ▸ Store.getElem?_shape_push_size st.store p 1)
          (fun hm => Nat.ne_of_lt (hbuf hm)) hAp hF
        refine ⟨out, ?_, ?_⟩
        · rw [exec_seq_skip, ← exec_normIdx I _ σ]
          rw [← exec_normIdx I _ σ] at hrun
          exact hrun
        · exact hA.writeBlock_of_blockFrame_pop (hσ ▸ hframe) hB)
  refine ⟨out, W, ?_, hwrite, hB⟩
  change exec I (.seq _ .skip) st = some out
  rw [exec_seq_skip]
  exact hrun

/-- With zero rows, exchanging arbitrary column expressions succeeds without reading any
matrix handle or checking either column index. This includes zero columns and invalid source
handles. The only scoped allocation is released and the store is unchanged. -/
theorem exec_swapColumns_of_zero_rows (I : Interp P ι K C) (p : P) (st : St P K C)
    (m n : IExp ℕ) (buf : ℕ) (off c d : IExp ℕ) (hm : m.eval = 0) :
    ∃ out, exec I (swapColumns p m n buf off c d).run st = some out ∧
      out.store = st.store ∧ st.store.writeBlock p buf off.eval #[] = some out.store := by
  obtain ⟨out, he, hstore⟩ := exists_exec_alloc I p 1 (fun T =>
      .seq (.loop m fun i => (swapCells p ⟨T, 0⟩ ⟨buf, off + .var i + m * c⟩
        ⟨buf, off + .var i + m * d⟩).run) .skip) st (fun s => s = st.store) (by
      intro σ hσ
      refine ⟨σ, ?_, ?_⟩
      · simp only [exec_seq_skip, exec_loop, hm, List.range_zero, List.foldlM_nil,
          Option.pure_def]
      · rw [hσ]; exact Array.pop_push)
  refine ⟨out, ?_, hstore, ?_⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip]; exact he
  · rw [hstore]
    exact Store.writeBlock_eq_some_of_size_eq_zero rfl

end NLAlib.Computation
