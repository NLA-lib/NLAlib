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
# Stored row exchanges

Row exchanges on a column-major rectangular matrix use three copies per column and one scoped
scratch word. They preserve the actual stored words under every scalar interpretation, including
when the two rows coincide. These are the exchanges needed by pivoted dense factorizations.

## Main results

* `NLAlib.Computation.executionComposable_swapRows`: exchanges compose with their consumer.
* `NLAlib.Computation.exec_swapRows`: successful execution and the complete output block write.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Exchange two rows of an $m\times n$ matrix stored column-major from `off`. Every column
uses a temporary copy, so exchanging a row with itself preserves its words. Scratch is scoped.
[GolubVanLoan2013, §3.4]. -/
def swapRows {P ι VB VI : Type} (tag : P) (m n : IExp VI) (A : VB)
    (off r s : IExp VI) : Builder P ι VB VI Unit := scope do
  let tmp ← alloc tag 1
  forRange n fun j => do
    swapCells tag ⟨tmp, 0⟩ ⟨A, off + r + m * .var j⟩ ⟨A, off + s + m * .var j⟩

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A row exchange composes with the following program for every interpretation. -/
theorem executionComposable_swapRows (I : Interp P ι K C) (tag : P)
    (m n : IExp ℕ) (A : ℕ) (off r s : IExp ℕ) :
    ExecutionComposable I (swapRows tag m n A off r s) :=
  executionComposable_single I (fun _ => rfl)

private def exchangedPrefix {m n : ℕ} (A : Matrix (Fin m) (Fin n) K)
    (r s : Fin m) (k : ℕ) : Matrix (Fin m) (Fin n) K :=
  fun i j => if (j : ℕ) < k then A (Equiv.swap r s i) j else A i j

private theorem holds_exchangedPrefix_succ {m n : ℕ} {A : Matrix (Fin m) (Fin n) K}
    (r s : Fin m) {k : ℕ} (hk : k < n) {before after : Store P K} {p : P} {buf off : ℕ}
    (hA : Holds before p buf off (exchangedPrefix A r s k))
    (hread : ∀ idx, after.read p buf idx =
      if idx = off + s + m * k then some (A r ⟨k, hk⟩)
      else if idx = off + r + m * k then some (A s ⟨k, hk⟩)
      else before.read p buf idx) :
    Holds after p buf off (exchangedPrefix A r s (k + 1)) := by
  intro i j
  rw [hread]
  have heqs : off + i + m * j = off + s + m * k ↔ i = s ∧ j = ⟨k, hk⟩ := by
    simpa only [Nat.add_assoc, Nat.add_left_cancel_iff, Fin.ext_iff] using
      (Nat.add_mul_eq_add_mul_iff_of_lt (j := (j : ℕ)) (j' := k) i.isLt s.isLt)
  have heqr : off + i + m * j = off + r + m * k ↔ i = r ∧ j = ⟨k, hk⟩ := by
    simpa only [Nat.add_assoc, Nat.add_left_cancel_iff, Fin.ext_iff] using
      (Nat.add_mul_eq_add_mul_iff_of_lt (j := (j : ℕ)) (j' := k) i.isLt r.isLt)
  by_cases hj : j = ⟨k, hk⟩
  · subst j
    simp only [heqs, heqr, and_true]
    by_cases his : i = s
    · subst i
      simp only [exchangedPrefix, Nat.lt_succ_self, if_true,
        Equiv.swap_apply_right]
    · by_cases hir : i = r
      · subst i
        simp only [his, if_false, exchangedPrefix, Nat.lt_succ_self, if_true,
          Equiv.swap_apply_left]
      · rw [if_neg his, if_neg hir, hA i ⟨k, hk⟩]
        simp only [exchangedPrefix, lt_self_iff_false, if_false, Nat.lt_succ_self, if_true,
          Equiv.swap_apply_of_ne_of_ne hir his]
  · rw [if_neg (by rw [heqs]; exact fun h => hj h.2),
      if_neg (by rw [heqr]; exact fun h => hj h.2), hA]
    have hjk : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
    have hiff : (j : ℕ) < k + 1 ↔ (j : ℕ) < k := by omega
    simp only [exchangedPrefix, hiff]

private theorem exists_swapRows_body (I : Interp P ι K C) (p : P)
    (m n : IExp ℕ) (buf T : ℕ) (off r s : IExp ℕ) (st : St P K C)
    {base : Store P K} (A : Matrix (Fin m.eval) (Fin n.eval) K)
    (hr : r.eval < m.eval) (hs : s.eval < m.eval) (hT : base.shape[T]? = some (p, 1))
    (hAT : 0 < n.eval → buf ≠ T) (hA : Holds st.store p buf off.eval A)
    (hF : ∃ g, Store.BlockFrame base p T buf off.eval (m.eval * n.eval) st.store g) :
    ∃ out g, exec I (.loop n fun j => (swapCells p ⟨T, 0⟩
      ⟨buf, .const (off.eval + r.eval + m.eval * j)⟩
      ⟨buf, .const (off.eval + s.eval + m.eval * j)⟩).run) st = some out ∧
      Store.BlockFrame base p T buf off.eval (m.eval * n.eval) out.store g ∧
      Holds out.store p buf off.eval (A.submatrix (Equiv.swap ⟨r.eval, hr⟩ ⟨s.eval, hs⟩) id) := by
  let R := fun k (σ : St P K C) =>
    (∃ g, Store.BlockFrame base p T buf off.eval (m.eval * n.eval) σ.store g) ∧
    Holds σ.store p buf off.eval (exchangedPrefix A ⟨r.eval, hr⟩ ⟨s.eval, hs⟩ k)
  have h0 : R 0 st := ⟨hF, fun i j => by
    simpa only [exchangedPrefix, Nat.not_lt_zero, if_false] using hA i j⟩
  obtain ⟨out, hrun, ⟨g, hg⟩, hAout⟩ := exists_exec_loop_eq_some_of_forall I R h0
    (fun j hj σ hR => by
      obtain ⟨⟨g, hg⟩, hB⟩ := hR
      have hx := hB ⟨r.eval, hr⟩ ⟨j, hj⟩
      have hy := hB ⟨s.eval, hs⟩ ⟨j, hj⟩
      simp only [exchangedPrefix, lt_self_iff_false, if_false] at hx hy
      obtain ⟨out, hrun, hframe, hreads⟩ := exec_swapCells_inBlock I p σ hg hT (hAT (by omega))
        (Nat.add_mul_lt_mul_of_lt_of_lt hr hj) (Nat.add_mul_lt_mul_of_lt_of_lt hs hj)
        (by simpa only [Nat.add_assoc] using hx) (by simpa only [Nat.add_assoc] using hy)
      refine ⟨out, ?_, ⟨_, hframe⟩,
        holds_exchangedPrefix_succ ⟨r.eval, hr⟩ ⟨s.eval, hs⟩ hj hB ?_⟩
      · simpa only [Nat.add_assoc] using hrun
      · simpa only [Nat.add_assoc] using hreads)
  refine ⟨out, g, ?_, hg, fun i j => by
    simpa only [exchangedPrefix, j.isLt, if_true, Matrix.submatrix_apply, id_eq] using hAout i j⟩
  simpa only [Nat.add_assoc] using hrun

/-- A stored rectangular row exchange succeeds for every interpretation and writes exactly one
packed output block, whose entries are the input entries with the two rows exchanged. The
indices and offset are index expressions, and the input words may have any carrier. No numerical
or index-conversion accuracy assumption is needed; the row indices must be in range. -/
theorem exec_swapRows (I : Interp P ι K C) (p : P) (st : St P K C)
    (m n : IExp ℕ) (buf : ℕ) (off r s : IExp ℕ)
    (A : Matrix (Fin m.eval) (Fin n.eval) K) (hr : r.eval < m.eval) (hs : s.eval < m.eval)
    (hA : Holds st.store p buf off.eval A) :
    ∃ (out : St P K C) (W : Fin (m.eval * n.eval) → K),
      exec I (swapRows p m n buf off r s).run st = some out ∧
      st.store.writeBlock p buf off.eval (Array.ofFn W) = some out.store ∧
      Holds out.store p buf off.eval
        (A.submatrix (Equiv.swap ⟨r.eval, hr⟩ ⟨s.eval, hs⟩) id) := by
  let B := A.submatrix (Equiv.swap ⟨r.eval, hr⟩ ⟨s.eval, hs⟩) id
  have hbuf : 0 < n.eval → buf < st.store.size := fun hn =>
    Store.lt_size_of_read_eq_some (hA ⟨r.eval, hr⟩ ⟨0, hn⟩)
  have halloc := exists_exec_alloc I p 1 (fun T =>
      .seq (.loop n fun j => .seq (.instr (.copy p ⟨T, 0⟩
        ⟨buf, off + r + m * .var j⟩)) (.seq (.instr (.copy p
          ⟨buf, off + r + m * .var j⟩ ⟨buf, off + s + m * .var j⟩))
            (.seq (.instr (.copy p ⟨buf, off + s + m * .var j⟩ ⟨T, 0⟩)) .skip))) .skip)
    st (fun store => ∃ W : Fin (m.eval * n.eval) → K,
      st.store.writeBlock p buf off.eval (Array.ofFn W) = some store ∧
      Holds store p buf off.eval B) (by
        intro σ hσ
        have hAp : Holds σ.store p buf off.eval A := fun i j => by
          rw [hσ, Store.read_push_of_lt (hbuf (Nat.zero_lt_of_lt j.isLt))]
          exact hA i j
        have hF : ∃ g, Store.BlockFrame σ.store p st.store.size buf off.eval
            (m.eval * n.eval) σ.store g := ⟨fun t => σ.store.read p buf (off.eval + t),
          rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
        obtain ⟨out, g, hrun, hframe, hB⟩ := exists_swapRows_body I p m n buf st.store.size
          off r s σ A hr hs (hσ ▸ Store.getElem?_shape_push_size st.store p 1)
          (fun hn => Nat.ne_of_lt (hbuf hn)) hAp hF
        refine ⟨out, ?_, ?_⟩
        · rw [exec_seq_skip, ← exec_normIdx I _ σ]
          rw [← exec_normIdx I _ σ] at hrun
          exact hrun
        · exact hA.writeBlock_of_blockFrame_pop (hσ ▸ hframe) hB)
  obtain ⟨out, hrun, W, hwrite, hB⟩ := halloc
  refine ⟨out, W, ?_, hwrite, hB⟩
  change exec I (.seq _ .skip) st = some out
  rw [exec_seq_skip]
  exact hrun

end NLAlib.Computation
