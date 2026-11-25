/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.Fin.Embedding
public import NLAlib.Matrix.Computation.PivotScan
public import NLAlib.Matrix.Computation.RowSwap

/-!
# Partial pivot search and row exchange

Partial pivoting scans the active suffix of a stored column, binds the selected relative
index through the bounded index binder, exchanges the corresponding full matrix rows and
records the absolute pivot index. The scan selects the first largest decoded magnitude.
The result is a pivot operation, not a complete pivoted factorization.

## Main results

* `NLAlib.Computation.executionComposable_partialPivot`: execution composes with a consumer.
* `NLAlib.Computation.IsRelErrSem.exec_partialPivot`: actual selection and exchange, with its
  complete matrix and index output frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Select the first largest absolute entry of column `k` on rows at least `k`, exchange
that row with row `k` across the full matrix and record the selected absolute row in `index`.
The matrix is packed column-major. The suffix must be nonempty, and the index occupies a
separate buffer. The stored relative choice is consumed by the bounded index binder.
[GolubVanLoan2013, §3.4]. -/
def partialPivot {P ι VB VI : Type} (tag : P) (n k : IExp VI) (R : VB) (off : IExp VI)
    (index : Cell VB VI) : Builder P ι VB VI Unit := scope do
  argmaxAbs tag (n - k) R (off + k + n * k) index
  bindIdx tag index (n - k) fun rel => do
    swapRows tag n n R off k (k + .var rel)
    ins (.litIdx tag index (k + .var rel))

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The scoped partial pivot operation composes under any interpretation. -/
theorem executionComposable_partialPivot (I : Interp P ι K C) (tag : P) (n k : IExp ℕ)
    (R : ℕ) (off : IExp ℕ) (index : Cell ℕ ℕ) :
    ExecutionComposable I (partialPivot tag n k R off index) :=
  executionComposable_single I (fun _ => rfl)

private theorem exec_scan_suffix {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P) (st : St P K C)
    (R : ℕ) (off : IExp ℕ) (index : Cell ℕ ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (htail : n.eval - k.eval ≤ n.eval)
    (hA : HoldsDecoded st.store dec tag R off.eval A)
    (hw : Writable st.store tag index.buf index.idx.eval 1) (hRI : R ≠ index.buf) :
    ∃ (out : St P K C) (w : K) (r : Fin (n.eval - k.eval)),
      exec I (argmaxAbs tag (n - k) R (off + k + n * k) index).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[w] = some out.store ∧
      dec tag w = r.val ∧
      (∀ j : Fin (n.eval - k.eval),
        |A ((Fin.natAdd_castLEEmb (htail)) j) ⟨k.eval, hk⟩| ≤
          |A ((Fin.natAdd_castLEEmb (htail)) r) ⟨k.eval, hk⟩|) ∧
      (∀ j : Fin (n.eval - k.eval), j < r →
        |A ((Fin.natAdd_castLEEmb (htail)) j) ⟨k.eval, hk⟩| <
          |A ((Fin.natAdd_castLEEmb (htail)) r) ⟨k.eval, hk⟩|) := by
  let x : Fin (n.eval - k.eval) → ℝ := fun j =>
    A ((Fin.natAdd_castLEEmb (htail)) j) ⟨k.eval, hk⟩
  have hin : ReadsDecoded st.store dec tag R (off + k + n * k).eval x := by
    intro j
    simpa only [x, Fin.val_natAdd_castLEEmb_sub, IExp.eval_add, IExp.eval_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
        hA ((Fin.natAdd_castLEEmb (htail)) j) ⟨k.eval, hk⟩
  obtain ⟨out, w, r, hr, hs, hd, hmax, hfirst⟩ := h.exec_argmaxAbs I hi.intLit
    (Nat.sub_le _ _) (Nat.sub_pos_of_lt hk) tag st x R (off + k + n * k) index hin hw hRI
  refine ⟨out, w, r, ?_, hs, hd, hmax, hfirst⟩
  exact (exec_eq_of_normIdx_eq I
    (s := (argmaxAbs tag (n - k) R (off + k + n * k) index).run)
    (s' := (argmaxAbs tag (.const (n.eval - k.eval)) R (off + k + n * k) index).run)
    rfl st).trans hr

private theorem exec_swap_record {dec : P → K → ℝ}
    (I : Interp P ι K C) (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem)
    (tag : P) (st : St P K C) (R : ℕ) (off : IExp ℕ) (index : Cell ℕ ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) K) (hk : k.eval < n.eval)
    (htail : n.eval - k.eval ≤ n.eval)
    (r : Fin (n.eval - k.eval)) (w : K)
    (hrd : st.store.read tag index.buf index.idx.eval = some w) (hd : dec tag w = r.val)
    (hM : Holds st.store tag R off.eval M)
    (hw : Writable st.store tag index.buf index.idx.eval 1) (hRI : R ≠ index.buf) :
    ∃ (out : St P K C) (W : Fin (n.eval * n.eval) → K) (z : K) (mid : Store P K),
      exec I (bindIdx tag index (n - k) fun rel => do
        swapRows tag n n R off k (k + .var rel)
        ins (.litIdx tag index (k + .var rel))).run st = some out ∧
      st.store.writeBlock tag R off.eval (Array.ofFn W) = some mid ∧
      mid.writeBlock tag index.buf index.idx.eval #[z] = some out.store ∧
      dec tag z = ((Fin.natAdd_castLEEmb (htail)) r).val ∧
      Holds out.store tag R off.eval
        (M.submatrix
          (Equiv.swap ⟨k.eval, hk⟩ ((Fin.natAdd_castLEEmb (htail)) r)) id) := by
  have hto : I.sem.toNat tag w = some (r : ℕ) := by
    rw [hi.toNat tag w, hd]
    simp
  let ready : St P K C := { st with cnt := st.cnt + I.charge (.toNat tag) }
  have hkr : (k + .var (r : ℕ)).eval < n.eval := by
    simpa only [IExp.eval_add, IExp.eval_var, Fin.val_natAdd_castLEEmb_sub] using
      ((Fin.natAdd_castLEEmb (htail)) r).isLt
  have hrFin : (⟨(k + .var (r : ℕ)).eval, hkr⟩ : Fin n.eval) =
      Fin.natAdd_castLEEmb (htail) r := by
    apply Fin.ext
    simp only [IExp.eval_add, IExp.eval_var, Fin.val_natAdd_castLEEmb_sub]
  obtain ⟨swapped, W, hr, hm, hMout⟩ := exec_swapRows I tag ready n n R off k
    (k + .var (r : ℕ)) M hk hkr hM
  rw [hrFin] at hMout
  obtain ⟨z, hz, hdz⟩ := hi.intLit tag (k.eval + r) (Nat.le_of_lt hkr)
  obtain ⟨len, hlen, hlt⟩ := hw 0 (by omega)
  obtain ⟨sf, hsf⟩ := Store.exists_write_eq_some_of_getElem?_shape z
    ((Store.shape_of_writeBlock_eq_some hm).symm ▸ hlen) (by simpa using hlt)
  let out : St P K C :=
    { swapped with store := sf, cnt := swapped.cnt + I.charge (.lit tag) }
  have hrlit : exec I (ins (.litIdx tag index (k + .var (r : ℕ)))).run swapped =
      some out := by
    change exec I (.seq (.instr (.litIdx tag index (k + .var (r : ℕ)))) .skip) swapped = _
    rw [exec_seq_instr_litIdx I (by simpa only [IExp.eval_add, IExp.eval_var] using hz) hsf]
    exact exec_skip I _
  refine ⟨out, W, z, swapped.store, ?_, hm, ?_,
    by simpa only [Fin.val_natAdd_castLEEmb_sub] using hdz, ?_⟩
  · change exec I (.seq (.bindIdx tag index (n - k) _) .skip) st = some out
    rw [exec_seq_skip, exec_bindIdx_of_read I hrd hto (by
      change (r : ℕ) ≤ n.eval - k.eval
      omega)]
    rw [exec_run_bind I (b := swapRows tag n n R off k (k + .var (r : ℕ)))
      (fun _ => rfl), hr, Option.bind_some]
    exact hrlit
  · simpa [Store.writeBlock] using hsf
  · exact hMout.write hsf (fun he => (hRI he.symm).elim)

/-- Partial pivoting executes an actual active-column scan, binds its stored choice, swaps
full matrix rows and stores the absolute chosen row. Under the standard real decoding model
and exact integer literals and index conversion through $n$, it succeeds for every nonempty
active suffix. The selected row is in the suffix, maximizes the original stored column's
absolute decoded value and is the first such maximum. The only net store effects are the
matrix block and one absolute index word, in that order. The index has a distinct buffer;
no matrix symmetry, invertibility or nonzero pivot is required.
[GolubVanLoan2013, §3.4]. -/
theorem IsRelErrSem.exec_partialPivot {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (tag : P) (st : St P K C) (n k : IExp ℕ)
    (hi : IsIndexExactSem dec n.eval I.sem) (R : ℕ) (off : IExp ℕ) (index : Cell ℕ ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hA : HoldsDecoded st.store dec tag R off.eval A)
    (hw : Writable st.store tag index.buf index.idx.eval 1) (hRI : R ≠ index.buf) :
    ∃ (out : St P K C) (chosen : Fin n.eval) (W : Fin (n.eval * n.eval) → K)
        (iw : K) (mid : Store P K),
      exec I (partialPivot tag n k R off index).run st = some out ∧
      st.store.writeBlock tag R off.eval (Array.ofFn W) = some mid ∧
      mid.writeBlock tag index.buf index.idx.eval #[iw] = some out.store ∧
      dec tag iw = chosen.val ∧ k.eval ≤ chosen.val ∧
      HoldsDecoded out.store dec tag R off.eval
        (A.submatrix (Equiv.swap ⟨k.eval, hk⟩ chosen) id) ∧
      (∀ j : Fin n.eval, k.eval ≤ j.val →
        |A j ⟨k.eval, hk⟩| ≤ |A chosen ⟨k.eval, hk⟩|) ∧
      (∀ j : Fin n.eval, k.eval ≤ j.val → j < chosen →
        |A j ⟨k.eval, hk⟩| < |A chosen ⟨k.eval, hk⟩|) := by
  classical
  choose M hM hdec using fun i j => hA i j
  obtain ⟨scanned, w, r, hr₁, hw₁, hrel, hmax, hfirst⟩ :=
    exec_scan_suffix I h n k hi tag st R off index A hk (Nat.sub_le _ _) hA hw hRI
  have hM' : Holds scanned.store tag R off.eval M := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hRI)).trans (hM i j)
  have hidx : scanned.store.read tag index.buf index.idx.eval = some w := by
    simpa using Store.read_of_writeBlock_eq_some_of_lt (j := 0) hw₁ (by simp)
  have hw' : Writable scanned.store tag index.buf index.idx.eval 1 := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hw i hi
    exact ⟨len, (Store.shape_of_writeBlock_eq_some hw₁).symm ▸ hlen, hlt⟩
  obtain ⟨out, W, iw, _, hr₂, hw₂, hw₃, habs, hmat⟩ :=
    exec_swap_record I n k hi tag scanned R off index M hk (Nat.sub_le _ _) r w hidx hrel
      hM' hw' hRI
  obtain ⟨mid, hmatrix, hindex⟩ := Store.writeBlock_comm hw₁ hw₂
    (fun _ _ => by simp [blockDisjoint_iff, hRI.symm])
  have hrecord := Store.writeBlock_writeBlock_self hindex hw₃ (by simp)
  refine ⟨out, (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) r, W,
    iw, mid, ?_, hmatrix, hrecord, habs,
    by simpa only [Fin.val_natAdd_castLEEmb_sub] using Nat.le_add_right k.eval r.val,
    ?_, ?_, ?_⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip, exec_run_bind I
      (b := argmaxAbs tag (n - k) R (off + k + n * k) index) (fun _ => rfl),
      hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    exact ⟨_, hmat i j, hdec _ _⟩
  · intro j hj
    let q : Fin (n.eval - k.eval) := ⟨j.val - k.eval, by have := j.isLt; omega⟩
    have hq : (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) q = j := by
      apply Fin.ext
      rw [Fin.val_natAdd_castLEEmb_sub]
      exact Nat.add_sub_of_le hj
    simpa only [hq] using hmax q
  · intro j hj hjc
    let q : Fin (n.eval - k.eval) := ⟨j.val - k.eval, by have := j.isLt; omega⟩
    have hq : (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval)) q = j := by
      apply Fin.ext
      rw [Fin.val_natAdd_castLEEmb_sub]
      exact Nat.add_sub_of_le hj
    have hqr : q < r := by
      change j.val - k.eval < r.val
      change j.val < (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k.eval) r).val at hjc
      rw [Fin.val_natAdd_castLEEmb_sub] at hjc
      omega
    simpa only [hq] using hfirst q hqr

end NLAlib.Computation
