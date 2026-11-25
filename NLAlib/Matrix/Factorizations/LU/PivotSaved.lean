/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.StridedCopy
public import NLAlib.Ops.Logic.ViewBlock
public import NLAlib.Ops.Logic.EntryRow

/-!
# Saving the original pivot row and column

The full Schur update copies both pivot vectors before it changes any residual entry.
The source is a packed column-major square matrix; the copied row and column are ordinary
contiguous vectors. Both copies use the shared scalar strided-copy routine.

## Main results

* `NLAlib.LU.pivotSaved_meets`: both outputs are words from the original source matrix.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Copy the original pivot column and row, without modifying the packed residual. -/
def pivotSaved : Routine Op Tst := routine% [n, k] (A : n * n) → (c : n, r : n) {
  run (copyStridedRoutine (Op := Op) (Tst := Tst)) [n, 1, 1] (A[k * n], c);
  run (copyStridedRoutine (Op := Op) (Tst := Tst)) [n, n, 1] (A[k], r)
}

variable [Inhabited K]

/-- The original packed pivot-column words. -/
def pivotColumnWords (xs : List K) (n k : ℕ) : List K :=
  (List.range n).map fun i => vec xs (k * n + i)

/-- The original packed pivot-row words. -/
def pivotRowWords (xs : List K) (n k : ℕ) : List K :=
  (List.range n).map fun j => vec xs (j * n + k)

/-- Both output vectors are copied from the input word block at the supplied pivot. -/
def pivotSavedSpec : Routine.Spec K :=
  spec% [n, k] (xs) → (cs, rs) requires k < n ensures
    cs = pivotColumnWords xs n k ∧ rs = pivotRowWords xs n k

omit [Has ScalarOp Op] in
/-- A packed matrix column is the singleton-stride view of its original source words.
The same read is used by saved-pivot updates and word-exact column exchanges. -/
theorem read_pivotColumnWords {s : Store K} {b off n k : ℕ} {xs : List K}
    (h : s.readBlock b off (n * n) = some xs) (hk : k < n) :
    s.readView b (off + k * n) ⟨1, some (n, 1)⟩ = some (pivotColumnWords xs n k) := by
  rw [Store.readView_unitStride]
  have hm := Store.holdsMat_of_readBlock (L := ⟨b, off, n, n, n⟩) rfl h
  exact Store.holdsVec_iff_readBlock.mp (hm.col hk)

omit [Has ScalarOp Op] in
private theorem read_pivotRowWords {s : Store K} {b off n k : ℕ} {xs : List K}
    (h : s.readBlock b off (n * n) = some xs) (hk : k < n) :
    s.readView b (off + k) ⟨1, some (n, n)⟩ = some (pivotRowWords xs n k) := by
  have hm := Store.holdsMat_of_readBlock (L := ⟨b, off, n, n, n⟩) rfl h
  simpa only [pivotRowWords, Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.sub_zero] using
    hm.readView_row_suffix hk 0

/-- Saving a pivot uses the original input for both copies and writes only the two declared
output vectors. No arithmetic accuracy law is required. -/
theorem pivotSaved_meets_of_isFn {I : Interp Op Tst K}
    (hcopy : I.IsFn .total (Has.inj ScalarOp.copy) (.un fun v => some v) AnyOperands) :
    (pivotSaved (Op := Op) (Tst := Tst)).Meets I pivotSavedSpec := by
  routine_intro [n, k] (A, c, r) reads (xs)
  have hc := read_pivotColumnWords hxs hpre
  call (copyStridedRoutine_meets_of_isFn hcopy) [n, 1, 1] ((A.1, A.2 + k * n), c)
    as m₁ hfr₁ hpos₁ (cs) hcol
  case' hcall => exact [pivotColumnWords xs n k]
  case' hr => exact Mem.readViews_of_cons hc rfl
  case' hpre => exact fun _ => Nat.zero_lt_one
  case' hroom =>
    change (∀ i < n * 1, c.2 + (⟨1, some (n, 1)⟩ : View).offset i <
      m.store.len c.1) ∧ True
    simp only [Nat.mul_one, View.offset_runs_one, Nat.one_mul, and_true]
    intro i hi
    omega
  have hxs₁ : m₁.store.readBlock A.1 A.2 (n * n) = some xs := by
    apply hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) ?_ hxs
    simpa only [Fp.views, sup_bot_eq] using Fp.disj_inView_inBlock_of_ne hAc.symm
  have hr := read_pivotRowWords hxs₁ hpre
  call (copyStridedRoutine_meets_of_isFn hcopy) [n, n, 1] ((A.1, A.2 + k), r)
    as m₂ hfr₂ hpos₂ (rs) hrow
  case' hcall => exact [pivotRowWords xs n k]
  case' hr => exact Mem.readViews_of_cons hr rfl
  case' hpre => exact fun _ => Nat.zero_lt_one
  case' hroom =>
    change (∀ i < n * 1, r.2 + (⟨1, some (n, 1)⟩ : View).offset i <
      m₁.store.len r.1) ∧ True
    simp only [Nat.mul_one, View.offset_runs_one, Nat.one_mul, and_true]
    intro i hi
    rw [hfr₁.len_eq]
    omega
  simp only [Store.readView_unitStride] at hcs hrs
  have hcs₂ : m₂.store.readBlock c.1 c.2 n = some cs := by
    apply hfr₂.keep (Store.readsOnly_readBlock _ _ _ _) ?_ hcs
    simpa only [Fp.views, sup_bot_eq] using Fp.disj_inView_inBlock_of_ne hcr.symm
  routine_exit
  exact ⟨hcol, hrow⟩

/-- The ordinary scalar machine provides the sole copy contract used to save pivots. -/
theorem pivotSaved_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (pivotSaved (Op := Op) (Tst := Tst)).Meets I pivotSavedSpec :=
  pivotSaved_meets_of_isFn (hI .copy)

end NLAlib.LU
