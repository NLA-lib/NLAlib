/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.StridedCopy
public import NLAlib.Ops.Logic.EntryDiagonal
public import NLAlib.Ops.Logic.ViewBlock

/-!
# Scalar copying of a packed matrix diagonal slice

The routine is one call to the existing strided-copy scalar loop. It gathers an active
diagonal suffix for pivot selection or the final pivot diagonal for an LDL factorization.
It reads the original words, without arithmetic or a numerical-model hypothesis.

## Main results

* `NLAlib.Ops.copyDiagonal_meets`: exact word copying of a bounded diagonal slice.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Gather `count` diagonal entries starting at `start` from a packed square matrix. -/
def copyDiagonal : Routine Op Tst :=
  routine% [n, start, count] (A : n * n) → (d : count) {
    run copyStridedRoutine [count, n + 1, 1] (A[start * n + start], d)
  }

variable [Inhabited K]

/-- The gathered vector contains the original diagonal words in increasing index order. -/
def copyDiagonalSpec : Routine.Spec K :=
  spec% [n, start, count] (as) → (ds) requires start + count ≤ n ensures
    ds = (List.range count).map fun i => vec as ((start + i) * n + (start + i))

/-- The actual scalar loop gathers every bounded diagonal slice, including an empty one. -/
theorem copyDiagonal_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (copyDiagonal (Op := Op) (Tst := Tst)).Meets I (copyDiagonalSpec (K := K)) := by
  routine_intro [n, start, count] (A, d) reads (as)
  have hm := Store.holdsMat_of_readBlock (L := ⟨A.1, A.2, n, n, n⟩) rfl has
  have hd := hm.readView_diagonal_from start count hpre hpre
  call (copyStridedRoutine_meets hI) [count, n + 1, 1]
    ((A.1, A.2 + start * n + start), d) as m₁ hfr₁ hpos₁ (ds) hpost
  case' hcall => exact [(List.range count).map fun i => vec as ((start + i) * n + (start + i))]
  case' hr => exact Mem.readViews_of_cons hd rfl
  case' hpre => exact fun _ => Nat.zero_lt_one
  case' hroom =>
    change (∀ i < count * 1, d.2 + (⟨1, some (count, 1)⟩ : View).offset i <
      m.store.len d.1) ∧ True
    simp only [Nat.mul_one, View.offset_runs_one, Nat.one_mul, and_true]
    intro i hi
    omega
  rw [Store.readView_unitStride] at hds
  exact ⟨by omega, [ds], Mem.readBlocks_of_cons hds rfl, hpost⟩

end NLAlib.Ops
