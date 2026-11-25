/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Layout
public import NLAlib.Ops.Logic.View

/-!
# Reading a matrix diagonal as a strided view

The diagonal of a scalar-word matrix occupies one cell every leading-dimension-plus-one
cells. The shared read rule lets diagonal-factor output and diagonal pivot selection use the
ordinary strided-copy routine, without introducing a diagonal operation.

## Main results

* `NLAlib.Ops.Store.HoldsMat.readView_diagonal`: the actual diagonal words of a stored matrix.
-/

@[expose] public section

namespace NLAlib.Ops.Store

variable {K : Type}

/-- A diagonal slice is the singleton-run view with stride `ld + 1`. The
statement permits rectangular matrices and padded layouts and needs no arithmetic on words. -/
theorem HoldsMat.readView_diagonal_from {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K}
    (h : s.HoldsMat L A) (start n : ℕ) (hrows : start + n ≤ L.rows)
    (hcols : start + n ≤ L.cols) :
    s.readView L.buf (L.off + start * L.ld + start) ⟨1, some (n, L.ld + 1)⟩ =
      some ((List.range n).map fun i => A (start + i) (start + i)) := by
  apply readView_eq_some_iff.mpr
  refine ⟨by simp [View.cells_runs], ?_⟩
  intro i hi
  have hi' : i < n := by simpa only [View.cells_runs, Nat.mul_one] using hi
  rw [View.offset_runs_one, List.getElem?_map, List.getElem?_range hi', Option.map_some]
  simpa only [MatLayout.cell, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
    Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using
    h (start + i) (by omega) (start + i) (by omega)

/-- The first `n` diagonal entries are read with the same strided rule at offset zero. -/
theorem HoldsMat.readView_diagonal {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K}
    (h : s.HoldsMat L A) (n : ℕ) (hrows : n ≤ L.rows) (hcols : n ≤ L.cols) :
    s.readView L.buf L.off ⟨1, some (n, L.ld + 1)⟩ =
      some ((List.range n).map fun i => A i i) := by
  simpa only [Nat.zero_add, Nat.zero_mul, Nat.add_zero] using
    h.readView_diagonal_from 0 n (by simpa only [Nat.zero_add] using hrows)
      (by simpa only [Nat.zero_add] using hcols)

end NLAlib.Ops.Store
