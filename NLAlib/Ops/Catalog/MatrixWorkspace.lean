/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Matrix
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite workspace envelopes for matrix operations

Matrix implementations need not have monotone workspace functions. Taking a finite maximum
over all legal dimensions up to a root size still yields one shared temporary reservation.
Zero dimensions are included, and multiplication and QR retain their actual argument lists.

## Main results

* `NLAlib.Ops.MatrixOp.workspaceEnvelope`: the finite maximum over both matrix operations.
* `NLAlib.Ops.MatrixOp.workspace_mul_le_envelope`: coverage of a bounded rectangular product.
* `NLAlib.Ops.MatrixOp.workspace_qr_le_envelope`: coverage of bounded rectangular QR.
-/

@[expose] public section

namespace NLAlib.Ops.MatrixOp

/-- Maximum primitive workspace for every multiplication and QR shape with each dimension
at most `n`. No monotonicity assumption on the supplied workspace function is required. -/
def workspaceEnvelope (W : MatrixOp → List ℕ → ℕ) (n : ℕ) : ℕ :=
  max ((Finset.range (n + 1)).sup fun l =>
    (Finset.range (n + 1)).sup fun m =>
      (Finset.range (n + 1)).sup fun k => W .mul [l, m, k])
    ((Finset.range (n + 1)).sup fun m =>
      (Finset.range (n + 1)).sup fun k => W .qr [m, k])

/-- Every multiplication shape whose three dimensions are bounded by the root fits the
finite shared matrix-workspace reservation. -/
theorem workspace_mul_le_envelope (W : MatrixOp → List ℕ → ℕ) {n l m k : ℕ}
    (hl : l ≤ n) (hm : m ≤ n) (hk : k ≤ n) :
    W .mul [l, m, k] ≤ workspaceEnvelope W n := by
  refine (Finset.le_sup (s := Finset.range (n + 1)) (b := k)
    (f := fun k => W .mul [l, m, k])
    (Finset.mem_range.mpr (by omega))).trans ?_
  refine (Finset.le_sup (s := Finset.range (n + 1)) (b := m)
    (f := fun m => (Finset.range (n + 1)).sup
    fun k => W .mul [l, m, k]) (Finset.mem_range.mpr (by omega))).trans ?_
  exact (Finset.le_sup (s := Finset.range (n + 1)) (b := l)
    (f := fun l => (Finset.range (n + 1)).sup fun m =>
    (Finset.range (n + 1)).sup fun k => W .mul [l, m, k])
      (Finset.mem_range.mpr (by omega))).trans (Nat.le_max_left ..)

/-- Every QR shape whose dimensions are bounded by the root fits the same finite shared
matrix-workspace reservation as multiplication. -/
theorem workspace_qr_le_envelope (W : MatrixOp → List ℕ → ℕ) {n m k : ℕ}
    (hm : m ≤ n) (hk : k ≤ n) : W .qr [m, k] ≤ workspaceEnvelope W n := by
  refine (Finset.le_sup (s := Finset.range (n + 1)) (b := k)
    (f := fun k => W .qr [m, k])
    (Finset.mem_range.mpr (by omega))).trans ?_
  exact (Finset.le_sup (s := Finset.range (n + 1)) (b := m)
    (f := fun m => (Finset.range (n + 1)).sup fun k => W .qr [m, k])
    (Finset.mem_range.mpr (by omega))).trans (Nat.le_max_right ..)

end NLAlib.Ops.MatrixOp
