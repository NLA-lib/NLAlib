/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.DenseFactorizationResources

/-!
# Dense factorization workspace tags

The seven concrete resource trees allocate only at their designated tag. Their workspace
is therefore zero at every other tag, independently of scalar charges and bit widths.

## Main results

* `NLAlib.Computation.luFactorResources_cells_eq_zero`: LU has no workspace at other tags.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι : Type} [DecidableEq P]

/-- The actual LU resource tree allocates no workspace away from its tag. -/
theorem luFactorResources_cells_eq_zero
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p q : P)
    (N ao lo uo : ℕ) (h : q ≠ p) :
    (luFactorResources charge width p N ao lo uo).cells q = 0 := by
  change max ((if q = p then N * N else 0) + _) 0 = 0
  simp only [h, ite_false, zero_add, Nat.max_zero]
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [h, StaticCost.sequence_cells_mk, IExp.evalIn]

/-- The actual partial-pivoted LU resource tree allocates no workspace away from its tag. -/
theorem pluFactorResources_cells_eq_zero
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p q : P)
    (N ao lo uo ho : ℕ) (h : q ≠ p) :
    (pluFactorResources charge width p N ao lo uo ho).cells q = 0 := by
  change max ((if q = p then N * N else 0) + _) 0 = 0
  simp only [h, ite_false, zero_add, Nat.max_zero]
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [h, StaticCost.sequence_cells_mk, StaticCost.supRange_cells_mk, IExp.evalIn]

/-- The actual complete-pivoted LU resource tree allocates no workspace away from its tag. -/
theorem pluqFactorResources_cells_eq_zero
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p q : P)
    (N ao lo uo hro hco : ℕ) (h : q ≠ p) :
    (pluqFactorResources charge width p N ao lo uo hro hco).cells q = 0 := by
  change max ((if q = p then N * N else 0) + _) 0 = 0
  simp only [h, ite_false, zero_add, Nat.max_zero]
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp only [StaticCost.sequence_cells_mk, StaticCost.supRange_cells_mk, IExp.evalIn,
    Fin.zero_eta, Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, Fin.mk_one,
    add_zero, max_self, List.range_eq_nil, ite_self, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty, zero_le, sup_of_le_left, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, ↓reduceIte, StaticCost.sequence_bits_mk, sup_of_le_right]
  apply Nat.eq_zero_of_le_zero
  apply StaticCost.sequence_cells_le
  intro i hi
  dsimp only
  simp [h]

/-- The actual fixed-scale pivoted LU resource tree allocates no workspace away from its tag. -/
theorem scaledPluFactorResources_cells_eq_zero
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p q : P)
    (N ao lo uo ho : ℕ) (h : q ≠ p) :
    (scaledPluFactorResources charge width p N ao lo uo ho).cells q = 0 := by
  change max ((if q = p then N * N + N else 0) + _) 0 = 0
  simp only [h, ite_false, zero_add, Nat.max_zero]
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [h, StaticCost.sequence_cells_mk, StaticCost.supRange_cells_mk, IExp.evalIn]

/-- The actual positive-definite Cholesky resource tree allocates no workspace away from its tag. -/
theorem choleskyResources_cells_eq_zero
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p q : P)
    (N ao lo : ℕ) (h : q ≠ p) :
    (choleskyResources charge width p N ao lo).cells q = 0 := by
  change max ((if q = p then N * N else 0) + _) 0 = 0
  simp only [h, ite_false, zero_add, Nat.max_zero]
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [h, StaticCost.sequence_cells_mk, IExp.evalIn]

/-- The actual semidefinite Cholesky resource tree allocates no workspace away from its tag. -/
theorem semidefiniteCholeskyResources_cells_eq_zero
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p q : P)
    (N ao lo : ℕ) (h : q ≠ p) :
    (semidefiniteCholeskyResources charge width p N ao lo).cells q = 0 := by
  change max ((if q = p then N * N else 0) + _) 0 = 0
  simp only [h, ite_false, zero_add, Nat.max_zero]
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [h, StaticCost.sequence_cells_mk, IExp.evalIn]

/-- The actual LDL resource tree allocates no workspace away from its tag. -/
theorem ldlFactorResources_cells_eq_zero
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p q : P)
    (N ao lo doff : ℕ) (h : q ≠ p) :
    (ldlFactorResources charge width p N ao lo doff).cells q = 0 := by
  change max ((if q = p then N * N else 0) + _) 0 = 0
  simp only [h, ite_false, zero_add, Nat.max_zero]
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [h, StaticCost.sequence_cells_mk, IExp.evalIn]

end NLAlib.Computation
