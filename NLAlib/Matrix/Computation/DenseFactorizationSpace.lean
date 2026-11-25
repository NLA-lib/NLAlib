/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.DenseFactorizationResources

/-!
# Dense factorization workspace formulas

Closed upper bounds for the additional live cells in stored dense routines.

## Main results

* `NLAlib.Computation.luFactorResources_cells_le`: the LU residual and scalar scratch space.
-/

@[expose] public section

namespace NLAlib.Computation

attribute [local simp] StaticCost.supRange_cells_mk

/-- The LU residual and saved operands need at most $N^2+2N+3$ additional live words. -/
theorem luFactorResources_cells_le {P ι : Type} [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P) (N ao lo uo : ℕ) :
    (luFactorResources charge width p N ao lo uo).cells p ≤ N * N + 2 * N + 3 := by
  change max ((if p = p then N * N else 0) + _) 0 ≤ N * N + 2 * N + 3
  simp only [ite_true]
  rw [max_eq_left (Nat.zero_le _)]
  refine le_trans ?_ (le_of_eq (Nat.add_assoc (N * N) (2 * N) 3).symm)
  apply Nat.add_le_add_left
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [StaticCost.sequence_cells_mk, IExp.evalIn]
  split_ifs <;> omega

/-- A closed additional-live-word upper bound for the actual positive-definite Cholesky tree.
Caller-owned input and output buffers are excluded. -/
theorem choleskyResources_cells_le {P ι : Type} [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P) (N ao lo : ℕ) :
    (choleskyResources charge width p N ao lo).cells p ≤ N * N + 2 * N + 3 := by
  change max ((if p = p then N * N else 0) + _) 0 ≤ N * N + 2 * N + 3
  simp only [ite_true]
  rw [max_eq_left (Nat.zero_le _)]
  refine le_trans ?_ (le_of_eq (show (N * N) + (2 * N + 3) = N * N + 2 * N + 3 by ring))
  apply Nat.add_le_add_left
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [StaticCost.sequence_cells_mk, IExp.evalIn]
  split_ifs <;> omega

/-- A closed additional-live-word upper bound for the actual semidefinite Cholesky tree.
Caller-owned input and output buffers are excluded. -/
theorem semidefiniteCholeskyResources_cells_le {P ι : Type} [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P) (N ao lo : ℕ) :
    (semidefiniteCholeskyResources charge width p N ao lo).cells p ≤ N * N + 2 * N + 4 := by
  change max ((if p = p then N * N else 0) + _) 0 ≤ N * N + 2 * N + 4
  simp only [ite_true]
  rw [max_eq_left (Nat.zero_le _)]
  refine le_trans ?_ (le_of_eq (show (N * N) + (2 * N + 4) = N * N + 2 * N + 4 by ring))
  apply Nat.add_le_add_left
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [StaticCost.sequence_cells_mk, IExp.evalIn]
  split_ifs <;> omega

/-- A closed additional-live-word upper bound for the actual one-by-one-pivot LDL tree.
Caller-owned input and output buffers are excluded. -/
theorem ldlFactorResources_cells_le {P ι : Type} [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P) (N ao lo doff : ℕ) :
    (ldlFactorResources charge width p N ao lo doff).cells p ≤ 2 * N * N + 2 * N + 3 := by
  change max ((if p = p then N * N else 0) + _) 0 ≤ 2 * N * N + 2 * N + 3
  simp only [ite_true]
  rw [max_eq_left (Nat.zero_le _)]
  refine le_trans ?_ (le_of_eq (show (N * N) + (N * N + 2 * N + 3) = 2 * N * N + 2 * N + 3 by ring))
  apply Nat.add_le_add_left
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [StaticCost.sequence_cells_mk, IExp.evalIn]
  split_ifs <;> omega

/-- A closed additional-live-word upper bound for the actual partial-pivoted LU tree.
Caller-owned input and output buffers are excluded. -/
theorem pluFactorResources_cells_le {P ι : Type} [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P) (N ao lo uo ho : ℕ) :
    (pluFactorResources charge width p N ao lo uo ho).cells p ≤ N * N + 2 * N + 7 := by
  change max ((if p = p then N * N else 0) + _) 0 ≤ N * N + 2 * N + 7
  simp only [ite_true]
  rw [max_eq_left (Nat.zero_le _)]
  refine le_trans ?_ (le_of_eq (show (N * N) + (2 * N + 7) = N * N + 2 * N + 7 by ring))
  apply Nat.add_le_add_left
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [StaticCost.sequence_cells_mk, IExp.evalIn]
  split_ifs <;> omega

/-- A closed additional-live-word upper bound for the actual complete-pivoted LU tree.
Caller-owned input and output buffers are excluded. -/
theorem pluqFactorResources_cells_le {P ι : Type} [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P) (N ao lo uo hro hco : ℕ) :
    (pluqFactorResources charge width p N ao lo uo hro hco).cells p ≤ N * N + 2 * N + 7 := by
  change max ((if p = p then N * N else 0) + _) 0 ≤ N * N + 2 * N + 7
  simp only [ite_true]
  rw [max_eq_left (Nat.zero_le _)]
  refine le_trans ?_ (le_of_eq (show (N * N) + (2 * N + 7) = N * N + 2 * N + 7 by ring))
  apply Nat.add_le_add_left
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp only [IExp.evalIn, Fin.zero_eta, Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk, Fin.mk_one,
    add_zero, max_self, StaticCost.sequence_cells_mk, List.range_eq_nil, ite_self,
    Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, zero_le, sup_of_le_left,
    StaticCost.supRange_cells_mk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    StaticCost.sequence_bits_mk, sup_of_le_right, add_le_add_iff_left,
    le_add_iff_nonneg_left]
  apply StaticCost.sequence_cells_le
  intro i hi
  dsimp only
  simp
  split_ifs <;> omega

/-- A closed additional-live-word upper bound for the actual fixed-scale pivoted LU tree.
Caller-owned input and output buffers are excluded. -/
theorem scaledPluFactorResources_cells_le {P ι : Type} [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P) (N ao lo uo ho : ℕ) :
    (scaledPluFactorResources charge width p N ao lo uo ho).cells p ≤ N * N + 3 * N + 7 := by
  change max ((if p = p then N * N + N else 0) + _) 0 ≤ N * N + 3 * N + 7
  simp only [ite_true]
  rw [max_eq_left (Nat.zero_le _)]
  refine le_trans ?_ (le_of_eq (show (N * N + N) + (2 * N + 7) = N * N + 3 * N + 7 by ring))
  apply Nat.add_le_add_left
  dsimp only [FStmt.staticCost, StaticCost.alloc, StaticCost.seq, StaticCost.step,
    StaticCost.zero, StaticCost.branch]
  simp [StaticCost.sequence_cells_mk, IExp.evalIn]
  split_ifs <;> omega

end NLAlib.Computation
