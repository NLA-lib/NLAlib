/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.StaticCost
public import NLAlib.Krylov.Processes.LanczosOracleTargets

/-!
# Static resource bounds for the fixed oracle Lanczos tree

The resource analysis reads the actual approved first-order oracle tree. It does not use the exact
arithmetic realization theorem. Consequently its successful-run bounds apply to arbitrary
scalar semantics with the standard operation charge.

## Main results

* `NLAlib.lanczosOracleProg.staticCost_count_le`: approved closed-form count budget.
* `NLAlib.lanczosOracleProg.bounds_of_exec_eq_some`: resources under arbitrary scalar semantics.
-/

@[expose] public section

namespace NLAlib

open Computation

/-- The standard-charge count of the fixed oracle Lanczos tree is bounded by the approved budget,
independently of scalar semantics or successful execution. -/
theorem lanczosOracleProg.staticCost_count_le {P ι : Type} [DecidableEq P] (tag : P) (o : ι)
    (width : P → ℕ) (N q : ℕ) :
    ((lanczosOracleProg.compiled (ι := ι) tag o).staticCost (fun k => Finsupp.single k 1)
      width N ![q]).count ≤ lanczosOracleCount tag o N q := by
  classical
  intro k
  change (FStmt.staticCost (fun k => Finsupp.single k 1) width
    (lanczosOracleProg.compiled (ι := ι) tag o) (Fin.cons N ![q])).count k ≤ _
  change (StaticCost.seq _ _).count k ≤ _
  simp only [FStmt.staticCost, StaticCost.seq, StaticCost.branch, StaticCost.alloc,
    StaticCost.step, StaticCost.zero, StaticCost.sequence_count_apply, Instr.kind, Instr.subst,
    IExp.evalIn, Finsupp.add_apply, Finsupp.sup_apply, List.map_const', List.sum_replicate,
    List.length_range, Finsupp.zero_apply, one_nsmul]
  cases k <;> simp only [lanczosOracleCount, Finsupp.add_apply, Finsupp.single_apply,
    OpKind.bin.injEq, OpKind.un.injEq, OpKind.lit.injEq, OpKind.cmp.injEq,
    OpKind.copy.injEq,
    OpKind.load.injEq, OpKind.matvec.injEq, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
    Fin.cons_zero, reduceCtorEq,
    add_zero, zero_add,
    smul_eq_mul, Matrix.Fin.cons_vecCons, Nat.succ_eq_add_one,
    Fin.snoc_apply_zero, Matrix.cons_val_zero, 
     List.map_const', List.length_range, List.sum_replicate,
    Fin.val_eq_zero, Fin.mk_one, Fin.cons_one,
    Matrix.cons_val_fin_one]
  case bin p b => cases b <;> simp only [reduceCtorEq, and_true, and_false, ite_false] <;>
    by_cases hp : tag = p <;> norm_num [hp] <;> ring_nf <;> omega
  case un p u => cases u <;> simp only [reduceCtorEq, and_true, and_false, ite_false] <;>
    by_cases hp : tag = p <;> norm_num [hp] <;> ring_nf <;> omega
  all_goals split_ifs <;> norm_num <;> ring_nf <;> omega

/-- Additional live workspace of the fixed oracle Lanczos tree is bounded by its work vector,
two scalar registers and one BLAS scratch cell, at the program's tag only. -/
theorem lanczosOracleProg.staticCost_cells_le {P ι : Type} [DecidableEq P] (tag : P) (o : ι)
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (N q : ℕ) (p : P) :
    ((lanczosOracleProg.compiled (ι := ι) tag o).staticCost charge width N ![q]).cells p ≤
      if p = tag then N + 3 else 0 := by
  change (StaticCost.seq _ _).cells p ≤ _
  simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.branch,
    StaticCost.step, StaticCost.zero, IExp.evalIn, Instr.kind, Instr.subst]
  simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero, Fin.cons_one,
    Fin.snoc_apply_zero, Matrix.Fin.cons_vecCons, 
     Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Fin.val_eq_zero, Fin.mk_one, StaticCost.sequence_cells_mk, List.range_eq_nil,
    max_self, zero_add, add_zero, Nat.zero_max, Nat.max_zero, ite_self]
  split_ifs <;> omega

/-- The width-weighted additional bit workspace of the fixed oracle Lanczos tree is bounded by its
work vector, scalar registers and BLAS scratch, all at the same tag. -/
theorem lanczosOracleProg.staticCost_bits_le {P ι : Type} [DecidableEq P] (tag : P) (o : ι)
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (N q : ℕ) :
    ((lanczosOracleProg.compiled (ι := ι) tag o).staticCost charge width N ![q]).bits ≤
      (N + 3) * width tag := by
  change (StaticCost.seq _ _).bits ≤ _
  simp only [FStmt.staticCost, StaticCost.seq, StaticCost.alloc, StaticCost.branch,
    StaticCost.step, StaticCost.zero, IExp.evalIn, Instr.kind, Instr.subst]
  simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.cons_zero, Fin.cons_one,
    Fin.snoc_apply_zero, Matrix.Fin.cons_vecCons, 
     Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Fin.val_eq_zero, Fin.mk_one, StaticCost.sequence_bits_mk, List.range_eq_nil,
    max_self, zero_add, add_zero, Nat.zero_max, Nat.max_zero, ite_self, one_mul]
  simp only [Nat.add_mul]
  split_ifs <;> omega

/-- Under arbitrary scalar semantics, every successful run of the approved oracle Lanczos tree with
standard charges obeys the approved count formula, the scoped workspace cell bound and its
width-weighted bit bound. This theorem establishes resources only; success is a premise. -/
theorem lanczosOracleProg.bounds_of_exec_eq_some {P ι K : Type} [DecidableEq P]
    (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι) (N q : ℕ)
    (hc : IsUnitCharge I) {st st' : St P K (OpCount P ι)}
    (h : (lanczosOracleProg.compiled (ι := ι) tag o).exec I N ![q] st = some st') :
    (StaticCost.mk (lanczosOracleCount tag o N q) (fun p => if p = tag then N + 3 else 0)
      ((N + 3) * I.width tag)).Bounds st st' := by
  exact (lanczosOracleProg.compiled tag o).bounds_of_exec_eq_some_of_staticCost_le I N ![q] hc _ _ _
    (lanczosOracleProg.staticCost_count_le (ι := ι) tag o I.width N q)
    (lanczosOracleProg.staticCost_cells_le tag o I.charge I.width N q)
    (lanczosOracleProg.staticCost_bits_le tag o I.charge I.width N q) h

end NLAlib
