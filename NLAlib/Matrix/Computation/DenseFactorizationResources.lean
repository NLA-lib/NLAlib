/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.LU
public import NLAlib.Matrix.Computation.PLU
public import NLAlib.Matrix.Computation.PLUQ
public import NLAlib.Matrix.Computation.ScaledPLU
public import NLAlib.Matrix.Computation.CholeskyFactorization
public import NLAlib.Matrix.Computation.SemidefiniteCholesky
public import NLAlib.Matrix.Computation.LDL
public import NLAlib.Computation.StaticCost

/-!
# Static resources of dense factorization routines

The first-order analysis of the actual routine bounds operation counts, additional live
cells and additional live bits. Success is supplied by the factorization theorems; the
resource statement itself applies to every successful run under any scalar interpretation.

## Main results

* `NLAlib.Computation.bounds_luFactor`: actual LU execution obeys its static resource summary.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι : Type}

/-- Symbolic first-order LU tree used by the existing static resource analysis. -/
def luResourceTree (p : P) : FStmt P ι 3 4 :=
  ((luFactor p (.var 0) 0 1 2 (.var 1) (.var 2) (.var 3)).run.compile 3 4).get (by rfl)

private theorem luResourceTree_toStmt (p : P) (n ao lo uo : IExp ℕ) (A L U : ℕ) :
    (luResourceTree (ι := ι) p).toStmt ![A, L, U] ![n, ao, lo, uo] =
      (luFactor p n A L U ao lo uo).run := by
  rfl

/-- The existing first-order static analysis of the actual LU tree at order `N`. Counts
include all explicit scalar instructions and copies; workspace includes scoped buffers and
uses the supplied per-tag bit width. This finite summary is an upper bound, not a flop-only
asymptotic estimate. -/
noncomputable def luFactorResources [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P) (N ao lo uo : ℕ) : StaticCost P ι :=
  (luResourceTree p).staticCost charge width ![N, ao, lo, uo]

/-- Every successful actual unpivoted LU run satisfies the static tree's count and live-memory
bounds and restores current cells and bits. Scalar semantics, initial contents, offsets and
oracles are arbitrary. This theorem supplies resource bounds; successful numerical
factorization is established separately. -/
theorem bounds_luFactor {K : Type} [DecidableEq P]
    (I : Interp P ι K (OpCount P ι)) (p : P) (n : IExp ℕ) (A L U : ℕ)
    (ao lo uo : IExp ℕ) {st out : St P K (OpCount P ι)}
    (hr : exec I (luFactor p n A L U ao lo uo).run st = some out) :
    (luFactorResources I.charge I.width p n.eval ao.eval lo.eval uo.eval).Bounds st out := by
  have hrun : (luResourceTree p).exec I ![A, L, U]
      (fun v => (![n, ao, lo, uo] v).eval) st = some out := by
    rw [FStmt.exec_eq_exec_toStmt, luResourceTree_toStmt]
    exact hr
  have hb := (luResourceTree p).bounds_staticCost_of_exec_eq_some I ![A, L, U]
    (fun v => (![n, ao, lo, uo] v).eval) hrun
  have henv : (fun v : Fin 4 => (![n, ao, lo, uo] v).eval) =
      ![n.eval, ao.eval, lo.eval, uo.eval] := by
    funext v
    fin_cases v <;> rfl
  rw [henv] at hb
  exact hb

/-- Symbolic first-order partial-pivoted LU tree used by the existing static resource analysis. -/
def pluResourceTree (p : P) : FStmt P ι 4 5 :=
  ((pluFactor p (.var 0) 0 1 2 3 (.var 1) (.var 2) (.var 3) (.var 4)).run.compile 4 5).get (by rfl)

private theorem pluResourceTree_toStmt (p : P) (n ao lo uo ho : IExp ℕ)
    (A L U H : ℕ) :
    (pluResourceTree (ι := ι) p).toStmt ![A, L, U, H] ![n, ao, lo, uo, ho] =
      (pluFactor p n A L U H ao lo uo ho).run := by
  rfl

/-- Static operation-count and additional-live-memory summary of the actual partial-pivoted LU tree.
The summary includes copies, pivot scans and every scoped allocation, under the supplied
instruction charges and per-tag bit widths. -/
noncomputable def pluFactorResources [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P)
    (N ao lo uo ho : ℕ) : StaticCost P ι :=
  (pluResourceTree p).staticCost charge width ![N, ao, lo, uo, ho]

/-- Every successful actual partial-pivoted LU run obeys its static count and live-memory bounds and
restores current cells and bits. Scalar semantics, store contents, offsets and oracles are
arbitrary; successful factorization is proved separately. -/
theorem bounds_pluFactor {K : Type} [DecidableEq P]
    (I : Interp P ι K (OpCount P ι)) (p : P) (n : IExp ℕ) (A L U H : ℕ)
    (ao lo uo ho : IExp ℕ) {st out : St P K (OpCount P ι)}
    (hr : exec I (pluFactor p n A L U H ao lo uo ho).run st = some out) :
    (pluFactorResources I.charge I.width p n.eval ao.eval lo.eval uo.eval ho.eval).Bounds st out
        := by
  have hrun : (pluResourceTree p).exec I ![A, L, U, H]
      (fun v => (![n, ao, lo, uo, ho] v).eval) st = some out := by
    rw [FStmt.exec_eq_exec_toStmt, pluResourceTree_toStmt]
    exact hr
  have hb := (pluResourceTree p).bounds_staticCost_of_exec_eq_some I ![A, L, U, H]
    (fun v => (![n, ao, lo, uo, ho] v).eval) hrun
  have henv : (fun v : Fin 5 => (![n, ao, lo, uo, ho] v).eval) =
      ![n.eval, ao.eval, lo.eval, uo.eval, ho.eval] := by
    funext v
    fin_cases v <;> rfl
  rw [henv] at hb
  exact hb

/-- Symbolic first-order complete-pivoted LU tree used by the existing static resource analysis. -/
def pluqResourceTree (p : P) : FStmt P ι 5 6 :=
  ((pluqFactor p (.var 0) 0 1 2 3 4 (.var 1) (.var 2) (.var 3) (.var 4) (.var 5)).run.compile 5
      6).get (by rfl)

private theorem pluqResourceTree_toStmt (p : P) (n ao lo uo hro hco : IExp ℕ)
    (A L U Hr Hc : ℕ) :
    (pluqResourceTree (ι := ι) p).toStmt ![A, L, U, Hr, Hc] ![n, ao, lo, uo, hro, hco] =
      (pluqFactor p n A L U Hr Hc ao lo uo hro hco).run := by
  rfl

/-- Static operation-count and additional-live-memory summary of the actual complete-pivoted LU
    tree.
The summary includes copies, pivot scans and every scoped allocation, under the supplied
instruction charges and per-tag bit widths. -/
noncomputable def pluqFactorResources [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P)
    (N ao lo uo hro hco : ℕ) : StaticCost P ι :=
  (pluqResourceTree p).staticCost charge width ![N, ao, lo, uo, hro, hco]

/-- Every successful actual complete-pivoted LU run obeys its static count and live-memory
    bounds and
restores current cells and bits. Scalar semantics, store contents, offsets and oracles are
arbitrary; successful factorization is proved separately. -/
theorem bounds_pluqFactor {K : Type} [DecidableEq P]
    (I : Interp P ι K (OpCount P ι)) (p : P) (n : IExp ℕ) (A L U Hr Hc : ℕ)
    (ao lo uo hro hco : IExp ℕ) {st out : St P K (OpCount P ι)}
    (hr : exec I (pluqFactor p n A L U Hr Hc ao lo uo hro hco).run st = some out) :
    (pluqFactorResources I.charge I.width p n.eval ao.eval lo.eval uo.eval hro.eval
        hco.eval).Bounds st out := by
  have hrun : (pluqResourceTree p).exec I ![A, L, U, Hr, Hc]
      (fun v => (![n, ao, lo, uo, hro, hco] v).eval) st = some out := by
    rw [FStmt.exec_eq_exec_toStmt, pluqResourceTree_toStmt]
    exact hr
  have hb := (pluqResourceTree p).bounds_staticCost_of_exec_eq_some I ![A, L, U, Hr, Hc]
    (fun v => (![n, ao, lo, uo, hro, hco] v).eval) hrun
  have henv : (fun v : Fin 6 => (![n, ao, lo, uo, hro, hco] v).eval) =
      ![n.eval, ao.eval, lo.eval, uo.eval, hro.eval, hco.eval] := by
    funext v
    fin_cases v <;> rfl
  rw [henv] at hb
  exact hb

/-- Symbolic first-order fixed-scale pivoted LU tree used by the existing static resource
    analysis. -/
def scaledPluResourceTree (p : P) : FStmt P ι 4 5 :=
  ((scaledPluFactor p (.var 0) 0 1 2 3 (.var 1) (.var 2) (.var 3) (.var 4)).run.compile 4 5).get
      (by rfl)

private theorem scaledPluResourceTree_toStmt (p : P) (n ao lo uo ho : IExp ℕ)
    (A L U H : ℕ) :
    (scaledPluResourceTree (ι := ι) p).toStmt ![A, L, U, H] ![n, ao, lo, uo, ho] =
      (scaledPluFactor p n A L U H ao lo uo ho).run := by
  rfl

/-- Static operation-count and additional-live-memory summary of the actual fixed-scale pivoted
    LU tree.
The summary includes copies, pivot scans and every scoped allocation, under the supplied
instruction charges and per-tag bit widths. -/
noncomputable def scaledPluFactorResources [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P)
    (N ao lo uo ho : ℕ) : StaticCost P ι :=
  (scaledPluResourceTree p).staticCost charge width ![N, ao, lo, uo, ho]

/-- Every successful actual fixed-scale pivoted LU run obeys its static count and live-memory
    bounds and
restores current cells and bits. Scalar semantics, store contents, offsets and oracles are
arbitrary; successful factorization is proved separately. -/
theorem bounds_scaledPluFactor {K : Type} [DecidableEq P]
    (I : Interp P ι K (OpCount P ι)) (p : P) (n : IExp ℕ) (A L U H : ℕ)
    (ao lo uo ho : IExp ℕ) {st out : St P K (OpCount P ι)}
    (hr : exec I (scaledPluFactor p n A L U H ao lo uo ho).run st = some out) :
    (scaledPluFactorResources I.charge I.width p n.eval ao.eval lo.eval uo.eval ho.eval).Bounds
        st out := by
  have hrun : (scaledPluResourceTree p).exec I ![A, L, U, H]
      (fun v => (![n, ao, lo, uo, ho] v).eval) st = some out := by
    rw [FStmt.exec_eq_exec_toStmt, scaledPluResourceTree_toStmt]
    exact hr
  have hb := (scaledPluResourceTree p).bounds_staticCost_of_exec_eq_some I ![A, L, U, H]
    (fun v => (![n, ao, lo, uo, ho] v).eval) hrun
  have henv : (fun v : Fin 5 => (![n, ao, lo, uo, ho] v).eval) =
      ![n.eval, ao.eval, lo.eval, uo.eval, ho.eval] := by
    funext v
    fin_cases v <;> rfl
  rw [henv] at hb
  exact hb

/-- Symbolic first-order positive-definite Cholesky tree used by the existing static resource
    analysis. -/
def choleskyResourceTree (p : P) : FStmt P ι 2 3 :=
  ((cholesky p (.var 0) 0 (.var 1) 1 (.var 2)).run.compile 2 3).get (by rfl)

private theorem choleskyResourceTree_toStmt (p : P) (n ao lo : IExp ℕ)
    (A L : ℕ) :
    (choleskyResourceTree (ι := ι) p).toStmt ![A, L] ![n, ao, lo] =
      (cholesky p n A ao L lo).run := by
  rfl

/-- Static operation-count and additional-live-memory summary of the actual positive-definite
    Cholesky tree.
The summary includes copies, pivot scans and every scoped allocation, under the supplied
instruction charges and per-tag bit widths. -/
noncomputable def choleskyResources [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P)
    (N ao lo : ℕ) : StaticCost P ι :=
  (choleskyResourceTree p).staticCost charge width ![N, ao, lo]

/-- Every successful actual positive-definite Cholesky run obeys its static count and
    live-memory bounds and
restores current cells and bits. Scalar semantics, store contents, offsets and oracles are
arbitrary; successful factorization is proved separately. -/
theorem bounds_cholesky {K : Type} [DecidableEq P]
    (I : Interp P ι K (OpCount P ι)) (p : P) (n : IExp ℕ) (A L : ℕ)
    (ao lo : IExp ℕ) {st out : St P K (OpCount P ι)}
    (hr : exec I (cholesky p n A ao L lo).run st = some out) :
    (choleskyResources I.charge I.width p n.eval ao.eval lo.eval).Bounds st out := by
  have hrun : (choleskyResourceTree p).exec I ![A, L]
      (fun v => (![n, ao, lo] v).eval) st = some out := by
    rw [FStmt.exec_eq_exec_toStmt, choleskyResourceTree_toStmt]
    exact hr
  have hb := (choleskyResourceTree p).bounds_staticCost_of_exec_eq_some I ![A, L]
    (fun v => (![n, ao, lo] v).eval) hrun
  have henv : (fun v : Fin 3 => (![n, ao, lo] v).eval) =
      ![n.eval, ao.eval, lo.eval] := by
    funext v
    fin_cases v <;> rfl
  rw [henv] at hb
  exact hb

/-- Symbolic first-order semidefinite Cholesky tree used by the existing static resource
    analysis. -/
def semidefiniteCholeskyResourceTree (p : P) : FStmt P ι 2 3 :=
  ((semidefiniteCholesky p (.var 0) 0 (.var 1) 1 (.var 2)).run.compile 2 3).get (by rfl)

private theorem semidefiniteCholeskyResourceTree_toStmt (p : P) (n ao lo : IExp ℕ)
    (A L : ℕ) :
    (semidefiniteCholeskyResourceTree (ι := ι) p).toStmt ![A, L] ![n, ao, lo] =
      (semidefiniteCholesky p n A ao L lo).run := by
  rfl

/-- Static operation-count and additional-live-memory summary of the actual semidefinite
    Cholesky tree.
The summary includes copies, pivot scans and every scoped allocation, under the supplied
instruction charges and per-tag bit widths. -/
noncomputable def semidefiniteCholeskyResources [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P)
    (N ao lo : ℕ) : StaticCost P ι :=
  (semidefiniteCholeskyResourceTree p).staticCost charge width ![N, ao, lo]

/-- Every successful actual semidefinite Cholesky run obeys its static count and live-memory
    bounds and
restores current cells and bits. Scalar semantics, store contents, offsets and oracles are
arbitrary; successful factorization is proved separately. -/
theorem bounds_semidefiniteCholesky {K : Type} [DecidableEq P]
    (I : Interp P ι K (OpCount P ι)) (p : P) (n : IExp ℕ) (A L : ℕ)
    (ao lo : IExp ℕ) {st out : St P K (OpCount P ι)}
    (hr : exec I (semidefiniteCholesky p n A ao L lo).run st = some out) :
    (semidefiniteCholeskyResources I.charge I.width p n.eval ao.eval lo.eval).Bounds st out := by
  have hrun : (semidefiniteCholeskyResourceTree p).exec I ![A, L]
      (fun v => (![n, ao, lo] v).eval) st = some out := by
    rw [FStmt.exec_eq_exec_toStmt, semidefiniteCholeskyResourceTree_toStmt]
    exact hr
  have hb := (semidefiniteCholeskyResourceTree p).bounds_staticCost_of_exec_eq_some I ![A, L]
    (fun v => (![n, ao, lo] v).eval) hrun
  have henv : (fun v : Fin 3 => (![n, ao, lo] v).eval) =
      ![n.eval, ao.eval, lo.eval] := by
    funext v
    fin_cases v <;> rfl
  rw [henv] at hb
  exact hb

/-- Symbolic first-order one-by-one-pivot LDL tree used by the existing static resource analysis. -/
def ldlResourceTree (p : P) : FStmt P ι 3 4 :=
  ((ldlFactor p (.var 0) 0 1 2 (.var 1) (.var 2) (.var 3)).run.compile 3 4).get (by rfl)

private theorem ldlResourceTree_toStmt (p : P) (n ao lo doff : IExp ℕ)
    (A L D : ℕ) :
    (ldlResourceTree (ι := ι) p).toStmt ![A, L, D] ![n, ao, lo, doff] =
      (ldlFactor p n A L D ao lo doff).run := by
  rfl

/-- Static operation-count and additional-live-memory summary of the actual one-by-one-pivot LDL
    tree.
The summary includes copies, pivot scans and every scoped allocation, under the supplied
instruction charges and per-tag bit widths. -/
noncomputable def ldlFactorResources [DecidableEq P]
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (p : P)
    (N ao lo doff : ℕ) : StaticCost P ι :=
  (ldlResourceTree p).staticCost charge width ![N, ao, lo, doff]

/-- Every successful actual one-by-one-pivot LDL run obeys its static count and live-memory
    bounds and
restores current cells and bits. Scalar semantics, store contents, offsets and oracles are
arbitrary; successful factorization is proved separately. -/
theorem bounds_ldlFactor {K : Type} [DecidableEq P]
    (I : Interp P ι K (OpCount P ι)) (p : P) (n : IExp ℕ) (A L D : ℕ)
    (ao lo doff : IExp ℕ) {st out : St P K (OpCount P ι)}
    (hr : exec I (ldlFactor p n A L D ao lo doff).run st = some out) :
    (ldlFactorResources I.charge I.width p n.eval ao.eval lo.eval doff.eval).Bounds st out := by
  have hrun : (ldlResourceTree p).exec I ![A, L, D]
      (fun v => (![n, ao, lo, doff] v).eval) st = some out := by
    rw [FStmt.exec_eq_exec_toStmt, ldlResourceTree_toStmt]
    exact hr
  have hb := (ldlResourceTree p).bounds_staticCost_of_exec_eq_some I ![A, L, D]
    (fun v => (![n, ao, lo, doff] v).eval) hrun
  have henv : (fun v : Fin 4 => (![n, ao, lo, doff] v).eval) =
      ![n.eval, ao.eval, lo.eval, doff.eval] := by
    funext v
    fin_cases v <;> rfl
  rw [henv] at hb
  exact hb

end NLAlib.Computation
