/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Count

/-!
# Residual reorthogonalization over operations

The full sweep visits every stored residual column. The columns need not be normalized:
the coefficient is the dot product divided by the column's squared norm. Scalar and BLAS
operations stay abstract, so the same tree can be linked to different implementations.

## Main results

* `NLAlib.Krylov.CG.Reorth.sweep` is the uniform sweep tree.
* `NLAlib.Krylov.CG.Reorth.staticCost_sweep` gives its operation counts.
* `NLAlib.Krylov.CG.Reorth.staticPeak_sweep_le` bounds scratch storage.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op]

/-- Sweep a residual against all `k` columns of an `n × k` stored basis. -/
def sweep : Stmt Op Tst := ops% [n, k] (Q, R) → (R) {
  let t ← alloc 2;
  for j < k {
    call (Has.inj Blas1Op.dot) [n] (Q[j * n], R) → (t[0]);
    call (Has.inj Blas1Op.dot) [n] (Q[j * n], Q[j * n]) → (t[1]);
    call (Has.inj ScalarOp.div) [] (t[0], t[1]) → (t[0]);
    call (Has.inj ScalarOp.neg) [] (t[0]) → (t[0]);
    call (Has.inj Blas1Op.axpy) [n] (t[0], Q[j * n], R) → (R)
  }
}

/-- The sweep has two dimensions, a basis and residual input, and one residual output. -/
def sweepImpl : Impl Op Tst := ⟨2, 2, 1, sweep⟩

/-- Two dots, division, negation and one vector update per stored column. -/
noncomputable def sweepCount (n k : ℕ) : Count Op Tst :=
  k • (2 • Count.one (Has.inj Blas1Op.dot) [n] +
    Count.one (Has.inj ScalarOp.div) [] + Count.one (Has.inj ScalarOp.neg) [] +
    Count.one (Has.inj Blas1Op.axpy) [n])

/-- Two scalar scratch cells and the largest workspace of an operation in the sweep. -/
def sweepPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  2 + max (W (Has.inj Blas1Op.dot) [n]) (max (W (Has.inj ScalarOp.div) [])
    (max (W (Has.inj ScalarOp.neg) []) (W (Has.inj Blas1Op.axpy) [n])))

/-- The static evaluator counts every projection operation. -/
theorem staticCost_sweep (n k q r r' : ℕ) :
    staticCost (sweep (Op := Op) (Tst := Tst)) [n, k, q, r, r'] = sweepCount n k := by
  simp [sweep, staticCost, useCost, sweepCount]
  module

/-- Scratch is reused at every column, including an empty sweep. -/
theorem staticPeak_sweep_le (W : Op → List ℕ → ℕ) (n k q r r' : ℕ) :
    staticPeak W (sweep (Op := Op) (Tst := Tst)) [n, k, q, r, r'] ≤ sweepPeak W n := by
  simp only [sweep, staticPeak, sweepPeak]
  refine Nat.add_le_add_left (Finset.sup_le fun j _ => ?_) _
  simp

end NLAlib.Krylov.CG.Reorth
