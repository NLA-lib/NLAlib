/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Catalog.Scalar
public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Count

/-!
# Hestenes–Stiefel conjugate-gradient programs over operations

A round updates the iterate, residual and search direction in three distinct buffers. Its
operations have the shared scalar, BLAS1 and matrix-vector contracts. The tree is independent
of their implementations and arithmetic precision. Scalar division is used only under the
nonbreakdown hypotheses in the exact certificate.

The direction update copies the residual to scratch, performs an axpy and copies the result
back. These copies are counted explicitly. The current BLAS1 axpy contract requires its output
to be the last input and the scaled input to use a different buffer.

## Main results

* `NLAlib.Krylov.CG.HSCG.step` is one round, as a uniform first-order tree.
* `NLAlib.Krylov.CG.HSCG.staticCost_step` gives its operation counts.
* `NLAlib.Krylov.CG.HSCG.staticPeak_step_le` bounds its scratch storage.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- One Hestenes–Stiefel round from `(X,R,P)` to `(X,R,P)`. Scratch consists of the product
`Q`, the new direction `Z`, and four scalar cells. [HestenesStiefel1952, (3:1)]. -/
def step : Stmt Op Tst := ops% [n] (X, R, P) → (X, R, P) {
  let Q ← alloc n;
  let Z ← alloc n;
  let t ← alloc 4;
  call (Has.inj Blas1Op.dot) [n] (R, R) → (t[0]);
  call (Has.inj OperatorOp.matvec) [n, n] (P) → (Q);
  call (Has.inj Blas1Op.dot) [n] (P, Q) → (t[1]);
  call (Has.inj ScalarOp.div) [] (t[0], t[1]) → (t[2]);
  call (Has.inj Blas1Op.axpy) [n] (t[2], P, X) → (X);
  call (Has.inj ScalarOp.neg) [] (t[2]) → (t[2]);
  call (Has.inj Blas1Op.axpy) [n] (t[2], Q, R) → (R);
  call (Has.inj Blas1Op.dot) [n] (R, R) → (t[3]);
  call (Has.inj ScalarOp.div) [] (t[3], t[0]) → (t[3]);
  call (Has.inj Blas1Op.copy) [n] (R) → (Z);
  call (Has.inj Blas1Op.axpy) [n] (t[3], P, Z) → (Z);
  call (Has.inj Blas1Op.copy) [n] (Z) → (P)
}

/-- One round is a block implementation with dimension `n` and three inputs and outputs. -/
def stepImpl : Impl Op Tst := ⟨1, 3, 3, step⟩

/-- The counts of one round, including the copies used by the direction update. -/
noncomputable def stepCount (n : ℕ) : Count Op Tst :=
  3 • Count.one (Has.inj Blas1Op.dot) [n] + Count.one (Has.inj OperatorOp.matvec) [n, n] +
    2 • Count.one (Has.inj ScalarOp.div) [] + 3 • Count.one (Has.inj Blas1Op.axpy) [n] +
    Count.one (Has.inj ScalarOp.neg) [] + 2 • Count.one (Has.inj Blas1Op.copy) [n]

/-- The workspace bound of one round, in addition to the caller's live buffers. -/
def stepPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * n + 4 + max (W (Has.inj OperatorOp.matvec) [n, n])
    (max (W (Has.inj Blas1Op.dot) [n]) (max (W (Has.inj ScalarOp.div) [])
      (max (W (Has.inj Blas1Op.axpy) [n])
        (max (W (Has.inj ScalarOp.neg) []) (W (Has.inj Blas1Op.copy) [n])))))

/-- The evaluator's static counter computes the stated operation counts. -/
theorem staticCost_step (n a b c a' b' c' : ℕ) :
    staticCost (step (Op := Op) (Tst := Tst)) [n, a, b, c, a', b', c'] = stepCount n := by
  count_eval [step, stepCount]

/-- The evaluator's peak accounting is bounded by two vectors, four cells and a call workspace. -/
theorem staticPeak_step_le (W : Op → List ℕ → ℕ) (n a b c a' b' c' : ℕ) :
    staticPeak W (step (Op := Op) (Tst := Tst)) [n, a, b, c, a', b', c'] ≤ stepPeak W n := by
  simp [step, staticPeak, stepPeak]
  omega

end NLAlib.Krylov.CG.HSCG
