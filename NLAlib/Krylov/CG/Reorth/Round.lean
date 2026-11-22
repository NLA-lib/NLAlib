/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Alg
public import NLAlib.Krylov.CG.Reorth.Exact

/-!
# A CG round with full residual reorthogonalization

The round forms the new iterate and residual, sweeps that residual against every stored
column, and only then computes its squared norm and the new search direction. The prefix and
suffix borrow the round's scratch. The standalone sweep frees its two cells before the suffix.

## Main results

* `NLAlib.Krylov.CG.Reorth.round` is the uniform reorthogonalized round.
* `NLAlib.Krylov.CG.Reorth.staticCost_round` counts the round and every projection.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Form the iterate and raw residual, saving the old residual self-product in `t[0]`. -/
def update : Stmt Op Tst := ops% [n] (X, R, P, W, t) → (X, R) {
  call (Has.inj Blas1Op.dot) [n] (R, R) → (t[0]);
  call (Has.inj OperatorOp.matvec) [n, n] (P) → (W);
  call (Has.inj Blas1Op.dot) [n] (P, W) → (t[1]);
  call (Has.inj ScalarOp.div) [] (t[0], t[1]) → (t[2]);
  call (Has.inj Blas1Op.axpy) [n] (t[2], P, X) → (X);
  call (Has.inj ScalarOp.neg) [] (t[2]) → (t[2]);
  call (Has.inj Blas1Op.axpy) [n] (t[2], W, R) → (R)
}

/-- Form the new direction using the swept residual and the saved old self-product. -/
def direction : Stmt Op Tst := ops% [n] (R, P, Z, t) → (P) {
  call (Has.inj Blas1Op.dot) [n] (R, R) → (t[3]);
  call (Has.inj ScalarOp.div) [] (t[3], t[0]) → (t[3]);
  call (Has.inj Blas1Op.copy) [n] (R) → (Z);
  call (Has.inj Blas1Op.axpy) [n] (t[3], P, Z) → (Z);
  call (Has.inj Blas1Op.copy) [n] (Z) → (P)
}

/-- The dimensions are `n,k`; inputs are `X,R,P,Q` and outputs are `X,R,P`.
The basis `Q` contains `k` columns. Projection precedes the new norm and direction update. -/
def round : Stmt Op Tst := ops% [n, k] (X, R, P, Q) → (X, R, P) {
  let W ← alloc n;
  let Z ← alloc n;
  let t ← alloc 4;
  run (update (Op := Op) (Tst := Tst)) [n] (X, R, P, W, t, X, R);
  run (sweepRoutine (Op := Op) (Tst := Tst)) [n, k] (Q, R);
  run (direction (Op := Op) (Tst := Tst)) [n] (R, P, Z, t, P)
}

/-- The ordinary round's calls plus every full projection against the basis. -/
noncomputable def roundCount (n k : ℕ) : Count Op Tst :=
  HSCG.stepCount n + sweepCount n k

/-- The ordinary round's workspace plus the sweep's two transient scalar cells. -/
def roundPeak (W : Op → List ℕ → ℕ) (n : ℕ) : ℕ := HSCG.stepPeak W n + 2

/-- The static evaluator counts both the CG recurrence and its complete projection sweep. -/
theorem staticCost_round (n k x r p q x' r' p' : ℕ) :
    stmtCost (round (Op := Op) (Tst := Tst)) [n, k, x, r, p, q, x', r', p'] =
      roundCount n k := by
  simp [round, update, direction, sweepRoutine, sweep, stmtCost, useCost, roundCount,
    HSCG.stepCount, sweepCount]
  module

/-- The sweep reuses the outer vector scratch and adds only its two temporary scalar cells. -/
theorem staticPeak_round_le (W : Op → List ℕ → ℕ) (n k x r p q x' r' p' : ℕ) :
    stmtPeak W (round (Op := Op) (Tst := Tst)) [n, k, x, r, p, q, x', r', p'] ≤
      roundPeak W n := by
  have hs := staticPeak_sweep_le (Op := Op) (Tst := Tst) W n k q r r
  simp only [sweepPeak] at hs
  simp [round, update, direction, sweepRoutine, stmtPeak, roundPeak, HSCG.stepPeak]
  omega

end NLAlib.Krylov.CG.Reorth
