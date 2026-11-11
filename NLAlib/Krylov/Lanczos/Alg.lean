/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Ops.Catalog.Blas1
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Count

/-!
# The ordinary Lanczos program over operations

The program follows Paige's three-term order. Its basis and packed coefficient outputs are
initialized to zero, and a squared-norm guard controls every square root and normalization.
Early breakdown returns the initialized zero tail. Scalar, BLAS and matvec calls stay abstract.

## Main results

* `NLAlib.Krylov.Lanczos.update` computes the raw three-term residual and alpha.
* `NLAlib.Krylov.Lanczos.normalize` guards square root and normalization by a positive self-dot.
* `NLAlib.Krylov.Lanczos.solve` computes the complete requested basis and coefficients.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

section Zero

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Initialize an output block with the machine's literal zero. -/
def zero : Stmt Op Tst := ops% [n] () → (Q) {
  for i < n { call (Has.inj (ScalarOp.lit 0)) [] () → (Q[i]) }
}

/-- A zero fill reads no input block and initializes one output block. -/
def zeroImpl : Impl Op Tst := ⟨1, 0, 1, zero⟩

/-- A zero fill performs one literal call per output cell. -/
noncomputable def zeroCount (n : ℕ) : Count Op Tst :=
  n • Count.one (Has.inj (ScalarOp.lit 0)) []

/-- Static evaluation counts every initialized cell. -/
theorem staticCost_zero (n q : ℕ) :
    stmtCost (zero (Op := Op) (Tst := Tst)) [n, q] = zeroCount n := by
  simp [zero, zeroCount, stmtCost, useCost]

/-- The fill borrows only a literal implementation's workspace. -/
theorem staticPeak_zero_le (W : Op → List ℕ → ℕ) (n q : ℕ) :
    stmtPeak W (zero (Op := Op) (Tst := Tst)) [n, q] ≤ W (Has.inj (ScalarOp.lit 0)) [] := by
  simp only [zero, stmtPeak]
  exact Finset.sup_le fun _ _ => le_rfl

end Zero

section Update

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- The Paige-order update borrows Work and two scalar cells. Alpha is formed after subtracting
beta times Prev, and before subtracting alpha times Cur. [Paige1972, §2]. -/
def update : Stmt Op Tst := ops% [n] (Prev, Cur, Beta, Work, Alpha, t) → (Work, Alpha) {
  call (Has.inj OperatorOp.matvec) [n, n] (Cur) → (Work);
  call (Has.inj ScalarOp.neg) [] (Beta) → (t[1]);
  call (Has.inj Blas1Op.axpy) [n] (t[1], Prev, Work) → (Work);
  call (Has.inj Blas1Op.dot) [n] (Cur, Work) → (Alpha);
  call (Has.inj ScalarOp.neg) [] (Alpha) → (t[1]);
  call (Has.inj Blas1Op.axpy) [n] (t[1], Cur, Work) → (Work)
}

/-- The raw recurrence calls before the squared-norm and direction normalization. -/
noncomputable def updateCount (n : ℕ) : Count Op Tst :=
  Count.one (Has.inj OperatorOp.matvec) [n, n] + 2 • Count.one (Has.inj ScalarOp.neg) [] +
    2 • Count.one (Has.inj Blas1Op.axpy) [n] + Count.one (Has.inj Blas1Op.dot) [n]

/-- Static accounting follows the actual raw recurrence tree. -/
theorem staticCost_update (n p q b w a t w' a' : ℕ) :
    stmtCost (update (Op := Op) (Tst := Tst)) [n, p, q, b, w, a, t, w', a'] =
      updateCount n := by
  simp [update, updateCount, stmtCost, useCost]
  module

end Update

section Normalization

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- Normalize Work into the initially zero Q and beta outputs only when sigma is positive.
The zero branch leaves those outputs unchanged, so no zero norm reaches sqrt or division. -/
def normalize : Stmt Op Tst := ops% [n] (Work, sigma, Q, beta) → (Q, beta) {
  if (Has.inj CmpTst.isPos) [] (sigma) {
    call (Has.inj ScalarOp.sqrt) [] (sigma) → (beta);
    call (Has.inj Blas1Op.copy) [n] (Work) → (Q);
    call (Has.inj Blas1Op.scal) [n] (beta, Q) → (Q)
  } else { skip }
}

/-- Guarded normalization has four inputs and two aliased outputs. -/
def normalizeImpl : Impl Op Tst := ⟨1, 4, 2, normalize⟩

/-- The branch budget includes its test, square root, copy and reciprocal scaling. -/
noncomputable def normalizeCount (n : ℕ) : Count Op Tst :=
  Count.test (Has.inj CmpTst.isPos) [] + Count.one (Has.inj ScalarOp.sqrt) [] +
    Count.one (Has.inj Blas1Op.copy) [n] + Count.one (Has.inj Blas1Op.scal) [n]

/-- The zero branch costs no calls; the positive branch gives the static upper budget. -/
theorem staticCost_normalize (n w s q b q' b' : ℕ) :
    stmtCost (normalize (Op := Op) (Tst := Tst)) [n, w, s, q, b, q', b'] =
      normalizeCount n := by
  simp [normalize, normalizeCount, stmtCost, testCost, useCost]
  module

end Normalization

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
variable [Has CmpTst Tst]

/-- One round in the enclosing B,V,C,Prev,Work,t layout. The appended index is the round.
The raw update and normalization are separate frames so a reorthogonalization sweep can be
inserted between them. [Paige1972, §2]. -/
def advance : Stmt Op Tst :=
  .seq (.frame [.var 0]
    [⟨3, .const 0⟩, ⟨1, .var 3 + .var 5 * .var 0⟩, ⟨2, .var 4 + .var 1 + .var 5⟩,
      ⟨4, .const 0⟩, ⟨2, .var 4 + .var 5⟩, ⟨5, .const 0⟩,
      ⟨4, .const 0⟩, ⟨2, .var 4 + .var 5⟩] update)
    (.seq (.call (Has.inj Blas1Op.dot) [.var 0]
      [⟨4, .const 0⟩, ⟨4, .const 0⟩] [⟨5, .const 0⟩])
      (.seq (.call (Has.inj Blas1Op.copy) [.var 0]
        [⟨1, .var 3 + .var 5 * .var 0⟩] [⟨3, .const 0⟩])
        (.frame [.var 0]
          [⟨4, .const 0⟩, ⟨5, .const 0⟩,
            ⟨1, .var 3 + (.var 5 + .const 1) * .var 0⟩,
            ⟨2, .var 4 + .var 1 + .var 5 + .const 1⟩,
            ⟨1, .var 3 + (.var 5 + .const 1) * .var 0⟩,
            ⟨2, .var 4 + .var 1 + .var 5 + .const 1⟩] normalize)))

/-- Stop before another active round when the last squared norm is zero, or at the cap. -/
def rounds : Stmt Op Tst :=
  .whileFuel (.var 1) (Has.inj CmpTst.isPos) [] [⟨5, .const 0⟩] advance .skip

/-- Initialize the shared output prefix and any extra coefficient suffix. Borrowed storage is
B,V,C,Prev,t; the coefficient length is an explicit dimension so reorthogonalization can add ν.
No work-vector buffer is needed during initialization. -/
def initializeState : Stmt Op Tst :=
  .seq (.frame [(.var 1 + .const 1) * .var 0] [⟨1, .var 4⟩] zero)
    (.seq (.frame [.var 2] [⟨2, .var 5⟩] zero)
      (.seq (.frame [.var 0] [⟨3, .var 6⟩] zero)
        (.seq (.call (Has.inj Blas1Op.dot) [.var 0]
          [⟨0, .var 3⟩, ⟨0, .var 3⟩] [⟨4, .var 7⟩])
          (.frame [.var 0]
            [⟨0, .var 3⟩, ⟨4, .var 7⟩, ⟨1, .var 4⟩,
              ⟨2, .var 5 + .const 2 * .var 1 + .const 1⟩,
              ⟨1, .var 4⟩, ⟨2, .var 5 + .const 2 * .var 1 + .const 1⟩] normalize))))

/-- Initialize zero output tails and the previous vector, form the initial direction with a
positive-only normalization, then execute at most cap rounds. [Paige1972, §2]. -/
def solve : Stmt Op Tst :=
  .alloc (.var 0) (.alloc (.var 0) (.alloc (.const 2)
    (.seq (.frame [.var 0, .var 1, .const 2 * .var 1 + .const 2]
      [⟨0, .var 2⟩, ⟨1, .var 3⟩, ⟨2, .var 4⟩, ⟨3, .const 0⟩, ⟨5, .const 0⟩] initializeState)
      rounds)))

/-- The complete program has dimensions n,cap, one input and two packed outputs. -/
def solveImpl : Impl Op Tst := ⟨2, 1, 2, solve⟩

/-- Calls and normalization test of one active round; the loop adds its continuation test. -/
noncomputable def advanceCount (n : ℕ) : Count Op Tst :=
  updateCount n + Count.one (Has.inj Blas1Op.dot) [n] +
    Count.one (Has.inj Blas1Op.copy) [n] + normalizeCount n

/-- Initialization, every zeroed output cell, and at most cap tested Lanczos rounds. -/
noncomputable def solveCount (n cap : ℕ) : Count Op Tst :=
  zeroCount ((cap + 1) * n) + zeroCount (2 * cap + 2) + zeroCount n +
    Count.one (Has.inj Blas1Op.dot) [n] + normalizeCount n +
    cap • (Count.test (Has.inj CmpTst.isPos) [] + advanceCount n)

end NLAlib.Krylov.Lanczos
