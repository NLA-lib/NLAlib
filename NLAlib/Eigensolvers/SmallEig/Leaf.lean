/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination

/-!
# The order-one leaf of the small-eigenvalue solver

The worklist of the small-eigenvalue solver runs at the bottom width $k = 1$, so its leaves are
blocks of order $0$ or $1$, whose eigenvalue is the entry itself ([BanksGarzaVargasSrivastava2025,
§6], the base case, the paper's erratum P13). The leaf copies the diagonal entries: exact on
every tape, with backward error $0$ and failure $0$ on orders at most $1$.

## Main definitions

* `NLAlib.SmallEig.copyLeaf`: the program `[d, np, T] (Bk, P) → (Ev)`.

## Main results

* `NLAlib.SmallEig.copyLeaf_randomLeafRoutineContract`, `NLAlib.SmallEig.copyLeaf_terminates`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

variable {O Q : Type} [Has ScalarOp O]

/-- **The order-one leaf**: copy the $d$ diagonal entries of the order-$d$ block `Bk` to `Ev`
(pairs). The interface is `[d, np, T] (Bk, P) → (Ev)`, that of the leaf routine of
`NLAlib.ShiftedQR.solveRoundedWith`; the words and the cap are not read.
Algorithm: small-eig -/
def copyLeaf : Impl O Q := opsImpl% [d, np, T] (Bk, P) → (Ev) {
  for i < d {
    call (Has.inj ScalarOp.copy) [] (Bk[2 * (i * d + i)]) → (Ev[2 * i]);
    call (Has.inj ScalarOp.copy) [] (Bk[2 * (i * d + i) + 1]) → (Ev[2 * i + 1])
  }
}

/-- **The leaf is exact on orders at most one** ([BanksGarzaVargasSrivastava2025, §6], the base
case): on a scalar machine, `NLAlib.SmallEig.copyLeaf` meets
`NLAlib.ShiftedQR.RandomLeafRoutineContract` with backward error $0$ and failure probability $0$
on orders at most $1$, for every norm bound, parameter words and cap, under every stream law. -/
theorem copyLeaf_randomLeafRoutineContract {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (law : ℕ → Measure ℝ) (Nmax : ℝ) (ps : List ℝ) (T : ℕ) :
    RandomLeafRoutineContract law 0 0 1 Nmax ps T (copyLeaf (O := O) (Q := Q)) I := by
  sorry

/-- The leaf terminates on every tape, at every order bound: on a scalar machine
`NLAlib.SmallEig.copyLeaf` is a terminating leaf routine
(`NLAlib.ShiftedQR.TerminatingLeafRoutine`) for every order bound, parameter words and cap. -/
theorem copyLeaf_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I) (kmax : ℕ)
    (ps : List ℝ) (T : ℕ) : TerminatingLeafRoutine kmax ps T (copyLeaf (O := O) (Q := Q)) I := by
  sorry

end NLAlib.SmallEig
