/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveTermination
public import NLAlib.Eigensolvers.Schur.Contracts

/-!
# The order-one leaf of the small-eigenvalue solver

The worklist of the small-eigenvalue solver runs at the bottom width $k = 1$, so its leaves are
blocks of order $0$ or $1$, whose eigenvalue is the entry itself ([BanksGarzaVargasSrivastava2025,
§6], the base case, the paper's erratum P13). In Schur mode the leaf keeps the block, which is
already upper triangular, and writes the identity accumulator: exact on
every tape, with backward error $0$ and failure $0$ on orders at most $1$.

## Main definitions

* `NLAlib.SmallEig.identityLeaf`: the order-one Schur leaf `[d, np, T] (Bk, P) → (Bk, Ub)`.

## Main results

* `NLAlib.SmallEig.identityLeaf_writes`,
  `NLAlib.SmallEig.identityLeaf_randomSchurLeafContract`,
  `NLAlib.SmallEig.identityLeaf_terminates`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

variable {O Q : Type} [Has ScalarOp O]

/-- **The order-one Schur leaf**: a block of order $d \le 1$ is already upper triangular, so it is
kept and its accumulator `Ub` is the identity of order $d$ (column-major pairs). The interface is
`[d, np, T] (Bk, P) → (Bk, Ub)`, that of the Schur leaf routine of
`NLAlib.ShiftedQR.solveRoundedWith`; the block, the words and the cap are not read. At any order
it writes the identity.
Algorithm: small-eig -/
def identityLeaf : Impl O Q := opsImpl% [d, np, T] (Bk, P) → (Bk, Ub) {
  for j < d {
    for i < d {
      call (Has.inj (ScalarOp.lit 0)) [] () → (Ub[2 * (j * d + i)]);
      call (Has.inj (ScalarOp.lit 0)) [] () → (Ub[2 * (j * d + i) + 1])
    }
  };
  for i < d {
    call (Has.inj (ScalarOp.lit 1)) [] () → (Ub[2 * (i * d + i)])
  }
}

/-- `NLAlib.SmallEig.identityLeaf` on a scalar machine with the literals $0$ and $1$ exact, at any
order $d$: with room for $2d^2$ words at `ub`, apart from the block, on every tape, it writes only
those words and stores the identity of order $d$. -/
theorem identityLeaf_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) {τ : Tape ℝ} {μ : Mem ℝ} {d : ℕ} {w p ub : ℕ × ℕ}
    {ps : List ℝ} {T : ℕ} (hl : μ.Live [w, p, ub]) (hroom : ub.2 + 2 * (d * d) ≤ μ.store.len ub.1)
    (hwu : Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d))) (Store.inBlock ub.1 ub.2 (2 * (d * d)))) :
    Writes .total I τ (identityLeaf (O := O) (Q := Q)).body
        (Env.frame [d, ps.length, T] [w, p, w, ub])
      (Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix ub (1 : Matrix (Fin d) (Fin d) ℂ) μ'.store) μ :=
  sorry

/-- **The order-one Schur leaf meets the Schur leaf contract** with errors $0$, for orders at most
$1$: a block of order at most $1$ is upper triangular, kept, with the identity accumulator. -/
theorem identityLeaf_randomSchurLeafContract {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (law : ℕ → Measure ℝ) (Nmax : ℝ)
    (ps : List ℝ) (T : ℕ) :
    Schur.RandomSchurLeafContract law 0 0 0 1 Nmax ps T (identityLeaf (O := O) (Q := Q)) I :=
  sorry

/-- The order-one Schur leaf terminates on every tape, with its accumulator exactly unitary on
orders at most $1$ (`NLAlib.ShiftedQR.TerminatingLeafRoutine` at $\varepsilon_L = 0$). -/
theorem identityLeaf_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (h0 : M.lit 0 = 0) (h1 : M.lit 1 = 1) (ps : List ℝ) (T : ℕ) :
    TerminatingLeafRoutine 0 1 ps T (identityLeaf (O := O) (Q := Q)) I :=
  sorry

end NLAlib.SmallEig
