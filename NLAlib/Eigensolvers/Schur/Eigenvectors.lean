/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Completion
public import NLAlib.Matrix.FinitePrecision.TriangularSolve
public import NLAlib.Matrix.Spectral.TriangularEigenvectors
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# The eigenvector stage of the dense eigensolver

After a Schur solver has stored $\widehat{\mathbf{U}}$ and an upper triangular
$\widehat{\mathbf{T}}$, the eigenvector stage `NLAlib.Schur.triEigvecStage` computes the
eigenvectors of $\widehat{\mathbf{T}}$ by rounded back substitution with a pivot floor
$s_{\min} = \mathrm{fl}(\rho\,\mathrm{fl}\|\widehat{\mathbf{T}}\|_{\mathsf F})$ (LAPACK `xTREVC`,
`NLAlib.shiftedTriSolve`), normalizes each column and multiplies by $\widehat{\mathbf{U}}$. For
$\widehat{\mathbf{T}} = \mathbf{0}$ it copies $\widehat{\mathbf{U}}$. It meets the normwise
contract `NLAlib.Schur.EigenvectorStageContract`: the columns are approximate eigenvectors of
$\widehat{\mathbf{T}}$ with a gap-free residual
(`NLAlib.IsTriangularEigenbasisApprox.norm_mulVec_col_le`), the floor enters the residual only
when the flag is set, and no pivot is floored when the diagonal gaps exceed
$4\rho\|\widehat{\mathbf{T}}\|_{\mathsf F}$.

## Main definitions

* `NLAlib.Schur.triEigColumn`, `NLAlib.Schur.triEigenvectors`: one column and all columns.
* `NLAlib.Schur.triEigvecStage`: the stage `[N, ne] (T, U, Pe) → (V, G)`.

## Main results

* `NLAlib.Schur.triEigColumn_writes`, `NLAlib.Schur.triEigenvectors_writes`,
  `NLAlib.Schur.triEigenvectors_isTriangularEigenbasisApprox`, `NLAlib.Schur.triEigenvectors_flag`:
  the columns.
* `NLAlib.Schur.triEigvecStage_eigenvectorStageContract`: the stage meets the contract.
* `NLAlib.Schur.triEigvecStage_completes`: the stage completes on any scalar machine.
* `NLAlib.Schur.size_stmtCost_triEigvecStage_le`: its static count is $O(N^3)$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Schur

open Ops

variable {O Q : Type}

/-! ### The programs -/

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **One eigenvector column**: `[N, j] (T, Sm, Y, G) → (Y, G)` runs `NLAlib.shiftedTriSolve` on
column $j$ with the floor `Sm`, stores the unit entry and the zeros below it, and scales the
column by $\mathrm{fl}(1/\hat\nu)$, $\hat\nu$ the rounded norm of the column ($\hat\nu \ge 1$ up to
rounding, because of the unit entry).
Algorithm: dense-eigendecomposition -/
def triEigColumn : Impl O Q := opsImpl% [N, j] (T, Sm, Y, G) → (Y, G) {
  let Nu ← alloc 1;
  let R ← alloc 1;
  run (shiftedTriSolve (O := O) (Q := Q)).body [N, j] (T, Sm, Y, G, Y, G);
  call (Has.inj (ScalarOp.lit 1)) [] () → (Y[2 * (j * N + j)]);
  call (Has.inj (ScalarOp.lit 0)) [] () → (Y[2 * (j * N + j) + 1]);
  for l < N - 1 - j {
    call (Has.inj (ScalarOp.lit 0)) [] () → (Y[2 * (j * N + (j + 1 + l))]);
    call (Has.inj (ScalarOp.lit 0)) [] () → (Y[2 * (j * N + (j + 1 + l)) + 1])
  };
  run (RoundedScalarBlas.nrm2 (Op := O) (Tst := Q)).body [2 * N] (Y[2 * (j * N)], Nu);
  call (Has.inj (ScalarOp.lit 1)) [] () → (R);
  call (Has.inj ScalarOp.div) [] (R, Nu) → (R);
  for t < 2 * N {
    call (Has.inj ScalarOp.mul) [] (Y[2 * (j * N) + t], R) → (Y[2 * (j * N) + t])
  }
}

/-- **The eigenvector columns**: `[N] (T, Sm, Y, G) → (Y, G)` runs `NLAlib.Schur.triEigColumn` for
$j = 0, \dots, N - 1$.
Algorithm: dense-eigendecomposition -/
def triEigenvectors : Impl O Q := opsImpl% [N] (T, Sm, Y, G) → (Y, G) {
  for j < N {
    run (triEigColumn (O := O) (Q := Q)).body [N, j] (T, Sm, Y, G, Y, G)
  }
}

/-- **The eigenvector stage**: `[N, ne] (T, U, Pe) → (V, G)` with the floor parameter $\rho$ =
`Pe[0]`. It stores the flag $0$ and the rounded Frobenius norm $\hat s$ of $\mathbf{T}$
(`NLAlib.Schur.frobNormStage`); if $\hat s > 0$, the floor $s_{\min} = \mathrm{fl}(\rho\hat s)$,
the columns `NLAlib.Schur.triEigenvectors` into scratch $\mathbf{Y}$ and $\mathbf{V} =
\mathrm{fl}(\mathbf{U}\mathbf{Y})$ (`NLAlib.matMulOn`); otherwise $\mathbf{V} = \mathbf{U}$
exactly.
Algorithm: dense-eigendecomposition -/
def triEigvecStage : Impl O Q := opsImpl% [N, ne] (T, U, Pe) → (V, G) {
  let S ← alloc 1;
  let Sm ← alloc 1;
  let Y ← alloc (2 * (N * N));
  call (Has.inj IndexOp.lit) [0] () → (G);
  run (frobNormStage (O := O) (Q := Q)).body [N] (T, S);
  if (Has.inj CmpTst.isPos) [] (S) {
    call (Has.inj ScalarOp.mul) [] (Pe, S) → (Sm);
    run (triEigenvectors (O := O) (Q := Q)).body [N] (T, Sm, Y, G, Y, G);
    run (matMulOn (O := O) (Q := Q)).body [N, N, N, N, N, N, 0] (U, Y, V)
  } else {
    run (PairMatrix.copy (Op := O) (Tst := Q)).body [N, N] (U, V)
  }
}

end Program

/-! ### The columns -/

section Columns

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **One eigenvector column under the standard model**: on a scalar machine with the standard
model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact comparisons,
from a memory holding an upper triangular $\mathbf{T}$ of order $N$ at `t`, the floor
$s_{\min} \ge 0$ at `sm`, room for `Y` and a flag word at `g`, the four blocks live and apart, the
run for $j < N$ writes only column $j$ of `Y` and the flag: column $j$ holds a vector
$\mathbf{y}$ with $\lvert\|\mathbf{y}\| - 1\rvert \le 4(N + 2)\boldsymbol{u}$ that is a
componentwise
backward solution of $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with
$16(N + 1)\boldsymbol{u}$ and the floor $\tfrac72 s_{\min}$ if a pivot was floored (the flag the
literal $1$), $0$ otherwise (the flag unchanged); no pivot is floored when
$\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for $i < j$. -/
theorem triEigColumn_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 ≤ smin) (j : Fin N) {τ : Tape ℝ}
    {μ : Mem ℝ} (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (triEigColumn (O := O) (Q := Q)).body
      (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * N) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ (yv : Fin N → ℂ) (fl : Bool),
        (∀ i : Fin N, μ'.store.get y.1 (y.2 + 2 * (j * N + i)) = some (yv i).re ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) = some (yv i).im) ∧
        |‖WithLp.toLp 2 yv‖ - 1| ≤ 4 * ((N : ℝ) + 2) * u ∧
        IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u)
          (if fl then 7 / 2 * smin else 0) (T - T j j • 1) 0 yv ∧
        (fl = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (fl = false → μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) ∧
        ((∀ i : Fin N, i < j → 2 * smin < ‖T i i - T j j‖) → fl = false)) μ := by
  sorry

/-- **The eigenvector columns complete**: on a scalar machine with index literals and exact
comparisons, from a memory holding a matrix $\mathbf{T}$ of order $N$ at `t`, a word at `sm`,
room for `Y` and a flag word at `g`, the four blocks live and apart, the run writes only `Y` and
the flag, and stores a matrix in `Y` and a word in the flag. -/
theorem triEigenvectors_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ} {t sm y g : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hg : ∃ x : ℝ, μ.store.get g.1 g.2 = some x)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q)).body
      (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => (∃ Y : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix y Y μ'.store) ∧
        ∃ x : ℝ, μ'.store.get g.1 g.2 = some x) μ := by
  sorry

/-- **The eigenvector columns are an approximate triangular eigenbasis**: on a scalar machine with
the standard model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact
comparisons, from a memory holding an upper triangular $\mathbf{T}$ of order $N$ at `t`, the floor
$s_{\min} \ge 0$ at `sm`, room for `Y` and the flag $0$ at `g`, the four blocks live and apart,
the run stores a $\mathbf{Y}$ with `NLAlib.IsTriangularEigenbasisApprox` at
$(16(N + 1)\boldsymbol{u}, \tfrac72 s_{\min}, 4(N + 2)\boldsymbol{u})$, and the flag $0$ or the
literal $1$; with the flag $0$, the same with no floor. -/
theorem triEigenvectors_isTriangularEigenbasisApprox {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 ≤ smin) {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hg : μ.store.get g.1 g.2 = some 0)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q)).body
      (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ Y : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix y Y μ'.store ∧
        (μ'.store.get g.1 g.2 = some 0 ∨ μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) (7 / 2 * smin)
          (4 * ((N : ℝ) + 2) * u) T Y ∧
        (μ'.store.get g.1 g.2 = some 0 →
          IsTriangularEigenbasisApprox (16 * ((N : ℝ) + 1) * u) 0 (4 * ((N : ℝ) + 2) * u) T Y))
      μ := by
  sorry

/-- **No pivot is floored when the diagonal is separated**: on a scalar machine with the standard
model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact comparisons,
from the memory of `NLAlib.Schur.triEigenvectors_isTriangularEigenbasisApprox`, if
$\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for $i \ne j$, the run stores the flag $0$. -/
theorem triEigenvectors_flag {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    {smin : ℝ} (hsmin : 0 ≤ smin) {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hg : μ.store.get g.1 g.2 = some 0)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1])
    (hgap : ∀ i j, i ≠ j → 2 * smin < ‖T i i - T j j‖) :
    Writes .total I τ (triEigenvectors (O := O) (Q := Q)).body
      (Env.frame [N] [t, sm, y, g, y, g])
      (Store.inBlock y.1 y.2 (2 * (N * N)) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => μ'.store.get g.1 g.2 = some 0) μ := by
  sorry

end Columns

/-! ### The stage -/

section Stage

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The eigenvector stage meets its contract**: on a scalar machine with the standard model at
$\boldsymbol{u}$, $64(N_{\max} + 1)^2\boldsymbol{u} \le 1$, index literals, exact literals $0$, $1$
and exact comparisons, for the floor parameter $\rho > 0$, `NLAlib.Schur.triEigvecStage` with the
word $\rho$ meets `NLAlib.Schur.EigenvectorStageContract` with $c_{R,0} = 16(1 +
\sqrt{N_{\max}})(N_{\max} + 1)\boldsymbol{u}$, $c_R = c_{R,0} + 4\rho$,
$c_V = 8(N_{\max} + 1)\boldsymbol{u}$, $c_N = 4(N_{\max} + 2)\boldsymbol{u}$ and $g_0 = 4\rho$.
No printed source; the floor is that of LAPACK `xTREVC`. -/
theorem triEigvecStage_eigenvectorStageContract {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M 1) (hC : IsCmp id I) {nmax : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : 64 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1) :
    EigenvectorStageContract (16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u)
      (16 * (1 + √(nmax : ℝ)) * ((nmax : ℝ) + 1) * u + 4 * ρ) (8 * ((nmax : ℝ) + 1) * u)
      (4 * ((nmax : ℝ) + 2) * u) (4 * ρ) nmax [ρ] (triEigvecStage (O := O) (Q := Q)) I := by
  sorry

/-- **The eigenvector stage completes** on any scalar machine with index literals and exact
comparisons: for every order at most $N_{\max}$ and every stored pair it succeeds on every tape,
writing only $\mathbf{V}$ and the flag, and stores a matrix and a word. -/
theorem triEigvecStage_completes {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (nmax : ℕ) (ρ : ℝ) :
    CompletingEigenvectorStage nmax [ρ] (triEigvecStage (O := O) (Q := Q)) I := by
  sorry

/-- **The static count of the eigenvector stage**: its instrumented static count at the order
$n + 1$, $n_e$ words and zero offsets is at most $10^4(n + 1)^3$. -/
theorem size_stmtCost_triEigvecStage_le (n ne : ℕ) :
    Count.size (stmtCost (triEigvecStage (O := O) (Q := Q)).body.instrument
      [n + 1, ne, 0, 0, 0, 0, 0]) ≤ 10000 * (n + 1) ^ 3 := by
  sorry

end Stage

end NLAlib.Schur
