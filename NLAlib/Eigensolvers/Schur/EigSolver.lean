/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Verified
public import NLAlib.Eigensolvers.Schur.Completion
public import NLAlib.Matrix.Perturbation.ApproximateEigendecomposition

/-!
# The generic eigensolver: a Schur solver and an eigenvector stage

`NLAlib.Schur.eigSolverWith Solve Ev` runs a Schur solver `Solve` and then an eigenvector stage
`Ev` (`NLAlib.Schur.EigenvectorStageContract`) on its own words, and sets the flag to $1$ if the
stage flagged. If the Schur solver stores, except with probability $\varphi$, a Schur output of a
regularized matrix $\mathbf{X}$ with $s^{-1}\mathbf{X}$ of the class $(B, \Gamma)$
(`NLAlib.Schur.RegularizedSchurOutput`), the eigensolver stores, except with probability
$\varphi$, an approximate eigendecomposition (`NLAlib.Schur.EigOutput`): column and matrix
residuals, $\kappa(\widehat{\mathbf{V}}) \le 2\sqrt{n + 1}\,B$, the backward form and the gaps of
the diagonal (`NLAlib.eigDecompOf_of_schur`). If the Schur solver is verified on every tape, the
flag $0$ certifies the residual part on every tape (`NLAlib.eigResidualOf_of_schur`).

## Main definitions

* `NLAlib.Schur.eigSolverWith`: the program `[N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl)`.
* `NLAlib.Schur.EigSolverInput`, `NLAlib.Schur.eigFp`, `NLAlib.Schur.EigResidual`,
  `NLAlib.Schur.EigOutput`: its input memory, footprint and outputs.

## Main results

* `NLAlib.Schur.eigSolverWith_pwrites`: the Monte Carlo composition.
* `NLAlib.Schur.eigSolverWith_writes_residual`: the verified composition on every tape.
* `NLAlib.Schur.eigSolverWith_terminates`: termination on every tape.
* `NLAlib.Schur.size_stmtCost_eigSolverWith_le`: the static count.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Schur

open Ops MeasureTheory

variable {O Q : Type}

/-! ### Memories and outputs -/

/-- The input of the eigensolver: the pipeline's input for the solver words `qs` at `P`
(`NLAlib.Schur.SchurPipelineInput`), the stage's words `qe` at `Pe`, and room for $\mathbf{V}$;
the six blocks live and pairwise apart. -/
def EigSolverInput {n : ℕ} (qs qe : List ℝ) (a p pe uo v f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  SchurPipelineInput qs a p uo f A μ ∧ μ.Live [pe, v] ∧
    μ.Room [pe, v] [qe.length, 2 * ((n + 1) * (n + 1))] ∧
    Fp.Apart [a, p, uo, f, pe, v] [2 * ((n + 1) * (n + 1)), qs.length,
      2 * ((n + 1) * (n + 1)), 1, qe.length, 2 * ((n + 1) * (n + 1))] ∧
    μ.store.readBlock pe.1 pe.2 qe.length = some qe

/-- The blocks the eigensolver writes: those of the Schur solver and $\mathbf{V}$. -/
def eigFp (n : ℕ) (a uo v f : ℕ × ℕ) : Fp :=
  schurFp n a uo f ⊔ Store.inBlock v.1 v.2 (2 * ((n + 1) * (n + 1)))

/-- **The residual part of an eigendecomposition output**: stored $\widehat{\mathbf{T}}$ at `a`
and $\widehat{\mathbf{V}}$ at `v` with `NLAlib.EigResidualOf` against $\mathbf{A}$. -/
def EigResidual {n : ℕ} (a v : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c : ℝ) (μ' : Mem ℝ) : Prop :=
  ∃ T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a T μ'.store ∧
    HoldsMatrix v V μ'.store ∧ EigResidualOf A T V eC eM c

/-- **An eigendecomposition output**: the flag $0$ and stored $\widehat{\mathbf{T}}$ at `a` and
$\widehat{\mathbf{V}}$ at `v` with `NLAlib.EigDecompOf` against $\mathbf{A}$. -/
def EigOutput {n : ℕ} (a v f : ℕ × ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (eC eM c eE K g : ℝ) (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧ ∃ T V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    HoldsMatrix a T μ'.store ∧ HoldsMatrix v V μ'.store ∧ EigDecompOf A T V eC eM c eE K g

/-- **The memories holding an eigendecomposition output form a measurable set.** -/
theorem measurableSet_eigOutput {n : ℕ} (a v f : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (eC eM c eE K g : ℝ) :
    MeasurableSet {μ' : Mem ℝ | EigOutput a v f A eC eM c eE K g μ'} := by
  sorry

/-- **The memories holding the residual part of an eigendecomposition form a measurable set.** -/
theorem measurableSet_eigResidual {n : ℕ} (a v : ℕ × ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (eC eM c : ℝ) :
    MeasurableSet {μ' : Mem ℝ | EigResidual a v A eC eM c μ'} := by
  sorry

/-! ### The program -/

section Program

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The eigensolver** with a Schur solver `Solve` (`[N, nr, nq, k, F, T] (A, P) → (A, U, Fl)`)
and an eigenvector stage `Ev` (`[N, ne] (T, U, Pe) → (V, G)`): run the solver, then the stage on
the stored pair and its own words `Pe`, and set the flag to $1$ if the stage's flag is positive.
The interface is `[N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl)`.
Algorithm: dense-eigendecomposition -/
def eigSolverWith (Solve Ev : Impl O Q) : Impl O Q :=
  opsImpl% [N, nr, nq, k, F, T, ne] (A, P, Pe) → (A, U, V, Fl) {
    let G ← alloc 1;
    run Solve.body [N, nr, nq, k, F, T] (A, P, A, U, Fl);
    run Ev.body [N, ne] (A, U, Pe, V, G);
    if (Has.inj CmpTst.isPos) [] (G) {
      call (Has.inj IndexOp.lit) [1] () → (Fl)
    } else { skip }
  }

end Program

/-! ### The compositions -/

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The Monte Carlo composition of the eigensolver.** On a scalar machine with the standard
model, index literals, exact natural literals up to $n + 1$ and exact comparisons, a measurable
interpretation reading the tape only in its windows, let `Solve` store, except with probability
$\varphi$, a Schur output with its regularized matrix $\mathbf{X}$, $s^{-1}\mathbf{X}$ of the class
$(B, \Gamma)$ (`NLAlib.Schur.RegularizedSchurOutput` with the errors $e_R$, $e_X$, $e_U$), and let
`Ev` meet `NLAlib.Schur.EigenvectorStageContract` with $(c_{R,0}, c_R, c_V, c_N, g_0)$ at the
order $n + 1$ and the words `qe`. With $\eta$ = `eigEta n eX eU cR₀ cV` and $c$ =
`eigColTol n eU cV cN`, let $\Gamma > 0$, $B \ge 1$, $c_1 > 0$, $e_R + e_X \le 1/2$,
$e_U \le 1/8$, $c \le 1/8$, $16g_0\sqrt{n + 1} < 7c_1\Gamma$,
$e_X + 6e_U \le c_1\Gamma/(16(n + 1)B)$ and $8\sqrt{n + 1}\,B\eta \le c_1\Gamma$. Then from every
input of the eigensolver, except with probability $\varphi$, the run writes only $\mathbf{A}$,
$\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$ and the flag, and stores a Schur output with the
errors $(e_R + e_X, e_U)$ and an eigendecomposition output (`NLAlib.Schur.EigOutput`): column
residuals $e_R + \eta$, matrix residual $e_R + \sqrt{n + 1}\,\eta$, column tolerance $c$,
backward form $e_R + 2(n + 1)B\eta$, $\kappa \le 2\sqrt{n + 1}\,B$ and gaps
$\tfrac78c_1\Gamma\|\mathbf{A}\|_2$. No printed source. -/
theorem eigSolverWith_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {Solve Ev : Impl O Q} {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a p pe uo v f : ℕ × ℕ} {qs qe : List ℝ} {B Γ c₁ c₂ eR eX eU φ cR₀ cR cV cN g₀ : ℝ}
    (hSolve : PWrites law I Solve.body (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f])
      (schurFp n a uo f) (SchurPipelineInput qs a p uo f A)
      (RegularizedSchurOutput (IsConditionedDiagonalizable B Γ) a uo f A c₁ c₂ eR eX eU) φ)
    (hEv : EigenvectorStageContract cR₀ cR cV cN g₀ (n + 1) qe Ev I)
    (hΓ : 0 < Γ) (hB : 1 ≤ B) (hc₁ : 0 < c₁) (he : eR + eX ≤ 1 / 2) (heU : eU ≤ 1 / 8)
    (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hfloor : 16 * g₀ * √((n : ℝ) + 1) < 7 * c₁ * Γ)
    (hsep : eX + 6 * eU ≤ c₁ * Γ / (16 * (n + 1) * B))
    (hκ : 8 * √((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV ≤ c₁ * Γ) :
    PWrites law I (eigSolverWith Solve Ev).body
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (EigSolverInput qs qe a p pe uo v f A)
      (fun μ' => SchurOutput a uo f A (eR + eX) eU μ' ∧
        EigOutput a v f A (eR + eigEta n eX eU cR₀ cV)
          (eR + √((n : ℝ) + 1) * eigEta n eX eU cR₀ cV) (eigColTol n eU cV cN)
          (eR + 2 * ((n : ℝ) + 1) * B * eigEta n eX eU cR₀ cV)
          (2 * √((n : ℝ) + 1) * B) (7 / 8 * c₁ * Γ) μ') φ := by
  sorry

/-- **The verified composition of the eigensolver, on every tape.** On a scalar machine with the
standard model, index literals, exact natural literals up to $n + 1$ and exact comparisons, let
`Solve` store on every tape a pair at `a`, `uo` and, if its flag is $0$, a Schur output with the
errors $(e_A, e_U)$ (as `NLAlib.Schur.verifiedSchurWith` does), and let `Ev` meet
`NLAlib.Schur.EigenvectorStageContract` with $(c_{R,0}, c_R, c_V, c_N, g_0)$ at the order $n + 1$
and the words `qe`. With $\eta$ = `eigEta n eA eU cR₀ cV` and $c$ = `eigColTol n eU cV cN`, let
$e_A \le 1/2$, $e_U \le 1/8$ and $c \le 1/8$. Then from every input of the eigensolver, on every
tape, the run writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$ and the
flag, and if the flag is $0$ it stores a Schur output and the residual part of an
eigendecomposition (`NLAlib.Schur.EigResidual`): column residuals $\eta$, matrix residual
$\sqrt{n + 1}\,\eta$ and column tolerance $c$. No probability and no hypothesis on $\mathbf{A}$.
No printed source. -/
theorem eigSolverWith_writes_residual {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I) {Solve Ev : Impl O Q}
    {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p pe uo v f : ℕ × ℕ}
    {qs qe : List ℝ} {τ : Tape ℝ} {μ : Mem ℝ} {eA eU cR₀ cR cV cN g₀ : ℝ}
    (hSolve : ∀ τ μ, SchurPipelineInput qs a p uo f A μ →
      Writes .total I τ Solve.body (Env.frame [n + 1, nr, nq, k, F, T] [a, p, a, uo, f])
        (schurFp n a uo f) (fun μ' => (∃ U T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          HoldsSchurPair a uo U T μ'.store) ∧
          (μ'.store.get f.1 f.2 = some 0 → SchurOutput a uo f A eA eU μ')) μ)
    (hEv : EigenvectorStageContract cR₀ cR cV cN g₀ (n + 1) qe Ev I)
    (he : eA ≤ 1 / 2) (heU : eU ≤ 1 / 8) (hc : eigColTol n eU cV cN ≤ 1 / 8)
    (hin : EigSolverInput qs qe a p pe uo v f A μ) :
    Writes .total I τ (eigSolverWith Solve Ev).body
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 →
        SchurOutput a uo f A eA eU μ' ∧
        EigResidual a v A (eigEta n eA eU cR₀ cV) (√((n : ℝ) + 1) * eigEta n eA eU cR₀ cV)
          (eigColTol n eU cV cN) μ') μ := by
  sorry

/-- **The eigensolver terminates on every tape**: on a scalar machine with index literals and exact
comparisons, if `Solve` terminates on every tape with the accumulator within $e_U$ of orthonormal
(`NLAlib.Schur.TerminatingSchurSolver`) and `Ev` completes
(`NLAlib.Schur.CompletingEigenvectorStage`), then from every input of the eigensolver the run
succeeds on every tape, writes only $\mathbf{A}$, $\widehat{\mathbf{U}}$, $\widehat{\mathbf{V}}$
and the flag, and stores a matrix at `a`, $\widehat{\mathbf{U}}$ within $e_U$ of orthonormal and a
matrix at `v`. -/
theorem eigSolverWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hC : IsCmp id I) {Solve Ev : Impl O Q}
    {nr nq k F T : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a p pe uo v f : ℕ × ℕ}
    {qs qe : List ℝ} {eU : ℝ} {μ : Mem ℝ}
    (hSolve : TerminatingSchurSolver eU n [n + 1, nr, nq, k, F, T] qs Solve I)
    (hEv : CompletingEigenvectorStage (n + 1) qe Ev I)
    (hin : EigSolverInput qs qe a p pe uo v f A μ) (τ : Tape ℝ) :
    Writes .total I τ (eigSolverWith Solve Ev).body
      (Env.frame [n + 1, nr, nq, k, F, T, qe.length] [a, p, pe, a, uo, v, f]) (eigFp n a uo v f)
      (fun μ' => SchurOrth (n := n) a uo eU μ' ∧
        ∃ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix v V μ'.store) μ := by
  sorry

/-- **The static count of the eigensolver** with its structural instructions, at zero offsets, is
at most the instrumented counts of the solver and the stage at the offsets the eigensolver passes
to them, plus $128$ for the glue (the flag word, the branch and the frames). -/
theorem size_stmtCost_eigSolverWith_le (Solve Ev : Impl O Q) (N nr nq k F T ne : ℕ) :
    Count.size (stmtCost (eigSolverWith Solve Ev).body.instrument
        [N, nr, nq, k, F, T, ne, 0, 0, 0, 0, 0, 0, 0]) ≤
      Count.size (stmtCost Solve.body.instrument [N, nr, nq, k, F, T, 0, 0, 0, 0, 0]) +
        Count.size (stmtCost Ev.body.instrument [N, ne, 0, 0, 0, 0, 0]) + 128 := by
  sorry

end Theorems

end NLAlib.Schur
