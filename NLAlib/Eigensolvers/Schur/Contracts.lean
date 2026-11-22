/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.StoredMatrix
public import NLAlib.Matrix.Perturbation.EigenvalueBackward
public import NLAlib.Matrix.Factorizations.Hessenberg
public import NLAlib.Ops.Logic.Probabilistic

/-!
# Contracts of the stages of a dense Schur solver

A dense Schur solver is a pipeline of four stages, each a routine parameter with a contract that
mentions no particular algorithm: a two-sided estimate of the Frobenius norm, a randomized
regularizer into a class of matrices, a Hessenberg reducer that accumulates its unitary, and a
randomized Schur core on upper Hessenberg input. The reducer and the core state their stored
accumulator through the tracked relation `NLAlib.IsTrackedUnitarySimilar` (a relative accumulator
error $\varepsilon_U$ and a backward error $\varepsilon_T$), so that the stages compose by its
`trans`. Each contract fixes its constants outside the quantifier over orders and memories.

## Main definitions

* `NLAlib.Schur.FrobNormEstimateContract`, `NLAlib.Schur.RandomRegularizerContract`,
  `NLAlib.Schur.HessenbergReducerContract`, `NLAlib.Schur.RandomSchurCoreContract`: the four
  stage contracts.
* `NLAlib.Schur.TerminatingSchurCore`: the all-tape companion of a core.
* `NLAlib.Schur.HoldsSchurPair`: the stored pair $(\widehat{\mathbf{U}}, \mathbf{T})$.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops MeasureTheory

variable {O Q : Type} [Inhabited ℝ]

/-- The stored pair: the matrix `T` at `a` and the accumulator `U` at `uo`. -/
def HoldsSchurPair {n : ℕ} (a uo : ℕ × ℕ) (U T : Matrix (Fin n) (Fin n) ℂ) (s : Store ℝ) :
    Prop :=
  HoldsMatrix a T s ∧ HoldsMatrix uo U s

/-- **A two-sided Frobenius norm estimate**, deterministic: for every order $N \le N_{\max}$,
`[N] (A) → (S)`, the output in another buffer, stores $x$ with
$c_1\|\mathbf{A}\|_{\mathsf F} \le x \le c_2\|\mathbf{A}\|_{\mathsf F}$. A rounded estimate has
constants that depend on the order, so the order is bounded outside the quantifier. -/
def FrobNormEstimateContract (c₁ c₂ : ℝ) (nmax : ℕ) (Nm : Stmt O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {N : ℕ} {a s : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A : Matrix (Fin N) (Fin N) ℂ),
    N ≤ nmax → HoldsMatrix a A μ.store → μ.Live [a, s] → s.2 + 1 ≤ μ.store.len s.1 →
    a.1 ≠ s.1 →
    Writes .total I tape Nm (Env.frame [N] [a, s]) (Store.inBlock s.1 s.2 1)
      (fun μ' => ∃ x : ℝ, μ'.store.get s.1 s.2 = some x ∧ c₁ * frobNorm A ≤ x ∧
        x ≤ c₂ * frobNorm A) μ

/-- **A randomized regularizer into the class `C`**: `[N, np] (A, P) → (A)` with the parameter
words `ps`; for every order at most `nmax` and input of norm at most `S`, except with probability
$\varphi$ the stored matrix is $\mathbf{A} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta$ and
`C (A + E)`. -/
def RandomRegularizerContract (law : ℕ → Measure ℝ) (δ φ : ℝ)
    (C : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop) (nmax : ℕ) (S : ℝ)
    (ps : List ℝ) (Reg : Stmt O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a q : ℕ × ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), n + 1 ≤ nmax →
    specNorm A ≤ S →
    PWrites law I Reg (Env.frame [n + 1, ps.length] [a, q, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => HoldsMatrix a A μ.store ∧ μ.store.readBlock q.1 q.2 ps.length = some ps ∧
        μ.Live [a, q] ∧
        Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
          (Store.inBlock q.1 q.2 ps.length))
      (fun μ' => ∃ E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a (A + E) μ'.store ∧ specNorm E ≤ δ ∧ C (A + E)) φ

/-- **A Hessenberg reducer with an accumulated unitary**, deterministic: for every order
$N \le N_{\max}$, `[N] (A, U) → (A, U)` stores an upper Hessenberg $\mathbf{H}$ and an
accumulator, tracked from $(\mathbf{U}, \mathbf{A})$ with the relative accumulator error
$\varepsilon_U$ and the backward error $\varepsilon_T\|\mathbf{A}\|_2$. A rounded reducer has
errors that grow with the order, so the order is bounded outside the quantifier. -/
def HessenbergReducerContract (εU εT : ℝ) (nmax : ℕ) (Red : Stmt O Q) (I : Interp O Q ℝ) :
    Prop :=
  ∀ {N : ℕ} {a uo : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ} (A U : Matrix (Fin N) (Fin N) ℂ),
    N ≤ nmax → HoldsSchurPair a uo U A μ.store → μ.Live [a, uo] →
    Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock uo.1 uo.2 (2 * (N * N))) →
    Writes .total I tape Red (Env.frame [N] [a, uo, a, uo])
      (Store.inBlock a.1 a.2 (2 * (N * N)) ⊔ Store.inBlock uo.1 uo.2 (2 * (N * N)))
      (fun μ' => ∃ U' H : Matrix (Fin N) (Fin N) ℂ, HoldsSchurPair a uo U' H μ'.store ∧
        IsUpperHessenberg H ∧ IsTrackedUnitarySimilar εU (εT * specNorm A) U A U' H) μ

/-- **A randomized Schur core from the class `C'`** on upper Hessenberg input:
`[N, np, k, F, T] (A, P, U) → (A, U, Fl)` (the last three dimensions are the core's own); for
every order at most `nmax` and input of norm at most `S`, except with probability $\varphi$ the
flag is $0$, the stored matrix is upper triangular, and the pair is tracked from $(\mathbf{U},
\mathbf{H})$ with $(\varepsilon_U, \varepsilon_T)$. Any threshold is among the words `ps`. -/
def RandomSchurCoreContract (law : ℕ → Measure ℝ) (εU εT φ : ℝ)
    (C' : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → Prop) (k F T nmax : ℕ)
    (S : ℝ) (ps : List ℝ) (Core : Stmt O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a p uo f : ℕ × ℕ} (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    n + 1 ≤ nmax → IsUpperHessenberg H → specNorm H ≤ S → C' H →
    PWrites law I Core (Env.frame [n + 1, ps.length, k, F, T] [a, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => HoldsSchurPair a uo U H μ.store ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps ∧ μ.Live [a, p, uo, f] ∧
        f.2 + 1 ≤ μ.store.len f.1 ∧
        Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1])
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsSchurPair a uo U' Tm μ'.store ∧ Tm.IsUpperTriangular ∧
        IsTrackedUnitarySimilar εU εT U H U' Tm) φ

/-- **The all-tape companion of a core**: for every order at most `nmax`, on every tape the core
is total and the accumulator stays within $\varepsilon_U\|\mathbf{U}\|_2$ of $\mathbf{U}\mathbf{V}$
for an exact unitary $\mathbf{V}$, whatever the shifts. -/
def TerminatingSchurCore (εU : ℝ) (k F T nmax : ℕ) (ps : List ℝ) (Core : Stmt O Q)
    (I : Interp O Q ℝ) : Prop :=
  ∀ {n : ℕ} {a p uo f : ℕ × ℕ} {tape : Tape ℝ} {μ : Mem ℝ}
    (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), n + 1 ≤ nmax →
    HoldsSchurPair a uo U H μ.store → μ.store.readBlock p.1 p.2 ps.length = some ps →
    μ.Live [a, p, uo, f] → f.2 + 1 ≤ μ.store.len f.1 →
    Fp.Apart [a, p, uo, f] [2 * ((n + 1) * (n + 1)), ps.length, 2 * ((n + 1) * (n + 1)), 1] →
    Writes .total I tape Core (Env.frame [n + 1, ps.length, k, F, T] [a, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => ∃ U' Tm V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsSchurPair a uo U' Tm μ'.store ∧ HasOrthonormalCols V ∧
        specNorm (U' - U * V) ≤ εU * specNorm U) μ

/-- **A randomized small-block Schur solver** (a leaf of the deflation worklist), for every block
of order at most `kmax` and norm at most `Nmax`: `[d, np, T] (Bk, P) → (Bk, Ub)` stores, except
with probability $\varphi$, an upper triangular $\mathbf{T}_b$ and an accumulator tracked from
$(\mathbf{I}, \mathbf{B})$ with $(\varepsilon_U, \varepsilon_T)$. -/
def RandomSchurLeafContract (law : ℕ → Measure ℝ) (εU εT φ : ℝ) (kmax : ℕ) (Nmax : ℝ)
    (ps : List ℝ) (T : ℕ) (L : Stmt O Q) (I : Interp O Q ℝ) : Prop :=
  ∀ {d : ℕ} {w p ub : ℕ × ℕ} (B : Matrix (Fin d) (Fin d) ℂ), d ≤ kmax → specNorm B ≤ Nmax →
    PWrites law I L (Env.frame [d, ps.length, T] [w, p, w, ub])
      (Store.inBlock w.1 w.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (fun μ => HoldsMatrix w B μ.store ∧ μ.store.readBlock p.1 p.2 ps.length = some ps ∧
        μ.Live [w, p, ub] ∧ ub.2 + 2 * (d * d) ≤ μ.store.len ub.1 ∧
        Fp.Apart [w, p, ub] [2 * (d * d), ps.length, 2 * (d * d)])
      (fun μ' => ∃ Ub Tb : Matrix (Fin d) (Fin d) ℂ, HoldsSchurPair w ub Ub Tb μ'.store ∧
        Tb.IsUpperTriangular ∧ IsTrackedUnitarySimilar εU εT 1 B Ub Tb) φ

end NLAlib.Schur
