/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.StoredProducts
public import NLAlib.Matrix.Perturbation.ComponentwiseBackward
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Compare

/-!
# Rounded shifted back substitution with a pivot floor

The eigenvector of an upper triangular $\mathbf{T}$ for its $j$-th diagonal entry is
$(\mathbf{x}; 1; \mathbf{0})$ with $(\mathbf{T}_{11} - t_{jj}\mathbf{I})\mathbf{x} =
-\mathbf{t}_{1j}$, $\mathbf{T}_{11}$ the leading block of order $j$ (LAPACK `xTREVC`). The
program `NLAlib.shiftedTriSolve` solves this system by rounded back substitution, $i = j - 1,
\dots, 0$: the pivot $\hat m = \mathrm{fl}(t_{ii} - t_{jj})$, floored to $s_{\min}$ (and the flag
set) when $\mathrm{fl}(\lvert\hat m\rvert^2) \le \mathrm{fl}(s_{\min}^2)$; the sum
$\hat s_i = \mathrm{fl}(t_{ij} + \sum_{i < k < j}t_{ik}\hat x_k)$ by rounded complex
multiply–adds; and $\hat x_i = -\mathrm{fl}(\hat s_i/\hat m)$. Under the standard model the
computed column is a componentwise backward solution of $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y}
= \mathbf{0}$ (`NLAlib.IsComponentwiseBackwardSolution`), with a diagonal floor only when a pivot
was floored, and no pivot is floored when the diagonal gaps exceed $2s_{\min}$.

## Main definitions

* `NLAlib.shiftedTriSolve`: the program.
* `NLAlib.shiftedTriSolveWord`, `NLAlib.shiftedTriSolveColumn`, `NLAlib.shiftedTriSolveFlag`: the
  words it computes on a machine, the column $(\hat{\mathbf{x}}; 1; \mathbf{0})$ and the flag.

## Main results

* `NLAlib.shiftedTriSolve_writes_word`: the program stores the computed words and the flag.
* `NLAlib.shiftedTriSolve_isComponentwiseBackwardSolution`: the computed column is a componentwise
  backward solution.
* `NLAlib.shiftedTriSolve_flag`: no pivot is floored when the diagonal gaps exceed $2s_{\min}$.
* `NLAlib.shiftedTriSolve_writes`: the program under the standard model.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

/-! ### The program -/

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **Rounded shifted back substitution with a pivot floor**: `[N, j] (T, Sm, Y, G) → (Y, G)`
solves $(\mathbf{T}_{11} - t_{jj}\mathbf{I})\mathbf{x} = -\mathbf{t}_{1j}$ for the leading block
of order $j$ of the stored $\mathbf{T}$ of order $N$ (column-major pairs) into the first $j$
entries of column $j$ of `Y`, $i = j - 1, \dots, 0$: the pivot $\mathrm{fl}(t_{ii} - t_{jj})$,
replaced by the word `Sm` (and the flag `G` set to $1$) when its rounded squared modulus is at
most the rounded square of `Sm`; the sum $\mathrm{fl}(t_{ij} + \sum_{i < k < j}t_{ik}x_k)$ by
rounded complex multiply–adds; the negated rounded quotient. The flag is not cleared.
Algorithm: dense-eigendecomposition -/
def shiftedTriSolve : Impl O Q := opsImpl% [N, j] (T, Sm, Y, G) → (Y, G) {
  let One ← alloc 2;
  let M ← alloc 2;
  let S ← alloc 2;
  let W ← alloc 2;
  let R ← alloc 2;
  let D ← alloc 4;
  let P ← alloc 2;
  call (Has.inj (ScalarOp.lit 1)) [] () → (One);
  call (Has.inj (ScalarOp.lit 0)) [] () → (One[1]);
  call (Has.inj ScalarOp.mul) [] (Sm, Sm) → (P[1]);
  for r < j {
    call (Has.inj ScalarOp.sub) []
      (T[2 * ((j - 1 - r) * N + (j - 1 - r))], T[2 * (j * N + j)]) → (M);
    call (Has.inj ScalarOp.sub) []
      (T[2 * ((j - 1 - r) * N + (j - 1 - r)) + 1], T[2 * (j * N + j) + 1]) → (M[1]);
    call (Has.inj ScalarOp.mul) [] (M, M) → (P);
    call (Has.inj ScalarOp.mul) [] (M[1], M[1]) → (W);
    call (Has.inj ScalarOp.add) [] (P, W) → (P);
    if (Has.inj CmpTst.le) [] (P, P[1]) {
      call (Has.inj ScalarOp.copy) [] (Sm) → (M);
      call (Has.inj (ScalarOp.lit 0)) [] () → (M[1]);
      call (Has.inj IndexOp.lit) [1] () → (G)
    } else { skip };
    call (Has.inj ScalarOp.copy) [] (T[2 * (j * N + (j - 1 - r))]) → (S);
    call (Has.inj ScalarOp.copy) [] (T[2 * (j * N + (j - 1 - r)) + 1]) → (S[1]);
    for l < r {
      run Pair.linearCombination.body []
        (T[2 * ((j - r + l) * N + (j - 1 - r))], One, Y[2 * (j * N + (j - r + l))], S, W, R);
      call (Has.inj ScalarOp.copy) [] (R) → (S);
      call (Has.inj ScalarOp.copy) [] (R[1]) → (S[1])
    };
    run Pair.complexDivideWithScratch.body [] (S, M, D, R);
    call (Has.inj ScalarOp.neg) [] (R) → (Y[2 * (j * N + (j - 1 - r))]);
    call (Has.inj ScalarOp.neg) [] (R[1]) → (Y[2 * (j * N + (j - 1 - r)) + 1])
  }
}

end Program

/-! ### The computed words -/

/-- The entry $(i, k)$ of a square matrix at natural indices, $0$ outside. -/
def entryAt {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ) (i k : ℕ) : ℂ :=
  if h : i < N ∧ k < N then T ⟨i, h.1⟩ ⟨k, h.2⟩ else 0

/-- **The words of the shifted back substitution** on the machine `M` for column `j`, after the
rows $j - 1, \dots, j - r$: the computed entries (at natural indices) and whether a pivot was
floored. -/
noncomputable def shiftedTriSolveWord (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (smin : ℝ) (j : ℕ) : ℕ → (ℕ → ℂ) × Bool
  | 0 => (fun _ => 0, false)
  | r + 1 =>
    let st := shiftedTriSolveWord M T smin j r
    let i := j - 1 - r
    let m : ℂ := ⟨M.sub (entryAt T i i).re (entryAt T j j).re,
      M.sub (entryAt T i i).im (entryAt T j j).im⟩
    let fl := decide (M.add (M.mul m.re m.re) (M.mul m.im m.im) ≤ M.mul smin smin)
    let m' : ℂ := if fl then ⟨smin, M.lit 0⟩ else m
    let s := (List.range r).foldl (fun s l =>
      linearComplex M (entryAt T i (j - r + l)) ⟨M.lit 1, M.lit 0⟩ (st.1 (j - r + l)) s)
      (entryAt T i j)
    let q := Pair.divideWords M (s.re, s.im) (m'.re, m'.im)
    (Function.update st.1 i ⟨M.neg q.1, M.neg q.2⟩, st.2 || fl)

/-- **The computed eigenvector column** $(\hat{\mathbf{x}}; 1; \mathbf{0})$ of column `j`. -/
noncomputable def shiftedTriSolveColumn (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (smin : ℝ) (j : ℕ) : Fin N → ℂ :=
  fun i => if (i : ℕ) < j then (shiftedTriSolveWord M T smin j j).1 i
    else if (i : ℕ) = j then 1 else 0

/-- **The flag of the shifted back substitution**: whether a pivot of column `j` was floored. -/
noncomputable def shiftedTriSolveFlag (M : Machine ℝ) {N : ℕ} (T : Matrix (Fin N) (Fin N) ℂ)
    (smin : ℝ) (j : ℕ) : Bool :=
  (shiftedTriSolveWord M T smin j j).2

/-! ### The theorems -/

/-- **The computed column is a componentwise backward solution**: under the standard model at
$\boldsymbol{u}$ with $64(N + 1)\boldsymbol{u} \le 1$, for an upper triangular $\mathbf{T}$ of
order $N$, $s_{\min} \ge 0$ and $j < N$, the column $(\hat{\mathbf{x}}; 1; \mathbf{0})$ is a
componentwise backward solution of $(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with
the relative perturbation $16(N + 1)\boldsymbol{u}$ and the diagonal floor $3s_{\min}$ if a pivot
was floored, $0$ otherwise (the per-row residual of the chain, the shift and the division, then
`NLAlib.isComponentwiseBackwardSolution_of_norm_sub_le`). [Higham2002, Theorem 8.5] -/
theorem shiftedTriSolve_isComponentwiseBackwardSolution {M : Machine ℝ} {u : ℝ}
    (hM : StdModel u id M) {N : ℕ} (hu : 64 * ((N : ℝ) + 1) * u ≤ 1)
    {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 ≤ smin)
    (j : Fin N) :
    IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u)
      (if shiftedTriSolveFlag M T smin j then 3 * smin else 0) (T - T j j • 1) 0
      (shiftedTriSolveColumn M T smin j) := by
  sorry

/-- **No pivot is floored when the diagonal is separated**: under the standard model at
$\boldsymbol{u} \le 1/32$, if $\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for every $i < j$,
$s_{\min} \ge 0$, the flag of column $j$ is not set. -/
theorem shiftedTriSolve_flag {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : u ≤ 1 / 32)
    {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} (hsmin : 0 ≤ smin) (j : Fin N)
    (hgap : ∀ i : Fin N, i < j → 2 * smin < ‖T i i - T j j‖) :
    shiftedTriSolveFlag M T smin j = false := by
  sorry

section Writes

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q]

/-- **The program stores the computed words**: on a scalar machine with index literals and exact
comparisons, from a memory holding $\mathbf{T}$ of order $N$ at `t`, the floor $s_{\min}$ at `sm`,
room for `Y` and a flag word at `g`, the four blocks live and apart, and $j < N$, the run writes
only the first $j$ entries of column $j$ of `Y` and the flag: they hold the words of
`NLAlib.shiftedTriSolveWord`, and the flag is the literal $1$ if a pivot was floored and unchanged
otherwise. -/
theorem shiftedTriSolve_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hC : IsCmp id I) {N j : ℕ} (hj : j < N) {t sm y g : ℕ × ℕ}
    {T : Matrix (Fin N) (Fin N) ℂ} {smin : ℝ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (shiftedTriSolve (O := O) (Q := Q)).body
      (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => (∀ i < j, μ'.store.get y.1 (y.2 + 2 * (j * N + i)) =
            some ((shiftedTriSolveWord M T smin j j).1 i).re ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) =
            some ((shiftedTriSolveWord M T smin j j).1 i).im) ∧
        (shiftedTriSolveFlag M T smin j = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (shiftedTriSolveFlag M T smin j = false →
          μ'.store.get g.1 g.2 = μ.store.get g.1 g.2)) μ := by
  sorry

/-- **Rounded shifted back substitution under the standard model**: on a scalar machine with the
standard model at $\boldsymbol{u}$, $64(N + 1)\boldsymbol{u} \le 1$, index literals and exact
comparisons, from the memory of `NLAlib.shiftedTriSolve_writes_word` with $\mathbf{T}$ upper
triangular, $s_{\min} \ge 0$ and $j < N$, the run stores the first $j$ entries of a column
$\mathbf{y}$ with $y_j = 1$, $y_i = 0$ for $i > j$, that is a componentwise backward solution of
$(\mathbf{T} - t_{jj}\mathbf{I})\mathbf{y} = \mathbf{0}$ with $16(N + 1)\boldsymbol{u}$ and the
floor $3s_{\min}$ if the flag was set, $0$ if the flag is unchanged; the flag is unchanged when
$\lvert t_{ii} - t_{jj}\rvert > 2s_{\min}$ for $i < j$. -/
theorem shiftedTriSolve_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hC : IsCmp id I) {N : ℕ}
    (hu : 64 * ((N : ℝ) + 1) * u ≤ 1) {t sm y g : ℕ × ℕ} {T : Matrix (Fin N) (Fin N) ℂ}
    (hTu : T.IsUpperTriangular) {smin : ℝ} (hsmin : 0 ≤ smin) (j : Fin N) {τ : Tape ℝ}
    {μ : Mem ℝ} (hT : HoldsMatrix t T μ.store) (hsm : μ.store.get sm.1 sm.2 = some smin)
    (hl : μ.Live [t, sm, y, g]) (hroom : μ.Room [y, g] [2 * (N * N), 1])
    (hap : Fp.Apart [t, sm, y, g] [2 * (N * N), 1, 2 * (N * N), 1]) :
    Writes .total I τ (shiftedTriSolve (O := O) (Q := Q)).body
      (Env.frame [N, j] [t, sm, y, g, y, g])
      (Store.inBlock y.1 (y.2 + 2 * (j * N)) (2 * j) ⊔ Store.inBlock g.1 g.2 1)
      (fun μ' => ∃ (yv : Fin N → ℂ) (fl : Bool),
        (∀ i : Fin N, (i : ℕ) < j → μ'.store.get y.1 (y.2 + 2 * (j * N + i)) = some (yv i).re ∧
          μ'.store.get y.1 (y.2 + 2 * (j * N + i) + 1) = some (yv i).im) ∧
        yv j = 1 ∧ (∀ i : Fin N, j < i → yv i = 0) ∧
        IsComponentwiseBackwardSolution (16 * ((N : ℝ) + 1) * u) (if fl then 3 * smin else 0)
          (T - T j j • 1) 0 yv ∧
        (fl = true → μ'.store.get g.1 g.2 = some (M.lit 1)) ∧
        (fl = false → μ'.store.get g.1 g.2 = μ.store.get g.1 g.2) ∧
        ((∀ i : Fin N, i < j → 2 * smin < ‖T i i - T j j‖) → fl = false)) μ := by
  sorry

end Writes

end NLAlib
