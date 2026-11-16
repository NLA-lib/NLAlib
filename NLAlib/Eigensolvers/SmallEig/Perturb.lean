/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedKernels
public import NLAlib.Eigensolvers.SmallEig.Draws
public import NLAlib.Eigensolvers.SmallEig.Precision
public import NLAlib.Matrix.FinitePrecision.OpsSampling
public import NLAlib.RandomMatrix.Gaussian.Tape

/-!
# The Gaussian perturbation of the input

The first step of the small-eigenvalue program of [BanksGarzaVargasSrivastava2025, Theorem 1.1]:
the input $\mathbf{A}$ of order $N$ becomes $\mathbf{A} + \gamma' \mathbf{G}$ with $\mathbf{G}$ a
standard complex Gaussian matrix drawn from $2N^2$ entries of a Gaussian stream and the scale
$\gamma' = \mathrm{fl}(\gamma/\sqrt N)$ computed by the program from the word $\gamma$, all rounded.
Except with a small probability the result is in the diagonalization class (condition $2/t_2$,
separation $t_1/2$) and is within $\delta/2$ of $\mathbf{A}$: the random-matrix hypotheses at the
order $N$ (`NLAlib.measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix`), the norm of
the perturbation, and the rounding, which the closed class absorbs
(`NLAlib.isClosed_setOf_exists_pseudoConditionNumber_le_and_le_norm_sub`).

## Main definitions

* `NLAlib.SmallEig.ginibrePerturb`: the program `[N, nq] (A, Q) → (A)`.

## Main results

* `NLAlib.SmallEig.ginibrePerturb_writes_word`: the stored words.
* `NLAlib.SmallEig.ginibrePerturb_pwrites`: the class after the perturbation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O]

/-- **The Gaussian perturbation** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], line 1 of
`Eig`, with the scale computed by the program): draw $2N^2$ words of the stream `sG` into scratch,
compute $\gamma' = \mathrm{fl}(\gamma/\mathrm{fl}(\sqrt N))$ from the word $\gamma$ = `Q[0]` and the
literal $N$, and the stored $\sqrt{1/2}$, and add $\gamma'\sqrt{1/2}(x_{2k} + i x_{2k+1})$ to the
$k$-th entry of `A`, rounded. The interface is `[N, nq] (A, Q) → (A)`.
Algorithm: small-eig -/
def ginibrePerturb (sG : ℕ) : Impl O Q := opsImpl% [N, nq] (A, Qw) → (A) {
  let G ← alloc (2 * (N * N));
  let Sc ← alloc 3;
  run (gaussDraws (O := O) (Q := Q) sG).body [2 * (N * N)] (G);
  call (Has.inj IndexOp.lit) [N] () → (Sc);
  call (Has.inj ScalarOp.sqrt) [] (Sc) → (Sc);
  call (Has.inj ScalarOp.div) [] (Qw, Sc) → (Sc);
  call (Has.inj (ScalarOp.lit 1)) [] () → (Sc[1]);
  call (Has.inj (ScalarOp.lit 2)) [] () → (Sc[2]);
  call (Has.inj ScalarOp.div) [] (Sc[1], Sc[2]) → (Sc[1]);
  call (Has.inj ScalarOp.sqrt) [] (Sc[1]) → (Sc[1]);
  for j < N * N {
    call (Has.inj ScalarOp.mul) [] (G[2 * j], Sc[1]) → (G[2 * j]);
    call (Has.inj ScalarOp.mul) [] (G[2 * j + 1], Sc[1]) → (G[2 * j + 1]);
    call (Has.inj ScalarOp.mul) [] (G[2 * j], Sc) → (G[2 * j]);
    call (Has.inj ScalarOp.mul) [] (G[2 * j + 1], Sc) → (G[2 * j + 1]);
    call (Has.inj ScalarOp.add) [] (A[2 * j], G[2 * j]) → (A[2 * j]);
    call (Has.inj ScalarOp.add) [] (A[2 * j + 1], G[2 * j + 1]) → (A[2 * j + 1])
  }
}

end Program

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O]

/-- `NLAlib.SmallEig.ginibrePerturb` on a scalar machine with index literals and draws that store
the tape entry: from $\mathbf{A}$ of order $N$ at `a` and the word $\gamma$ at `q`, apart, it
writes only the matrix, advances the position by $2N^2$, and stores
`NLAlib.Ops.Machine.perturbWords` $\gamma$ $\mathbf{A}$ of the $2N^2$ entries of the stream `sG`
at the start position. -/
theorem ginibrePerturb_writes_word {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hSmp : IsSample I) {sG N nq : ℕ} {τ : Tape ℝ} {μ : Mem ℝ}
    {a q : ℕ × ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {γ : ℝ} (hl : μ.Live [a, q])
    (hA : HoldsMatrix a A μ.store) (hq : μ.store.get q.1 q.2 = some γ)
    (haq : Fp.Disj (Store.inBlock a.1 a.2 (2 * (N * N))) (Store.inBlock q.1 q.2 1)) :
    Writes .total I τ (ginibrePerturb (O := O) (Q := Q) sG).body (Env.frame [N, nq] [a, q, a])
      (Store.inBlock a.1 a.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos + 2 * (N * N) ∧
        HoldsMatrix a (M.perturbWords γ A fun j => τ (μ.pos + j) sG) μ'.store) μ := by
  sorry

/-- **The perturbation is in the class** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], the
perturbation step, with Lemma 6.5 replaced by the class): on a scalar machine with the standard
model at $\boldsymbol{u} \le$ `NLAlib.SmallEig.uSmallEigReduce`, index literals, a measurable
interpretation reading the tape only in its windows whose draws store the tape entry, a stream
`sG` with the standard real Gaussian law, and the random-matrix tails $c_1$ (gap) and $c_2$
(condition) with $b_1, b_2 > 0$: let $1 \le n_{\max}$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$, $\mathbf{A}$ of order $n + 1 \le n_{\max}$ with $\|\mathbf{A}\|_2 \le \Sigma$,
stored at `a`, and the words `NLAlib.SmallEig.smallEigParams` at `q`, apart. Then, except with
probability at most $3\varphi/4$, the run writes only the matrix and stores
$\widehat{\mathbf{A}} = \mathbf{A} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta/2$ and a
diagonalization $\mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le 2/t_2$ and eigenvalues separated by $t_1/2$, for
$t_1, t_2$ = `NLAlib.SmallEig.smallEigGap`, `NLAlib.SmallEig.smallEigCond`. -/
theorem ginibrePerturb_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hL : IsIndexLit M I) (hSmp : IsSample I) (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {sG : ℕ}
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hA : ComplexGaussianGapTail c₁)
    (hB : ComplexGaussianConditionTail c₂) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEigReduce nmax S δ φ c₁ c₂) {n : ℕ} (hn : n + 1 ≤ nmax)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hAS : specNorm A ≤ S) {a q : ℕ × ℕ} :
    PWrites law I (ginibrePerturb (O := O) (Q := Q) sG).body
      (Env.frame [n + 1, (smallEigParams nmax S δ φ c₁ c₂).length] [a, q, a])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (fun μ => HoldsMatrix a A μ.store ∧
        μ.store.readBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length =
          some (smallEigParams nmax S δ φ c₁ c₂) ∧ μ.Live [a, q] ∧
        Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
          (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length))
      (fun μ' => ∃ (E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ),
        HoldsMatrix a (A + E) μ'.store ∧ specNorm E ≤ δ / 2 ∧ IsUnit V ∧
        (A + E) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ 2 / smallEigCond nmax S δ φ c₂ ∧
        ∀ i j, i ≠ j → smallEigGap nmax S δ φ c₁ / 2 ≤ ‖d i - d j‖)
      (3 * φ / 4) := by
  sorry

end Theorems

end NLAlib.SmallEig
