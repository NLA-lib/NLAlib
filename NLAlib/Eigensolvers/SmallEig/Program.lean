/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.HessenbergReduction
public import NLAlib.Eigensolvers.SmallEig.Core
public import NLAlib.Eigensolvers.SmallEig.Perturb

/-!
# The small-eigenvalue program

The algorithm `Eig` of [BanksGarzaVargasSrivastava2025, Theorem 1.1] as a fixed program
`[d, nq, T] (Bk, Q) → (Ev)` over scalar arithmetic, index literals, draws of a Gaussian stream and
the polar disk sampler, with no eigenvalue oracle: a block of order at most $1$ is copied; a
larger one is copied to scratch, perturbed by a scaled complex Gaussian matrix
(`NLAlib.SmallEig.ginibrePerturb`), reduced to Hessenberg form (`NLAlib.hessenbergReduceLast`), and
deflated by the core (`NLAlib.SmallEig.smallEigCore` at the bottom width $1$) with the threshold
word `Q[6]` and the words `Q`. The program has the interface of a small-eigenvalue routine
(`NLAlib.ShiftedQR.RandomSmallEigContract`), so the shifted QR algorithm can run it in the place
of its kernel.

## Main definitions

* `NLAlib.SmallEig.smallEigProg`: the program.
* `NLAlib.SmallEig.smallEigDims`, `NLAlib.SmallEig.SmallEigInput`,
  `NLAlib.SmallEig.SmallEigSpectrum`: the dimensions, the memory of the input and the memory of
  the output of a run.

## Main results

* `NLAlib.SmallEig.smallEigProg_terminates`: termination on every tape.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The small-eigenvalue program** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], `Eig`, with
the base case of order at most $1$ and every loop capped): for $d \le 1$ copy the entry
(`NLAlib.SmallEig.copyLeaf`); otherwise copy the block to scratch `W`, perturb it
(`NLAlib.SmallEig.ginibrePerturb` with the Gaussian stream `sG` and the scale word `Q[0]`), reduce
it to Hessenberg form, and run the core at the bottom width $1$ with the threshold word `Q[6]`, the
$n_q$ words `Q` and the cap $T$, into `Ev` and a scratch failure word. The interface is
`[d, nq, T] (Bk, Q) → (Ev)`.
Algorithm: small-eig -/
def smallEigProg (sG : ℕ) : Impl O Q := opsImpl% [d, nq, T] (Bk, Qw) → (Ev) {
  ifPos 2 - d {
    run (copyLeaf (O := O) (Q := Q)).body [d, nq, T] (Bk, Qw, Ev)
  };
  ifPos d - 1 {
    let W ← alloc (2 * (d * d));
    let Fl ← alloc 1;
    run (unaryMap (Tst := Q) (Has.inj ScalarOp.copy)).body [2 * (d * d)] (Bk, W);
    run (ginibrePerturb (O := O) (Q := Q) sG).body [d, nq] (W, Qw, W);
    run (hessenbergReduceLast (O := O) (Q := Q)).body [d] (W, W);
    run (smallEigCore (O := O) (Q := Q) sG).body [d, 1, nq, T, T] (W, Qw[6], Qw, Ev, Fl)
  }
}

end Program

/-- The dimensions of a run at the order $n + 1$: the order, the number of words of
`NLAlib.SmallEig.smallEigParams` and the cap `NLAlib.SmallEig.smallEigCap`. -/
noncomputable def smallEigDims (n nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℕ :=
  [n + 1, (smallEigParams nmax S δ φ c₁ c₂).length, smallEigCap nmax S δ φ c₁ c₂]

/-- **The memory holding the input** of the small-eigenvalue program: $\mathbf{M}$ at `w`, the
words `NLAlib.SmallEig.smallEigParams` at `q`, room for the $2(n + 1)$ output words at `o`, the
views live and the output apart from the matrix and the words. -/
def SmallEigInput {n : ℕ} (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) (w q o : ℕ × ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  HoldsMatrix w M μ.store ∧
    μ.store.readBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length =
      some (smallEigParams nmax S δ φ c₁ c₂) ∧
    μ.Live [w, q, o] ∧ o.2 + 2 * (n + 1) ≤ μ.store.len o.1 ∧
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock o.1 o.2 (2 * (n + 1))) ∧
    Fp.Disj (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length)
      (Store.inBlock o.1 o.2 (2 * (n + 1)))

/-- **The memory holding the spectrum of a nearby matrix**: the output at `o` lists all
eigenvalues, with multiplicity, of $\mathbf{M} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le \delta$. -/
def SmallEigSpectrum {n : ℕ} (o : ℕ × ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (δ : ℝ)
    (μ' : Mem ℝ) : Prop :=
  ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), specNorm E ≤ δ ∧
    IsEigenvalueListing (M + E) roots ∧
    HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The small-eigenvalue program terminates on every tape** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], with every loop capped): on a scalar machine with index literals, exact natural
literals up to $k_{\max}$, exact comparisons and conversion, draws that store the tape entry and
an exact polar sampler, for words `qs` with valid cap words for the cap $T$
(`NLAlib.SmallEig.SmallEigCaps`), `NLAlib.SmallEig.smallEigProg` is a
terminating small-eigenvalue routine (`NLAlib.ShiftedQR.TerminatingSmallEig`) on orders at most
$k_{\max}$: from any matrix and on every tape the run is total and writes only its output. A run
with junk cap words fails at a bounded index read, so the cap words are a hypothesis. -/
theorem smallEigProg_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I)
    {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I) {T : ℕ} {qs : List ℝ}
    (hqs : SmallEigCaps T qs) {kmax : ℕ} (hNat : IsExactNatLit id M kmax) :
    TerminatingSmallEig kmax T qs (smallEigProg (O := O) (Q := Q) sG) I := by
  sorry

end Theorems

end NLAlib.SmallEig
