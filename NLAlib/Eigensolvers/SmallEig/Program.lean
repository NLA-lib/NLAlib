/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.HessenbergReduction
public import NLAlib.Eigensolvers.SmallEig.Core
public import NLAlib.Eigensolvers.SmallEig.Perturb
public import NLAlib.Ops.Blas.Fill

/-!
# The small-eigenvalue program

The algorithm `Eig` of [BanksGarzaVargasSrivastava2025, Theorem 1.1] as a fixed program
`[d, nq, T] (Bk, Q) → (Ev)` over scalar arithmetic, index literals, draws of a Gaussian stream and
the polar disk sampler, with no eigenvalue oracle: a block of order at most $1$ is copied; for a
larger one the output words are set to zero (so that they are stored even when the core stops
early), the block is copied to scratch, perturbed by a scaled complex Gaussian matrix
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

/-- **The small-eigenvalue program in Schur mode** ([BanksGarzaVargasSrivastava2025, Theorem 1.1],
`Eig`, with the base case of order at most $1$, every loop capped, and the Schur form): for
$d \le 1$ keep the block and write the identity accumulator (`NLAlib.SmallEig.identityLeaf`);
otherwise write the identity accumulator, copy the threshold word `Q[6]` to scratch `Th`, perturb
the block in place (`NLAlib.SmallEig.ginibrePerturb` with the Gaussian stream `sG` and the scale
word `Q[0]`), reduce it to Hessenberg form recording the rotations
(`NLAlib.hessenbergReduceLast` into a scoped log of $d$ slots of $d$ entries), replay them on the
accumulator (`NLAlib.givensReplayColumns`), and run the core in Schur mode at the bottom width
$1$ with the threshold word `Th`, the $n_q$ words `Q`, the cap $T$ and the log shape
$(T + d, d)$, into the block, the accumulator and a scratch failure word. The output is the
triangular block $\widehat{\mathbf{T}}_b$ in `Bk` and its accumulator $\widehat{\mathbf{U}}_b$ in
`Ub`; the eigenvalues are the diagonal of $\widehat{\mathbf{T}}_b$. The interface is
`[d, nq, T] (Bk, Q) → (Bk, Ub)`, that of a Schur leaf (`NLAlib.Schur.RandomSchurLeafContract`).
Algorithm: small-eig -/
def smallEigProg (sG : ℕ) : Impl O Q := opsImpl% [d, nq, T] (Bk, Qw) → (Bk, Ub) {
  run (identityLeaf (O := O) (Q := Q)).body [d, nq, T] (Bk, Qw, Bk, Ub);
  ifPos d - 1 {
    let Fl ← alloc 1;
    let Th ← alloc 1;
    let Lg ← alloc (d * (1 + 5 * d));
    call (Has.inj ScalarOp.copy) [] (Qw[6]) → (Th);
    run (ginibrePerturb (O := O) (Q := Q) sG).body [d, nq] (Bk, Qw, Bk);
    run (slottedLogOpen (O := O) (Q := Q)).body [d, d] (Lg);
    run (hessenbergReduceLast (O := O) (Q := Q)).body [d, d, 0] (Bk, Bk, Lg);
    run (givensReplayColumns (O := O) (Q := Q)).body [d, 0, 0, d, d, d] (Lg, Ub, Ub);
    run (smallEigCore (O := O) (Q := Q) sG).body [d, 1, nq, T, T, T + d, d]
      (Bk, Th, Qw, Ub, Bk, Ub, Fl)
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
    μ.Live [w, q, o] ∧ o.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len o.1 ∧
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) ∧
    Fp.Disj (Store.inBlock q.1 q.2 (smallEigParams nmax S δ φ c₁ c₂).length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))

/-- **The memory holding the spectrum of a nearby matrix**: the output at `o` lists all
eigenvalues, with multiplicity, of $\mathbf{M} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le \delta$. -/
def SmallEigSpectrum {n : ℕ} (w o : ℕ × ℕ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (δ : ℝ)
    (μ' : Mem ℝ) : Prop :=
  ∃ (Tb Ub E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), HoldsMatrix w Tb μ'.store ∧
    HoldsMatrix o Ub μ'.store ∧ Tb.IsUpperTriangular ∧ specNorm E ≤ δ ∧
    IsEigenvalueListing (M + E) (fun i => Tb i i)

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

end Theorems

section Termination

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The small-eigenvalue program in Schur mode terminates, with its accumulator near a unitary
on every tape**: for blocks of order at most $k_{\max}$, the words `qs` with valid cap words for
the cap $T$ (`NLAlib.SmallEig.SmallEigCaps`), on a scalar machine with the standard model, index
literals and exact natural literals up to $k_{\max} + 1$, exact comparisons and conversion, draws
that store the tape entry and an exact polar sampler, `NLAlib.SmallEig.smallEigProg` is a
terminating Schur leaf (`NLAlib.ShiftedQR.TerminatingLeafRoutine`) with the accumulator error
$(1 + 24\boldsymbol{u})^{k^2 + 2(k+1)((T + k)k + 6)} - 1$ at $k = k_{\max}$: the replay of the
reduction and the replays of the core's rounds (`NLAlib.ShiftedQR.solveRoundedWith_terminates`
at the bottom width $1$, whose leaf is exact). -/
theorem smallEigProg_terminates {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hS : IsScalar M I)
    (hM : StdModel u id M) (hu : u ≤ 1 / 100) (hL : IsIndexLit M I) {kmax : ℕ}
    (hNat : IsExactNatLit id M (kmax + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I) {T : ℕ} {qs : List ℝ}
    (hqs : SmallEigCaps T qs) (hlen : 12 ≤ qs.length) :
    TerminatingLeafRoutine
      ((1 + 24 * u) ^ (kmax * kmax + 2 * (kmax + 1) * ((T + kmax) * kmax + 6)) - 1) kmax qs T
      (smallEigProg (O := O) (Q := Q) sG) I :=
  sorry

end Termination

end NLAlib.SmallEig
