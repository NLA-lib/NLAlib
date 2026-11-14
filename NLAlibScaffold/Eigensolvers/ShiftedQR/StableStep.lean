/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Hessenberg
public import NLAlib.Eigensolvers.ShiftedQR.MultiStep
public import NLAlib.Eigensolvers.ShiftedQR.SweepOutput
public import NLAlibScaffold.Matrix.QRIteration.StableStep

/-!
# The rounded shifted QR step as a backward-stable step

[BanksGarzaVargasSrivastava2022, Definition 3.4] asks of an implicit QR step two inequalities
with **one** unitary $\widehat{\mathbf{Q}}$: the output is close to
$\widehat{\mathbf{Q}}^{\mathsf H}\mathbf{H}\widehat{\mathbf{Q}}$, and $\mathbf{H} - s$ is close to
$\widehat{\mathbf{Q}}\widehat{\mathbf{R}}$ with $\widehat{\mathbf{R}}$ upper triangular; the
output is upper Hessenberg and the last diagonal entry of $\widehat{\mathbf{R}}$ is returned (it
drives the computed potential). The existing scalar step returns only the conjugated matrix, and
in floating point its output is Hessenberg only up to rounding. This file assembles, from the
exact development's components and without editing them, the step that meets the definition:
the shift initialization, the sweep that also copies the last working diagonal entry
(`NLAlib.ShiftedQR.sweepWithDiag`), and a pass that zeroes the entries below the subdiagonal
(`NLAlib.ShiftedQR.clearBelowSubdiagonal`). A degree $k$ step repeats it in place with the $k$
shifts of a stored list.

The error base is $\|\mathbf{H}\|_2 + \lvert s\rvert$, not the paper's $\|\mathbf{H} - s\|_2$
(adding the shift back rounds the diagonal with error $\boldsymbol{u}\lvert s\rvert$). The
constant $300(n+1)^2$ covers the rounds, the shift initialization, the triangular part kept of the
working matrix (its rounded entries below the diagonal are dropped) and the zeroing pass, whose
error is bounded entrywise and so costs a factor $\sqrt{n+1}$ in the spectral norm; the paper has
$32n^{3/2}$.

## Main definitions

* `NLAlib.ShiftedQR.stepWithDiag`, `NLAlib.ShiftedQR.stepWithDiagInPlace`,
  `NLAlib.ShiftedQR.multiStepStable`: the programs.

## Main results

* `NLAlib.ShiftedQR.stepWithDiag_isStableQRStep`: one rounded step is a backward-stable step.
* `NLAlib.ShiftedQR.multiStepStable_isStableQRChain`: the degree $k$ step is a stable chain.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- **One shifted QR step with its last triangular diagonal entry and a Hessenberg output**:
initialize a working copy $\mathbf{H} - s$ and the output $\mathbf{H}$, run the Givens sweep that
also copies the last working diagonal entry to `Dg`, and zero the output below its subdiagonal.
The interface is `[n] (A, S) → (Z, Dg)`; the working matrix and the four coefficient words are
scoped. -/
def stepWithDiag : Impl Op Tst := opsImpl% [n] (A, S) → (Z, Dg) {
  let W ← alloc (2 * (n * n));
  let Cf ← alloc 4;
  run (initializeState (Op := Op) (Tst := Tst)).body [n] (A, S, W, Z);
  run (sweepWithDiag (Op := Op) (Tst := Tst)).body [n] (W, Z, Cf, W, Z, Dg);
  run (clearBelowSubdiagonal (Op := Op) (Tst := Tst)).body [n] (Z)
}

/-- The step in place: run `NLAlib.ShiftedQR.stepWithDiag` into the scratch matrix `T`, then copy
it back to `A`. The interface is `[n] (A, S, T) → (A, Dg)`. -/
def stepWithDiagInPlace : Impl Op Tst := opsImpl% [n] (A, S, T) → (A, Dg) {
  run (stepWithDiag (Op := Op) (Tst := Tst)).body [n] (A, S, T, Dg);
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (n * n)] (T, A)
}

/-- **The degree $k$ rounded step**: $k$ steps in place with the shifts `S[2j]`, the last
triangular diagonal entry of step $j$ written to `Ds[2j]`. The interface is
`[n, k] (A, S) → (A, Ds)`; the scratch matrix is scoped. -/
def multiStepStable : Impl Op Tst := opsImpl% [n, k] (A, S) → (A, Ds) {
  let T ← alloc (2 * (n * n));
  for j < k {
    run (stepWithDiagInPlace (Op := Op) (Tst := Tst)).body [n] (A, S[2 * j], T, A, Ds[2 * j])
  }
}

/-- **The rounded single shifted QR step is backward stable** (corrected
[BanksGarzaVargasSrivastava2022, Lemma 3.5]): on a machine with the standard model at the unit
roundoff $\boldsymbol{u} \ge 0$ with $(n+1)\boldsymbol{u} \le 1/2500$, from an upper Hessenberg
$\mathbf{H}$ of order $n + 1$ and a shift $s$, the program `stepWithDiag` stores an
$\widehat{\mathbf{H}}'$ and the last diagonal entry of an $\widehat{\mathbf{R}}$ such that
$(\widehat{\mathbf{H}}', \widehat{\mathbf{R}})$ is a backward-stable QR step of $(\mathbf{H}, s)$
with error $300(n+1)^2\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert s\rvert)$. The input, the shift and
the outputs are given views; the output matrix is disjoint from the input matrix, the shift and
the diagonal pair. -/
theorem stepWithDiag_isStableQRStep {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s z dg : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shift : ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hl : m.Live [a, s, z, dg]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 2 = some [shift.re, shift.im])
    (hz : z.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len z.1)
    (hd : dg.2 + 2 ≤ m.store.len dg.1)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hsz : Fp.Disj (Store.inBlock s.1 s.2 2)
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1)))))
    (hzd : Fp.Disj (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock dg.1 dg.2 2)) :
    Writes .total I τ stepWithDiag.body (Env.frame [n + 1] [a, s, z, dg])
      (Store.inBlock z.1 z.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock dg.1 dg.2 2)
      (fun m' => m'.pos = m.pos ∧ ∃ H' R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsStableQRStep (300 * (n + 1) ^ 2 * u * (specNorm H + ‖shift‖)) H shift H' R ∧
          HoldsMatrix z H' m'.store ∧
          m'.store.readBlock dg.1 dg.2 2 =
            some [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im]) m := by
  sorry

/-- **The degree $k$ rounded step is a stable chain** (the setting of
[BanksGarzaVargasSrivastava2022, Lemma 3.6]): on a machine with the standard model at
$\boldsymbol{u} \ge 0$ with $(n+1)\boldsymbol{u} \le 1/2500$, from an upper Hessenberg
$\mathbf{H}$ of order $n + 1$ and the shifts $s_1, \dots, s_k$ stored as $2k$ words, the program
`multiStepStable` stores in place an $\widehat{\mathbf{H}}'$, and in `Ds` the last diagonal entries
of triangular factors $\widehat{\mathbf{R}}_1, \dots, \widehat{\mathbf{R}}_k$, such that the steps
form a backward-stable chain with relative error $x = 300(n+1)^2\boldsymbol{u}$ (step $\ell$ has
error $x(\|\mathbf{H}_\ell\|_2 + \lvert s_\ell\rvert)$ at its own input). The matrix, the shifts
and the diagonal outputs are pairwise disjoint views. -/
theorem multiStepStable_isStableQRChain {M : Machine ℝ} {I : Interp Op Tst ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a s ds : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ss : List ℂ} (hH : IsUpperHessenberg H)
    (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (hl : m.Live [a, s, ds]) (hA : HoldsMatrix a H m.store)
    (hs : m.store.readBlock s.1 s.2 (2 * ss.length) =
      some (ss.flatMap fun z => [z.re, z.im]))
    (hd : ds.2 + 2 * ss.length ≤ m.store.len ds.1)
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * ss.length)))
    (had : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ds.1 ds.2 (2 * ss.length)))
    (hsd : Fp.Disj (Store.inBlock s.1 s.2 (2 * ss.length))
      (Store.inBlock ds.1 ds.2 (2 * ss.length))) :
    Writes .total I τ multiStepStable.body (Env.frame [n + 1, ss.length] [a, s, a, ds])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock ds.1 ds.2 (2 * ss.length))
      (fun m' => m'.pos = m.pos ∧ ∃ (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)),
        IsStableQRChain (300 * (n + 1) ^ 2 * u) H ss H' Rs ∧ IsUpperHessenberg H' ∧
          HoldsMatrix a H' m'.store ∧
          m'.store.readBlock ds.1 ds.2 (2 * ss.length) =
            some (Rs.flatMap fun R =>
              [(R (Fin.last n) (Fin.last n)).re, (R (Fin.last n) (Fin.last n)).im])) m := by
  sorry

end NLAlib.ShiftedQR
