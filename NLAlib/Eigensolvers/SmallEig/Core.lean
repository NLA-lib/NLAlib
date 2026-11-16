/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination
public import NLAlib.Eigensolvers.SmallEig.Decoupler
public import NLAlib.Eigensolvers.SmallEig.Leaf

/-!
# The core of the small-eigenvalue solver

The deflation of [BanksGarzaVargasSrivastava2025, §6] is the merged rounded worklist
(`NLAlib.ShiftedQR.solveRoundedWith`) at the bottom width $k = 1$, with the decoupler
`NLAlib.SmallEig.smallEigDecoupler` and the order-one leaf `NLAlib.SmallEig.copyLeaf`. On an upper
Hessenberg matrix in the class of the core (condition $B_c$, separation $g_c$) it stores, except
with probability at most $\varphi/4$, all eigenvalues of a matrix within $\delta/4$
(Theorem 6.1 in class form: no shattering vocabulary).

## Main definitions

* `NLAlib.SmallEig.smallEigCore`: the program `[N, k, np, F, T] (A, Thr, P) → (Out, Fl)`.
* `NLAlib.SmallEig.SmallEigCoreInput`: the memory of a call.

## Main results

* `NLAlib.SmallEig.smallEigCore_measureReal_not_spectrum_le`,
  `NLAlib.SmallEig.smallEigCore_terminates`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The core of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, Theorem 6.1]):
the rounded worklist `NLAlib.ShiftedQR.solveRoundedWith` with the decoupler
`NLAlib.SmallEig.smallEigDecoupler` and the leaf `NLAlib.SmallEig.copyLeaf`. Run at the bottom
width $k = 1$. The interface is `[N, k, np, F, T] (A, Thr, P) → (Out, Fl)`.
Algorithm: small-eig -/
def smallEigCore (sG : ℕ) : Impl O Q :=
  solveRoundedWith (smallEigDecoupler (O := O) (Q := Q) sG) (copyLeaf (O := O) (Q := Q))

end Program

/-- The memory of a call of the core on $\mathbf{H}$ of order $n + 1$ with the words `qs`: the
views of the matrix, the threshold word (the word $6$ of `qs`), the words, the output and the
failure word are live, have room and are apart, and the matrix, the threshold and the words are
stored. -/
def SmallEigCoreInput {n : ℕ} (qs : List ℝ) (a t p out f : ℕ × ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, t, p, out, f] ∧
    μ.Room [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, qs.length, 2 * (n + 1), 1] ∧
    Fp.Apart [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, qs.length, 2 * (n + 1), 1] ∧
    HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some (qs.getD 6 0) ∧
    μ.store.readBlock p.1 p.2 qs.length = some qs

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The core stores a nearby spectrum** ([BanksGarzaVargasSrivastava2025, Theorem 6.1], in
class form): on a scalar machine with the standard model at $\boldsymbol{u} \le$
`NLAlib.SmallEig.uSmallEig`, $M.\mathrm{lit}(0) = 0$, index literals, exact natural literals up to
$n_{\max} + 1$, exact comparisons and conversion, a measurable interpretation reading the tape
only in its windows whose draws store the tape entry, a stream `sG` with the standard real
Gaussian law and an exact polar sampler on a stream `sU` uniform on $[0, 1]$: for tail records
with $b_1, b_2 > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$, let $\mathbf{H}$ of order
$n + 1 \le n_{\max}$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B_c$, eigenvalues separated by $g_c$
(`NLAlib.SmallEig.smallEigCondition`, `NLAlib.SmallEig.smallEigSeparation`) and
$\|\mathbf{H}\|_2 \le \Sigma + 3\delta/4$, stored with the words
`NLAlib.SmallEig.smallEigParams` (`NLAlib.SmallEig.SmallEigCoreInput`). Then, under a random tape
with the stream laws, the probability that `NLAlib.SmallEig.smallEigCore` at the bottom width $1$
fails to write only the matrix, the output and the failure word, set the failure word to $0$ and
store all eigenvalues of $\mathbf{H} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta/4$ is at
most $\varphi/4$. -/
theorem smallEigCore_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hzero : Mch.lit 0 = 0)
    (hL : IsIndexLit Mch I) {nmax : ℕ} (hNat : IsExactNatLit id Mch (nmax + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {n : ℕ} (hn : n + 1 ≤ nmax)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ smallEigCondition nmax S δ φ c₂)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ ≤ ‖d i - d j‖)
    (hHS : specNorm H ≤ S + 3 * δ / 4) {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SmallEigCoreInput (smallEigParams nmax S δ φ c₁ c₂) a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (smallEigCore (O := O) (Q := Q) sG).body
      (Env.frame [n + 1, 1, (smallEigParams nmax S δ φ c₁ c₂).length,
        smallEigCap nmax S δ φ c₁ c₂, smallEigCap nmax S δ φ c₁ c₂] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
          HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
          specNorm E ≤ δ / 4 ∧ (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)) μ} ≤
      φ / 4 := by
  sorry

/-- **The core terminates**: on a scalar machine with index literals, exact natural literals up
to $n + 1$, exact comparisons and conversion, draws that store the tape entry and an exact polar
sampler, for words `qs` with valid cap words for the cap $T$ (`NLAlib.SmallEig.SmallEigCaps`) and
at least twelve words, from `NLAlib.SmallEig.SmallEigCoreInput` with any matrix of order $n + 1$
and on every tape, `NLAlib.SmallEig.smallEigCore` at the bottom width $1$ writes only the matrix,
the output and the failure word. -/
theorem smallEigCore_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {T F : ℕ} {qs : List ℝ} (hqs : SmallEigCaps T qs) (hlen : 12 ≤ qs.length)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tape : Tape ℝ} {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : SmallEigCoreInput qs a t p out f H μ) :
    Writes .total I tape (smallEigCore (O := O) (Q := Q) sG).body
      (Env.frame [n + 1, 1, qs.length, F, T] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun _ => True) μ := by
  sorry

end Theorems

end NLAlib.SmallEig
