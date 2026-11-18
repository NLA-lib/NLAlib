/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import NLAlib.Ops.Confined
public import NLAlib.Ops.MonomialWork
public import NLAlib.Ops.Static
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleRoutine
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleSpec
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheoremsBits
public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedParameterChoices
public import NLAlib.Eigensolvers.SmallEig.Precision

/-!
# The rounded shifted QR algorithm: headline theorems

[BanksGarzaVargasSrivastava2022, Theorem 6.3] with the quantifiers of
[BanksGarzaVargasSrivastava2022, Theorem 1.4], in floating point, corrected: the decoupling loop
is capped, the deflation scan covers the bottom $k$ subdiagonal entries, and the precision
threshold is recomputed for the corrected constants of the blocks, and the output is a Schur form.
The program is the rounded deflation worklist in Schur mode (`NLAlib.ShiftedQR.solveRoundedWith`)
with the decoupling loop of Lemma 6.4 (`NLAlib.ShiftedQR.roundedDecoupleWith`: `Regularize`, then
$\mathrm{Sh}_{k,B}$, capped at $F$ rounds) and a small-block Schur solver as the leaf
(`NLAlib.ShiftedQR.roundedShQRWith L`), whose diagonal also gives `Regularize` its Ritz values
(`NLAlib.ShiftedQR.schurDiag`); `NLAlib.ShiftedQR.roundedShQRSmallEig` runs the `SmallEig`
program as the leaf. It is run with the parameter words of `NLAlib.ShiftedQR.shqrParams` and the
threshold word `NLAlib.ShiftedQR.shqrDeflationThreshold` on a machine with unit roundoff
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ (`NLAlib.ShiftedQR.uShQR`) and at most the
replay term (`NLAlib.ShiftedQR.uShQRSchurReplay`).

The parameters are those of `NLAlib.ShiftedQR.shqrParams_spec` (condition $4B$, separation
$\Gamma/4$ and iterate norm $4\Sigma$ inside the loop, block norm $2\Sigma$ in the worklist) and of
`NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract` with $n_{\max} = n$,
$N_{\max} = 2\Sigma$, $S = 4\Sigma$, the loop's threshold word $t_L$
(`NLAlib.ShiftedQR.shqrLoopThreshold`) and $\omega_D$ from it.

What is not claimed here: no Hessenberg reduction or preprocessing of a general matrix
(`NLAlib.Eigensolvers.Schur.Dense`); nothing on the leaf's own cost or precision; no forward
error for the eigenvalues; no rounded disk sampler; nothing for repeated eigenvalues. Modelling
assumptions the paper does not make: the parameter words are exact reals. With a generic leaf the
leaf is an oracle, a hypothesis `NLAlib.Schur.RandomSchurLeafContract` (the Schur form of
[BanksGarzaVargasSrivastava2022, Definition 1.2]).

## Main definitions

* `NLAlib.ShiftedQR.roundedShQRSmallEig`: the program.
* `NLAlib.ShiftedQR.shqrParams`, `NLAlib.ShiftedQR.shqrDims`: its parameter words and
  dimensions.
* `NLAlib.ShiftedQR.ShQRInput`, `NLAlib.ShiftedQR.ShQRSpectrum`: the memory holding the input,
  and the memory holding the spectrum of a nearby matrix.

## Main results

* `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le`: the headline.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_terminates`: termination on every tape.
* `NLAlib.ShiftedQR.logb_inv_uShQR_le`: the bits of precision.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_relative`: the relative backward error.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_hermitian`: Hermitian inputs.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_work_le`: the operation count.
* `NLAlib.ShiftedQR.roundedShQRWith`,
  `NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le`,
  `NLAlib.ShiftedQR.roundedShQRWith_terminates`: the algorithm with a small-block Schur solver
  (`NLAlib.Schur.RandomSchurLeafContract`) in the place of the eigenvalue oracle.
* `NLAlib.ShiftedQR.roundedShQRSchurWith`,
  `NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`,
  `NLAlib.ShiftedQR.roundedShQRSchurWith_terminatingSchurCore`: the same algorithm as the Schur
  core stage of the dense Schur pipeline, with any small-block Schur solver.

The headline on one run, with explicit work and span bounds conjoined with correctness, is the
certificate `NLAlib.ShiftedQR.roundedShQRSmallEigAlgorithm`
(`NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEigCertificate`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The eigenvalue routine of a Schur leaf**: run the Schur leaf `L` on a scoped copy of the
block `Bk` with a scoped accumulator and copy the diagonal of the triangular result to `Ev` (the
eigenvalues of the leaf's perturbed block). `Regularize` needs only these Ritz values. The
interface is `[d, nq, T] (Bk, Qw) → (Ev)`, that of a small-eigenvalue routine. -/
def schurDiag (L : Impl O Q) : Impl O Q := opsImpl% [d, nq, T] (Bk, Qw) → (Ev) {
  let W ← alloc (2 * (d * d));
  let Ub ← alloc (2 * (d * d));
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (d * d)] (Bk, W);
  run L.body [d, nq, T] (W, Qw, W, Ub);
  for i < d {
    call (Has.inj ScalarOp.copy) [] (W[2 * (i * d + i)]) → (Ev[2 * i]);
    call (Has.inj ScalarOp.copy) [] (W[2 * (i * d + i) + 1]) → (Ev[2 * i + 1])
  }
}

/-- **A Schur leaf on the tail words**: run the Schur leaf `L` (`[d, 12, T] (Bk, Q) → (Bk, Ub)`)
with the last $12$ of the $n_p$ parameter words, `P[np - 12]`, as its words. The interface is
`[d, np, T] (Bk, P) → (Bk, Ub)`, that of the leaf routine of `NLAlib.ShiftedQR.solveRoundedWith`;
the decoupling loop hands the same tail to the leaf's eigenvalue routine
(`NLAlib.ShiftedQR.roundedDecoupleLoopWith`). -/
def leafOnTailWords (L : Impl O Q) : Impl O Q := opsImpl% [d, np, T] (Bk, P) → (Bk, Ub) {
  run L.body [d, 12, T] (Bk, P[np - 12], Bk, Ub)
}

/-- **The rounded shifted QR algorithm in Schur mode with a Schur leaf**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with the routine of
[BanksGarzaVargasSrivastava2025, Corollary 1.3], with the Schur form): the worklist
`NLAlib.ShiftedQR.solveRoundedWith` in Schur mode with the decoupling loop
`NLAlib.ShiftedQR.roundedDecoupleWith` (whose Ritz values come from the leaf,
`NLAlib.ShiftedQR.schurDiag L`) and the Schur leaf `L` (`NLAlib.ShiftedQR.leafOnTailWords L`). The
leaf reads the last $12$ parameter words and the cap $T$. The interface is
`[N, k, np, F, T, ns, w] (A, Thr, P, U) → (A, U, Fl)`.
Algorithm: shifted-qr-rounded -/
def roundedShQRWith (L : Impl O Q) : Impl O Q :=
  solveRoundedWith (roundedDecoupleWith (schurDiag L)) (leafOnTailWords L)

/-- **The rounded shifted QR algorithm as a Schur core stage** with the Schur leaf `L`: the
threshold word is the first parameter word, and the log shape is the one the decoupler needs,
$n_s = F(k + 1 + n_p')$ slots of $w = kN$ entries ($n_p' = n_p - 1$ the remaining words). The
interface is `[N, np, k, F, T] (A, P, U) → (A, U, Fl)`, that of the core stage of the dense Schur
pipeline (`NLAlib.Schur.RandomSchurCoreContract`).
Algorithm: shifted-qr-rounded -/
def roundedShQRSchurWith (L : Impl O Q) : Impl O Q :=
  opsImpl% [N, np, k, F, T] (A, P, U) → (A, U, Fl) {
    run (roundedShQRWith L).body [N, k, np - 1, F, T, F * (k + 1 + (np - 1)), k * N]
      (A, P, P[1], U, A, U, Fl)
  }

end Program

/-- **The parameter words of the rounded shifted QR algorithm** at the order $n + 1$, the shift
degree $k$, the condition bound $B$, the separation $\Gamma$, the norm bound $\Sigma$ (`S`), the
backward error $\delta$ and the failure $\varphi$: the words of
`NLAlib.ShiftedQR.roundedDecoupleParams` with the loop's threshold word $t_L$, Regularize's
radius, the iteration's threshold word, $\gamma = 0.2$, the class constant $4B$, its $\alpha$ and
Exc's $\varepsilon$, and $k = 2^{\log_2 k}$. -/
noncomputable def shqrParams (n k : ℕ) (B Γ S δ φ : ℝ) : List ℝ :=
  roundedDecoupleParams (shqrLoopThreshold n k B Γ S δ φ) (shqrRadius n B Γ S δ)
    (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B) (shqrAlpha k (4 * B)) (shqrEps k (4 * B)) k
    (Nat.log 2 k)

/-- The dimensions of a run: the order $n + 1$, the shift degree $k$, the number of parameter
words and the iteration cap $F$ (`NLAlib.ShiftedQR.shqrCap`). -/
noncomputable def shqrDims (n k : ℕ) (B Γ S δ φ : ℝ) : List ℕ :=
  [n + 1, k, (shqrParams n k B Γ S δ φ).length, shqrCap n B Γ S δ]

/-- **The memory holding the input** of the rounded shifted QR algorithm: the views of the
matrix, the threshold word, the parameter words, the output and the failure word are live, have
room and are apart; the matrix $\mathbf{H}$, the deflation threshold word and the parameter words
are stored. -/
def ShQRInput {n : ℕ} (k : ℕ) (B Γ S δ φ : ℝ) (a t p out f : ℕ × ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, t, p, out, f] ∧
    μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ).length, 2 * ((n + 1) * (n + 1)), 1] ∧
    Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ).length, 2 * ((n + 1) * (n + 1)), 1] ∧
    (∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix out U μ.store) ∧
    HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ) ∧
    μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ).length = some (shqrParams n k B Γ S δ φ)

/-- **The memory holding the spectrum of a nearby matrix**: the failure word is $0$ and the
output holds all eigenvalues, with multiplicity, of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le e$. -/
def ShQRSpectrum {n : ℕ} (a out f : ℕ × ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e : ℝ)
    (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧
    ∃ (Tm U E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a Tm μ'.store ∧ HoldsMatrix out U μ'.store ∧ Tm.IsUpperTriangular ∧
        specNorm E ≤ e ∧ (H + E).charpoly.roots = (List.ofFn fun i => Tm i i : Multiset ℂ)

/-- The regions the rounded shifted QR algorithm writes: the matrix, the output and the failure
word. -/
def shqrFp (n : ℕ) (a out f : ℕ × ℕ) : Fp :=
  Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock out.1 out.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1


section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The bits of precision** ([BanksGarzaVargasSrivastava2022, Theorem 1.4], corrected: the
printed argument $nB/(\delta\Gamma\varphi)$ is not invariant under scaling of $\mathbf{H}$, and
Optimal's rounding constant, [BanksGarzaVargasSrivastava2022, Lemma 4.5], is $kn^{3/2}$ in place
of $2n^2$): there are absolute constants $c_1, c_2$ such that for every order $n + 1$,
$B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$,
$$\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}}) \le
  c_1 k \log_2\frac{4(n + 1)B\Sigma^2}{\delta\min(\Gamma, \Sigma)\varphi} + c_2.$$
The argument is scale-invariant ($\delta$ is an absolute error, so $\Sigma^2/(\delta\Gamma)$, not
$\Sigma/(\delta\Gamma)$) and at least $4$; $\min(\Gamma, \Sigma)$ covers $n = 0$, where the gap is
vacuous and $\Gamma$ unbounded (for $n \ge 1$, $\Gamma \le 2\Sigma$). The constants $c_1 = 63$ and
$c_2 = 0$ suffice: $\boldsymbol{u}_{\mathrm{ShQR}}$ is at least the argument to the power
$-(53k + 40)$ (`NLAlib.ShiftedQR.one_le_uShQR_mul`). -/
theorem logb_inv_uShQR_le : ∃ c₁ c₂ : ℝ, ∀ {n k : ℕ} {B Γ S δ φ : ℝ}, 1 ≤ B → 0 < Γ → 0 < δ →
    δ ≤ S → 0 < φ → φ ≤ 1 → k = shqrDegree (4 * B) →
    Real.logb 2 (uShQR n k B Γ S δ φ)⁻¹ ≤
      c₁ * k * Real.logb 2 (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) + c₂ := by
  refine ⟨63, 0, fun {n k B Γ S δ φ} hB hΓ hδ hδS hφ hφ1 hk => ?_⟩
  obtain ⟨hY4, h⟩ := one_le_uShQR_mul (n := n) hB hΓ hδ hδS hφ hφ1 hk
  set Y := 4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)
  have hk4 : (4 : ℝ) ≤ k := hk ▸ (shqrDegree_facts (by linarith : (1 : ℝ) ≤ 4 * B)).1
  have hu : 0 < uShQR n k B Γ S δ φ :=
    uShQR_pos (by exact_mod_cast (show (0 : ℝ) < k by linarith)) hB hΓ hδ (hδ.trans_le hδS) hφ
  have hY0 : 0 < Y := by linarith
  have hL : 0 ≤ Real.logb 2 Y := Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (uShQR n k B Γ S δ φ)⁻¹ ≤ Y ^ (53 * k + 40) := by
    rw [inv_le_iff_one_le_mul₀ hu, mul_comm]; exact h
  calc Real.logb 2 (uShQR n k B Γ S δ φ)⁻¹ ≤ Real.logb 2 (Y ^ (53 * k + 40)) :=
        Real.logb_le_logb_of_le (by norm_num) (inv_pos.mpr hu) h1
    _ = ((53 * k + 40 : ℕ) : ℝ) * Real.logb 2 Y := by rw [Real.logb_pow]
    _ ≤ 63 * k * Real.logb 2 Y := by push_cast; nlinarith
    _ = 63 * k * Real.logb 2 Y + 0 := by ring

end Theorems

/-! ### The algorithm with a Schur leaf -/

/-- The capacity $n_s w$ of the log of the Schur-mode worklist at the order $n + 1$, the shift
degree $k$, $n_p$ words and the cap $F$: $n_s = F(k + 1 + n_p)$ slots of $w = k(n + 1)$ entries. -/
def shqrSchurLogSize (n k np F : ℕ) : ℕ := F * (k + 1 + np) * (k * (n + 1))

/-- **The replay term of the precision threshold** of the Schur-mode algorithm: the unit roundoff
at which the replays of the logs on the couplings and on the accumulator
($78\boldsymbol{u}\,n_s w N_0$ per round) and the leaf products
($8(n + 1)(k + 2)\boldsymbol{u}N_0$ per round), over $2(n + 1)$ rounds at $N_0 = 2\Sigma$, cost at
most a quarter of the budget $\min(\delta, \Gamma/(16(n + 1)B))$ (`NLAlib.ShiftedQR.shqrBudget`). -/
noncomputable def uShQRSchurReplay (n k np F : ℕ) (B Γ S δ : ℝ) : ℝ :=
  shqrBudget n B Γ δ /
    (16 * ((n : ℝ) + 1) * (78 * shqrSchurLogSize n k np F + 8 * ((n : ℝ) + 1) * (k + 2)) * S)

/-- The rotation count of the accumulator of the Schur-mode algorithm with a leaf of $R_L$
rotation-equivalents: $2(n + 1)$ rounds of at most $n_s w$ replayed rotations and the leaf
products ($2k(k + 2)$), and $n + 1$ leaves. -/
def shqrSchurRotations (n k np F RL : ℕ) : ℕ :=
  2 * (n + 1) * (shqrSchurLogSize n k np F + 2 * k * (k + 2)) + (n + 1) * RL

section Routine

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q] [Inhabited ℝ]

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The headline's hypotheses, with their long real constants, make elaboration heavy.
/-- **The rounded shifted QR algorithm with a small-block Schur solver**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with the quantifiers of Theorem 1.4, corrected,
with any small-block Schur solver in the place of `SmallEig`). Let the machine have the standard
model at $\boldsymbol{u}$, index literals, exact natural literals up to $n + 1$, exact `toNat` and
comparisons, a measurable interpretation reading the tape only in its windows, and a stream
$s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it. Let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$
with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues separated by $\Gamma > 0$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$. Let the leaf `L` be a randomized small-block Schur solver on the orders at
most $\min(k, n + 1)$ and norms at most $4\Sigma$ with the cap $T$ and $12$ words `qs`: except
with probability $\varphi_L$ it stores an upper triangular $\mathbf{T}_b$ and an accumulator
$\mathbf{U}_b$ with $\|\mathbf{U}_b - \mathbf{V}_b\|_2 \le \varepsilon_L$ and $\mathbf{T}_b =
\mathbf{V}_b^{\mathsf H}(\mathbf{B} + \mathbf{F})\mathbf{V}_b$ for an exact unitary
$\mathbf{V}_b$ and $\|\mathbf{F}\|_2 \le \beta_L$, with $\varepsilon_L, \beta_L, \varphi_L \ge 0$,
$\beta_L$ at most the backward accuracy $\Sigma'(\beta/(4(2k + 1)\Sigma'))^k$ of the forward
accuracy $\beta$ = `shqrSmallEigAccuracy` at $\Sigma' = 4\Sigma$ and
$\varphi_L \le$ `shqrSmallEigFailure`. Let
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ and $\boldsymbol{u} \le$ the replay term. Then
from a memory holding $\mathbf{H}$, an accumulator $\mathbf{U}_0$, the deflation threshold word
and the words of `shqrParams` followed by `qs`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{roundedShQRWith}_L(\mathbf{H}) \text{ fails, or writes outside the
  matrix, the accumulator and the failure word, or lists no }
  \operatorname{spec}(\mathbf{H} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr] \le \varphi\,.$$
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there `SmallEig` is an oracle returning
eigenvalues.

Note: The leaf is a hypothesis, `NLAlib.Schur.RandomSchurLeafContract`: this is the algorithm
with a small-block Schur oracle. The diagonal of the leaf's triangular block serves as its Ritz
values (`NLAlib.ShiftedQR.schurDiag`), turned into forward accuracy by the matching
(`NLAlib.SmallEig.forwardBackwardError`). Instance: `SmallEig`
(`NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le`). The Schur form itself:
`NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`. -/
theorem roundedShQRWith_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) {εL βL φL : ℝ} {T : ℕ}
    {qs : List ℝ} {L : Impl O Q}
    (hLeaf : Schur.RandomSchurLeafContract law εL βL φL (min k (n + 1)) (4 * S) qs T L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hφL0 : 0 ≤ φL) (hφL : φL ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k (shqrParams n k B Γ S δ φ ++ qs).length (shqrCap n B Γ S δ)
      B Γ S δ)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} {U₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (ha : Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hU₀ : HoldsMatrix out U₀ μ.store)
    (ht : μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ))
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRWith L).body
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (ShQRSpectrum a out f H δ) μ} ≤ φ :=
  sorry

/-- **The rounded shifted QR algorithm with a terminating small-block Schur solver terminates on
every tape**: on a scalar machine with the standard model at $\boldsymbol{u} \le 1/100$, index
literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons and an exact polar
disk sampler, and a leaf `L` that terminates on orders at most $\min(k, n + 1)$ with the cap $T$
and $12$ words `qs`, its accumulator within $\varepsilon_L \ge 0$ of a unitary
(`NLAlib.ShiftedQR.TerminatingLeafRoutine`), for any $(n + 1) \times (n + 1)$ matrix
$\mathbf{H}$, accumulator $\mathbf{U}_0$, any $B, \Gamma, \Sigma, \delta, \varphi$ and $k$ the
degree of (eqn:setk) at $4B$, the run of `NLAlib.ShiftedQR.roundedShQRWith L` from a memory
holding the input with the words `NLAlib.ShiftedQR.shqrParams` followed by `qs` succeeds on every
tape and writes only the matrix, the accumulator and the failure word. -/
theorem roundedShQRWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hk : k = shqrDegree (4 * B)) {εL : ℝ} {T : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : TerminatingLeafRoutine εL (min k (n + 1)) qs T L I) (hqs : qs.length = 12)
    (hεL : 0 ≤ εL) {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    {U₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (ha : Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hU₀ : HoldsMatrix out U₀ μ.store) {thr : ℝ}
    (ht : μ.store.get t.1 t.2 = some thr)
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs)) (τ : Tape ℝ) :
    Writes .total I τ (roundedShQRWith L).body
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (fun _ => True) μ :=
  sorry

/-- **The rounded shifted QR algorithm with any small-block Schur solver is a Schur core**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] in Schur form, with a small-block Schur oracle).
Let the machine have the standard model at $\boldsymbol{u}$, index literals, exact natural
literals up to $n + 1$, exact `toNat` and comparisons, a measurable interpretation reading the
tape only in its windows, and a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler
on it. Let $B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree
of (eqn:setk) at $4B$. Let the leaf `L` be a randomized small-block Schur solver on the orders at
most $\min(k, n + 1)$ and norms at most $4\Sigma$ with the cap $T$ and $12$ words `qs`, with
accumulator error $\varepsilon_L \ge 0$, backward error $0 \le \beta_L \le
\Sigma'(\beta/(4(2k + 1)\Sigma'))^k$ ($\beta$ = `shqrSmallEigAccuracy`, $\Sigma' = 4\Sigma$) and
failure $0 \le \varphi_L \le$ `shqrSmallEigFailure`; let $\boldsymbol{u} \le
\boldsymbol{u}_{\mathrm{ShQR}}$ and $\boldsymbol{u}$ at most the replay term. Then
`roundedShQRSchurWith L` meets the Schur core contract on the orders at most $n + 1$, the class
$(B, \Gamma)$ and norms at most $\Sigma$, with the words: the deflation threshold, `shqrParams`,
`qs`. Except with probability $\varphi$ its flag is $0$, its matrix upper triangular, and the
pair is tracked from $(\mathbf{U}, \mathbf{H})$ with the backward error $\delta$ and the relative
accumulator error $(1 + 24\boldsymbol{u})^{R}(1 + \varepsilon_L)^{n+1} - 1$,
$R = 2(n + 1)(n_s w + 2k(k + 2))$.
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there only the eigenvalues are computed, with an
eigenvalue oracle.

Note: The leaf is a hypothesis (`NLAlib.Schur.RandomSchurLeafContract`): this is the core with a
small-block Schur oracle, the general form of
`NLAlib.ShiftedQR.roundedShQRSchur_randomSchurCoreContract` (the `SmallEig` leaf). The proof is
`NLAlib.ShiftedQR.solveRoundedWith_pwrites` with the decoupler
of `NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract`; the replay term keeps the
replays and products within a quarter of the merged budget.
Result: shifted-qr-rounded-schur-any-leaf -/
theorem roundedShQRSchurWith_randomSchurCoreContract {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1)) {k : ℕ} {B Γ S δ φ : ℝ} (hB : 1 ≤ B)
    (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hk : k = shqrDegree (4 * B)) {εL βL φL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : Schur.RandomSchurLeafContract law εL βL φL (min k (n + 1)) (4 * S) qs T L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hφL0 : 0 ≤ φL) (hφL : φL ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k (shqrParams n k B Γ S δ φ ++ qs).length (shqrCap n B Γ S δ)
      B Γ S δ) :
    Schur.RandomSchurCoreContract law
      ((1 + 24 * u) ^ shqrSchurRotations n k (shqrParams n k B Γ S δ φ ++ qs).length
        (shqrCap n B Γ S δ) RL - 1) δ φ (fun H => IsConditionedDiagonalizable B Γ H) k
      (shqrCap n B Γ S δ) T (n + 1) S
      (shqrDeflationThreshold n k B Γ S δ φ :: (shqrParams n k B Γ S δ φ ++ qs))
      (roundedShQRSchurWith L) I :=
  sorry

/-- **The Schur core with any terminating small-block Schur solver terminates on every tape**:
on a scalar machine with the standard model at $\boldsymbol{u} \le 1/100$, index literals, exact
natural literals up to $n + 1$, exact `toNat` and comparisons and an exact polar disk sampler, and
a leaf `L` that terminates on orders at most $\min(k, n + 1)$ with the cap $T$ and $12$ words
`qs`, its accumulator within $0 \le \varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$ of a
unitary, `roundedShQRSchurWith L` meets `NLAlib.Schur.TerminatingSchurCore` on the orders at most
$n + 1$ with the relative accumulator error $(1 + 24\boldsymbol{u})^R - 1$,
$R$ = `NLAlib.ShiftedQR.shqrSchurRotations` (`NLAlib.ShiftedQR.solveRoundedWith_terminates`). -/
theorem roundedShQRSchurWith_terminatingSchurCore {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I) {k : ℕ} {B Γ S δ φ : ℝ}
    (hk : k = shqrDegree (4 * B)) {εL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Impl O Q}
    (hLeaf : TerminatingLeafRoutine εL (min k (n + 1)) qs T L I) (hqs : qs.length = 12)
    (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) :
    Schur.TerminatingSchurCore
      ((1 + 24 * u) ^ shqrSchurRotations n k (shqrParams n k B Γ S δ φ ++ qs).length
        (shqrCap n B Γ S δ) RL - 1) k (shqrCap n B Γ S δ) T (n + 1)
      (shqrDeflationThreshold n k B Γ S δ φ :: (shqrParams n k B Γ S δ φ ++ qs))
      (roundedShQRSchurWith L) I :=
  sorry

end Routine

end NLAlib.ShiftedQR
