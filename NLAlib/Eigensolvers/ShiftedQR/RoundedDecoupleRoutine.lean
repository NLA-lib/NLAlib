/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleTermination

/-!
# The decoupling loop with a small-eigenvalue routine

The decoupling loop of [BanksGarzaVargasSrivastava2022, Lemma 6.4] calls `SmallEig` once per
iteration, in `Regularize`. Here the call runs a routine `SE : Impl O Q` with the interface
`[d, nq, T] (Bk, Q) → (Ev)`: its parameter words are the last $12$ words of the decoupler's
parameter words (the view `P[np - 12]`), and its cap dimension $T$ is a dimension of the
decoupler. Inside, `SE.body` is inlined, so every operation the proofs see is an operation of the
routine; a randomized program such as the one of [BanksGarzaVargasSrivastava2025] meets the
routine contract `NLAlib.ShiftedQR.RandomSmallEigContract`, and the kernel does as a routine
(`NLAlib.ShiftedQR.IsRandomSmallEig.randomSmallEigContract`). The programs
(`NLAlib.ShiftedQR.regularizeWith`, `NLAlib.ShiftedQR.shIterationWith`,
`NLAlib.ShiftedQR.roundedDecoupleWith`) are defined with their merged wrappers
(`NLAlib.ShiftedQR.regularize`, `NLAlib.ShiftedQR.shIteration`, `NLAlib.ShiftedQR.roundedDecouple`,
the routine the kernel and the cap $0$); the theorems here are the cases of the general ones with
the word count `qs.length` (`NLAlib.ShiftedQR.regularizeWith_pwrites_at` and the like).

## Main results

* `NLAlib.ShiftedQR.regularizeWith_pwrites`, `NLAlib.ShiftedQR.shIterationWith_pwrites`,
  `NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract`: the probabilistic
  contracts.
* `NLAlib.ShiftedQR.regularizeWith_terminates`, `NLAlib.ShiftedQR.shIterationWith_terminates`,
  `NLAlib.ShiftedQR.roundedDecoupleWith_terminatingDecouplerRoutine`: termination.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q] {n : ℕ}

omit [Has IdxTst Q] in
/-- **`Regularize` with a small-eigenvalue routine as a probabilistic block**
([BanksGarzaVargasSrivastava2022, Lemma 4.6], corrected; the routine of
[BanksGarzaVargasSrivastava2025, Corollary 1.3]): on a scalar machine with the standard model, exact
comparisons, index literals and exact natural literals up to $n + 1$, a measurable interpretation
reading the tape only in its windows and an exact polar disk sampler on a stream `s₀` uniform on
$[0, 1]$, let the routine `SE` meet `NLAlib.ShiftedQR.RandomSmallEigContract` on orders at most
$k$ and norms at most $\Sigma$ with forward error $\beta \ge 0$, failure probability
$\varphi_{\mathrm{se}} \ge 0$, cap $T$ and words `qs` stored at `qw`, apart from the outputs. Let
$\mathbf{H}$ be upper Hessenberg of order $n + 1$,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, $B^{2/k} \le 2$, $1 \le k \le n$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, eigenvalues separated by
$2\omega^2/\Sigma$, the radius word $R > 0$, $0 < \varphi \le 1$, the word $0.999\theta^k$, a
threshold word $t \ge (1 + \boldsymbol{u})^2\omega^2$, and the precision conditions in the
signature (the translates, `Optimal`, the forward error of the rounded steps). Then
`NLAlib.ShiftedQR.regularizeWith` writes only the matrix, the $k$ output pairs and the flag, and
except with probability at most $\varphi_{\mathrm{se}} + \varphi/2$ ends in
`NLAlib.ShiftedQR.RegularizeOutcome`. -/
theorem regularizeWith_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I) {n : ℕ}
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ} {s₀ : ℕ}
    {β φse : ℝ} (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I) (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φ tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φ / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φ / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hbound : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φ / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContract law β φse k T S qs SE I) {qw : ℕ × ℕ}
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + k ≤ ns)
    (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, qw, s, f], b.1 ≠ lg.1) :
    PWrites law I (regularizeWith SE).body
      (Env.frame [n + 1, k, qs.length, T, w, LL.length] [a, rd, c, thr, qw, a, s, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, qw, s, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ s.2 + 2 * k ≤ m.store.len s.1 ∧
        f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (RegularizeOutcome k H e u (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) *
        (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) (R * √(φ / (2 * k)) / 2) tv
        ((1 + 1.1) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) a s f lg ns w LL)
      (φse + φ / 2) := sorry

/-- **One iteration of the decoupling loop with a small-eigenvalue routine**
([BanksGarzaVargasSrivastava2022, Lemma 6.4], the body of the loop; the routine of
[BanksGarzaVargasSrivastava2025, Corollary 1.3]): on a scalar machine with the standard model, exact
comparisons, index literals, index conversion and exact natural literals up to $n + 1$, a
measurable interpretation reading the tape only in its windows and an exact polar disk sampler on
a stream `s₀` uniform on $[0, 1]$, let the routine `SE` meet
`NLAlib.ShiftedQR.RandomSmallEigContract` on orders at most $k$ and norms at most $\Sigma$ with
forward error $\beta \ge 0$, failure probability $\varphi_{\mathrm{se}} \ge 0$, cap $T$ and words
`qs` stored at `qw`, apart from the outputs. Let $\mathbf{H}$ be upper Hessenberg of order
$n + 1$ in the class $(B, 2\omega^2/\Sigma)$, $B^{2/k} \le 2$, $2 \le k = 2^m \le n$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \omega \le \psi_k(\mathbf{H})$, with the words of `Regularize`
and `Sh` and the precision conditions in the signature. Then
`NLAlib.ShiftedQR.shIterationWith` writes only the matrix and the flag and, except with
probability at most $\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi$, ends in
`NLAlib.ShiftedQR.ShIterationOutcome`. -/
theorem shIterationWith_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u ≤ 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ} (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hD : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {ε : ℝ} {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
          Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
          Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ}
    {B S ω R φR α γ φ C tv : ℝ} (hH : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ B)
    (hBk : B ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hψ : ω ≤ hessenbergPotential k H)
    (hSH : specNorm H ≤ S) (hgap : ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖e i - e j‖)
    (hR : 0 < R) (hφR : 0 < φR) (hφR1 : φR ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φR / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxuR : 300 * (n + 1) ^ 2 * u ≤
      (16 * B)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hboundR : (66 + 2 * 1.1) * B * S * ((2 + 2 * 1.1) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hα : α = (1.01 * B) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * B ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ 2)) ^
        ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : R * √(φR / (2 * k)) / 2 ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹)) ≤ C)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (8004 * B)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * B * S * ((2 + 2 * C) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * S)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * S)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        B ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContract law β φse k T S qs SE I) {qw : ℕ × ℕ}
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns)
    (hw : k * n ≤ w)
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, f], b.1 ≠ lg.1) :
    PWrites law I (shIterationWith SE).body
      (Env.frame [n + 1, q, k, (excNet ε).length, qs.length, T, w, LL.length]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m => m.Live [a, rd, c, thr, wg, wr, ww, wp, g, qw, f] ∧ HoldsMatrix a H m.store ∧
        m.store.readBlock qw.1 qw.2 qs.length = some qs ∧
        m.store.get rd.1 rd.2 = some R ∧ m.store.get c.1 c.2 = some
          (0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k) ∧
        m.store.get thr.1 thr.2 = some tv ∧ m.store.get wg.1 wg.2 = some ((1 - γ) ^ k) ∧
        m.store.get wr.1 wr.2 = some ((2 : ℝ) ^ ((k : ℝ)⁻¹) *
          ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
            B ^ ((k : ℝ)⁻¹))) ∧
        m.store.get ww.1 ww.2 = some (ε / 2) ∧ m.store.get wp.1 wp.2 = some (1.0015 * (1 - γ)) ∧
        m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
          some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < m.store.len f.1 ∧
        HoldsSlottedLog lg ns w LL [] m.store ∧ m.Live [lg])
      (ShIterationOutcomeBy u k H γ tv
          ((1 + C) * specNorm H * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1))
        a lg ns w LL (k + 1 + (excNet ε).length)) (φse + φR / 2 + φ) := sorry
-- The hypotheses of the iteration make the elaboration of the statement heavy.
set_option maxHeartbeats 4000000 in
/-- **The rounded decoupling loop with a small-eigenvalue routine meets the randomized
decoupling contract** ([BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating point, corrected;
the routine of [BanksGarzaVargasSrivastava2025, Corollary 1.3]): on a machine with the
standard model
at
$\boldsymbol{u} < 1$, exact natural literals up to $n_{\max} + 1$, a measurable interpretation
reading the tape only in its windows and an exact polar disk sampler on a stream `s₀` uniform on
$[0, 1]$, let the routine `SE` meet `NLAlib.ShiftedQR.RandomSmallEigContract` on orders at most
$k$ and norms at most $S$ (the iterate norm) with forward error $\beta \ge 0$, failure probability
$\varphi_{\mathrm{se}} \ge 0$, cap $T$ and $12$ words `qs`. Under the conditions of one iteration
at the order $n_{\max} + 1$, the class constant $B_i \ge 4B$ and the iterate norm $S$, and those
of the loop (the scan thresholds, the cap, $N_{\max} + FE \le S$ and
$FE \le (g/2)/(16(n_{\max} + 1) \cdot 2B)$ for
$E = (1 + C)S((1 + 300(n_{\max} + 1)^2\boldsymbol{u})^k - 1)$), all in the signature,
`NLAlib.ShiftedQR.roundedDecoupleWith` with the words `NLAlib.ShiftedQR.roundedDecoupleParams`
followed by `qs` meets `NLAlib.ShiftedQR.RandomDecouplingRoutineContract` on the class $(2B, g/2)$
with failure probability $F(\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi)$, the level $\omega_D$
and
the backward error $FE$. -/
theorem roundedDecoupleWith_randomDecouplingRoutineContract {M : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I) {nmax : ℕ}
    (hNat : IsExactNatLit id M (nmax + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ} (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse)
    (hDisk : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q F : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    {B g Bi Nmax S ω ωD tL tv R φR α γ φ C ε : ℝ} (hg : 0 < g) (hBi : 4 * B ≤ Bi)
    (hS0 : 0 ≤ S) (hBk : Bi ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hgapS : 2 * ω ^ 2 / S ≤ g / 4)
    (hR : 0 < R) (hφR : 0 < φR) (hφR1 : φR ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φR / (2 * k))) (hnu : (nmax + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((nmax + 1 : ℕ) : ℝ) * √((nmax + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((nmax + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxuR : 300 * (nmax + 1) ^ 2 * u ≤
      (16 * Bi)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hboundR : (66 + 2 * 1.1) * Bi * S * ((2 + 2 * 1.1) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(nmax + 1) * (300 * (nmax + 1) ^ 2 * u) ≤ ω / 2)
    (hα : α = (1.01 * Bi) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * Bi ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ 2)) ^
        ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : R * √(φR / (2 * k)) / 2 ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((nmax + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹)) ≤ C)
    (hxu : 300 * (nmax + 1) ^ 2 * u ≤
      (8004 * Bi)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * Bi * S * ((2 + 2 * C) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(nmax + 1) * (300 * (nmax + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * S)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * S)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((nmax + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) (hthr : (1 + u) ^ 2 * tv ≤ (1 - u) ^ 2 * tL)
    (hcut : tL ≤ (1 - u) ^ 2 * ωD ^ 2) (hωD : 0 ≤ ωD)
    (hfuel : (1 + u) ^ 2 * ((1.002 * (1 - γ)) ^ F * Nmax) ^ 2 ≤ tL)
    (hSN : Nmax + F * ((1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1)) ≤ S)
    (hsmall : F * ((1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1)) ≤
      g / 2 / (16 * (nmax + 1) * (2 * B))) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContract law β φse k T S qs SE I) (hqs : qs.length = 12) {ns ws : ℕ}
    (hns : F * (k + 1 + (excNet ε).length) ≤ ns) (hws : k * nmax ≤ ws) :
    RandomDecouplingRoutineContract law (2 * B) (g / 2) (F * (φse + φR / 2 + φ)) k F T nmax
      Nmax (roundedDecoupleParams tL R tv γ Bi α ε k q ++ qs) ns ws ωD
      (fun _ => F * ((1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecoupleWith SE) I := sorry

omit [Has IdxTst Q] in
/-- **`Regularize` with a terminating small-eigenvalue routine terminates on any matrix**
([BanksGarzaVargasSrivastava2022, §4.2]): on a scalar machine with exact comparisons, index
literals and exact natural literals up to $n + 1$, with an exact polar sampler and a routine `SE`
that terminates on orders at most $k$ with the cap $T$ and the words `qs`
(`NLAlib.ShiftedQR.TerminatingSmallEig`) stored at `qw`, from any matrix of order $n + 1$ at `a`,
any words at `rd`, `c`, `thr`, room for $k \le n$ output pairs at `s` and the flag at `f` (the
views live, the matrix, the pairs and the flag apart from each other and from the inputs),
`NLAlib.ShiftedQR.regularizeWith` writes only the matrix, the pairs and the flag, and leaves all
three stored, on every tape. -/
theorem regularizeWith_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) {n : ℕ} (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k : ℕ} (hk : k ≤ n) {a rd c thr s f : ℕ × ℕ}
    (has : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock s.1 s.2 (2 * k)))
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hsf : Fp.Disj (Store.inBlock s.1 s.2 (2 * k)) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {R cw tv : ℝ}
    (hl : m.Live [a, rd, c, thr, s, f]) (hA : HoldsMatrix a H m.store)
    (hrd : m.store.get rd.1 rd.2 = some R) (hc : m.store.get c.1 c.2 = some cw)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hrs : s.2 + 2 * k ≤ m.store.len s.1)
    (hrf : f.2 < m.store.len f.1) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : TerminatingSmallEig k T qs SE I) {qw : ℕ × ℕ} (hlq : qw.1 < m.store.length)
    (hq : m.store.readBlock qw.1 qw.2 qs.length = some qs)
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
      Store.inBlock s.1 s.2 (2 * k) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))} (hj : LL.length + k ≤ ns)
    (hw : k * n ≤ w)
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hlgl : m.Live [lg])
    (hlgv : ∀ b ∈ [a, rd, c, thr, qw, s, f], b.1 ≠ lg.1) :
    Writes .total I τ (regularizeWith SE).body
      (Env.frame [n + 1, k, qs.length, T, w, LL.length] [a, rd, c, thr, qw, a, s, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock s.1 s.2 (2 * k) ⊔
        Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        (∃ ys, m'.store.readBlock s.1 s.2 (2 * k) = some ys) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = k ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m :=
  sorry

/-- One iteration with a terminating small-eigenvalue routine terminates on any matrix: on a
scalar machine with exact comparisons, index literals, index conversion and exact natural
literals up to $n + 1$, an exact polar sampler and a routine `SE` that terminates on orders at
most $k$ with the cap $T$ and the words `qs` stored at `qw`, for $k = 2^q \le n$, from any matrix
of order $n + 1$ at `a`, any words at `rd`, `c`, `thr`, `wg`, `wr`, `ww`, `wp`, the net words at
`g` and room for the flag, the matrix and the flag apart from each other and from the inputs,
`NLAlib.ShiftedQR.shIterationWith` writes only the matrix and the flag and leaves both stored, on
every tape. -/
theorem shIterationWith_terminates {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    (hQ : IsToNat id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I) {τ : Tape ℝ}
    {m : Mem ℝ} {k q : ℕ} (hkq : k = 2 ^ q) (hkn : k ≤ n) {ε : ℝ}
    {a rd c thr wg wr ww wp g f : ℕ × ℕ}
    (haf : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1))
    (hio : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock rd.1 rd.2 1 ⊔ Store.inBlock c.1 c.2 1 ⊔ Store.inBlock thr.1 thr.2 1 ⊔
        Store.inBlock wg.1 wg.2 1 ⊔ Store.inBlock wr.1 wr.2 1 ⊔ Store.inBlock ww.1 ww.2 1 ⊔
        Store.inBlock wp.1 wp.2 1 ⊔ Store.inBlock g.1 g.2 (2 * (excNet ε).length)))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {R cv tv cg cr cw cp : ℝ}
    (hl : m.Live [a, rd, c, thr, wg, wr, ww, wp, g, f]) (hA : HoldsMatrix a H m.store)
    (hrd : m.store.get rd.1 rd.2 = some R) (hc : m.store.get c.1 c.2 = some cv)
    (hthr : m.store.get thr.1 thr.2 = some tv) (hwg : m.store.get wg.1 wg.2 = some cg)
    (hwr : m.store.get wr.1 wr.2 = some cr) (hww : m.store.get ww.1 ww.2 = some cw)
    (hwp : m.store.get wp.1 wp.2 = some cp)
    (hg : m.store.readBlock g.1 g.2 (2 * (excNet ε).length) =
      some ((excNet ε).flatMap fun z => [z.re, z.im])) (hrf : f.2 < m.store.len f.1)
    {T : ℕ} {qs : List ℝ} {SE : Impl O Q} (hSE : TerminatingSmallEig k T qs SE I)
    {qw : ℕ × ℕ} (hlq : qw.1 < m.store.length)
    (hq : m.store.readBlock qw.1 qw.2 qs.length = some qs)
    (hqw : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock qw.1 qw.2 qs.length))
    {ns w : ℕ} {lg : ℕ × ℕ} {LL : List (Option (List GivensEntry))}
        (hj : LL.length + (k + 1 + (excNet ε).length) ≤ ns)
    (hw : k * n ≤ w)
    (hlog : HoldsSlottedLog lg ns w LL [] m.store) (hlgl : m.Live [lg])
    (hlgv : ∀ b ∈ [a, rd, c, thr, wg, wr, ww, wp, g, qw, f], b.1 ≠ lg.1) :
    Writes .total I τ (shIterationWith SE).body
      (Env.frame [n + 1, q, k, (excNet ε).length, qs.length, T, w, LL.length]
        [a, rd, c, thr, wg, wr, ww, wp, g, qw, a, f, lg])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun m' => (∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a H' m'.store) ∧
        ∃ x, m'.store.get f.1 f.2 = some x ∧
        ∃ Ls : List (Option (List GivensEntry)), Ls.length = (k + 1 + (excNet ε).length) ∧
          (∀ x ∈ slotEntries w Ls, x.1 + 1 < n + 1) ∧
              HoldsSlottedLog lg ns w (LL ++ Ls) [] m'.store) m :=
  sorry

/-- **The rounded decoupling loop with a terminating small-eigenvalue routine terminates on
every tape and every matrix** ([BanksGarzaVargasSrivastava2022, Lemma 6.4], termination only): on
a scalar machine with exact comparisons, index literals, index conversion and exact natural
literals up to $n_{\max} + 1$, an exact polar sampler and a routine `SE` that terminates on
orders at most $k$ with the cap $T$ and $12$ words `qs`,
`NLAlib.ShiftedQR.roundedDecoupleWith` with the words `NLAlib.ShiftedQR.roundedDecoupleParams`
followed by `qs` and $k = 2^q$ is a `NLAlib.ShiftedQR.TerminatingDecouplerRoutine` for orders up
to $n_{\max} + 1$, with any iteration cap $F$. -/
theorem roundedDecoupleWith_terminatingDecouplerRoutine {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) {nmax : ℕ} (hNat : IsExactNatLit id M (nmax + 1))
    (hC : IsCmp id I) (hQ : IsToNat id I) {s₀ : ℕ} (hD : IsPolarDiskSampler s₀ I)
    {k q F : ℕ} (hkq : k = 2 ^ q) (tL R tv γ B α ε : ℝ) {T : ℕ} {qs : List ℝ}
    {SE : Impl O Q} (hSE : TerminatingSmallEig k T qs SE I) (hqs : qs.length = 12) {ns ws : ℕ}
    (hns : F * (k + 1 + (excNet ε).length) ≤ ns) (hws : k * nmax ≤ ws) :
    TerminatingDecouplerRoutine nmax k F T (roundedDecoupleParams tL R tv γ B α ε k q ++ qs) ns ws
      (roundedDecoupleWith SE) I := sorry

end Theorems

end NLAlib.ShiftedQR
