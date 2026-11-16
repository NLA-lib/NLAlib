/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import NLAlib.RandomMatrix.Gaussian.Complex.Shattering

/-!
# The parameters of the small-eigenvalue solver

The parameters of [BanksGarzaVargasSrivastava2025, Theorem 1.1] as closed forms of the order bound
$n_{\max}$, the norm bound $\Sigma$ (`S`), the backward error $\delta$, the failure probability
$\varphi$ and the two tail records of the random-matrix hypotheses: the perturbation scale
$\gamma$, the class it produces (separation $t_1$, condition $t_2^{-1}$, from the inverted tails,
`NLAlib.SmallEig.ginibreClass_spec`), the coupling threshold $\omega$ of the decoupler and the
accuracy $\beta' = \omega/20$ of `OneEig`, the radii $\eta_1, \eta_2$ of the regularized net, the
degree $m = 2^q$ of `DistSpec`, the round cap $t$ of `OneEig` and the step cap $m_2$ of
`Decouple`, and the scan thresholds. The words are fixed at the outer bound $n_{\max}$ and serve
every order $d \le n_{\max}$: the program computes the scale $\gamma/\sqrt d$ itself. Logarithms
are in base $2$ (the paper's erratum P7); the corrections of the paper's choices of $t$ (P6) and
$\eta_2$ (P5) are in `NLAlib.SmallEig.oneEigRounds_spec` and `NLAlib.SmallEig.oneEigRadii_spec`.

## Main definitions

* `NLAlib.SmallEig.distSpecDegree`, `NLAlib.SmallEig.oneEigRounds`,
  `NLAlib.SmallEig.oneEigOuterRadius`, `NLAlib.SmallEig.oneEigInnerRadius`: the choices of
  `DistSpec` and `OneEig`.
* `NLAlib.SmallEig.ginibreGapThreshold`, `NLAlib.SmallEig.ginibreConditionThreshold`: the class
  of the perturbation.
* `NLAlib.SmallEig.smallEigParams`, `NLAlib.SmallEig.smallEigCap`, `NLAlib.SmallEig.SmallEigCaps`:
  the twelve parameter words, the cap dimension and the validity of the cap words.

## Main results

* `NLAlib.SmallEig.distSpecDegree_spec`, `NLAlib.SmallEig.oneEigRounds_spec`,
  `NLAlib.SmallEig.oneEigRadii_spec`, `NLAlib.SmallEig.ginibreClass_spec`: the scalar facts.
* `NLAlib.SmallEig.length_smallEigParams`, `NLAlib.SmallEig.smallEigParams_spec`,
  `NLAlib.SmallEig.smallEigParams_pos`, `NLAlib.SmallEig.smallEigCaps_smallEigParams`: the words.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Real

/-! ### The choices of `DistSpec` and `OneEig` -/

/-- The degree $m_1 = \lceil 12\log_2\kappa + 6\log_2(1/p)\rceil$ of `DistSpec` for the condition
$\kappa$ and the weight $p$ ([BanksGarzaVargasSrivastava2025, Proposition 3.5], line 1 of
`OneEig`, with $\log = \log_2$). -/
noncomputable def distSpecDegree (κ p : ℝ) : ℕ := ⌈12 * logb 2 κ + 6 * logb 2 p⁻¹⌉₊

/-- **The degree of `DistSpec` is large enough** ([BanksGarzaVargasSrivastava2025,
Observation 3.3], "$m$ is large enough", with $\log = \log_2$): for $\kappa \ge 1$,
$0 < p \le 1$ and $m \ge 1$ at least `NLAlib.SmallEig.distSpecDegree` $\kappa$ $p$,
$$0.9 \le 0.998\,\kappa^{-1/m} \quad\text{and}\quad 1.003\,\kappa^{1/m}p^{-1/(2m)} \le 1.1\,,$$
the two factors by which the estimate of `DistSpec` may miss the distance to the spectrum. -/
theorem distSpecDegree_spec {κ p : ℝ} (hκ : 1 ≤ κ) (hp : 0 < p) (hp1 : p ≤ 1) {m : ℕ}
    (hm0 : 0 < m) (hm : distSpecDegree κ p ≤ m) :
    0.9 ≤ 0.998 * κ ^ (-(m : ℝ)⁻¹) ∧ 1.003 * κ ^ ((m : ℝ)⁻¹) * p ^ (-(2 * (m : ℝ))⁻¹) ≤ 1.1 := by
  sorry

/-- The round cap $t = \lceil 2\log_2(5.2\,\Sigma/\beta)\rceil$ of `OneEig` (the paper's
$\lceil 2\log(\Sigma/(5\beta))\rceil$ corrected, its erratum P6). -/
noncomputable def oneEigRounds (S β : ℝ) : ℕ := ⌈2 * logb 2 (5.2 * S / β)⌉₊

/-- **The round cap of `OneEig` suffices** ([BanksGarzaVargasSrivastava2025, Proposition 3.5],
the choice of $t$ corrected): for $0 < \beta \le \Sigma$ and $t$ =
`NLAlib.SmallEig.oneEigRounds` $\Sigma$ $\beta$,
$$\frac{4.6 \cdot 0.66^t}{0.9} \le \frac{\beta}{\Sigma} \quad\text{and}\quad
  6t + 1 \le 12\log_2\frac{7.8\,\Sigma}{\beta}\,.$$
The paper's $t$ fails the first for $\Sigma/\beta < 6 \cdot 10^7$. -/
theorem oneEigRounds_spec {S β : ℝ} (hβ : 0 < β) (hβS : β ≤ S) :
    4.6 * 0.66 ^ oneEigRounds S β / 0.9 ≤ β / S ∧
      6 * (oneEigRounds S β : ℝ) + 1 ≤ 12 * logb 2 (7.8 * S / β) := by
  sorry

/-- The radius $\eta_2 = \min(\beta/40, g/3)$ of the disk samples of `OneEig` (the paper's
$\beta/5$ corrected, its erratum P5). -/
noncomputable def oneEigOuterRadius (β g : ℝ) : ℝ := min (β / 40) (g / 3)

/-- The radius $\eta_1 = \eta_2\sqrt{\varphi/(12\log_2(8\Sigma/\beta))}$ that the accepted point of
`OneEig` keeps from the spectrum. -/
noncomputable def oneEigInnerRadius (S β g φ : ℝ) : ℝ :=
  oneEigOuterRadius β g * √(φ / (12 * logb 2 (8 * S / β)))

/-- **The radii of `OneEig`** ([BanksGarzaVargasSrivastava2025, Observation 3.4], with
$\eta_2 = \min(\beta/40, g/3)$, its errata P5 and N6): for $0 < \beta \le 0.8\,\Sigma$, $g > 0$
and $0 < \varphi \le 1$, with $\eta_1, \eta_2$ = `NLAlib.SmallEig.oneEigInnerRadius`,
`NLAlib.SmallEig.oneEigOuterRadius` and $t$ = `NLAlib.SmallEig.oneEigRounds` $\Sigma$ $\beta$:
$\eta_1 > 0$, $\eta_1 + \eta_2 \le g/2$, $\eta_2 \le 0.02\,\Sigma$ and
$(6t + 1)(\eta_1/\eta_2)^2 \le \varphi$. -/
theorem oneEigRadii_spec {S β g φ : ℝ} (hβ : 0 < β) (hβS : β ≤ 0.8 * S) (hg : 0 < g)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < oneEigInnerRadius S β g φ ∧ oneEigInnerRadius S β g φ + oneEigOuterRadius β g ≤ g / 2 ∧
      oneEigOuterRadius β g ≤ 0.02 * S ∧
      (6 * (oneEigRounds S β : ℝ) + 1) * (oneEigInnerRadius S β g φ / oneEigOuterRadius β g) ^ 2
        ≤ φ := by
  sorry

/-- The step cap $m_2 = \lceil\log_2(\kappa/\sqrt p)\rceil + 1$ of `Decouple` for the condition
$\kappa$ and the weight $p$: $\kappa \le 2^{m_2}\sqrt p$. -/
noncomputable def decoupleSteps (κ p : ℝ) : ℕ := ⌈logb 2 (κ / √p)⌉₊ + 1

/-! ### The class of the perturbation -/

/-- The separation $t_1 = \gamma\tau_1$ of the eigenvalues of a Ginibre perturbation of scale
$\gamma$ of a matrix of norm at most $\Sigma$ and order at most $n_{\max}$, at the failure
probability $\varphi$, for the gap tail $c_1$: $\tau_1$ inverts the normalized tail at the norm
ratio $K = (\Sigma + 4\gamma)/\gamma$ (`NLAlib.polyLogTailInverse`). -/
noncomputable def ginibreGapThreshold (nmax : ℕ) (S γ φ : ℝ) (c₁ : PolyLogTail) : ℝ :=
  γ * polyLogTailInverse c₁.normalize nmax ((S + 4 * γ) / γ) φ

/-- The condition bound $t_2^{-1}$ of the eigenvectors of a Ginibre perturbation, as
`NLAlib.SmallEig.ginibreGapThreshold`, for the condition tail $c_2$. -/
noncomputable def ginibreConditionThreshold (nmax : ℕ) (S γ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  polyLogTailInverse c₂.normalize nmax ((S + 4 * γ) / γ) φ

/-- **The inverted tails** ([BanksGarzaVargasSrivastava2025, Lemma 6.5], replaced by the class):
for tail records with $b_1, b_2 > 0$, $n_{\max} \ge 1$, $\Sigma \ge 0$, $\gamma > 0$ and
$0 < \varphi \le 1$, with $K = (\Sigma + 4\gamma)/\gamma$ and $t_1, t_2$ =
`NLAlib.SmallEig.ginibreGapThreshold`, `NLAlib.SmallEig.ginibreConditionThreshold`: $0 < t_1 \le
\gamma$, $0 < t_2 \le 1$, at every order $1 \le N \le n_{\max}$ the two normalized tails
$$\bar C_1 N^{\bar a_1}(t_1/\gamma)^{\bar b_1}(K + \log(\gamma/t_1))^{\bar c_1}, \qquad
  \bar C_2 N^{\bar a_2}t_2^{\bar b_2}(K + \log(1/t_2))^{\bar c_2}$$
are at most $\varphi$, and $\log_2(\gamma/t_1)$, $\log_2(1/t_2)$ are at most $2/b_i$ times
$\log_2(s_i/\varphi)$, $s_i$ the scale `NLAlib.polyLogTailScale` of the normalized record at
$n_{\max}$ and $K$. -/
theorem ginibreClass_spec {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S γ φ : ℝ} (hS : 0 ≤ S) (hγ : 0 < γ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < ginibreGapThreshold nmax S γ φ c₁ ∧ ginibreGapThreshold nmax S γ φ c₁ ≤ γ ∧
      0 < ginibreConditionThreshold nmax S γ φ c₂ ∧ ginibreConditionThreshold nmax S γ φ c₂ ≤ 1 ∧
      (∀ N : ℕ, 1 ≤ N → N ≤ nmax →
        c₁.normalize.C * (N : ℝ) ^ c₁.normalize.a *
            (ginibreGapThreshold nmax S γ φ c₁ / γ) ^ c₁.normalize.b *
            ((S + 4 * γ) / γ + log (γ / ginibreGapThreshold nmax S γ φ c₁)) ^ c₁.normalize.c ≤ φ ∧
        c₂.normalize.C * (N : ℝ) ^ c₂.normalize.a *
            ginibreConditionThreshold nmax S γ φ c₂ ^ c₂.normalize.b *
            ((S + 4 * γ) / γ + log (ginibreConditionThreshold nmax S γ φ c₂)⁻¹) ^ c₂.normalize.c
          ≤ φ) ∧
      logb 2 (γ / ginibreGapThreshold nmax S γ φ c₁) ≤
        2 / c₁.b * logb 2 (polyLogTailScale c₁.normalize nmax ((S + 4 * γ) / γ) / φ) ∧
      logb 2 (ginibreConditionThreshold nmax S γ φ c₂)⁻¹ ≤
        2 / c₂.b * logb 2 (polyLogTailScale c₂.normalize nmax ((S + 4 * γ) / γ) / φ) := by
  sorry

/-! ### The parameter words -/

/-- The noise level $W = 3 + \sqrt{\log(4/\varphi)}$: the norm of $\gamma n^{-1/2}\mathbf{G}$ is
at most $\gamma W$ except with probability $\varphi/4$, at every order. -/
noncomputable def smallEigNoiseLevel (φ : ℝ) : ℝ := 3 + √(log (4 / φ))

/-- The perturbation scale $\gamma = \delta/(4W)$, $W$ = `NLAlib.SmallEig.smallEigNoiseLevel`. -/
noncomputable def smallEigScale (δ φ : ℝ) : ℝ := δ / (4 * smallEigNoiseLevel φ)

/-- The separation $t_1$ of the perturbed matrix: the gap threshold at the scale $\gamma/2$ and the
failure $\varphi/(4 \cdot 2^{\bar c_1})$, so that the tail at any scale in
$[\gamma/2, 2\gamma]$ (the rounded scale of the program) is at most $\varphi/4$. -/
noncomputable def smallEigGap (nmax : ℕ) (S δ φ : ℝ) (c₁ : PolyLogTail) : ℝ :=
  ginibreGapThreshold nmax S (smallEigScale δ φ / 2) (φ / (4 * 2 ^ c₁.normalize.c)) c₁

/-- The condition parameter $t_2$ of the perturbed matrix: the condition threshold at the scale
$\gamma/2$ and the failure $\varphi/4$. -/
noncomputable def smallEigCond (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  ginibreConditionThreshold nmax S (smallEigScale δ φ / 2) (φ / 4) c₂

/-- The condition bound $B_c = 4/t_2$ of the matrix the core receives (one doubling for the
rounding of the perturbation, one for the reduction). -/
noncomputable def smallEigCondition (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  4 / smallEigCond nmax S δ φ c₂

/-- The separation $g_c = t_1/4$ of the matrix the core receives. -/
noncomputable def smallEigSeparation (nmax : ℕ) (S δ φ : ℝ) (c₁ : PolyLogTail) : ℝ :=
  smallEigGap nmax S δ φ c₁ / 4

/-- The coupling threshold
$\omega = \min(\delta/4, g_c/(16n_{\max}B_c))/(12n_{\max})$ of the decoupler. -/
noncomputable def smallEigOmega (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (δ / 4) (smallEigSeparation nmax S δ φ c₁ / (16 * nmax * smallEigCondition nmax S δ φ c₂)) /
    (12 * nmax)

/-- The accuracy $\beta' = \omega/20$ of `OneEig`. -/
noncomputable def smallEigAccuracy (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  smallEigOmega nmax S δ φ c₁ c₂ / 20

/-- The failure $\varphi_D = \varphi/(16n_{\max})$ allowed to one decoupler call; half of it to
`RHess`, half to `OneEig`. -/
noncomputable def smallEigDecouplerFailure (nmax : ℕ) (φ : ℝ) : ℝ := φ / (16 * nmax)

/-- The norm bound $R = 3\sqrt{n_{\max}} + \sqrt{2\log(4/\varphi_D)}$ of the Gaussian direction of
`RHess`. -/
noncomputable def smallEigVectorRadius (nmax : ℕ) (φ : ℝ) : ℝ :=
  3 * √nmax + √(2 * log (4 / smallEigDecouplerFailure nmax φ))

/-- The lower bound $p = (\varphi_D/(4n_{\max}))/(64R^2(4B_c)^2)$ of the last-row weights after
`RHess`. -/
noncomputable def smallEigWeight (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  smallEigDecouplerFailure nmax φ / (4 * nmax) /
    (64 * smallEigVectorRadius nmax φ ^ 2 * (4 * smallEigCondition nmax S δ φ c₂) ^ 2)

/-- The exponent $q$ of the degree $m = 2^q$ of `DistSpec`:
$q = \lceil\log_2 m_1\rceil$ for $m_1$ = `NLAlib.SmallEig.distSpecDegree` at the condition
$8B_c$ and the weight $p$. -/
noncomputable def smallEigDegreeLog (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℕ :=
  Nat.clog 2 (distSpecDegree (8 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂))

/-- The round cap $t$ of `OneEig` at the block norm $2\Sigma$ and the accuracy $\beta'$. -/
noncomputable def smallEigRounds (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  oneEigRounds (2 * S) (smallEigAccuracy nmax S δ φ c₁ c₂)

/-- The step cap $m_2$ of `Decouple` at the condition $8B_c$ and the weight $p$. -/
noncomputable def smallEigDecoupleSteps (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℕ :=
  decoupleSteps (8 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂)

/-- The radius $\eta_2$ of the disk samples of `OneEig`, at the separation $g_c/4$ inside the
decoupler. -/
noncomputable def smallEigOuterRadius (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  oneEigOuterRadius (smallEigAccuracy nmax S δ φ c₁ c₂) (smallEigSeparation nmax S δ φ c₁ / 4)

/-- The radius $\eta_1$ of `OneEig`, at the failure $\varphi_D/2$. -/
noncomputable def smallEigInnerRadius (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  oneEigInnerRadius (2 * S) (smallEigAccuracy nmax S δ φ c₁ c₂)
    (smallEigSeparation nmax S δ φ c₁ / 4) (smallEigDecouplerFailure nmax φ / 2)

/-- **The twelve parameter words of the small-eigenvalue program**
([BanksGarzaVargasSrivastava2025, Theorem 1.1]): in this order, the scale $\gamma$, the coupling
threshold $\omega$, the accuracy $\beta' = \omega/20$, the radii $\eta_1$ and $\eta_2$ of
`OneEig`, its exit threshold $0.9\beta'$, the worklist's scan threshold $2(1.5\,\omega)^2$, the
scan threshold $t_L = 2\omega^2$ of `Decouple`, and the cap words $m = 2^q$, $q$, $t$, $m_2$. The
program reads them at these offsets. -/
noncomputable def smallEigParams (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℝ :=
  [smallEigScale δ φ, smallEigOmega nmax S δ φ c₁ c₂, smallEigAccuracy nmax S δ φ c₁ c₂,
    smallEigInnerRadius nmax S δ φ c₁ c₂, smallEigOuterRadius nmax S δ φ c₁ c₂,
    0.9 * smallEigAccuracy nmax S δ φ c₁ c₂, 2 * (1.5 * smallEigOmega nmax S δ φ c₁ c₂) ^ 2,
    2 * smallEigOmega nmax S δ φ c₁ c₂ ^ 2, ((2 ^ smallEigDegreeLog nmax S δ φ c₂ : ℕ) : ℝ),
    (smallEigDegreeLog nmax S δ φ c₂ : ℝ), (smallEigRounds nmax S δ φ c₁ c₂ : ℝ),
    (smallEigDecoupleSteps nmax S δ φ c₂ : ℝ)]

/-- The cap dimension $T = \max(m, t, m_2)$ of the program. -/
noncomputable def smallEigCap (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  max (2 ^ smallEigDegreeLog nmax S δ φ c₂)
    (max (smallEigRounds nmax S δ φ c₁ c₂) (smallEigDecoupleSteps nmax S δ φ c₂))

/-- **Valid cap words** for the cap dimension $T$: the words $8$ to $11$ of `qs` are exact
naturals $m, q, t, m_2$ with $m = 2^q$ and $m, t, m_2 \le T$. The program reads them with bounded
index reads, which fail on a negative or too large word. -/
def SmallEigCaps (T : ℕ) (qs : List ℝ) : Prop :=
  ∃ m q t m₂ : ℕ, qs.getD 8 0 = m ∧ qs.getD 9 0 = q ∧ qs.getD 10 0 = t ∧ qs.getD 11 0 = m₂ ∧
    m = 2 ^ q ∧ m ≤ T ∧ t ≤ T ∧ m₂ ≤ T

/-- The program has twelve parameter words. -/
theorem length_smallEigParams (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) :
    (smallEigParams nmax S δ φ c₁ c₂).length = 12 := by
  simp [smallEigParams]

/-- **The side conditions of the parameter words** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], the parameter choices, corrected): for tail records with $b_1, b_2 > 0$,
$n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$, with $\gamma, t_1, t_2, B_c,
g_c, \omega, \beta', \eta_1, \eta_2, p, m = 2^q, t, m_2$ the choices of this file: the noise is
within budget, $\gamma W \le \delta/4$; the class tails hold at every order $N \le n_{\max}$ with
$\varphi/4$ each (`NLAlib.SmallEig.ginibreClass_spec`); the worklist's cut level
$2.25\,\omega$ over $2n_{\max}$ rounds is within $\delta/4$ and the class bound
$g_c/(16n_{\max}B_c)$; the choices of `OneEig` hold at the block norm $2\Sigma$
(`NLAlib.SmallEig.oneEigRadii_spec` at $\beta'$, $g_c/4$, $\varphi_D/2$), the degree $m$ is at
least `NLAlib.SmallEig.distSpecDegree` $8B_c$ $p$, and $8B_c \le 2^{m_2}\sqrt p$. -/
theorem smallEigParams_spec {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < smallEigScale δ φ ∧ smallEigScale δ φ * smallEigNoiseLevel φ ≤ δ / 4 ∧
      0 < smallEigGap nmax S δ φ c₁ ∧ smallEigGap nmax S δ φ c₁ ≤ smallEigScale δ φ ∧
      0 < smallEigCond nmax S δ φ c₂ ∧ smallEigCond nmax S δ φ c₂ ≤ 1 ∧
      0 < smallEigOmega nmax S δ φ c₁ c₂ ∧
      2 * nmax * (2.25 * smallEigOmega nmax S δ φ c₁ c₂) ≤ δ / 4 ∧
      2 * nmax * (2.25 * smallEigOmega nmax S δ φ c₁ c₂) ≤
        smallEigSeparation nmax S δ φ c₁ / (16 * nmax * smallEigCondition nmax S δ φ c₂) ∧
      smallEigAccuracy nmax S δ φ c₁ c₂ ≤ 0.8 * (2 * S) ∧
      0 < smallEigWeight nmax S δ φ c₂ ∧ smallEigWeight nmax S δ φ c₂ ≤ 1 ∧
      distSpecDegree (8 * smallEigCondition nmax S δ φ c₂) (smallEigWeight nmax S δ φ c₂) ≤
        2 ^ smallEigDegreeLog nmax S δ φ c₂ ∧
      8 * smallEigCondition nmax S δ φ c₂ ≤
        2 ^ smallEigDecoupleSteps nmax S δ φ c₂ * √(smallEigWeight nmax S δ φ c₂) := by
  sorry

/-- **The parameter words are positive** ([BanksGarzaVargasSrivastava2025, Theorem 1.1]): for
tail records with $b_1, b_2 > 0$, $n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and
$0 < \varphi \le 1$, the first eight words of `NLAlib.SmallEig.smallEigParams` (the scale, the
thresholds and the radii) are positive. Without it a headline under
$0 \le \boldsymbol{u} \le \boldsymbol{u}_0$ could be vacuous. -/
theorem smallEigParams_pos {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    ∀ i < 8, 0 < (smallEigParams nmax S δ φ c₁ c₂).getD i 0 := by
  sorry

/-- **The cap words are valid** for the cap `NLAlib.SmallEig.smallEigCap`: the words $8$ to $11$
of `NLAlib.SmallEig.smallEigParams` are the exact naturals $m = 2^q$, $q$, $t$, $m_2$, all at
most the cap, for any arguments. -/
theorem smallEigCaps_smallEigParams (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) :
    SmallEigCaps (smallEigCap nmax S δ φ c₁ c₂) (smallEigParams nmax S δ φ c₁ c₂) := by
  sorry

end NLAlib.SmallEig
