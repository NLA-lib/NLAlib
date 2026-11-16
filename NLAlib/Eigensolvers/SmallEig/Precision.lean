/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.Parameters

/-!
# The precision of the small-eigenvalue solver

The unit roundoff $\boldsymbol{u}_{\mathsf{SmallEig}}$ of [BanksGarzaVargasSrivastava2025,
Theorem 1.1], defined once as the minimum of named terms, one per block of the program: the
counts, the perturbation and the Hessenberg reduction, `RHess`, `DistSpec`, `Decouple` and the
backward error of the decoupler in the worklist. Each block's theorem takes its own term; the
headline takes the minimum. Its logarithm is $O(\log^2(n_{\max}\Sigma/(\delta\varphi)))$ for
fixed tail records (Theorem 1.1's $O(\log^2)$ bits). The forward form of Corollary 1.3 runs the
backward form at the accuracy $\delta_b = \Sigma(\beta/(4(2k_{\max} + 1)\Sigma))^{k_{\max}}$, which
the Ostrowski–Elsner matching turns into the forward error $\beta$.

## Main definitions

* `NLAlib.SmallEig.uSmallEig` and its terms.
* `NLAlib.SmallEig.forwardBackwardError`, `NLAlib.SmallEig.uSmallEigForward`,
  `NLAlib.SmallEig.smallEigForwardParams`, `NLAlib.SmallEig.smallEigForwardCap`: the forward form.

## Main results

* `NLAlib.SmallEig.uSmallEig_spec`: positivity and the terms.
* `NLAlib.SmallEig.logb_inv_uSmallEig_le`: the bits.
* `NLAlib.SmallEig.forwardBackwardError_spec`: the backward accuracy gives the forward one.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Real

/-- The precision term of the counts:
$\boldsymbol{u} \le 1/20$ and $10^5(n_{\max} + 1)^2\boldsymbol{u} \le 1$. -/
noncomputable def uSmallEigBasic (nmax : ℕ) : ℝ :=
  min (1 / 20) (1 / (100000 * ((nmax : ℝ) + 1) ^ 2))

/-- The precision term of the perturbation and the Hessenberg reduction: their rounding, at most
$1000(n_{\max} + 1)^2\boldsymbol{u}\cdot 2\Sigma$, is within $\delta/8$ and keeps the class of the
perturbation (condition $2/t_2$, separation $t_1$) up to one doubling. -/
noncomputable def uSmallEigReduce (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (δ / 8) (smallEigGap nmax S δ φ c₁ / (64 * ((nmax : ℝ) + 1) * (2 / smallEigCond nmax S δ φ c₂))) /
    (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S))

/-- The precision term of `RHess` on a block of the core (condition $2B_c$, separation $g_c/2$):
its backward error keeps the class up to one doubling and the weights up to the factor of
`NLAlib.exists_lastRowWeights_ge_of_norm_sub_le`. -/
noncomputable def uSmallEigRHess (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (smallEigSeparation nmax S δ φ c₁ / 2 /
      (64 * ((nmax : ℝ) + 1) * (2 * smallEigCondition nmax S δ φ c₂)))
    (√(smallEigWeight nmax S δ φ c₂) * (smallEigSeparation nmax S δ φ c₁ / 2) /
      (1024 * ((nmax : ℝ) + 1) * (2 * smallEigCondition nmax S δ φ c₂) ^ 2)) /
    (1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S))

/-- The precision term of `DistSpec` (`NLAlib.SmallEig.distSpec_accuracy`) at the condition
$8B_c$, the shift reach $10$, the norm $2\Sigma$ and the distance $\eta_1$. -/
noncomputable def uSmallEigDistSpec (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (1 / (30000 * ((2 : ℝ) ^ smallEigDegreeLog nmax S δ φ c₂ + 1)))
    ((8004 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ *
      (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^ (2 ^ smallEigDegreeLog nmax S δ φ c₂)
      / (300 * ((nmax : ℝ) + 1) ^ 2))

/-- The precision term of `Decouple` (`NLAlib.SmallEig.decoupleLast_spec`): the forward error of
$m_2$ rounded steps at the distance $\eta_1$ within $\omega/2$. -/
noncomputable def uSmallEigDecouple (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min ((16 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ *
      (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^ smallEigDecoupleSteps nmax S δ φ c₂)
    (smallEigOmega nmax S δ φ c₁ c₂ / 2 / (86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) *
      (22 * (2 * S) / smallEigInnerRadius nmax S δ φ c₁ c₂) ^ smallEigDecoupleSteps nmax S δ φ c₂ *
        √((nmax : ℝ) + 1))) / (300 * ((nmax : ℝ) + 1) ^ 2)

/-- The precision term of the core: the backward error of $2(n_{\max} + 1)$ decoupler calls is
within $\delta/8$. -/
noncomputable def uSmallEigCore (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) : ℝ :=
  δ / 8 / (2 * ((nmax : ℝ) + 1) * (1000 * ((nmax : ℝ) + 1) ^ 2 +
    1050 * smallEigDecoupleSteps nmax S δ φ c₂ * ((nmax : ℝ) + 1) ^ 2) * (2 * S))

/-- **The precision threshold of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], recomputed for the corrected constants of the blocks): the minimum of the terms
`NLAlib.SmallEig.uSmallEigBasic`, `NLAlib.SmallEig.uSmallEigReduce`,
`NLAlib.SmallEig.uSmallEigRHess`, `NLAlib.SmallEig.uSmallEigDistSpec`,
`NLAlib.SmallEig.uSmallEigDecouple` and `NLAlib.SmallEig.uSmallEigCore`, at the outer order bound
$n_{\max}$. -/
noncomputable def uSmallEig (nmax : ℕ) (S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (uSmallEigBasic nmax) <| min (uSmallEigReduce nmax S δ φ c₁ c₂) <|
    min (uSmallEigRHess nmax S δ φ c₁ c₂) <| min (uSmallEigDistSpec nmax S δ φ c₁ c₂) <|
      min (uSmallEigDecouple nmax S δ φ c₁ c₂) (uSmallEigCore nmax S δ φ c₂)

/-- **The precision threshold is positive and below every term**: for tail records with
$b_1, b_2 > 0$, $n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
$0 < \boldsymbol{u}_{\mathsf{SmallEig}}$ and $\boldsymbol{u}_{\mathsf{SmallEig}}$ is at most each of
its six terms. Without positivity the headline would be vacuous through
$0 \le \boldsymbol{u} \le \boldsymbol{u}_{\mathsf{SmallEig}}$. -/
theorem uSmallEig_spec {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ}
    (hn : 1 ≤ nmax) {S δ φ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < uSmallEig nmax S δ φ c₁ c₂ ∧ uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigBasic nmax ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigReduce nmax S δ φ c₁ c₂ ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigRHess nmax S δ φ c₁ c₂ ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigDistSpec nmax S δ φ c₁ c₂ ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigDecouple nmax S δ φ c₁ c₂ ∧
      uSmallEig nmax S δ φ c₁ c₂ ≤ uSmallEigCore nmax S δ φ c₂ := by
  sorry

/-- **The bits of precision of the small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], $O(\log^2)$ bits): for tail records with $b_1, b_2 > 0$ there are constants
$e_1, e_2$ (depending on the records) such that for every $n_{\max} \ge 1$,
$0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
$$\log_2\frac{1}{\boldsymbol{u}_{\mathsf{SmallEig}}} \le e_1\log_2^2 Y + e_2, \qquad
  Y = \frac{4n_{\max}\Sigma}{\delta\varphi}\,.$$ -/
theorem logb_inv_uSmallEig_le (c₁ c₂ : PolyLogTail) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    ∃ e₁ e₂ : ℝ, ∀ {nmax : ℕ} {S δ φ : ℝ}, 1 ≤ nmax → 0 < δ → δ ≤ S → 0 < φ → φ ≤ 1 →
      logb 2 (uSmallEig nmax S δ φ c₁ c₂)⁻¹ ≤
        e₁ * logb 2 (4 * nmax * S / (δ * φ)) ^ 2 + e₂ := by
  sorry

/-! ### The forward form -/

/-- The backward accuracy $\delta_b = \Sigma(\beta/(4(2k_{\max} + 1)\Sigma))^{k_{\max}}$ that gives
the forward error $\beta$ on orders at most $k_{\max}$ and norms at most $\Sigma$. -/
noncomputable def forwardBackwardError (kmax : ℕ) (S β : ℝ) : ℝ :=
  S * (β / (4 * (2 * kmax + 1) * S)) ^ kmax

/-- **The backward accuracy gives the forward error** ([BanksGarzaVargasSrivastava2025,
Corollary 1.3], the arithmetic): for $0 < \beta \le \Sigma$ and
$\delta_b$ = `NLAlib.SmallEig.forwardBackwardError` $k_{\max}$ $\Sigma$ $\beta$:
$0 < \delta_b \le \Sigma$ and, for every order $d + 1 \le k_{\max}$,
$(2d + 1)(3\Sigma)^{1 - 1/(d + 1)}\delta_b^{1/(d + 1)} \le \beta$, the Ostrowski–Elsner bound of a
perturbation of norm $\delta_b$ of a matrix of norm at most $\Sigma$ and order $d + 1$. -/
theorem forwardBackwardError_spec {kmax : ℕ} {S β : ℝ} (hβ : 0 < β) (hβS : β ≤ S) :
    0 < forwardBackwardError kmax S β ∧ forwardBackwardError kmax S β ≤ S ∧
      ∀ d : ℕ, d + 1 ≤ kmax → (2 * d + 1) * (3 * S) ^ (1 - 1 / ((d : ℝ) + 1)) *
        forwardBackwardError kmax S β ^ (1 / ((d : ℝ) + 1)) ≤ β := by
  sorry

/-- The precision threshold of the forward form: `NLAlib.SmallEig.uSmallEig` at the backward
accuracy `NLAlib.SmallEig.forwardBackwardError` and $n_{\max} = k_{\max}$. -/
noncomputable def uSmallEigForward (kmax : ℕ) (S β φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  uSmallEig kmax S (forwardBackwardError kmax S β) φ c₁ c₂

/-- The parameter words of the forward form: `NLAlib.SmallEig.smallEigParams` at the backward
accuracy `NLAlib.SmallEig.forwardBackwardError` and $n_{\max} = k_{\max}$. -/
noncomputable def smallEigForwardParams (kmax : ℕ) (S β φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℝ :=
  smallEigParams kmax S (forwardBackwardError kmax S β) φ c₁ c₂

/-- The cap of the forward form: `NLAlib.SmallEig.smallEigCap` at the backward accuracy
`NLAlib.SmallEig.forwardBackwardError` and $n_{\max} = k_{\max}$. -/
noncomputable def smallEigForwardCap (kmax : ℕ) (S β φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  smallEigCap kmax S (forwardBackwardError kmax S β) φ c₁ c₂

end NLAlib.SmallEig
