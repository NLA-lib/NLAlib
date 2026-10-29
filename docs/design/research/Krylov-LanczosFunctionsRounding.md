# Design note (research): finite-precision Lanczos quadrature and Lanczos-FA (Knizhnerman 1996 and Druskin–Knizhnerman 1991 type bounds)

2026-10-29. Branch `research/dk-bounds` (from `fix/main-checks` @ e88d2e3). **Status: RESEARCH,
all 16 statements proved** (2026-10-29, after the maintainer approved DK1–DK5 as recommended;
see §7) (maintainer: "next thing to do is the Druskin–Knizhnerman 1990s and
Knizhnerman 1996 type bounds"). Precedents: `docs/design/Krylov-LanczosRounding.md` (the
finite-precision chain this builds on), `docs/design/research/Krylov-CGRounding.md`. Decision
sheet: harness `state/decisions/DK-Bounds.json` (ids DK1–DK5 below). Skeleton:
`NLAlibScaffold/Krylov/FinitePrecision/LanczosFunctions.lean` (16 sorried statements, typechecks,
`check_rules` clean).

## Summary

Setting (all proved, `NLAlib/Krylov/FinitePrecision/`): a run `L : LanczosRun N k` with accuracy
$\varepsilon$ ($k\varepsilon \le 1/100$; from the program, $\varepsilon = \max(\varepsilon_{\rm mv},
\gamma_{N+4}) \approx N^{3/2}u$ dense) on symmetric $\mathbf H$ with spectrum in $[a, a']$ has a
symmetric backward model $\tilde{\mathbf H}$ of size $N(k+1)$ with
$$\|\tilde{\mathbf H} - \mathbf I_{k+1}\otimes\mathbf H\|_{\mathsf F} \le c := 2000k^4\varepsilon\|\mathbf H\|_2
\quad(\texttt{lanczosBackwardFactor}),$$
on which exact Lanczos from $\tilde{\mathbf v} = (\bar{\mathbf v}_1, \mathbf 0, \dots)$ computes
$\mathbf T_k$, $\beta_k$ and the orthonormal dilated basis $\hat{\mathbf V}_k$; the spectrum of
$\tilde{\mathbf H}$ and the Ritz values lie in $I_c = [a - c, a' + c]$; the spectral measures of
$(\mathbf H, \bar{\mathbf v}_1)$ and $(\tilde{\mathbf H}, \tilde{\mathbf v})$ are $W_1$-close
($\le c$, Kittaneh). Write $E_m(f; I) = $ `minimaxError f I m` (best uniform approximation by
polynomials of degree $\le m$).

**Headlines** (informal; Lean shapes in §3):

* **(K96-type) quadrature.** For $f$ $L$-Lipschitz on $I_c$,
  $$\bigl|\bar{\mathbf v}_1^{\mathsf T}f(\mathbf H)\bar{\mathbf v}_1 - (f(\mathbf T_k))_{00}\bigr|
  \le 2E_{2k-1}(f; I_c) + L\,c .$$
  Explicit rates: $L\bigl(\pi(a'-a+2c)/(2k+1) + c\bigr)$ (Jackson), $4M/(\rho^{2k-1}(\rho-1)) + Lc$
  (Bernstein ellipse). Bounded-$f$ form ($|f| \le M$ on $I_c$, no Lipschitz):
  $4E_{2k-1} + 11k^3(M + E_{2k-1})\,c/(a'-a+2c)$. Route: the backward model (§3.1); ~300 lines.
* **(DK91-type) Lanczos-FA with the computed basis.** For $f$ continuous on $I_c$, $|f| \le M$,
  $$\|f(\mathbf H)\mathbf v_1 - \mathbf V_kf(\mathbf T_k)\mathbf e_0\| \le (2+\sqrt k)\,E_{k-1}(f; I_c)
  + 16k^{9/2}\varepsilon\|\mathbf H\|_2\,\frac{M}{a'-a+2c} .$$
  Route: Druskin–Knizhnerman's Chebyshev-recurrence stability on the computed recurrence, with
  **our** containment supplying $\eta = c$ (§3.2); the backward model alone cannot give the
  computed-basis statement (§2.3). ~700 lines, new.
* **CG corollary** (research branch `research/cg-error-tracking`): the computed A-norm error is
  the Gauss quadrature error of the CG tridiagonal up to $200k^2\varepsilon\kappa\|\mathbf b\|^2/a$;
  the K96-type bound for $f = 1/x$ on the CG model turns this into an a priori rate (§4).
* Ritz-value consequences of DK91 (convergence of extreme Ritz values): not this round (§5, DK5).

Corrections to the brief's summaries: (i) DK91/MMS18 bound Lanczos-FA by $O(k)\cdot E_{k-1}$ on
the enlarged interval plus $\mathrm{poly}(k)\varepsilon\sup|f|$ (an $O(k)$ loss from the
non-orthogonal basis, not the exact-arithmetic constant 2); our quadrature route avoids this
loss but the FA route inherits it as $2 + \sqrt k$. (ii) K96's primary statement is on
*Chebyshev moments* ($\int T_n\,d\psi$ vs $\int T_n\,d\psi_k$ for $n \le 2k-1$, error
$\mathrm{poly}(k)\varepsilon$), proved through Paige's commutator identity, not through a
backward model; the "degree-$2k$ approximation on the enlarged interval" form is its corollary.
(iii) Neither paper uses Greenbaum's model; both use Paige's bounds (local errors, containment
(3.28) of [Paige1980]) and the Chebyshev recurrence.

---

## 1. Literature (what is actually proved)

Access: the originals [DK91] (*Zh. Vychisl. Mat. Mat. Fiz.* 31:7, 970–983; transl. *USSR
Comput. Math. Math. Phys.* 31:7, 20–30) and [Kni96] (36:11, 5–19; transl. 36:11, 1481–1492)
are on mathnet.ru behind a browser-session gate; **not read in the original**. Checked through:
Musco–Musco–Sidford (SODA 2018, arXiv 1708.07788, §§2, 6), Chen's thesis (*Lanczos-based
methods for matrix functions*, 2022, §8.2–8.6: "The result in this section first appeared in
[DK91, Section 4]; see also [MMS18, Lemma 10]"; "The results in this section are summarized
from [Kni96]"), Chen's handbook (arXiv 2410.11090, §4.3, §6.2, §7.2), Chen–Greenbaum–Musco–Musco
2022 (§5). Theorem numbers below are those of the secondary sources; the DK91/K96 numbering is
unknown.

### 1.1 Druskin–Knizhnerman 1991 (and DK 1989, 1995; DGK 1998)

* Model: Paige's local-error form $\mathbf A\mathbf Q_k = \mathbf Q_k\mathbf T_k +
  \beta_k\mathbf q_{k+1}\mathbf e_k^{\mathsf T} + \mathbf F_k$, $\|\mathbf F_k\| = O(\mathrm{poly}(k)
  \epsilon_{\rm mach}\|\mathbf A\|)$; MMS18 also note that DK "only address roundoff errors that
  arise during matrix vector multiplication with $\mathbf A$, assuming stability for other
  components" and "give an error bound which depends on a coarse upper bound for $\delta_k$".
* Core lemma (DK91 §4 = MMS18 Lemma 10 = thesis Thm 8.4): with $\mathbf A$, $\mathbf T_k$ scaled
  so both spectra lie in $[-1, 1]$ (the enlarged interval; Paige's (3.28) gives the Ritz
  containment with $\eta \ge 85n^{3/2}k^{5/2}\|\mathbf A\|\epsilon_{\rm mach}$ in MMS18),
  $$\|T_i(\mathbf A)\mathbf q_1 - \mathbf Q_kT_i(\mathbf T_k)\mathbf e_1\| \le 4i^2\|\mathbf F_k\|/
  (\lambda_{\max}-\lambda_{\min}+2\eta), \quad i < k,$$
  from the perturbed Chebyshev recurrence $\mathbf d_i = 2\mathbf A\mathbf d_{i-1} - \mathbf d_{i-2}
  + 2\mathbf F_k T_{i-1}(\mathbf T_k)\mathbf e_1$ (the $\beta_k$ term vanishes by the bandwidth of
  $\mathbf T_k$), solved with Chebyshev polynomials of the second kind, $\|U_m(\mathbf A)\| \le m+1$.
  **No orthogonality is used.**
* Consequence (MMS18 Lemma 9, Lemma 11, Theorem 1): for $p$ of degree $< k$ with $|p| \le C$ on
  the enlarged interval, Chebyshev coefficients $\le 2C$ give $\|\mathbf Qp(\mathbf T)\mathbf e_1
  - p(\mathbf A)\mathbf q_1\| \le 4Ck^3\|\mathbf F\|/\gamma$; then
  $$\|f(\mathbf A)\mathbf q_1 - \mathbf Qf(\mathbf T)\mathbf e_1\| \le (k+2)\delta_k +
  \epsilon_{\rm mach}\,92Ck^4n^{3/2}\|\mathbf A\|/\gamma,\qquad \gamma = \lambda_{\max}-\lambda_{\min}+2\eta,$$
  $\delta_k = E_{k-1}(f; [\lambda_{\min}-\eta, \lambda_{\max}+\eta])$, the $k+2$ from
  $\|\mathbf Q\| \le k$ (non-orthogonal columns) + 2. Theorem 1 adds the stable evaluation of
  $f(\mathbf T)\mathbf e_1$ (Gu–Eisenstat) and gives $(7k\delta_k + \epsilon C)\|\mathbf x\|$ with
  $B = \log(nk\|\mathbf A\|/(\epsilon\eta))$ bits. Handbook Thm 6.6 / Cor. 6.7 state the DK91
  content as $\|T_n(\mathbf A)\mathbf b - \mathbf Q_kT_n(\mathbf T_k)\mathbf e_1\| =
  O(\mathrm{poly}(k)\epsilon_{\rm mach})$ and $\|f(\mathbf A)\mathbf b - \mathbf Q_kf(\mathbf T_k)
  \mathbf e_1\| \le O(k)\min_{\deg p<k}\|f-p\|_{I} + O(\|f\|_I\mathrm{poly}(k)\epsilon_{\rm mach})$,
  $I = [-1-\eta_k, 1+\eta_k]$; Remark 6.8 stresses that the analysed output is
  $\|\mathbf b\|\mathbf Q_kf(\mathbf T_k)\mathbf e_1$, **not** $\mathbf Q_kf(\mathbf T_k)\mathbf Q_k^{\mathsf T}\mathbf b$
  (which need not converge).
* DK95 (NLAA 2:205–217): SLDM error vs. truncated Chebyshev series, superconvergence for the
  parabolic case, interior eigenvalue estimates independent of intermediate eigenvalues; the
  "computer arithmetic" part is the same Chebyshev-stability mechanism (abstract only checked).
  DGK98 (SISC 19:38–54): non-orthogonal Lanczos vectors remain usable for $\exp(t\mathbf A)\mathbf v$
  and linear systems; the thesis cites it for the error of $\exp(t\mathbf A)\mathbf v$ vs. the best
  approximation over $s \in [0,t]$ in a Krylov space of slightly lower dimension (abstract only).
* The eigenvalue part of DK91 ("estimates for the convergence of the computed eigenvalues, which
  explain the Lanczos phenomenon") follows from the function bounds by choosing test functions;
  the mechanism (and its difficulty: eigenvector weights) is discussed in §5.

### 1.2 Knizhnerman 1996

* Statement (thesis Thm 8.6, handbook Thm 4.4): with $\|\mathbf A\| = \|\mathbf b\| = 1$,
  $\epsilon_{\rm mach} = O(\mathrm{poly}(k)^{-1})$, for all $n \le 2k-1$,
  $$\Bigl|\int T_n\,d\psi_{\mathbf A,\mathbf b} - \int T_n\,d\psi_{\mathbf T_k,\mathbf e_1}\Bigr|
  \preceq k^2(\|\mathbf F\| + \|\mathbf H_{\rm Paige}\|) + \|\mathbf D - \mathbf I\|
  = O(\mathrm{poly}(k)\epsilon_{\rm mach}),$$
  where $\mathbf Q^{\mathsf T}\mathbf Q = \mathbf R + \mathbf R^{\mathsf T} + \mathbf D$ and Paige's
  commutator identity $\mathbf T\mathbf R = \mathbf R\mathbf T - \beta_{k-1}\mathbf Q^{\mathsf T}
  \mathbf q_k\mathbf e_{k-1}^{\mathsf T} + \mathbf H_{\rm Paige}$ [Paige1976, eq. 41]. Proof:
  $T_{2i} = 2T_i^2 - 1$, $T_{2i+1} = 2T_iT_{i+1} - x$; $\mathbf t_i^{\mathsf T}\mathbf t_j$ vs
  $\tilde{\mathbf t}_i^{\mathsf T}\tilde{\mathbf t}_j$ with the DK91 lemma for
  $\mathbf t_i - \mathbf Q\tilde{\mathbf t}_i$ and a second Chebyshev-recurrence lemma
  $\|\mathbf RT_i(\mathbf T)\mathbf e_0\| \le k^2\|\mathbf H_{\rm Paige}\|$ (thesis Lemma 8.5).
  The thesis proves $n \le 2k-2$ and notes K96 reaches $2k-1$ (Remark 8.7).
* Corollary (handbook Cor. 7.5): $|\mathbf b^{\mathsf T}f(\mathbf A)\mathbf b - \mathbf e_1^{\mathsf T}
  f(\mathbf T_k)\mathbf e_1| = O(k)\min_{\deg p<2k}\|f-p\|_I + O(\|f\|_I\mathrm{poly}(k)\epsilon_{\rm mach})$.
* The thesis (§8.5.1) derives from K96 a *simple backward-stability statement*: a signed measure
  $\hat\Psi = \Psi_{\mathbf A,\mathbf v} + \Xi$ with the first $2k$ Chebyshev moments of
  $\Psi_{\mathbf T,\mathbf e_0}$ and $d_W(\Psi, \hat\Psi) \le 4k\epsilon(k)$; it is not a positive
  measure and its support is all of $[-1,1]$. Our proved model (Greenbaum-type, positive,
  $W_1$-close, exact reproduction of $\mathbf T_k$) is strictly stronger here.

### 1.3 Later re-derivations

* MMS18 (as above): first end-to-end bit-complexity statement; lower bound (Theorem 3) showing
  Greenbaum's union-of-intervals bound for $1/x$ can be $\Omega(\kappa^{1/5})$ steps.
* Chen–Greenbaum–Musco–Musco 2022 §5: the Cauchy-integral bounds hold in finite precision with an
  additive term in $\mathbf F_k$ (a posteriori, computable), no a priori $\eta$.
* Chen (stability draft, formalised as `NLAlib/Krylov/FinitePrecision/`): Paige's identity and a
  Greenbaum-type backward model with explicit constants and $W_1$ remark; no function bounds
  (the design note lists "the quadrature reading … not in the paper" as not done).
* Chen–Trogdon 2024 (LAA 682): backward/forward stability for regular spectral distributions;
  the handbook says K96 is "more-or-less rederived" there (Lemma 3.7: $\|T_k\|_{[-1-\eta_k,1+\eta_k]}
  \le 2$ for $\eta_k = 1/(2k^2)$, the slack that replaces exact containment).
* Meurant–Strakoš 2006 (Acta Numerica) surveys Paige/Greenbaum; no function bounds beyond CG.

## 2. Routes

### 2.1 Backward-model route (ours) for the quadrature

$(f(\mathbf T_k))_{00} = \int f\,d\,\mathsf{lanczosQuadrature}(\tilde{\mathbf H}, \tilde{\mathbf v}, k)$
(`lanczosTridiagonal_backwardH_dilatedStart`, `Matrix.IsHermitian.integral_lanczosQuadrature_succ`,
$\|\tilde{\mathbf v}\| = 1$). The Gauss rule of $(\tilde{\mathbf H}, \tilde{\mathbf v})$ is exact to
degree $2k-1$ and its spectrum lies in $I_c$, so
$|\tilde{\mathbf v}^{\mathsf T}f(\tilde{\mathbf H})\tilde{\mathbf v} - (f(\mathbf T_k))_{00}| \le 2\delta$
for any $p$ of degree $< 2k$ within $\delta$ of $f$ on $I_c$
(`norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`,
`spectrum_backwardH_subset_Icc`). Transfer: $|\bar{\mathbf v}_1^{\mathsf T}f(\mathbf H)\bar{\mathbf v}_1
- \tilde{\mathbf v}^{\mathsf T}f(\tilde{\mathbf H})\tilde{\mathbf v}| \le Lc$ by
`abs_dotProduct_cfc_mulVec_sub_le_frobNorm` (Kittaneh) applied to the 1-Lipschitz extension of
$f/L$ from $I_c$ (`LipschitzOnWith.extend_real`; both spectra lie in $I_c$, so `cfc_congr`). Total
$2\delta + Lc$. Every ingredient is proved; the new work is bookkeeping (~300 lines incl. the
`LanczosRun` and end-to-end forms). The polynomial moments of $(\mathbf H, \bar{\mathbf v}_1)$ and
$(\tilde{\mathbf H}, \tilde{\mathbf v})$ are **not** equal (that is K96's theorem), so the transfer
must go through Lipschitz/Kittaneh, not exactness.

### 2.2 DK's route for the quadrature

Needs the DK91 Chebyshev lemma, Paige's commutator identity (we have `specNorm_gramCommutator_le`
and the normalised version, $40k^2\varepsilon\|\mathbf H\|$) and a second Chebyshev-recurrence
lemma on $\mathbf R$; gives $O(k)E_{2k-1} + \mathrm{poly}(k)\varepsilon\sup|f|$. Strictly more work
and a worse leading constant. **Rejected for the quadrature (DK1).**

### 2.3 Why the backward model does not give the computed-basis Lanczos-FA bound

The model's Lanczos basis is $\hat{\mathbf V}_{k+1} = $ `orthonormalDilation` of
$\bar{\mathbf V}_{k+1}$: block $r$ is $\bar{\mathbf V}\mathbf C\mathbf K^r$ with
$\mathbf C = (\mathbf I + \mathbf R)^{-1}$, $\mathbf R$ the strict upper part of the Gram matrix
(`OrthonormalDilation.lean`). So block 0 of $\hat{\mathbf V}_kf(\mathbf T_k)\mathbf e_0$ is
$\bar{\mathbf V}_k\mathbf C_kf(\mathbf T_k)\mathbf e_0$, not $\bar{\mathbf V}_kf(\mathbf T_k)\mathbf e_0$;
the model gives, cleanly,
$$\|f(\mathbf H)\bar{\mathbf v}_1 - \bar{\mathbf V}_k(\mathbf I+\mathbf R_k)^{-1}f(\mathbf T_k)\mathbf e_0\|
\le 2E_{k-1}(f; I_c) + Lc$$
(projection of the model's exact-arithmetic bound onto block 0, plus Kittaneh on
$\|f(\tilde{\mathbf H}) - f(\hat{\mathbf H})\|_{\mathsf F}$). The gap to the algorithm's output is
$\bar{\mathbf V}_k\mathbf K_kf(\mathbf T_k)\mathbf e_0$, $\mathbf K = \mathbf R\mathbf C$, i.e. a bound
on $\mathbf R_kp(\mathbf T_k)\mathbf e_0$ — exactly K96's Lemma (thesis 8.5), proved by the
Chebyshev recurrence. The loss of orthogonality $\mathbf R$ is not small (Paige), only its action
on $p(\mathbf T_k)\mathbf e_0$ is. Hence the computed-basis statement needs the Chebyshev
machinery in any case, and the direct DK/MMS argument on the computed recurrence
$\mathbf H\mathbf V_k = \mathbf V_{k+1}\underline{\mathbf T}_k + \mathbf F_k$ (`mul_basis`, no
normalisation, no orthogonality) is the shortest path. The model still contributes the
containment $\operatorname{spec}\mathbf T_k \subseteq I_c$ (the $\eta$) — which is otherwise
Paige's (3.28), not in the library. **Recommended (DK2a).** The corrected-output bound is a free
remark (DK2b), not an algorithm.

### 2.4 Comparison of $\eta$ and error terms

| | $\eta$ | leading term | rounding term |
|---|---|---|---|
| DK91 / MMS18 FA | $85n^{3/2}k^{5/2}\|\mathbf A\|\epsilon$ (Paige (3.28)) | $(k+2)\delta_k$ | $92Ck^4n^{3/2}\|\mathbf A\|\epsilon/\gamma$ |
| ours, FA | $c = 2000k^4\varepsilon\|\mathbf H\|_2$, $\varepsilon \approx N^{3/2}u$ | $(2+\sqrt k)E_{k-1}$ | $16Mk^{9/2}\varepsilon\|\mathbf H\|_2/\gamma$ |
| K96 / handbook Cor. 7.5 quadrature | Paige's | $O(k)E_{2k-1}$ | $O(\mathrm{poly}(k)\epsilon)\sup|f|$ |
| ours, quadrature | $c$ as above | $2E_{2k-1}$ | $Lc$ (Lipschitz) or $11k^3(M+E)c/\gamma$ |

Our $\eta$ is worse by $k^{3/2}$ (the $k^4$ of the backward model vs Paige's $k^{5/2}$); the
maintainer's rule "cleanest proof matters more than constants" applies. $\sqrt k$ instead of $k$
in the FA leading term because $\|\mathbf V_k\|_2 \le \|\mathbf V_k\|_{\mathsf F} \le (1+\varepsilon/2)\sqrt k$
(`frobNorm_basis_le`).

## 3. Statements (Lean shapes; all in the skeleton)

### 3.1 Quadrature (generic, `LanczosData`, hypotheses `hW` unit columns, `hβ`, `hβpos`, `hs`, `hc`)

```lean
theorem LanczosData.cfc_tridiagonal_firstIndex_eq_integral … (f) :
    cfc f D.tridiagonal D.firstIndex D.firstIndex =
      ∫ x, f x ∂lanczosQuadrature D.backwardH D.dilatedStart k
theorem LanczosData.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_isUniformApproxOn …
    (hs : spectrum ℝ D.H ⊆ Icc a a') (hc : frobNorm (D.backwardH - D.dilatedH) ≤ c)
    (hp : p.degree < 2 * k) (hδ : IsUniformApproxOn (eval p) f (Icc (a - c) (a' + c)) δ)
    (hf : LipschitzOnWith L f (Icc (a - c) (a' + c))) :
    |D.v 1 ⬝ᵥ (cfc f D.H *ᵥ D.v 1) - cfc f D.tridiagonal D.firstIndex D.firstIndex| ≤ 2 * δ + L * c
theorem …_of_isUniformApproxOn_of_abs_le … (hM : ∀ x ∈ Icc (a - c) (a' + c), |f x| ≤ M) :
    … ≤ 4 * δ + 11 * k ^ 3 * (M + δ) * c / (a' - a + 2 * c)
```

`LanczosRun` forms (`L.enlargement := lanczosBackwardFactor k * L.ε * specNorm L.H`):
`abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn` ($2\,$`minimaxError f I_c (2k-1)`
$+ L_f c$, for `normalizedV 1`), `…_of_lipschitzOnWith` (Jackson, $L(\pi(a'-a+2c)/(2k+1) + c)$),
`abs_dotProduct_cfc_mulVec_v_sub_cfc_tridiagonal_le_of_continuousOn` (computed unnormalised
$\mathbf v_1$, extra $\varepsilon M$). End to end: `HasLanczosQuadratureBound` and
`IsRelErrSem.exists_lanczosQuadratureBound_of_lanczosBasisDenseProg` (hypotheses of the dense
bridge plus $\operatorname{spec}\mathbf H \subseteq [a, a']$), with
`lanczosOutputTridiagonal α β k` the matrix assembled from the outputs.

### 3.2 Lanczos-FA (generic lemma on `LanczosData`, no finite-precision hypotheses)

```lean
noncomputable def chebyshevOn (α β : ℝ) (i : ℕ) : ℝ[X]   -- T_i scaled to [α, β]
theorem LanczosData.norm_aeval_chebyshevOn_mulVec_sub_basis_mulVec_le (hαβ : α < β)
    (hs : spectrum ℝ D.H ⊆ Icc α β) (hT : spectrum ℝ D.tridiagonal ⊆ Icc α β) (hi : i < k) :
    ‖T̂_i(H) v₁ - V_k T̂_i(T_k) e₀‖ ≤ 2 * i * (i + 1) / (β - α) * specNorm D.residual
theorem LanczosData.norm_aeval_mulVec_sub_basis_mulVec_le_of_degree_lt … (hp : p.degree < k)
    (hM : IsUniformApproxOn (eval p) 0 (Icc α β) M) :
    ‖p(H) v₁ - V_k p(T_k) e₀‖ ≤ 4 / 3 * k ^ 3 * M / (β - α) * specNorm D.residual
theorem LanczosRun.spectrum_tridiagonal_subset_Icc (hs) :
    spectrum ℝ L.tridiagonal ⊆ Icc (a - L.enlargement) (a' + L.enlargement)
theorem LanczosRun.norm_cfc_mulVec_sub_basis_mulVec_le_of_continuousOn (haa) (hs) (hf) (hM) :
    ‖f(H) v₁ - V_k f(T_k) e₀‖ ≤ (2 + √k) * minimaxError f I_c (k - 1)
      + 16 * k ^ 4 * √k * L.ε * specNorm L.H * M / (a' - a + 2 * L.enlargement)
```

Supporting polynomial facts (new, small): `degree_chebyshevOn_le`, `abs_eval_chebyshevOn_le_one`,
`lipschitzOnWith_eval_chebyshevOn` ($2i^2/(\beta-\alpha)$, from `T_derivative_eq_U` and
$|U_{i-1}| \le i$, currently private in `Polynomial/Chebyshev/EvenFilter.lean`),
`exists_eq_sum_smul_chebyshevOn_of_isUniformApproxOn` (Chebyshev expansion with
$|a_0| \le M$, $|a_i| \le 2M$: `chebyshevTrunc_eval` scaled plus the coefficient bound, of which
only the $k = 0$ case `norm_chebyshevCoeff_zero_le` exists),
`lipschitzOnWith_eval_of_degree_le_of_isUniformApproxOn` ($\frac43(m+1)^3M/(\beta-\alpha)$;
Markov's inequality would give $2m^2M/(\beta-\alpha)$ but is not in the library).

Constants: $\sum_{i<k}2M\cdot 2i(i+1)/(\beta-\alpha) = \frac43M(k-1)k(k+1)/(\beta-\alpha)$;
headline: $(1 + (1+\varepsilon/2)\sqrt k)E \le (2+\sqrt k)E$ and
$\frac43k^3(M+E)\cdot 6k\sqrt k\varepsilon\|\mathbf H\|/\gamma \le 16k^{9/2}\varepsilon\|\mathbf H\|M/\gamma$
using $E \le M$. All unoptimised; to be named per CONTRIBUTING §5.2 rule 2 when proved.

### 3.3 Proof sketch of the recurrence lemma (the only genuinely new argument)

$\mathbf d_i := \hat T_i(\mathbf H)\mathbf v_1 - \mathbf V_k\hat T_i(\mathbf T_k)\mathbf e_0$;
$\mathbf d_0 = \mathbf 0$ (`basis` column 0 is $\mathbf v_1$). With $\hat{\mathbf H} =
(2\mathbf H - (\alpha+\beta)\mathbf I)/(\beta-\alpha)$ and the same for $\mathbf T_k$,
$\hat T_{i+1} = 2x\hat T_i - \hat T_{i-1}$ (`Polynomial.Chebyshev.T_add_two` under `comp`), and
`mul_basis`: $\mathbf H\mathbf V_k = \mathbf V_k\mathbf T_k + \beta_k\mathbf v_{k+1}\mathbf e_{k-1}^{\mathsf T}
+ \mathbf F_k$. Since $\mathbf T_k$ is tridiagonal (`isTridiagonal_tridiagonal`),
$\mathbf e_{k-1}^{\mathsf T}q(\mathbf T_k)\mathbf e_0 = 0$ for $\deg q < k-1$ (new bandwidth lemma:
$(\mathbf T^j)_{i0} = 0$ for $i > j$, induction), so for $i \le k-2$
$$\mathbf d_{i+1} = 2\hat{\mathbf H}\mathbf d_i - \mathbf d_{i-1} + \tfrac{4}{\beta-\alpha}\mathbf F_k
\hat T_i(\mathbf T_k)\mathbf e_0 ,$$
whence $\mathbf d_i = \tfrac{4}{\beta-\alpha}\sum_{j<i}\hat U_{i-j-1}(\mathbf H)\mathbf F_k\hat T_j(\mathbf T_k)\mathbf e_0$
(Clenshaw; handbook Lemma 6.10). Bounds: $\|\hat U_m(\mathbf H)\|_2 \le m+1$ (spectrum in
$[\alpha,\beta]$, `specNorm_cfc_le`/`aeval`), $\|\hat T_j(\mathbf T_k)\mathbf e_0\| \le 1$
(Ritz values in $[\alpha,\beta]$), so $\|\mathbf d_i\| \le \tfrac{4}{\beta-\alpha}\|\mathbf F_k\|_2
\sum_{j<i}(i-j) = \tfrac{2i(i+1)}{\beta-\alpha}\|\mathbf F_k\|_2$. Difficulty: medium (the
recurrence bookkeeping); ~250 lines plus ~80 for the bandwidth lemma.

## 4. CG corollary

On `research/cg-error-tracking`, `CGRun.abs_quadForm_sub_x_succ_sub_sub_inv_cgTridiagonal_le`
gives $|E_{j+1}^2 - (\|\mathbf x_\star\|_{\mathbf A}^2 - \|\mathbf b\|^2(\mathbf T_{j+1}^{-1})_{00})|
\le 200k^2\varepsilon\kappa\|\mathbf b\|^2/a$ under (H) $k^3\varepsilon\kappa^2 \le 10^{-5}$, with
the CG backward model $\|\tilde{\mathbf H} - \mathbf I\otimes\mathbf A\|_{\mathsf F} \le c_{\rm CG}
= 4\cdot10^4k^3\varepsilon\kappa a' \le a/2$ (`CGBackward.frobNorm_backwardH_sub_dilatedH_le`,
a `NormalizedLanczosData`). The generic quadrature theorem (§3.1, on `LanczosData`) with
$f = 1/x$, $L = 1/(a - c_{\rm CG})^2 \le 4/a^2$, $I = [a - c_{\rm CG}, a' + c_{\rm CG}]$ gives
$$\|\mathbf x_\star\|_{\mathbf A}^2 - \|\mathbf b\|^2(\mathbf T_{j+1}^{-1})_{00} \le
\|\mathbf b\|^2\bigl(2E_{2j+1}(1/x; I) + 4c_{\rm CG}/a^2\bigr),$$
and `minimaxError_inv_le` (`Polynomial/Approximation/Inverse.lean`) supplies the Chebyshev rate
$E_{2j+1}(1/x; I) \lesssim \frac{(1+\sqrt{\kappa'})^2}{2a}\bigl(\frac{\sqrt{\kappa'}-1}{\sqrt{\kappa'}+1}\bigr)^{2j+2}$
with $\kappa' \le 2\kappa+1$. Combined: an a priori Chebyshev-rate bound for the **computed**
A-norm error, $E_{j+1}^2 \le \|\mathbf b\|^2(2E_{2j+1} + 4c_{\rm CG}/a^2) + 200k^2\varepsilon\kappa\|\mathbf b\|^2/a$,
the finite-precision form of [Greenbaum1989]'s "CG converges at least as fast as the Chebyshev
bound for $2\kappa+1$". Not in the skeleton (lives on another branch; one lemma once both merge).

## 5. Ritz-value consequences (DK91's "Lanczos phenomenon"): deferred (DK5)

Containment and Paige's stabilised Ritz values are proved (`BackwardSpectral.lean`). DK91's
convergence of extreme Ritz values at the Kaniel–Paige–Saad rate would, through the model, read:
Ritz values of $\mathbf T_k$ are exact Ritz values of $(\tilde{\mathbf H}, \tilde{\mathbf v})$, so
$\theta_{\max} \ge \lambda_{\max}(\tilde{\mathbf H}) - (\lambda_{\max}-\lambda_{\min})(\tilde{\mathbf H})
\tan^2\angle(\tilde{\mathbf v}, \tilde{\mathbf u}_{\max})/T_{k-1}(1+2\gamma)^2$ and
$|\lambda_{\max}(\tilde{\mathbf H}) - \lambda_{\max}(\mathbf H)| \le c$ (Weyl, proved). Two gaps:
(i) no Kaniel–Paige–Saad bound in the library (`Krylov/Eigenvalues/Ritz.lean` is exact Ritz
basics); (ii) the angle/weight of $\tilde{\mathbf v}$ on the top eigenvectors of $\tilde{\mathbf H}$
versus that of $\bar{\mathbf v}_1$ on those of $\mathbf H$ is Greenbaum's weight-clustering
statement, not implied by $W_1$-closeness alone (weights near a well-separated eigenvalue can be
recovered from $W_1$-closeness with a Lipschitz bump test function; the general case needs
separation). A clean sub-target for later: "if $\lambda_{\max}(\mathbf H)$ is separated by $g > 2c$
from the rest, the total $\tilde{\mathbf v}$-weight of $\tilde{\mathbf H}$'s eigenvalues within $c$
of it equals $(\bar{\mathbf v}_1^{\mathsf T}\mathbf u_{\max})^2$ up to $2c/g$" (bump of slope $1/(g-2c)$).

## 6. What exists vs new; order; size; risks

Exists (proved, `NLAlib/`): backward model and its spectral consequences; exactness and
uniform bounds of `lanczosFA`/`lanczosQuadrature`; `minimaxError`, Jackson, Bernstein, Chebyshev
truncation of polynomials; Kittaneh; `mul_basis`, residual bounds ($6k\sqrt k$), `frobNorm_basis_le`;
`IsTridiagonal`; Mathlib's `T_derivative_eq_U`, `LipschitzOnWith.extend_real`.

New, in dependency order:
1. Polynomial: `chebyshevOn` and its degree/bound/Lipschitz lemmas; Chebyshev coefficient bound
   $|a_i| \le 2M$ for $i \ge 1$ (generalising `norm_chebyshevCoeff_zero_le`) and the scaled
   expansion; `abs_eval_U_le` made public. ~250 lines, `NLAlib/Polynomial/Chebyshev/`.
2. Tridiagonal bandwidth lemma $(\mathbf T^j)_{i0} = 0$ for $i > j$. ~80 lines,
   `Matrix/Factorizations/Hessenberg.lean`.
3. Quadrature chain (§3.1): `LanczosData` theorem, `LanczosRun` forms, `spectrum_tridiagonal_subset_Icc`
   (from the two containment theorems), end-to-end. ~300 lines, `Krylov/FinitePrecision/`.
4. Recurrence lemma and polynomial form (§3.3). ~350 lines.
5. FA headline. ~100 lines.
Total ≈ 1.1–1.3k lines; batches 1–2 and 3 are independent, 4–5 depend on 1–2.

Risks: (a) `cfc` on `Matrix (Fin k) (Fin k) ℝ` vs `aeval` of the scaled polynomials (coercions
between `cfc (fun x => p.eval x)` and `aeval`; `cfc_eq_aeval_of_forall_eval_eq` exists);
(b) the Chebyshev expansion on $[\alpha,\beta]$ needs an affine pullback of `chebyshevTrunc_eval`
(the analytic file does this for functions, not polynomials; small); (c) `2 * k - 1` and `k - 1`
natural subtractions in `minimaxError` indices (fine since `k_pos`, but statements may be
restated with `q + 1`); (d) the end-to-end predicate quantifies over an index $i_0 = 0$ of
`Fin (lanczosSteps β q)` to avoid a proof term (T9); (e) constants unoptimised and all "other"
(CONTRIBUTING §5.2 rule 2): name them when proved. No `constants.toml` entries yet.

Open for the maintainer (DK1–DK5 on the decision sheet): routes (DK1, DK2), the generic level
(DK3), the hypothesis classes (DK4), and deferring the eigenvalue consequences (DK5). Also:
whether to try to obtain the DK91/K96 originals (mathnet full text requires a browser session)
to fix theorem numbers and constants before the docstrings cite them.

## 7. Proof record (2026-10-29)

All 16 skeleton statements are proved with their statements, hypotheses and constants unchanged
(no constant was weakened): quadrature $2E_{2k-1}(f; I_c) + Lc$ (bounded form
$4\delta + 11k^3(M+\delta)c/(a'-a+2c)$, Jackson form $L(\pi(a'-a+2c)/(2k+1) + c)$, unnormalised
$\mathbf v_1$ with $+\varepsilon M$), Chebyshev stability $2i(i+1)\|\mathbf F_k\|_2/(\beta-\alpha)$,
polynomial form $\frac43k^3M\|\mathbf F_k\|_2/(\beta-\alpha)$, Lanczos-FA
$(2+\sqrt k)E_{k-1}(f; I_c) + 16k^{9/2}\varepsilon\|\mathbf H\|_2M/(a'-a+2c)$, $\eta = c =
2000k^4\varepsilon\|\mathbf H\|_2$; end to end for the dense program. Axioms: the standard three.

Placement. The polynomial facts are sorry-free and general, so they moved to the library:
`NLAlib/Polynomial/Chebyshev/Interval.lean` (`chebyshevOn`, its degree, bound and Lipschitz
lemmas, the bounded Chebyshev expansion, the Lipschitz constant of a bounded polynomial, and
`abs_div_mul_sub_div_le_one`, the affine map onto $[-1, 1]$), `NLAlib.norm_chebyshevCoeff_le`
($\lvert a_k\rvert \le 2M$, in `Approximation/ChebyshevCoefficients.lean`), and
`NLAlib.abs_eval_U_le` ($\lvert U_n\rvert \le n + 1$ on $[-1, 1]$, made public in
`Chebyshev/EvenFilter.lean`). The rest stays in the scaffold file (the end-to-end statement
imports the scaffold `Krylov/Processes/LanczosRounding.lean`). New public helpers in the
scaffold: `LanczosData.isHermitian_tridiagonal`, `LanczosData.norm_toLp_dilatedStart`,
`LanczosData.spectrum_tridiagonal_subset_Icc` (Ritz containment for any datum with unit vectors,
via the compression $\hat{\mathbf V}_k^{\mathsf T}\tilde{\mathbf H}\hat{\mathbf V}_k = \mathbf T_k$),
`LanczosRun.enlargement_nonneg`.

Proof notes. (i) The Lipschitz constant of $\hat T_i$ uses Mathlib's
`abs_iterate_derivative_T_real_le` and `derivative_T_eval_one` ($\lvert T_i'\rvert \le i^2$).
(ii) The Clenshaw step is a pure algebraic identity: for any sequence with $\mathbf d_0 = 0$,
$\mathbf d_i = \sum_{j<i}U_{i-1-j}(\hat{\mathbf H})\mathbf f_j$ with $\mathbf f_0 = \mathbf d_1$,
$\mathbf f_{j+1} = \mathbf d_{j+2} - 2\hat{\mathbf H}\mathbf d_{j+1} + \mathbf d_j$ (integer-indexed
$U$, $U_{-1} = 0$); the recurrence facts only bound $\mathbf f_j$ ($\|\mathbf f_0\| \le \sigma
\|\mathbf F_k\|$, $\|\mathbf f_{j+1}\| \le 2\sigma\|\mathbf F_k\|$, $\sigma = 2/(\beta-\alpha)$, the
$\beta_k\mathbf v_{k+1}$ term killed by the bandwidth $(q(\mathbf T_k))_{k-1,0} = 0$ for
$\deg q < k-1$). (iii) The Kittaneh transfer for an $L$-Lipschitz function scales the
1-Lipschitz statement by $1/L$; $L = 0$ is the constant case.

