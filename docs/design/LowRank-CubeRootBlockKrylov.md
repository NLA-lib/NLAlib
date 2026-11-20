# Low-rank approximation with $\varepsilon^{-1/3}$ products: two block Krylov spaces

2026-11-20. Design note; **status: design only, awaiting the maintainer's decisions (§9).
Nothing is proved and there is no skeleton.** Branch `design/lra-cube-root` from `origin/main` @
`edb7e0ee`. Stage LRA-CUBE-ROOT, board card T150. Targets: harness
`pilot/lra-cube-root-targets.json`. Decision sheet: harness `state/decisions/LRA-CUBE-ROOT.json`
(ids below). Every Lean statement in Appendix A elaborated, with `sorry` proofs, against the
library at `edb7e0ee` (scratch file outside `NLAlib/`, not committed; §A.0).

The maintainer asked: "I want to work on formalizing the eps^{1/3} LRA results. as with RBKI, we
can begin with the mathematical theorems for mathematical objects first, and then put it in to
the routines later."

**Reading of the request.** The source is Bakshi, Clarkson and Woodruff, "Low-Rank Approximation
with $1/\epsilon^{1/3}$ Matrix-Vector Products" (STOC 2022, arXiv 2202.05120; "BCW"): a
$(1+\varepsilon)$ rank-$k$ approximation in every Schatten $p$-norm from
$\tilde O(kp^{1/6}\varepsilon^{-1/3})$ products, by combining block Krylov runs of two different
block sizes and depths. This stage is mathematics only: matrices, projectors, Krylov spaces,
Gaussian start blocks. One correction to the brief: board card T047's "$k\varepsilon^{-1/3}$
Frob" is the adaptive *lower* bound of Zhang et al. 2026 (report `MatvecLowerBounds.md` §1), not
an upper bound; it does not settle the scope of norms here, which is decision SCOPE-NORMS.

Label convention as in `LowRank-BlockLanczos.md`: **known** is a published result; **planned** is
a statement this note proposes to prove, with a proof outline; **checked** means the derivation
was done by hand for this note and spot-checked numerically (a sanity check, never evidence for a
rate), but is not formalized. Singular values are indexed from $0$:
$\sigma_0\ge\sigma_1\ge\cdots$; a rank-$k$ problem has head $i<k$ and
$\mathrm{OPT}_p=\|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{S_p}=(\sum_{i\ge k}\sigma_i^p)^{1/p}$.
$\mathbf H=\mathbf A^{\mathsf H}\mathbf A$. The paper indexes from $1$, so its $\sigma_{k+1}$ is
$\sigma_k$ here.

## Summary

* **What the paper proves** (§1). Theorem 3.1: with probability $9/10$, a $(1+\varepsilon)$
  rank-$k$ Schatten-$p$ approximation from
  $O(kp^{1/6}\log(d/\varepsilon)\varepsilon^{-1/3}+k\sqrt p\log(d/\varepsilon))$ products,
  $1\le p\le O(\log d/\varepsilon)$. The title drops a $\log(d/\varepsilon)$ and the $p^{1/6}$.
  The proof is a case analysis on the spectrum: a deep run with block $k$ gives every top
  singular value to additive accuracy $\gamma_1\sigma_k^2$, $\gamma_1=\varepsilon^{2/3}p^{-1/3}$,
  which is enough when the tail is heavy; when it is light a block of
  $\Theta(k(\varepsilon p)^{-1/3})$ columns sees a gap and a shallow run gives accuracy
  $\mathrm{poly}(\varepsilon/d)$. Musco and Musco's per-vector guarantees are used as a black
  box; Schatten norms enter through a pinching inequality for a pair of projectors. The
  algorithm picks one of the two runs from estimated singular values.
* **The paper's argument does not formalize as written** (§1.3, 16 items). Two matter: the
  algorithm's step 4 refers to an undefined output, and the head index $\ell$ in the case
  $p>2$ "is guaranteed to exist" only under an unstated condition of the kind
  $kp\varepsilon\lesssim d$. Both are repaired here (§2.4, §2.5); the repairs are **checked**,
  not published.
* **The design does not select between two runs.** Singular values of a compression
  $\mathbf P_{\mathcal K}\mathbf A$ are monotone in the subspace $\mathcal K$. So Rayleigh–Ritz
  on the *sum* of the two block Krylov spaces has both accuracy guarantees at once, and the
  case analysis becomes a statement about one projector. The object is
  $\mathsf{rbkiSum}(\mathbf A,\mathbf\Omega_1,\mathbf\Omega_2,q_1,q_2)$, the projection of
  $\mathbf A$ onto $\mathcal K_{q_1}(\mathbf A\mathbf A^{\mathsf H},\mathbf A\mathbf\Omega_1)+
  \mathcal K_{q_2}(\mathbf A\mathbf A^{\mathsf H},\mathbf A\mathbf\Omega_2)$ (§2.6). The
  paper's choose-one form is kept as a corollary with `min` (decision SELECT).
* **Layering, as for RBKI** (§2). (1) Matrix analysis for a pair of projectors
  $\mathbf P,\mathbf Q$ with $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$: error of
  $\mathbf A\mathbf Q$ from the *singular value deficits*
  $\sigma_i(\mathbf A)^2-\sigma_i(\mathbf P\mathbf A)^2$, $i<k$, and a count of tail singular
  values. No Krylov space, no randomness; any sketch can plug in. (2) Deterministic bounds for
  the deficits of a filtered sketch and of `rbki`, in terms of the library's sketch residual
  $(\mathbf A-\llbracket\mathbf A\rrbracket_t)\mathbf\Omega(\mathbf Z^{\mathsf H}\mathbf\Omega)^+$.
  (3) Gaussian start blocks.
* **The needed black box is not in the library.** The library has no bound on individual
  singular values of `rbki` (Musco–Musco's per-vector guarantee) and no gapless Frobenius bound
  for truncated RBKI. §2.3 plans the deficit bound directly (targets RZ1–RZ4); it is a
  one-page argument on a Rayleigh quotient and reuses the existing head capture and Chebyshev
  filter. A by-product is a gapless Frobenius bound for one RBKI run (GA0).
* **Headline (planned, Frobenius), constants explicit, no dependence on the dimensions.** For
  Gaussian $\mathbf X_1$ with $2k+1$ columns and $\mathbf X_2$ with $2(k+j)+1$ columns (any
  joint law), $0<\varepsilon\le1$, $j+1\ge 6k\varepsilon^{-1/3}$,
  $q_1\ge1+\log(12k/\varepsilon)/(2\sqrt2\,\varepsilon^{1/3})$ and
  $q_2\ge1+\log(12k/\varepsilon)/3$,
  $$\mathbb E\,\|\mathbf A-\llbracket\mathsf{rbkiSum}(\mathbf A,\mathbf X_1,\mathbf X_2,q_1,q_2)
  \rrbracket_k\|_{\mathsf F}^2\le(1+\varepsilon)\,
  \|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2 .$$
  That is $O(k\varepsilon^{-1/3}\log(k/\varepsilon))$ products: the logarithm is of
  $k/\varepsilon$, not of the dimension (BCW have $\log(d/\varepsilon)$; Bakshi–Narayanan
  2023 remove $\log d$ for $k=1$ by a different route). The same statement with the same
  constants holds for $\|\cdot\|_{S_p}^p$, $1\le p\le2$, for the two-sided output
  $\mathbf A\mathbf Q$ (GA2p). For $2<p<\infty$ the planned form is a tail bound with
  $\log(nkp/(\varepsilon\delta))$ and BCW's $p^{1/6}$ (GA3).
* **Size.** 43 targets: S 19, M 19, L 5, in waves 0–5 (§6). Waves 0–3 are deterministic.
  The Frobenius headline needs 16 of them (no pinching, no Schatten norm).
* **Not in this stage** (recommendations, §9): the lower bound $\Omega(\varepsilon^{-1/3})$
  (needs the hidden-Wishart hardness of Braverman et al., which the library does not have);
  programs; block size below $k+2$; $p=\infty$ (already in the library).

## 0. What main already has (reused, not re-derived)

| Need | In the library |
|---|---|
| RBKI as a projection | `rbki A Ω q = rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q)`, `rbki_eq_rangeProjector`, `rsvd A Y = rangeProjector (A * Y) * A` |
| RBKI contains every filtered sketch | `range_mul_aeval_mul_le_range_mul_blockKrylovMatrix`, `singularValues_sub_rbki_le_of_degree_lt` |
| Head capture by a filtered sketch | `HasOrthonormalCols.singularValues_one_sub_rangeProjector_mul_mul_le` (TW Lemma 9.5, MM Lemma 9 property 1) |
| Chebyshev filter with $(a/c)^2\le4e^{-8d\sqrt\gamma}$ | `exists_degree_lt_div_sq_le_exp_singularGapRatio` (indexed by singular values of a real matrix), `Polynomial.Chebyshev.abs_eval_T_comp_C_mul_X_sub_one_le` |
| Gapped RBKI, Gaussian block $\ell\ge t+2$, expectation, spectral/Frobenius/quadratic gauges, truncated outputs | `LowRank/Gaussian/BlockKrylov.lean` |
| Gapless RBKI, spectral norm only | `LowRank/Gaussian/BlockKrylovGapless.lean` ((1+ε) form and TW form) |
| Small blocks | `LowRank/Structural/SmallBlock.lean`, `LowRank/Gaussian/SmallBlock.lean` (one vector, gap hypothesis on the head) |
| Sketch residual moments | `integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix`: $\mathbb E\|\mathbf S\mathbf G_2\mathbf G_1^+\|_{\mathsf F}^2=\|\mathbf S\|_{\mathsf F}^2\,r/(\ell-r-1)$; tail `measureReal_frobNorm_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix` |
| Schatten norms | `schattenNorm (q : ℝ≥0∞)`, `schattenNorm_rpow`, triangle inequality, Hölder, monotonicity in $q$, `schattenNorm_le_rank_rpow_mul_schattenNorm`, unitary invariance; `SymmetricGauge.matrixNorm`, `lpGauge` |
| Eckart–Young in every unitarily invariant norm | `SymmetricGauge.matrixNorm_sub_truncatedSVD_le_of_rank_le`, `isLeast_matrixNorm_sub_of_rank_le`, `singularValues_sub_truncatedSVD` |
| Weyl for singular values, low-rank perturbation | `singularValues_add_le`, `singularValues_add_le_of_rank_le`, `singularValues_le_singularValues_add_of_rank_le` |
| Orthogonal projectors | `IsStarProjection` API (`Matrix/Norms/Projector.lean`), `IsStarProjection.singularValues_mul_le`, `IsStarProjection.frobNorm_sq_eq_add` |
| Measurability | `measurable_truncatedSVD`, `measurable_rangeProjector`, `measurable_rsvd`, `measurable_blockKrylovMatrix`, `measurable_singularValues`; `integrable_frobNorm_sub_truncatedSVD_rbki_sq` |
| Program transfer | `BlockKrylov.measureReal_not_accepts_le`, `BlockKrylov.storedOutput_eq_rbki` (`LowRank/BlockKrylov/Probability.lean`) |

**Missing** (each is a target): any Schatten-norm inequality for compressions (pinching,
orthogonal sums); lower bounds on individual singular values of `rsvd`/`rbki`; monotonicity of
$\sigma_i(\mathbf P_{\mathbf Y}\mathbf A)$ in the range of $\mathbf Y$ (the library has it only for
$\mathbf A-\mathbf P_{\mathbf Y}\mathbf A$); a Chebyshev filter lemma not tied to two singular
value indices; the exact Frobenius identity for a compression.

Mathlib (searched at the pinned revision): no Schatten norm, no pinching inequality, no
Courant–Fischer; `one_add_mul_self_le_rpow_one_add` and `rpow_one_add_le_one_add_mul_self`
(Bernoulli, both directions) found and used for SC1; `Polynomial.Chebyshev.one_le_eval_T_real`
and `abs_eval_T_real_le_one` found (the library's growth bound is in
`ForMathlib/.../Chebyshev/Growth.lean`).

## 1. The source

Read: BCW arXiv 2202.05120 (LaTeX source, all of `algorithms.tex`, `prelims.tex`, `intro.tex`,
the statements of `lower_bounds.tex`); Musco–Musco arXiv 1504.05477 (Lemma 9 "Main
Approximation Lemma", Theorems 10–13); Bakshi–Narayanan arXiv 2304.03191 (abstract and §
"Upper bounds for Schatten-$p$ LRA"). Sources are in the harness, `research/lra-cube-root/`.

### 1.1 Statements (known)

* **BCW Theorem 3.1** (`thm:optimal_schatten_p_lra`). $\mathbf A\in\mathbb R^{n\times d}$,
  $k\in[d]$, $\varepsilon\in(0,1)$, $p\in[1,O(\log d/\varepsilon)]$. Algorithm 3.2 performs
  $O(kp^{1/6}\log(d/\varepsilon)\varepsilon^{-1/3}+\log(d/\varepsilon)k\sqrt p)$ products and
  outputs $\mathbf Z$ with $k$ orthonormal columns such that with probability at least $9/10$,
  $\|\mathbf A(\mathbf I-\mathbf Z\mathbf Z^{\mathsf T})\|_{S_p}\le(1+\varepsilon)\mathrm{OPT}_p$.
* **Lemma 3.1 / 3.2** (from Musco–Musco Theorems 1 and 13, black boxes). Block Krylov with block
  $k$ and $q=\Omega(\log(d/\gamma)/\sqrt\gamma)$ iterations gives, with probability $99/100$,
  $\|\mathbf A\mathbf z_i\|^2=\sigma_i^2\pm\gamma\sigma_{k+1}^2$ for all $i\le k$; with block
  $b\ge k$ and $q=\Omega(\log(n/\gamma)\sqrt{\sigma_k}/\sqrt{\sigma_k-\sigma_b})$ the same.
* **Lemma 3.3** (Schatten-$p$ norms for orthogonal projections). For orthogonal projectors
  $\mathbf P,\mathbf Q$ of rank $k$ and $p\ge1$:
  $\|\mathbf A\|_{S_p}^p\ge\|\mathbf P\mathbf A\mathbf Q\|_{S_p}^p+
  \|(\mathbf I-\mathbf P)\mathbf A(\mathbf I-\mathbf Q)\|_{S_p}^p$, from the pinching
  inequality.
* **Lemma 3.4** (per-vector guarantees to Schatten norms):
  $\|\mathbf A\mathbf Z\mathbf Z^{\mathsf T}\|_{S_p}^p\ge\|\mathbf A_k\|_{S_p}^p-
  \sum_{i\le k}O(\gamma_ip)\sigma_{k+1}^2\sigma_i^{p-2}$.
* **Lemma 3.5, 3.6, Corollary 3.7** (high-accuracy vectors capture the head): if
  $\|\mathbf A^{\mathsf T}\mathbf w_i\|^2\ge\sigma_i^2-\mathrm{poly}(\varepsilon/d)\sigma_{k+1}^2$
  for $i\le\ell$ and $(\sigma_\ell-\sigma_{\ell+1})/\sigma_\ell\ge\varepsilon/d$, then
  $\|\mathbf A_\ell(\mathbf I-\mathbf Z\mathbf Z^{\mathsf T})\|_{\mathsf F}^2\le
  \mathrm{poly}(\varepsilon/d)\sigma_{k+1}^2$ for $\mathbf Z$ a basis of the range of
  $\mathbf A^{\mathsf T}\mathbf W$.
* **BCW Theorems 5.1, 5.4** (lower bound): $\Omega(\varepsilon^{-1/3})$ adaptive products for
  rank $1$ and fixed $p$, by reduction to the smallest eigenvalue of a Wishart matrix
  (Braverman, Hazan, Simchowitz, Woodworth 2020, Theorem 3.1), with Araki–Lieb–Thirring for
  $p\le2$ and an aligned norm-compression inequality for $p>2$.
* **Bakshi–Narayanan 2023**: $\Omega(\log n/\sqrt\varepsilon)$ for spectral rank-$1$;
  Theorem 1.5: $O(\log(1/\varepsilon)\varepsilon^{-1/3})$ products for rank $1$ and $p=O(1)$
  from a *single* Krylov run with one start vector, analysed through BCW's Lemma 3.3 at
  $\mathbf P=\mathbf w\mathbf w^{\mathsf T}$, $\mathbf Q=\mathbf v\mathbf v^{\mathsf T}$,
  $\mathbf v\propto\mathbf A^{\mathsf T}\mathbf w$.

### 1.2 Proof structure of Theorem 3.1

Algorithm 3.2 runs block Krylov on $\mathbf A^{\mathsf T}$ twice: $\mathbf W_1$ (block $k$,
$q=O(\log(d/\gamma_1)/\sqrt{\gamma_1}+\log(d/\varepsilon)\sqrt p)$,
$\gamma_1=\varepsilon^{2/3}p^{-1/3}$) and $\mathbf W_2$ (block $s=O(k(\varepsilon p)^{-1/3})$,
$q=O(\log(d/\varepsilon)\sqrt p)$). Two further runs estimate $\sigma_1,\sigma_{k+1},\sigma_s$ to
relative accuracy $0.1/p$. It outputs a basis $\mathbf Z$ of the range of
$\mathbf A^{\mathsf T}\mathbf W_j$, with $j=2$ if $\hat\sigma_s^2\le\hat\sigma_{k+1}^2/(1+0.5/p)$.

1. With $\mathbf P=\mathbf W\mathbf W^{\mathsf T}$, $\mathbf Q=\mathbf Z\mathbf Z^{\mathsf T}$:
   $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$ and
   $(\mathbf I-\mathbf P)\mathbf A(\mathbf I-\mathbf Q)=\mathbf A(\mathbf I-\mathbf Q)$, so
   Lemma 3.3 gives $\|\mathbf A(\mathbf I-\mathbf Q)\|_p^p\le\|\mathbf A\|_p^p-
   \|\mathbf W^{\mathsf T}\mathbf A\|_p^p$.
2. Case "no large singular values" ($\sigma_1<(1+1/p)\sigma_{k+1}$): Lemma 3.4 turns accuracy
   $\gamma$ into $\|\mathbf A(\mathbf I-\mathbf Q)\|_p^p\le\mathrm{OPT}^p+O(k\gamma p)\sigma_{k+1}^p$.
   If the tail is light, $\mathrm{OPT}^p\le k(\varepsilon p)^{-1/3}\sigma_{k+1}^p$, then
   $\sigma_{k+1+t}\le\sigma_{k+1}/(1+1/p)$ for $t=\Theta(k(\varepsilon p)^{-1/3})$, the wide run
   sees a relative gap $1/p$ and has $\gamma=\mathrm{poly}(\varepsilon/d)$. Otherwise
   $\mathrm{OPT}^p=\Omega(k(\varepsilon p)^{-1/3})\sigma_{k+1}^p$ and
   $O(k\gamma_1p)\sigma_{k+1}^p=O(p\varepsilon)\mathrm{OPT}^p$.
3. Case "large singular values": $\sigma_i^{p-2}$ in Lemma 3.4 is not comparable to
   $\sigma_{k+1}^{p-2}$ for $p>2$. Split at an index $\ell$ with
   $\sigma_\ell>(1+0.5/p)\sigma_{k+1}$ and a relative gap $\varepsilon/d$ after it: the head
   $\mathbf A_\ell$ is captured to $\mathrm{poly}(\varepsilon/d)$ in Frobenius norm (Corollary
   3.7), and Lemma 3.3 is applied to $\mathbf A-\mathbf A_\ell$, with Weyl's inequality
   $\sigma_j(\mathbf W^{\mathsf T}(\mathbf A-\mathbf A_\ell)\mathbf Z)\ge
   \sigma_{j+\ell}(\mathbf W^{\mathsf T}\mathbf A)$.

### 1.3 Errata and ambiguities

Numbering E1–E16 is used in the targets. "Fixed by" names the planned statement.

| # | Where | Issue | Fixed by |
|---|---|---|---|
| E1 | title, abstract, Thm 1.1 | "$1/\epsilon^{1/3}$" is $kp^{1/6}\log(d/\varepsilon)\varepsilon^{-1/3}+k\sqrt p\log(d/\varepsilon)$; $\tilde O$ hides $\mathrm{polylog}(dk/\varepsilon)$; success $99/100$ in the introduction, $9/10$ in Theorem 3.1; no constant is given anywhere | explicit constants (GA1–GA3) |
| E2 | Algorithm 3.2 step 4 | "set $\mathbf Z=\mathbf Z_1$" when $\hat\sigma_1^2\ge(1+0.5/p)\hat\sigma_{k+1}^2$: $\mathbf Z_1$ is never defined ($\hat{\mathbf Z}_1$ has $k+1$ columns), and the proof's case "large singular values" does not use this branch; there the text says the output is $\mathbf W_2$ in both sub-cases | no selection (§2.6) |
| E3 | Algorithm 3.2, proof end | output box states the bound for $\|\cdot\|_p^p$, the theorem for $\|\cdot\|_p$; the proof reaches $(1+O(p\varepsilon))$ in $p$-th powers, constant unspecified, and uses $\varepsilon<1/2$ | CB3, GA3 |
| E4 | Lemma 3.2 | "$p,k\in\mathcal N$ such that $b\ge k$", "$O(pq)$ products" ($p$ should be $b$); the gap is written $\sigma_k-\sigma_b$, MM Theorem 13 has $\min\{1,\sigma_k/\sigma_{b+1}-1\}$ | RZ4 (`singularGapRatio A h t`) |
| E5 | Lemma 3.3 | stated for $\mathbf P,\mathbf Q$ of equal rank $k$; proved from a pinching fact stated for square blocks of equal size, applied to blocks $k\times k$ and $(n-k)\times(d-k)$. True for arbitrary ranks and rectangular $\mathbf A$ | PN1–PN3 (no rank hypothesis, no bases) |
| E6 | Lemma 3.4 | a probability inside a deterministic lemma; Bernoulli $(1-x)^{p/2}\ge1-(p/2)x$ is false for $p<2$ (the true constant is $\max(1,p/2)$ and needs $x\le1$); "$\sigma_i(\mathbf A\mathbf Z)^2\ge\|\mathbf A\mathbf z_i\|^2$" holds for Ritz vectors, not for an arbitrary orthonormal $\mathbf Z$ | hypotheses on $\sigma_i(\mathbf P\mathbf A)$; SC1 |
| E7 | Lemma 3.6 | "full-rank $\mathbf A$" not needed; the sentence before it has the roles of $\mathbf W,\mathbf Z$ swapped | not needed (HD2 uses $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$) |
| E8 | proof, eq. (small-gap-case) and after | mixes $\hat\sigma$ and $\hat\sigma^2$; the negation of the test is written $\hat\sigma_s\ge(1+0.5/p)\hat\sigma_{k+1}$ and "$\sigma_s\ge(1+0.1/p)\sigma_{k+1}$", impossible since $\sigma_s\le\sigma_{k+1}$ (meant: $\sigma_s\ge\sigma_{k+1}/(1+c/p)$); the tail count is $s-k$, not $s$ | SV3, CB1 |
| E9 | proof, choice of $\ell$ | "the largest $\ell\in[k]$ with $\sigma_\ell>(1+0.5/p)\sigma_{k+1}$ and $\sigma_{\ell+1}<(1-\varepsilon/d)\sigma_\ell$ ... is guaranteed to exist", and "$\sigma_j\le(1+1/p)\sigma_{k+1}$ for $j>\ell$ by definition": both need $(1-\varepsilon/d)^k(1+1/p)>1+0.5/p$, roughly $kp\varepsilon\lesssim d/4$, which is not assumed ($k$ may be close to $d$) | SP1: gap threshold $1/(2k(p+1))$ on squares, no condition (§2.5) |
| E10 | proof, head | Lemma 3.2 is applied with target $\ell$ and block $k$; its error is then in $\sigma_{\ell+1}^2$, not $\sigma_{k+1}^2$ (harmless factor $(1+1/p)^2$, unstated); it needs depth $\Omega(\sqrt p\log(d/\varepsilon))$ in the run that is selected | RZ4 with head count $r\le k$; depth conditions of GA3 |
| E11 | Lemma 3.5, Cor. 3.7 | proved for $\mathbf Z$ with exactly $\ell$ columns, applied to the $k$-column $\mathbf Z$ (fine by monotonicity, unstated) | HD1 (frame with at most $L$ columns), HD2 |
| E12 | proof | $\mathrm{poly}(\varepsilon/d)$ is never specified; "$\sqrt d$" then "$\sqrt k$" between Schatten and Frobenius norms | explicit $\delta$ in ST4, CB3 |
| E13 | Lemmas 3.5, 3.7 | "integer $p\ge1$" (not used) | — |
| E14 | Step 3 | the estimates $\hat\sigma$ cost two more runs and enter the failure probability; the mathematical statement does not need them | no selection (§2.6) |
| E15 | Lemma 3.1 | MM Theorem 1 is for accuracy $\varepsilon\in(0,1)$ at $q=\Theta(\log d/\sqrt\varepsilon)$ with probability $99/100$ and unspecified constants; BCW use it at $\gamma=\varepsilon^{2/3}p^{-1/3}$ and $\mathrm{poly}(\varepsilon/d)$ | RZ3 (deterministic, explicit) |
| E16 | whole paper | exact arithmetic throughout; no finite-precision or bit-complexity statement; "RAM model" times count exact operations | §8 |

Not errata, but relevant: Musco–Musco's Frobenius $(1+\varepsilon)$ bound at depth
$O(\log d/\sqrt\varepsilon)$ is *not* a consequence of the per-vector guarantee (which gives
$k\varepsilon\sigma_k^2$, to be compared with $\mathrm{OPT}_2^2\ge\sigma_k^2$ only); it uses their
Property 3, a rank argument on the number $w$ of singular values in
$[\sigma_k/(1+\varepsilon/2),\sigma_k)$. BCW do not need it. The by-product GA0 is therefore the
per-rank form $\mathrm{OPT}^2+k\gamma\sigma_k^2$, not MM's theorem (decision MM-FROB).

## 2. The mathematics as planned

All of §2 is **checked** unless marked known.

### 2.1 Projector pairs and Schatten norms (PN1–PN4, ST1, ST2)

Orthogonal projectors are `IsStarProjection`. For $\mathbf P$ ($m\times m$), $\mathbf Q$
($n\times n$) of any ranks:

* **PN1 (pinching).** In every unitarily invariant norm,
  $\|\mathbf P\mathbf A\mathbf Q+(\mathbf I-\mathbf P)\mathbf A(\mathbf I-\mathbf Q)\|\le
  \|\mathbf A\|$: the left side is $\tfrac12(\mathbf A+\mathbf U\mathbf A\mathbf V)$ with the
  unitaries $\mathbf U=2\mathbf P-\mathbf I$, $\mathbf V=2\mathbf Q-\mathbf I$. No bases, no
  block matrices.
* **PN2 (orthogonal sums).** If $\mathbf X^{\mathsf H}\mathbf Y=\mathbf 0$ and
  $\mathbf X\mathbf Y^{\mathsf H}=\mathbf 0$ then
  $\|\mathbf X+\mathbf Y\|_{S_p}^p=\|\mathbf X\|_{S_p}^p+\|\mathbf Y\|_{S_p}^p$, $0<p<\infty$.
* **PN3** = PN1 + PN2: BCW Lemma 3.3 without the rank hypothesis.
* **PN4** (one-sided, $p\ge2$):
  $\|\mathbf P\mathbf A\|_p^p+\|(\mathbf I-\mathbf P)\mathbf A\|_p^p\le\|\mathbf A\|_p^p$
  (McCarthy: $\operatorname{tr}(\mathbf S+\mathbf T)^{r}\ge\operatorname{tr}\mathbf S^r+
  \operatorname{tr}\mathbf T^r$, $r\ge1$). It is false for $p<2$, which is why the two-sided
  output is needed there. Optional (decision ONE-SIDED).
* **ST1.** If $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$ (the range of $\mathbf Q$
  contains the row space of $\mathbf P\mathbf A$) then
  $\|\mathbf A-\mathbf A\mathbf Q\|_p^p+\|\mathbf P\mathbf A\|_p^p\le\|\mathbf A\|_p^p$.
* **ST2.** Hence, for every $k$,
  $\|\mathbf A-\mathbf A\mathbf Q\|_p^p\le\mathrm{OPT}_p^p+
  \sum_{i<k}\bigl(\sigma_i(\mathbf A)^p-\sigma_i(\mathbf P\mathbf A)^p\bigr)$.
  For $p=2$ and $\operatorname{rank}\mathbf P\le k$ there is the identity
  $\|\mathbf A-\mathbf P\mathbf A\|_{\mathsf F}^2=\mathrm{OPT}_2^2+
  \sum_{i<k}(\sigma_i(\mathbf A)^2-\sigma_i(\mathbf P\mathbf A)^2)$ (ST2F), and its instance
  $\mathbf A-\llbracket\mathbf P\mathbf A\rrbracket_k$ (ST2T): the Frobenius headline needs no
  pinching.

The hypothesis of every later structural theorem is a bound on the **deficits**
$\sigma_i(\mathbf A)^2-\sigma_i(\mathbf P\mathbf A)^2\le\gamma\,\sigma_k(\mathbf A)^2$, $i<k$.
For the top-$k$ Ritz vectors this is the per-vector guarantee (E6); as a hypothesis on singular
values it does not mention vectors. Since $\sigma_i(\mathbf P\mathbf A)\le\sigma_i(\mathbf A)$,
deficits are nonnegative, and for $p=2$ a bound on the Frobenius error of
$\llbracket\mathbf P\mathbf A\rrbracket_k$ is the same thing as a bound on their sum.

### 2.2 The tail-count form (CB1, CB2): BCW's case analysis as one inequality

SC1: for $0\le b\le a$ and $r>0$, $a^r-b^r\le\max(1,r)\,a^{r-1}(a-b)$. With $a=\sigma_i^2$,
$b=\sigma_i(\mathbf P\mathbf A)^2$, $r=p/2$: a deficit $\gamma\sigma_k^2$ costs at most
$\max(1,p/2)\,\gamma\,\sigma_k^2\sigma_i^{p-2}$ in ST2. For $p\le2$, $\sigma_i^{p-2}\le
\sigma_k^{p-2}$, so the cost is $\gamma\sigma_k^p$ whatever the head looks like.

SV3: $(j+1)\,\sigma_{k+j}^p\le\mathrm{OPT}_p^p$.

**CB1** ($1\le p\le2$). If all deficits are at most $\gamma\sigma_k^2$ and
$\sigma_k\le\kappa\,\sigma_{k+j}$, then
$$\|\mathbf A-\mathbf A\mathbf Q\|_p^p\le\Bigl(1+\frac{k\gamma\kappa^p}{j+1}\Bigr)\mathrm{OPT}_p^p .$$
At $j=0,\kappa=1$ this is the plain bound $(1+k\gamma)$; at $j\approx k\varepsilon^{-1/3}$ it is
the heavy-tail case. The whole case analysis is then: either $\sigma_k\le\kappa\sigma_{k+j}$
(use CB1 with the deep run's $\gamma_1$), or $\sigma_{k+j}<\sigma_k/\kappa$ (a gap; use CB1 at
$j=0$ with the wide run's $\gamma_2$). **CB2** states it for two candidates
$(\mathbf P_1,\mathbf Q_1)$, $(\mathbf P_2,\mathbf Q_2)$ produced in any way:
$\min$ of the two errors is at most
$(1+k\max(\gamma_1\kappa^p/(j+1),\gamma_2))\,\mathrm{OPT}_p^p$, where the second candidate's
accuracy is assumed only under the gap. This is the combination step, independent of Krylov
spaces. With $\mathbf P_1=\mathbf P_2$ it is the statement for one projector.

### 2.3 Deficits of a filtered sketch and of RBKI (RZ1–RZ5)

Setting of `LowRank/Structural/Filter.lean`: $\mathbf P$ the range projector of
$\mathbf A g(\mathbf H)\mathbf\Omega$, $\mathbf Z$ an orthonormal frame with
$\mathbf Z^{\mathsf H}\mathbf\Omega$ of full row rank, $\lvert g\rvert\ge c$ at
$\sigma_j^2$, $j\le i$.

* **RZ1 (gap).** If $\mathbf A\mathbf Z\mathbf Z^{\mathsf H}=\llbracket\mathbf A\rrbracket_t$,
  $i<t$ and $\lvert g\rvert\le a$ on $[0,\sigma_t^2]$:
  $\sigma_i(\mathbf P\mathbf A)^2\ge\sigma_i^2-(a/c)^2\|\mathbf M_t\|_2^2$,
  $\mathbf M_t=(\mathbf A-\llbracket\mathbf A\rrbracket_t)\mathbf\Omega
  (\mathbf Z^{\mathsf H}\mathbf\Omega)^+$. Proof: SV1,
  $\sigma_i(\mathbf P\mathbf A)^2\ge\sigma_i^2-\|(\mathbf I-\mathbf P)\llbracket\mathbf A
  \rrbracket_{i+1}\|_2^2$ (Courant–Fischer on the top right singular subspace), then the
  existing head capture.
* **RZ2 (cut, no gap).** If the range of $\mathbf Z$ contains the row space of
  $\llbracket\mathbf A\rrbracket_{i+1}$, $0\le\tau\le\sigma_i$ and $\lvert g\rvert\le a$ on
  $[0,\tau^2]$:
  $\sigma_i(\mathbf P\mathbf A)^2\ge\tau^2-(a/c)^2\|(\mathbf A-\mathbf A\mathbf Z
  \mathbf Z^{\mathsf H})\mathbf\Omega(\mathbf Z^{\mathsf H}\mathbf\Omega)^+\|_2^2$.
  Proof (new, one page): for $\tilde{\mathbf c}$ supported on the first $i+1$ coordinates of
  the frame, $\mathbf y=\mathbf Ag(\mathbf H)\mathbf\Omega(\mathbf Z^{\mathsf H}\mathbf\Omega)^+
  \tilde{\mathbf c}=\mathbf u+\mathbf n+\mathbf f$ with $\mathbf u$ in the top $i+1$ left
  singular directions, $\mathbf n$ in directions with $\sigma^2\ge\tau^2$ and $\mathbf f$ in
  directions with $\sigma^2<\tau^2$, mutually orthogonal and with orthogonal images under
  $\mathbf A^{\mathsf H}$. Then
  $\|\mathbf A^{\mathsf H}\mathbf y\|^2\ge\tau^2(\|\mathbf u\|^2+\|\mathbf n\|^2)$,
  $\|\mathbf u\|\ge\sigma_ic\|\tilde{\mathbf c}\|$ and
  $\|\mathbf f\|\le a\|(\mathbf A-\mathbf A\mathbf Z\mathbf Z^{\mathsf H})\mathbf\Omega
  (\mathbf Z^{\mathsf H}\mathbf\Omega)^+\|\|\tilde{\mathbf c}\|$; Courant–Fischer on this
  $(i+1)$-dimensional subspace of the range of $\mathbf P$.
* **RZ3 (RBKI, no gap).** For $0<\gamma\le1$, $q\ge1$, $i<k$,
  $\mathbf A\mathbf Z\mathbf Z^{\mathsf H}=\llbracket\mathbf A\rrbracket_k$:
  $$\sigma_i(\mathsf{rbki}(\mathbf A,\mathbf\Omega,q))^2\ge\sigma_i^2-\gamma\sigma_k^2-
  4e^{-2\sqrt2(q-1)\sqrt\gamma}\,\|\mathbf M_k\|_2^2 .$$
  If $\sigma_i^2\ge(1+\gamma)\sigma_k^2$: RZ1 at $t=k$ with the Chebyshev filter of $[0,\sigma_k^2]$
  (relative gap $(\sigma_i-\sigma_k)/(\sigma_i+\sigma_k)\ge\gamma/(1+\sqrt2)^2$). Otherwise RZ2
  with $\tau^2=\sigma_i^2-\gamma\sigma_k^2$ and the filter of $[0,\tau^2]$ (relative gap
  $\ge\gamma/8$). The filter depends on $i$; all are in the Krylov space (SV2). This is the
  per-vector guarantee of Musco–Musco Theorem 1 in deterministic form (E15).
* **RZ4 (RBKI, gap).** Head count $r=h+1\le t$, $i<r$,
  $\mathbf A\mathbf Z\mathbf Z^{\mathsf H}=\llbracket\mathbf A\rrbracket_t$:
  $\sigma_i(\mathsf{rbki})^2\ge\sigma_i^2-4e^{-8(q-1)\sqrt{\gamma_{h,t}}}\|\mathbf M_t\|_2^2$,
  $\gamma_{h,t}$ = `singularGapRatio A h t` (MM Theorem 13; E4, E10).
* **RZ5.** $\|\mathbf A-\llbracket\mathsf{rbki}\rrbracket_k\|_{\mathsf F}^2\le\mathrm{OPT}_2^2+
  k\gamma\sigma_k^2+4ke^{-2\sqrt2(q-1)\sqrt\gamma}\|\mathbf M_k\|_2^2$ (ST2T + RZ3).

The residual $\mathbf M_t$ is the library's: for a Gaussian block with $\ell\ge t+2$ columns,
$\mathbb E\|\mathbf M_t\|_{\mathsf F}^2=\frac{t}{\ell-t-1}\|\mathbf A-\llbracket\mathbf A
\rrbracket_t\|_{\mathsf F}^2$. That is why the Frobenius headline has no dimension in it.

### 2.4 Large singular values, $p>2$ (HD1, HD2, ST3, ST4, CB3)

* **HD1** (BCW Lemma 3.5 / Corollary 3.7, frame form). $\mathbf Z$ with at most $L$
  orthonormal columns, $\|\mathbf A\mathbf Z\|_{\mathsf F}^2\ge\sum_{i<L}\sigma_i^2-\eta$,
  $\sigma_L^2\le(1-\theta)\sigma_{L-1}^2$:
  $\theta\,\|\llbracket\mathbf A\rrbracket_L(\mathbf I-\mathbf Z\mathbf Z^{\mathsf H})
  \|_{\mathsf F}^2\le\eta$.
* **HD2.** For $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$:
  $\theta\,\|\llbracket\mathbf A\rrbracket_L(\mathbf I-\mathbf Q)\|_{\mathsf F}^2\le
  \sum_{i<L}(\sigma_i^2-\sigma_i(\mathbf P\mathbf A)^2)$, by HD1 at a frame of the row space of
  $\llbracket\mathbf P\mathbf A\rrbracket_L$ (inside the range of $\mathbf Q$).
* **ST3 (head split).** For every $L\le k$ and $p\ge1$:
  $$\|\mathbf A-\mathbf A\mathbf Q\|_p\le2\,\|\llbracket\mathbf A\rrbracket_L(\mathbf I-\mathbf Q)
  \|_p+\Bigl(\mathrm{OPT}_p^p+\sum_{L\le i<k}\bigl(\sigma_i^p-\sigma_i(\mathbf P\mathbf A)^p
  \bigr)\Bigr)^{1/p}.$$
  Proof: $\mathbf A(\mathbf I-\mathbf Q)=\mathbf A_L(\mathbf I-\mathbf Q)-
  \mathbf P\mathbf A_L(\mathbf I-\mathbf Q)+(\mathbf I-\mathbf P)(\mathbf A-\mathbf A_L)
  (\mathbf I-\mathbf Q)$; PN3 on $\mathbf A-\mathbf A_L$; Weyl
  $\sigma_j(\mathbf P(\mathbf A-\mathbf A_L)\mathbf Q)\ge\sigma_{j+L}(\mathbf P\mathbf A)$.
* **ST4** = ST3 + HD2 + SC1 for $p\ge2$, with head deficits $\delta\sigma_k^2$, middle deficits
  $\gamma\sigma_k^2$, $\sigma_L\le\kappa\sigma_k$:
  $\|\mathbf A-\mathbf A\mathbf Q\|_p\le2\sqrt{L\delta/\theta}\,\sigma_k+
  (\mathrm{OPT}_p^p+\tfrac p2\kappa^{p-2}(k-L)\gamma\sigma_k^p)^{1/p}$.
* **CB3** = ST4 + SP1 (§2.5) + SV3: with head deficits $\delta\sigma_k^2$ at the indices with
  $\sigma_i>(1+\frac1{2p})\sigma_k$, all deficits $\le\gamma\sigma_k^2$ and
  $\sigma_k\le\kappa\sigma_{k+j}$:
  $$\|\mathbf A-\mathbf A\mathbf Q\|_p\le\Bigl(2k\sqrt{2(p+1)\delta}+
  \bigl(1+\tfrac{e\,p\,k\gamma\kappa^p}{2(j+1)}\bigr)^{1/p}\Bigr)\mathrm{OPT}_p .$$

### 2.5 The head index exists (SP1; repair of E9)

**SP1.** For every $\mathbf A$, $k$ and real $p\ge1$ there is $L\le k$ with
$\sigma_L\le(1+\frac1p)\sigma_k$ and, if $L>0$,
$\sigma_{L-1}>(1+\frac1{2p})\sigma_k$ and
$\sigma_L^2\le(1-\frac1{2k(p+1)})\sigma_{L-1}^2$.
Proof: take the largest $i<k$ with $\sigma_i>(1+\frac1{2p})\sigma_k$ and
$\sigma_i/\sigma_{i+1}\ge\rho:=(1+\frac1{2p+1})^{1/k}$, $L=i+1$ (or $L=0$ if there is none). If
$\sigma_0>(1+\frac1p)\sigma_k$ such an $i$ exists by the pigeonhole principle, since the ratios
multiply to more than $(1+\frac1p)/(1+\frac1{2p})=1+\frac1{2p+1}$ over at most $k$ steps; after
$L$ all ratios above the threshold are less than $\rho$, so
$\sigma_L<\rho^k(1+\frac1{2p})\sigma_k=(1+\frac1p)\sigma_k$; and
$1-\rho^{-2}\ge\frac{9}{16k(p+1)}$. The case $\sigma_k=0$ is separate. The relative gap is
$1/(kp)$ instead of the paper's $\varepsilon/d$; it enters ST4 through
$\sqrt{L\delta/\theta}\le k\sqrt{2(p+1)\delta}$ and costs $\log(kp)$ in the depth.

### 2.6 The sum of two block Krylov spaces (TS1–TS3)

`rbkiSum A Ω₁ Ω₂ q₁ q₂ := rsvd A (fromCols (blockKrylovMatrix (Aᴴ * A) Ω₁ q₁)
(blockKrylovMatrix (Aᴴ * A) Ω₂ q₂))`, the projection of $\mathbf A$ onto the sum of the two left
Krylov spaces. By SV2, $\sigma_i(\mathsf{rbki}(\mathbf A,\mathbf\Omega_j,q_j))\le
\sigma_i(\mathsf{rbkiSum})$ (TS1), so RZ3 for $(\mathbf\Omega_1,q_1)$ and RZ4 for
$(\mathbf\Omega_2,q_2)$ hold for the one projector, and CB1 applies with no selection:

**TS2 (Frobenius, deterministic).** With $t=k+j$, frames $\mathbf Z_1,\mathbf Z_2$ of the row
spaces of $\llbracket\mathbf A\rrbracket_k$, $\llbracket\mathbf A\rrbracket_t$, $0<\gamma\le1$:
$$\|\mathbf A-\llbracket\mathsf{rbkiSum}\rrbracket_k\|_{\mathsf F}^2\le
\Bigl(1+\frac{2k\gamma}{j+1}\Bigr)\mathrm{OPT}_2^2+
4k\,e^{-2\sqrt2(q_1-1)\sqrt\gamma}\,\|\mathbf M^{(1)}_k\|_2^2+
4k\,e^{-3(q_2-1)}\,\|\mathbf M^{(2)}_{t}\|_2^2 .$$
Case $\sigma_t^2\le\sigma_k^2/2$: RZ4 with gap ratio $\ge3-2\sqrt2$, so
$8\sqrt{\gamma_{h,t}}\ge8(\sqrt2-1)>3$. Case $\sigma_k^2<2\sigma_t^2$: RZ3 and
$\sigma_k^2<2\,\mathrm{OPT}_2^2/(j+1)$ (SV3). **TS3** is the same for $\|\cdot\|_{S_p}^p$,
$1\le p\le2$, for the output $\mathbf A\mathbf Q$,
$\mathbf Q$ the projector onto the row space of $\llbracket\mathsf{rbkiSum}\rrbracket_k$, with
the two residual terms multiplied by $\sigma_k^{p-2}$; SV4
($\sigma_k^{p-2}\|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2\le\mathrm{OPT}_p^p$
for $p\le2$) removes that factor in expectation. **TS2m** is the choose-one form:
$\min$ of the errors of the two separate runs has the same bound; for the Frobenius norm the
better run is the one with the larger $\|\llbracket\mathsf{rbki}\rrbracket_k\|_{\mathsf F}$
(ST2T), which a routine has for free.

Cost in Tropp and Webber's count: $2(\ell_1q_1+\ell_2q_2)$ products for `rbkiSum`, plus $k$
for $\mathbf A\mathbf Q$ in the two-sided form. The two start blocks need not be independent:
only linearity of expectation (or a union bound) is used, so $\mathbf X_1$ may be a sub-block of
$\mathbf X_2$.

### 2.7 Gaussian start blocks (GA0–GA4)

**GA1.** $\ell_1\ge k+2$, $\ell_2\ge k+j+2$:
$$\mathbb E\,\|\mathbf A-\llbracket\mathsf{rbkiSum}\rrbracket_k\|_{\mathsf F}^2\le
\Bigl(1+\frac{2k\gamma}{j+1}+4k\,e^{-2\sqrt2(q_1-1)\sqrt\gamma}\frac{k}{\ell_1-k-1}+
4k\,e^{-3(q_2-1)}\frac{k+j}{\ell_2-k-j-1}\Bigr)\mathrm{OPT}_2^2 ,$$
from TS2, $\|\cdot\|_2\le\|\cdot\|_{\mathsf F}$, the block moment and
$\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{\mathsf F}\le\mathrm{OPT}_2$. **GA2** (headline,
`Fin` sizes): $\ell_1=2k+1$, $\ell_2=2(k+j)+1$, $\gamma=\varepsilon^{2/3}$,
$j+1\ge6k\varepsilon^{-1/3}$, $q_1\ge1+\log(12k/\varepsilon)/(2\sqrt2\varepsilon^{1/3})$,
$q_2\ge1+\log(12k/\varepsilon)/3$: each of the three terms is at most $\varepsilon/3$.
**GA1p, GA2p**: the same for $1\le p\le2$. **GA4**: asymptotic form, "$O(k\varepsilon^{-1/3})$
columns and depths $O(\varepsilon^{-1/3}\log(k/\varepsilon))$, $O(\log(k/\varepsilon))$
suffice". **GA0**: one run, $\mathbb E\|\mathbf A-\llbracket\mathsf{rbki}\rrbracket_k
\|_{\mathsf F}^2\le(1+4ke^{-2\sqrt2(q-1)\sqrt\gamma}\frac k{\ell-k-1})\mathrm{OPT}_2^2+
k\gamma\sigma_k^2$.

**GA3** ($2\le p<\infty$, tail form). With probability at least $1-\delta$,
$\|\mathbf A-\mathbf A\mathbf Q\|_{S_p}\le(1+\varepsilon)\mathrm{OPT}_p$, when
$j+1\ge e^2k(\varepsilon p)^{-1/3}$,
$q_1\ge1+\bigl(\frac{p^{1/6}}{2\varepsilon^{1/3}}+\frac{\sqrt{4p+1}}8\bigr)\Lambda_1$,
$q_2\ge1+\frac{\sqrt{4p+1}}8\Lambda_2$, with
$\Lambda_1=\log\frac{256k^3(p+1)n}{\varepsilon^2\delta}$,
$\Lambda_2=\log\frac{256k^2(k+j)(p+1)n}{\varepsilon^2\delta}$. Derivation: on the events
$\|\mathbf M^{(1)}_k\|_{\mathsf F}^2\le\frac{2kn}{\delta}\sigma_k^2$ and
$\|\mathbf M^{(2)}_t\|_{\mathsf F}^2\le\frac{2tn}{\delta}\sigma_t^2$ (Markov; $n$ is the number
of columns of $\mathbf A$), CB3 with $\delta_{\mathrm{head}}=\varepsilon^2/(32k^2(p+1))$ and
either $\kappa=1+\frac1p$, $\gamma=\varepsilon^{2/3}p^{-1/3}$ (no gap; RZ3 at $\gamma/2$) or
$j=0$, $\kappa=1$, $\gamma=\varepsilon/(ek)$ (gap $\sigma_{k+j}<\sigma_k/(1+\frac1p)$; RZ4 with
gap ratio $\ge1/(2p+1)$); head deficits from RZ4 at $t=k$ with gap ratio $\ge1/(4p+1)$. Here the
dimension enters, because for $p>2$ the Frobenius norm of the tail is not controlled by
$\mathrm{OPT}_p$. Appendix A states GA3 with these thresholds.

## 3. Objects, interfaces, statement shapes (items 1–3)

**Objects.** One definition:

| Notion | NLAlib | Bridge |
|---|---|---|
| RBKI on the sum of two block Krylov spaces, $\mathsf{rbkiSum}(\mathbf A,\mathbf\Omega_1,\mathbf\Omega_2,q_1,q_2)$ | `rbkiSum A Ω₁ Ω₂ q₁ q₂ := rsvd A (fromCols (blockKrylovMatrix (Aᴴ * A) Ω₁ q₁) (blockKrylovMatrix (Aᴴ * A) Ω₂ q₂))`; deterministic; `Algorithm: rbki-sum` | `rbkiSum_def`, `rbkiSum_eq_rangeProjector`, `singularValues_rbki_le_singularValues_rbkiSum_left/right`; Mathlib has none |

Used directly: `schattenNorm`, `frobNorm`, `specNorm`, `singularValues`, `truncatedSVD`,
`rangeProjector`, `rsvd`, `rbki`, `pinv`, `singularGapRatio`, `HasOrthonormalCols`,
`IsStarProjection`, `gaussianMatrix`, `HasLaw`. The two-sided output is written
`A * rangeProjector (truncatedSVD B k)ᴴ`, not named (decision CORANGE-NAME).

**Interfaces.** None introduced. The hypothesis "$\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$"
is an equation between `IsStarProjection`s; deficits are inequalities between `singularValues`.
A predicate bundling "deficits at most $\gamma\sigma_k^2$" was considered and rejected: it would
have one field and two consumers.

**Statement shapes.** Appendix A has every signature except TS4 and GA3a, whose statements are
to be fixed with GA3's proof (§9, risks). Field: `RCLike 𝕜` for waves 0–3; ℝ for the
Gaussian wave, as everywhere in `LowRank/Gaussian` (the law `gaussianMatrix` is real). Index
types `Type*` with `Fintype`; the headlines GA2, GA2p instantiate at `Fin`. Exponent
`p : ℝ≥0∞` with `1 ≤ p`, `p ≤ 2` or `2 ≤ p`, `p ≠ ⊤`, powers `^ p.toReal`, as
`schattenNorm_rpow`. Constants: written out ($4$, $2\sqrt2$, $3$, $e$), all proof artifacts of
Chebyshev values in readable form [B6]; no named bound is introduced (decision CONSTANTS).
Probability: expectations of squared (or $p$-th power) errors in closed form (GA0, GA1, GA1p),
sample-size headlines (GA2, GA2p), asymptotic form (GA4, GA4p), tail form for $p>2$ (GA3).
Corollaries: Frobenius from Schatten at $p=2$ is *not* how the Frobenius results are proved
(they are one-sided and need no pinching); a tail bound from GA1 by Markov is a one-liner left to
consumers.

## 4. Consumers (item 4)

| Statement | Consumer |
|---|---|
| PN1–PN4 | any analysis of a two-sided compression in a Schatten norm; nuclear-norm lower bounds (`LowerBounds/LowRank/NuclearMinimax.lean` proves a special case by hand); generalized Nyström in Schatten norms |
| ST1, ST2, CB1, CB2 | any sketch that controls singular values of $\mathbf P\mathbf A$: `rsvd` with a subspace embedding, subspace iteration, Nyström through the Gram correspondence; the routine of §8 |
| SV1, SV2 | Ritz-value statements for Lanczos and block Lanczos (`Krylov/`), the eigenvalue accuracy of Nyström |
| RZ1–RZ4 | singular value estimation by RBKI (per-vector PCA guarantee, MM Theorem 1 (3)); block-size-aware bounds of `LowRank-BlockLanczos.md` §2.5; BCW's lower-bound reduction uses the special case $k=1$ of RZ3 (their Corollary 5.5) |
| RZ5, GA0 | a Frobenius guarantee for the block Golub–Kahan program through `BlockKrylov.integral_comp_storedOutput`, today |
| TS2, GA1, GA2 | the routine of §8; the explorer's pairing with the lower bound $\Omega(k\varepsilon^{-1/3})$ when it lands |
| CH1 | every Chebyshev filter argument whose interval is not $[0,\sigma_t^2]$ (deflation, stopping criteria) |
| SP1, HD1, HD2 | Schatten-$p$ bounds, $p>2$; HD1 is a $\sin\Theta$-type statement from an energy deficit and a gap, usable for eigenvector accuracy from Rayleigh quotients |

## 5. Files and placement (item 5)

New files:

* `NLAlib/Matrix/Norms/SchattenPinching.lean`: PN1, PN2, PN3, PN4.
* `NLAlib/Matrix/Spectral/CompressionSingularValues.lean`: SV1, SV2, ST2F, ST2T, HD1 (singular
  values and Frobenius error of $\mathbf P\mathbf A$).
* `NLAlib/Matrix/Spectral/SingularValueDecay.lean`: SV3, SV4, SP1 (statements about the spectrum
  alone).
* `NLAlib/LowRank/Structural/SingularValueDeficit.lean`: ST1, ST2, CB1, CB2, HD2, ST3, ST4, CB3.
* `NLAlib/LowRank/Structural/RitzValues.lean`: RZ1–RZ5.
* `NLAlib/LowRank/Structural/BlockKrylovSum.lean`: `rbkiSum`, TS0–TS3, TS2m, TS4.
* `NLAlib/LowRank/Gaussian/BlockKrylovSum.lean`: GA0–GA4, integrability companions.

Additions to existing files, each with its reason:

* SC1 `Real.rpow_sub_rpow_le_max_mul` → `NLAlib/ForMathlib/Analysis/SpecialFunctions/Pow/Real.lean`
  (a fact about real powers; Mathlib candidate).
* CH1 `exists_degree_lt_div_sq_le_exp_of_le` →
  `NLAlib/ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean` (a statement
  about Chebyshev polynomials and two real numbers; today its content is private inside
  `LowRank/Gaussian/BlockKrylov.lean`).
* integrability of the `rbkiSum` errors → `NLAlib/LowRank/Random/RangeFinder.lean` (where
  `integrable_frobNorm_sub_truncatedSVD_rbki_sq` lives); `measurable_rbkiSum` →
  `NLAlib/Probability/Measurability/Krylov.lean`.
* vocabulary row for `rbkiSum`; `docs/constants.toml` unchanged (no named bound).

**Changes to merged statements** (old → new): none is required. One is proposed (decision
CHEB-GENERAL): `exists_degree_lt_div_sq_le_exp_singularGapRatio (A : Matrix m n ℝ) …` →
`(A : Matrix m n 𝕜) …` with the same conclusion, reproved from CH1; needed so that RZ4 is over
`𝕜` [T7]. Its four call sites pass a real matrix and are unaffected. No deviation from Mathlib is
introduced.

## 6. Targets

Sizes S/M/L. "Needs" lists targets of this note; library lemmas are named in the outline.
Paper locations are BCW unless marked.

### Wave 0: matrix analysis (no Krylov, no probability)

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| SC1 | $a^r-b^r\le\max(1,r)a^{r-1}(a-b)$ | S | — | Fact 2.4, E6 | $r\ge1$: `one_add_mul_self_le_rpow_one_add` at $s=b/a-1$; $r<1$: $b^r\ge b\,a^{r-1}$ |
| CH1 | Chebyshev filter for reals $0\le\tau\le s$ | M | — | MM Lemma 5 | move the body of `exp_div_two_le_abs_eval_T_comp`; cases $\tau=0$ ($x^d$), $\tau>0$ ($T_d(2x/\tau^2-1)$, monotone beyond $1$) |
| PN1 | pinching for a projector pair, every `SymmetricGauge` | S | — | Fact 2.9, Lemma 3.3 | $\tfrac12(\mathbf A+\mathbf U\mathbf A\mathbf V)$, `matrixNorm_add_le`, unitary invariance (`matrixNorm_mul_of_mul_mul_conjTranspose_eq`) |
| PN2 | Schatten powers add on orthogonal sums | M | — | Lemma 3.3 (proof) | $(\mathbf X+\mathbf Y)^{\mathsf H}(\mathbf X+\mathbf Y)=\mathbf X^{\mathsf H}\mathbf X+\mathbf Y^{\mathsf H}\mathbf Y$ with commuting orthogonal summands; `PosSemidef.schattenNorm_rpow_eq_re_trace_rpow`; cfc of an orthogonal sum |
| PN3 | $\|\mathbf P\mathbf A\mathbf Q\|_p^p+\|(\mathbf I-\mathbf P)\mathbf A(\mathbf I-\mathbf Q)\|_p^p\le\|\mathbf A\|_p^p$ | S | PN1, PN2 | Lemma 3.3 | `lpGauge_matrixNorm`, monotone `rpow` |
| PN4 | one-sided, $p\ge2$ | M | — | Fact 2.7 (Maher) | McCarthy superadditivity of $\operatorname{tr}(\cdot)^{p/2}$ on PSD matrices; searched the library: none; optional |
| SV1 | $\sigma_i(\mathbf P\mathbf A)^2\ge\sigma_i(\mathbf A)^2-\|(\mathbf I-\mathbf P)\llbracket\mathbf A\rrbracket_{i+1}\|_2^2$ | M | — | MM Thm 12 (proof) | Courant–Fischer (`Matrix/Spectral/CourantFischer.lean`) on the row space of $\llbracket\mathbf A\rrbracket_{i+1}$; Pythagoras |
| SV2 | $\sigma_i(\mathbf P_{\mathbf Y'}\mathbf A)\le\sigma_i(\mathbf P_{\mathbf Y}\mathbf A)$ for nested ranges | S | — | — | $\mathbf P_{\mathbf Y'}=\mathbf P_{\mathbf Y'}\mathbf P_{\mathbf Y}$, `IsStarProjection.singularValues_mul_le` |
| SV3 | $(j+1)\sigma_{k+j}^p\le\mathrm{OPT}_p^p$ | S | — | eq. (tradeoff-analysis), E8 | `schattenNorm_rpow`, `singularValues_sub_truncatedSVD`, antitone |
| SV4 | $\sigma_k^{p-2}\|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2\le\mathrm{OPT}_p^p$, $p\le2$ | S | — | — | termwise $\sigma_i^2\sigma_k^{p-2}\le\sigma_i^p$; junk value $0^{p-2}=0$ checked |
| SP1 | head index with gap $1/(2k(p+1))$ | M | — | proof of Thm 3.1, E9 | §2.5; `Nat.findGreatest`; real-analysis estimate $1-\rho^{-2}\ge9/(16k(p+1))$ |
| ST2F | Frobenius identity for $\mathbf A-\mathbf P\mathbf A$, rank $\le k$ | S | — | eq. (inf_cost_lra) | `IsStarProjection.frobNorm_sq_eq_add`, `frobNorm_sq_eq_sum_range_singularValues_sq`, `frobNorm_sub_truncatedSVD_sq` |
| ST2T | the same for $\mathbf A-\llbracket\mathbf P\mathbf A\rrbracket_k$ | S | ST2F | MM Def. 8 | $\llbracket\mathbf P\mathbf A\rrbracket_k=\mathbf\Pi\mathbf A$, $\mathbf\Pi\le\mathbf P$ (`IsBestRankApprox.rangeProjector_mul`) |
| HD1 | energy deficit and gap give head capture | M | — | Lemma 3.5, Cor. 3.7, E11 | §1.1 proof with the frame of the row space of $\llbracket\mathbf A\rrbracket_L$; rows of $\mathbf V_L^{\mathsf H}\mathbf Z$ have norm $\le1$ |

### Wave 1: structural theorems for a projector pair

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| ST1 | $\|\mathbf A-\mathbf A\mathbf Q\|_p^p+\|\mathbf P\mathbf A\|_p^p\le\|\mathbf A\|_p^p$ | S | PN3 | eq. (upper-bound-cost-sp-intro); BN Lemma 4.4 | algebra from $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$ |
| ST2 | error $\le\mathrm{OPT}_p^p+\sum_{i<k}$ deficits in $p$-th powers | S | ST1 | Lemma 3.4 | split $\|\mathbf A\|_p^p$ at $k$; drop $\sigma_i(\mathbf P\mathbf A)$, $i\ge k$ |
| CB1 | tail-count form, $1\le p\le2$ | M | ST2, SC1, SV3 | Thm 3.1 proof, case 1 | §2.2 |
| CB2 | two candidates, `min` | S | CB1 | Algorithm 3.2 | case split on $\kappa\sigma_{k+j}<\sigma_k$ |
| HD2 | head capture for a projector pair | M | HD1, ST2T | Cor. 3.7 | frame of the row space of $\llbracket\mathbf P\mathbf A\rrbracket_L$ |
| ST3 | head split | M | PN3 | eq. (tri_ineq)–(tail-bound-projection-sp) | §2.4; `singularValues_le_singularValues_add_of_rank_le` |
| ST4 | ST3 with deficits, $p\ge2$ | M | ST3, HD2, SC1 | Thm 3.1 proof, case 2 | `schattenNorm_anti` ($\|\cdot\|_p\le\|\cdot\|_{\mathsf F}$) |
| CB3 | tail-count form, $2\le p<\infty$ | L | ST4, SP1, SV3 | Thm 3.1 proof | §2.4; arithmetic with $(1+\frac1p)^{p}\le e$ |

### Wave 2: singular values of sketches

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| RZ1 | filtered sketch, gap form | M | SV1 | MM Lemma 9 property 1 | head capture `singularValues_one_sub_rangeProjector_mul_mul_le` at the frame of $\llbracket\mathbf A\rrbracket_{i+1}$; $\|\mathbf M\|\le a\|\mathbf M_t\|$ by functional calculus on the tail |
| RZ2 | filtered sketch, cut form | L | — | MM Lemma 9 property 2 (eq. good_k_subspace) | §2.3; spectral projector of $\mathbf A\mathbf A^{\mathsf H}$ at $\tau^2$; Courant–Fischer |
| RZ3 | RBKI deficits, no gap | M | RZ1, RZ2, CH1, SV2 | Lemma 3.1, MM Thm 12, E15 | two cases on $\sigma_i^2\ge(1+\gamma)\sigma_k^2$ |
| RZ4 | RBKI deficits, gap | S | RZ1, SV2 | Lemma 3.2, MM Thm 13, E4, E10 | `exists_degree_lt_div_sq_le_exp_singularGapRatio` |
| RZ5 | Frobenius error of one truncated run | S | RZ3, ST2T | — | sum over $i<k$ |

### Wave 3: the sum of two Krylov spaces (deterministic)

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| TS0 | `rbkiSum`, `rbkiSum_def`, `rbkiSum_eq_rangeProjector`, `measurable_rbkiSum` | S | — | abstract ("multiple Krylov subspaces") | definitions; `measurable_rsvd` |
| TS1 | $\sigma_i(\mathsf{rbki})\le\sigma_i(\mathsf{rbkiSum})$, left and right | S | TS0, SV2 | — | `Matrix.fromCols` range |
| TS2 | Frobenius, deterministic | M | TS1, RZ3, RZ4, ST2T, SV3 | Thm 3.1 at $p=2$ | §2.6 |
| TS2m | `min` over the two runs, Frobenius | S | RZ3, RZ4, ST2T, SV3 | Algorithm 1.2 (sketch) | same proof without TS1 |
| TS3 | Schatten $1\le p\le2$, two-sided output | M | TS1, RZ3, RZ4, CB1 | Thm 3.1, $p\le2$ | $\mathbf P$ = range projector of $\llbracket\mathsf{rbkiSum}\rrbracket_k$ |
| TS4 | Schatten $2\le p<\infty$, deterministic, in terms of the residuals | L | TS1, RZ3, RZ4, CB3 | Thm 3.1, $p>2$ | §2.7; statement to be fixed with GA3 |

### Wave 4: Gaussian start blocks

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| GI1 | integrability of the `rbki`/`rbkiSum` errors (Frobenius, Schatten two-sided) | M | TS0 | — | bounded by $\|\mathbf A\|$, measurable (`measurable_truncatedSVD`, `measurable_rangeProjector`) |
| GA0 | one run, expectation | S | RZ5 | MM Thm 12 | `integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix` at $\mathbf S=(\mathbf A-\llbracket\mathbf A\rrbracket_k)\mathbf V_2$ |
| GA1 | Frobenius, expectation, closed form | M | TS2, GI1 | Thm 3.1 at $p=2$ | linearity; rank-deficient $\mathbf A$ as in `Gaussian/Filter.lean` (`filter_reduction`) |
| GA1p | Schatten $1\le p\le2$, expectation | M | TS3, SV4, GI1 | Thm 3.1, $p\le2$ | as GA1 |
| GA3 | Schatten $2\le p<\infty$, tail | L | TS4 | Thm 3.1 | §2.7 |

### Wave 5: headlines and asymptotic forms

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| GA2 | Frobenius headline at `Fin` sizes | M | GA1 | Thm 1.1 at $p=2$ | three terms $\le\varepsilon/3$; `Real.log`/`rpow` arithmetic |
| GA2p | Schatten $1\le p\le2$ headline | S | GA1p | Thm 1.1 | same arithmetic |
| GA4 | asymptotic form, Frobenius | M | GA1 | Thm 1.1 | `exists_forall_`; block sizes are free, so the oversampling ratio must be bounded: $\ell_1\ge2k+1$ and $\ell_2\ge C k\varepsilon^{-1/3}$ with $j$ chosen inside the proof |
| GA4p | asymptotic form, $1\le p\le2$ | S | GA1p | Thm 1.1 | as GA4 |
| GA3a | asymptotic form of GA3 | L | GA3 | Thm 1.1 | threshold $kp^{1/6}\varepsilon^{-1/3}\log(nkp/(\varepsilon\delta))$ |

Counts: S 19, M 19, L 5 (43). By wave: 0: 14, 1: 8, 2: 5, 3: 6, 4: 5, 5: 5. The Frobenius
headline GA2 is itself plus 15 targets, with no PN, SC, CB, HD or SP: CH1, SV1, SV2, SV3, ST2F,
ST2T, RZ1–RZ4, TS0, TS1, TS2, GI1, GA1 (RZ5, GA0, TS2m are by-products of the same chain).
Batch 1 (Frobenius and $1\le p\le2$) is 33 targets; batch 2 ($p>2$: SP1, HD1, HD2, ST3, ST4,
CB3, TS4, GA3, GA3a, PN4) is 10.

## 7. Shared proof machinery (item 7)

| Argument repeated | Handled by |
|---|---|
| unitary invariance of a gauge under $2\mathbf P-\mathbf I$ | existing `SymmetricGauge.matrixNorm_mul_of_mul_mul_conjTranspose_eq` and `matrixNorm_mul_left_of_hasOrthonormalCols`; PN1 is proved once and never unfolded again |
| $p$-th powers of Schatten norms as sums over a range | existing `schattenNorm_rpow` with `N` at least the rank; SV3, SV4 package the two tail estimates so that no later proof manipulates the sums |
| "deficit in squares to deficit in $p$-th powers" | SC1, once |
| Chebyshev value to $4e^{-8d\sqrt\gamma}$ | CH1, once; the constants $2\sqrt2$ and $3$ are two numeric lemmas next to RZ3 and TS2 ($8/\sqrt8=2\sqrt2$, $8(\sqrt2-1)>3$) |
| "the Krylov space contains the filtered sketch" | existing `range_mul_aeval_mul_le_range_mul_blockKrylovMatrix` + SV2 |
| frames of the row space of $\llbracket\mathbf A\rrbracket_t$, full row rank of $\mathbf Z^{\mathsf H}\mathbf\Omega$ almost surely, rank-deficient $\mathbf A$ | existing pattern of `LowRank/Gaussian/Filter.lean` (`exists_filter_residual`, `filter_reduction`); these are private there. Planned: make the frame existence a public lemma in wave 2 (part of RZ1's file) instead of repeating it in GA0, GA1, GA1p, GA3 |
| threshold arithmetic of the headlines ($\log$, $\varepsilon^{1/3}$) | `NLAlib/ForMathlib/Analysis/SpecialFunctions/Log/Basic.lean` has the pattern for the RBKI asymptotic forms; GA2 and GA2p share one private lemma "the three terms are at most $\varepsilon/3$" |
| measurability and integrability of outputs | GI1, once, before GA1 |

Mathlib searches recorded: Schatten norm: searched, none (library's own). Pinching: searched,
none. Courant–Fischer: searched, none (library's `Matrix/Spectral/CourantFischer.lean`).
Bernoulli for real exponents: found `one_add_mul_self_le_rpow_one_add`,
`rpow_one_add_le_one_add_mul_self`. Chebyshev outside $[-1,1]$: found
`Polynomial.Chebyshev.one_le_eval_T_real`; growth rate: library only. McCarthy trace inequality:
searched Mathlib and `NLAlib/Matrix/Functions`, none (`PosSemidef.schattenNorm_sub_rpow_le` is
the related Powers–Størmer-type bound for differences).

## 8. Routines later

Nothing here is a program. The planned consumption, in the order it becomes available:

1. **Today, with no new program**: the certified block Golub–Kahan program stores
   $\mathsf{rbki}(\mathbf A,\mathbf X,q)$ exactly (`BlockKrylov.storedOutput_eq_rbki`), so GA0
   and RZ3/RZ4-based tails transfer through `BlockKrylov.measureReal_not_accepts_le` and
   `integral_comp_storedOutput`.
2. **Two runs and a choice** (TS2m): two certified runs, truncate each to rank $k$, keep the
   one with the larger $\|\llbracket\cdot\rrbracket_k\|_{\mathsf F}$. This needs a small-SVD
   leaf on the stored bidiagonal factors and one comparison; the mathematics is CB2/TS2m, and
   for the Frobenius norm the choice is exact. For $p\ne2$ no computable exact criterion is
   proved (the paper's estimated-singular-value test is E2, E8, E14); the routine would use
   `rbkiSum`.
3. **`rbkiSum` as a program**: one orthonormal basis for the sum of the two Krylov spaces. The
   existing orthogonalization contract (`LowRank-BlockLanczos.md` §3.1a: extend a stored basis
   by a block) covers it if the second run orthogonalizes against the first run's basis; the
   block recurrence is then no longer a block bidiagonalization, so the stored factor is a
   general projected matrix $\mathbf Q^{\mathsf H}\mathbf A$. Open (decision ROUTINE-FORM).

**Tolerance to inexact steps.** The structural layer is stated so that an inexact inner step
changes hypotheses, not theorems:

* *A larger subspace is harmless.* Deficits are monotone (SV2): any $\mathcal K$ containing
  the two Krylov spaces has the guarantee. A routine that keeps extra directions (breakdown
  handling, deflation, restart vectors) needs no new mathematics.
* *An inexact best rank-$k$ within the subspace.* ST1–ST4, CB1–CB3 take *any* projector
  $\mathbf P$ and are quantitative in the deficits of $\mathbf P\mathbf A$. If the small SVD
  returns $\mathbf P'$ with $\sigma_i(\mathbf P'\mathbf A)^2\ge\sigma_i(\mathbf P_{\mathcal K}
  \mathbf A)^2-\eta\sigma_k^2$, the theorems apply with $\gamma+\eta$. For the Frobenius norm,
  ST2F holds for every $\mathbf P'$ of rank at most $k$, exact Ritz vectors or not.
* *An inexact $\mathbf Q$.* The hypothesis is $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$,
  an exact inclusion of the row space of $\mathbf P\mathbf A$ in the range of $\mathbf Q$. An
  orthonormalization with errors still spans the same space, so the *projector* is exact even
  when the stored basis is not orthonormal. If $\mathbf A^{\mathsf H}\mathbf W$ itself is
  computed with error $\mathbf E$ the inclusion fails; then
  $\|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|\le\|\mathbf E\|$ and ST1 needs a perturbed form.
  **Not planned; flagged** (decision INEXACT-Q): a version of ST1/ST3 with
  $\|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|_p\le\eta$ in place of the equation costs one
  triangle inequality in ST3 but in ST1 it loses the $p$-th power structure.
* *Rounded matrix–vector products and loss of orthogonality* change the Krylov space itself.
  RZ1–RZ4 are for exact filtered sketches. The existing backward model for the block program
  (`LowRank-BlockLanczos.md` §4.4, a run on $\mathbf A+\mathbf E$) composes with every theorem
  here because they are stated for an arbitrary matrix; what is missing is the same thing that
  is missing for RBKI (their obstacle BL8), not something specific to this stage.
* *Output as a perturbation.* A returned $\mathbf B$ with
  $\|\mathbf B-\llbracket\mathsf{rbkiSum}\rrbracket_k\|\le\eta$ costs $\eta$ by
  `schattenNorm_add_le`; no statement is needed.

## 9. Risks and open questions (item 8)

### Risks

* **RZ2 is new as a statement** (it is Musco–Musco's property 2 reorganized so that the filter
  cut is a parameter). The proof is short on paper but uses spectral projectors of
  $\mathbf A\mathbf A^{\mathsf H}$ against a frame that is only assumed to contain the top
  $i+1$ right singular vectors; ties $\sigma_{i}=\sigma_{i+1}$ make "the top $i+1$ directions" a
  choice, fixed here by `truncatedSVD`. Size L for that reason. If it fails as stated, the
  fallback hypothesis is $\mathbf A\mathbf Z\mathbf Z^{\mathsf H}=\llbracket\mathbf A\rrbracket_k$
  (which RZ3 has anyway).
* **CB3, TS4, GA3 ($p>2$) are the research-grade part.** The chain SP1 → HD2 → ST4 → CB3
  replaces the paper's argument at E9 and E12; it was checked by hand and numerically on random
  instances of size up to $10$ (ST3, HD2, SP1 individually), but the composite constants of GA3
  have not been machine-checked in any way. TS4's exact statement is deliberately left to be
  fixed together with GA3 (it is not in Appendix A); what could be false there is a constant,
  not the rate.
* **GA1p/GA2p integrate a function of `rangeProjector (truncatedSVD ·)ᴴ`.** Measurability is
  available; if integrability (GI1) is harder than expected the fallback is the tail form by
  Markov on the residuals, as in GA3. A Bochner integral of a non-integrable function is $0$, so
  GA1p without GI1 would be a vacuous statement: GI1 is listed before it for that reason.
* **Junk values.** `singularValues A k ^ (p.toReal - 2)` at $\sigma_k=0$, $p<2$ is $0$ in
  Lean; TS3 and SV4 were checked against this (when $\sigma_k=0$ the residuals vanish).
  `Real.log (12 * k / ε)` is positive for $k\ge1$, $\varepsilon\le1$. `singularGapRatio` is $0$
  when $\sigma_h=0$. In GA3, $\Lambda_i>0$ needs $n\ge1$ and $\delta\le1$; for $\delta>1$ the
  statement is trivial and for an empty column type the error is $0$.
* **What is not claimed.** No statement for block size $k$ exactly (BCW's block; the square
  Gaussian block has no inverse second moment), none for $p=\infty$ (use
  `BlockKrylovGapless`), none for $p<1$. The bound for $p\in(1,2)$ is for the two-sided output
  only. Musco–Musco's Frobenius theorem at depth $\varepsilon^{-1/2}$ is not a by-product.

### Open questions, with recommendations

| Id | Question | Recommendation |
|---|---|---|
| SCOPE-NORMS | Frobenius only; Schatten $1\le p\le2$; or all $1\le p<\infty$? | All three planned, in two batches: Frobenius and $p\le2$ first (33 targets, expectation form, dimension-free); $p>2$ second (SP1, HD1, HD2, ST3, ST4, CB3, TS4, GA3, GA3a, PN4) after the first batch's statements have survived proof |
| SCOPE-LB | Lower bound $\Omega(\varepsilon^{-1/3})$ in this stage? | No. It needs the Wishart smallest-eigenvalue hardness of Braverman et al. (not in the library; cut earlier as R4) and belongs to the lower-bound track (stage C of `MatvecLowerBounds`), where Zhang et al.'s $\Omega(k\varepsilon^{-1/3})$ is the stronger target |
| SELECT | One projector on the sum of the Krylov spaces, or the paper's choice between two runs? | Sum as the headline; `min` forms CB2, TS2m as corollaries |
| OUTPUT | Frobenius headline for $\llbracket\mathsf{rbkiSum}\rrbracket_k$ (one-sided, the usual RBKI output) or for $\mathbf A\mathbf Q$ (BCW's)? | One-sided for Frobenius (identity ST2F, no extra products); two-sided for $p\ne2$, where it is needed for $p<2$ |
| ONE-SIDED | Add PN4 and the one-sided statements for $p\ge2$? | Yes for PN4 (S–M, independent interest); one-sided corollaries only if a routine wants them |
| PROB-FORM | Expectation of the squared error (dimension-free, $\log(k/\varepsilon)$) with oversampled blocks $2k+1$, or BCW's "probability $9/10$" with block $k$ and $\log(d/\varepsilon)$? | Expectation, as the RBKI files; tail by Markov left to consumers; tail form only for $p>2$ |
| BLOCK-K | Also cover block size exactly $k$ (and $k+j$)? | Not now: needs a tail bound for the inverse of a square Gaussian matrix in the form $\mathbb P[\|\mathbf G^{-1}\|>t]$; a follow-up, with BL-stage small-block results |
| CONSTANTS | Constants written out ($4$, $2\sqrt2$, $3$, $6$, $12$) or named bounds with registry entries? | Written out: they are Chebyshev values in readable form [B6] and thresholds of a headline; no consumer inverts them |
| FIELD | `RCLike 𝕜` for waves 0–3, ℝ for Gaussian? | Yes (library convention) |
| CHEB-GENERAL | Generalize `exists_degree_lt_div_sq_le_exp_singularGapRatio` from ℝ to `𝕜` (merged statement) | Yes; otherwise RZ4 is real only |
| MM-FROB | Also formalize Musco–Musco's Frobenius bound at depth $O(\log/\sqrt\varepsilon)$ (their Property 3)? | Not in this stage; GA0 is the per-rank form. Record as a candidate: it is the natural Frobenius twin of `BlockKrylovGapless` |
| SINGLE-RUN | Bakshi–Narayanan's single run (one block, depth $\varepsilon^{-1/3}$, simulated wide block)? | Later: by `rbki_blockKrylovMatrix` the single run contains `rbkiSum` of simulated blocks, so CB1 applies verbatim; the missing input is the conditioning of the simulated block (the BL-stage Vandermonde bound, which needs a head gap) |
| CORANGE-NAME | Name the two-sided output $\mathbf A\mathbf P_{\mathrm{row}(\mathbf B)}$? | No definition now; revisit when the routine exists |
| NAME | `rbkiSum`, $\mathsf{rbkiSum}$ | Accept, or give the name you want |
| INEXACT-Q | Perturbed form of ST1 ($\|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|\le\eta$)? | Not planned until a routine shows it is needed |
| ROUTINE-FORM | Routine as two runs and a choice (Frobenius), or one basis for the sum? | Decide at the routine stage; both are covered by this stage's statements |

## 10. Material (item 6)

Read: the three papers of §1; library files of §0; `LowRank-BlockLanczos.md`,
`Matrix-GaugeAndSchattenNorms.md`, `Headline-Statements.md`. Reused as mathematics: BCW Lemma
3.3 (generalized), Lemma 3.5/Corollary 3.7 (as HD1), the head/tail split; Musco–Musco Lemma 9
properties 1 and 2 (as RZ1, RZ2), Theorem 13 (RZ4). Reused as proof material: the library's
head capture and Chebyshev growth. Deliberately not reproduced: BCW's rotation-to-block-matrix
proof of Lemma 3.3 (PN1 is two lines without bases); Lemma 3.4's use of Ritz vectors (hypotheses
are on singular values); Lemma 3.6 (not needed); the singular value estimates and the selection
rule of Algorithm 3.2 (E2, E14); `transpose` twins (BCW run Krylov on $\mathbf A^{\mathsf T}$;
the library's `rbki` already projects on the left).

## Appendix A. Lean statements

### A.0 Check

The file below was elaborated with `lake env lean` against the build of `origin/main` @
`edb7e0ee` (toolchain `leanprover/lean4:v4.33.1`) on 2026-11-20: no error; every declaration
reports only "declaration uses `sorry`" (and one unused-section-variable linter note on
`rbkiSum_def`). It lives in an untracked `scratch/` directory of the worktree and is reproduced
here verbatim; it adds nothing under `NLAlib/`. Comments `-- ID` give the target ids of §6.
Not stated: TS4 and GA3a (§9, risks). Names follow the naming guide as far as the design agent
could judge and are to be reviewed with the skeleton; implicit instance arguments will be
trimmed per declaration (`omit … in`) there.

```lean
import NLAlib.LowRank.Gaussian.SmallBlock
import NLAlib.Matrix.Norms.SchattenPowers
import NLAlib.RandomMatrix.Gaussian.BlockTail

/-! Scratch statements for the LRA-CUBE-ROOT design note. Every proof is `sorry`; this file only
checks that the statements elaborate. Not part of the library. -/

open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix ENNReal

namespace NLAlib

/-! ## Wave 0: shared machinery -/

-- SC1
theorem _root_.Real.rpow_sub_rpow_le_max_mul {a b r : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (hr : 0 < r) :
    a ^ r - b ^ r ≤ max 1 r * a ^ (r - 1) * (a - b) := sorry

-- CH1
theorem exists_degree_lt_div_sq_le_exp_of_le {s τ : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) (hs : 0 < s)
    (d : ℕ) :
    ∃ f : ℝ[X], f.degree < (d + 1 : ℕ) ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ x, s ^ 2 ≤ x → c ≤ |f.eval x|) ∧
      (∀ x ∈ Set.Icc 0 (τ ^ 2), |f.eval x| ≤ a) ∧
      (a / c) ^ 2 ≤ 4 * Real.exp (-8 * (d : ℝ) * Real.sqrt ((s - τ) / (s + τ))) := sorry

section Det

variable {𝕜 : Type*} [RCLike 𝕜] {l l₁ l₂ m n s s₁ s₂ : Type*} [Fintype l] [Fintype l₁] [Fintype l₂]
  [Fintype m] [Fintype n] [Fintype s] [Fintype s₁] [Fintype s₂] [DecidableEq m] [DecidableEq n]
  [DecidableEq s] [DecidableEq s₁] [DecidableEq s₂]

-- PN1
theorem SymmetricGauge.matrixNorm_mul_mul_add_one_sub_mul_mul_one_sub_le (Φ : SymmetricGauge)
    {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (A : Matrix m n 𝕜) :
    Φ.matrixNorm (P * A * Q + (1 - P) * A * (1 - Q)) ≤ Φ.matrixNorm A := sorry

-- PN2
theorem schattenNorm_add_rpow_of_conjTranspose_mul_eq_zero_of_mul_conjTranspose_eq_zero
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤) {X Y : Matrix m n 𝕜} (h₁ : Xᴴ * Y = 0)
    (h₂ : X * Yᴴ = 0) :
    schattenNorm p (X + Y) ^ p.toReal =
      schattenNorm p X ^ p.toReal + schattenNorm p Y ^ p.toReal := sorry

-- PN3
theorem _root_.IsStarProjection.schattenNorm_mul_mul_rpow_add_le {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (A : Matrix m n 𝕜) :
    schattenNorm p (P * A * Q) ^ p.toReal + schattenNorm p ((1 - P) * A * (1 - Q)) ^ p.toReal ≤
      schattenNorm p A ^ p.toReal := sorry

-- PN4
theorem _root_.IsStarProjection.schattenNorm_mul_rpow_add_le {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P) (A : Matrix m n 𝕜) :
    schattenNorm p (P * A) ^ p.toReal + schattenNorm p ((1 - P) * A) ^ p.toReal ≤
      schattenNorm p A ^ p.toReal := sorry

-- SV1
theorem _root_.IsStarProjection.sq_singularValues_sub_sq_specNorm_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (i : ℕ) :
    singularValues A i ^ 2 - specNorm ((1 - P) * truncatedSVD A (i + 1)) ^ 2 ≤
      singularValues (P * A) i ^ 2 := sorry

-- SV2
omit [DecidableEq n] [DecidableEq s] in
theorem singularValues_rangeProjector_mul_le_of_range_le {Y : Matrix m l 𝕜} {Y' : Matrix m s 𝕜}
    (h : LinearMap.range Y'.mulVecLin ≤ LinearMap.range Y.mulVecLin) (A : Matrix m n 𝕜) (i : ℕ) :
    singularValues (rangeProjector Y' * A) i ≤ singularValues (rangeProjector Y * A) i := sorry

-- SV3
theorem mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ⊤) (A : Matrix m n 𝕜) (k j : ℕ) :
    ((j : ℝ) + 1) * singularValues A (k + j) ^ p.toReal ≤
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- SV4
theorem singularValues_rpow_mul_frobNorm_sub_truncatedSVD_sq_le {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) (A : Matrix m n 𝕜) (k : ℕ) :
    singularValues A k ^ (p.toReal - 2) * frobNorm (A - truncatedSVD A k) ^ 2 ≤
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- SP1
theorem exists_le_singularValues_le_and_gap (A : Matrix m n 𝕜) (k : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ L ≤ k, singularValues A L ≤ (1 + 1 / p) * singularValues A k ∧
      ∀ h, h + 1 = L → (1 + 1 / (2 * p)) * singularValues A k < singularValues A h ∧
        singularValues A L ^ 2 ≤ (1 - 1 / (2 * k * (p + 1))) * singularValues A h ^ 2 := sorry

-- HD1
theorem HasOrthonormalCols.mul_frobNorm_truncatedSVD_sub_mul_sq_le {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (A : Matrix m n 𝕜) {h L : ℕ} (hL : h + 1 = L)
    (hcard : Fintype.card s ≤ L) {θ η : ℝ}
    (hgap : singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hη : ∑ i ∈ Finset.range L, singularValues A i ^ 2 - η ≤ frobNorm (A * Z) ^ 2) :
    θ * frobNorm (truncatedSVD A L - truncatedSVD A L * Z * Zᴴ) ^ 2 ≤ η := sorry

/-! ## Wave 1: structural theorems for a pair of projectors -/

-- ST1
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_add_le {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) :
    schattenNorm p (A - A * Q) ^ p.toReal + schattenNorm p (P * A) ^ p.toReal ≤
      schattenNorm p A ^ p.toReal := sorry

-- ST2
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) (k : ℕ) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤ schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
      ∑ i ∈ Finset.range k,
        (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal) := sorry

-- ST2F
theorem _root_.IsStarProjection.frobNorm_sub_mul_sq_eq_add_sum {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) {k : ℕ} (hk : P.rank ≤ k) :
    frobNorm (A - P * A) ^ 2 = frobNorm (A - truncatedSVD A k) ^ 2 +
      ∑ i ∈ Finset.range k, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

-- ST2T
theorem _root_.IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (P * A) k) ^ 2 = frobNorm (A - truncatedSVD A k) ^ 2 +
      ∑ i ∈ Finset.range k, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

-- CB1 (tail-count form, 1 ≤ p ≤ 2)
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_of_sq_singularValues_sub_le
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) {k j : ℕ} {γ κ : ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤
      (1 + k * γ * κ ^ p.toReal / ((j : ℝ) + 1)) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- CB2 (two candidates, 1 ≤ p ≤ 2)
theorem min_schattenNorm_sub_mul_rpow_le_of_sq_singularValues_sub_le
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P₁ P₂ : Matrix m m 𝕜} {Q₁ Q₂ : Matrix n n 𝕜}
    (hP₁ : IsStarProjection P₁) (hQ₁ : IsStarProjection Q₁) (hP₂ : IsStarProjection P₂)
    (hQ₂ : IsStarProjection Q₂) {A : Matrix m n 𝕜} (h₁ : P₁ * A * Q₁ = P₁ * A)
    (h₂ : P₂ * A * Q₂ = P₂ * A) {k j : ℕ} {γ₁ γ₂ κ : ℝ} (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂) (hκ : 0 ≤ κ)
    (hritz₁ : ∀ i < k, singularValues A i ^ 2 - γ₁ * singularValues A k ^ 2 ≤
      singularValues (P₁ * A) i ^ 2)
    (hritz₂ : κ * singularValues A (k + j) < singularValues A k →
      ∀ i < k, singularValues A i ^ 2 - γ₂ * singularValues A k ^ 2 ≤
        singularValues (P₂ * A) i ^ 2) :
    min (schattenNorm p (A - A * Q₁) ^ p.toReal) (schattenNorm p (A - A * Q₂) ^ p.toReal) ≤
      (1 + k * max (γ₁ * κ ^ p.toReal / ((j : ℝ) + 1)) γ₂) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- HD2
theorem _root_.IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le {P : Matrix m m 𝕜}
    {Q : Matrix n n 𝕜} (hP : IsStarProjection P) (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) {h L : ℕ} (hL : h + 1 = L) {θ : ℝ}
    (hgap : singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2) :
    θ * frobNorm (truncatedSVD A L - truncatedSVD A L * Q) ^ 2 ≤
      ∑ i ∈ Finset.range L, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

-- ST3
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_two_mul_add_rpow {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) {L k : ℕ}
    (hLk : L ≤ k) :
    schattenNorm p (A - A * Q) ≤
      2 * schattenNorm p (truncatedSVD A L - truncatedSVD A L * Q) +
        (schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
          ∑ i ∈ Finset.Ico L k,
            (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal)) ^
          p.toReal⁻¹ := sorry

-- ST4
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_of_sq_singularValues_sub_le
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) {L k : ℕ} (hLk : L ≤ k) {δ γ θ κ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hθ : 0 < θ) (hκ : 1 ≤ κ)
    (hgap : ∀ h, h + 1 = L → singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hflat : singularValues A L ≤ κ * singularValues A k)
    (hhead : ∀ i < L, singularValues A i ^ 2 - δ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2)
    (hmid : ∀ i, L ≤ i → i < k → singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - A * Q) ≤
      2 * Real.sqrt (L * δ / θ) * singularValues A k +
        (schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
          p.toReal / 2 * κ ^ (p.toReal - 2) * ((k : ℝ) - L) * γ *
            singularValues A k ^ p.toReal) ^ p.toReal⁻¹ := sorry

-- CB3 (tail-count form, 2 ≤ p < ∞)
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_mul_of_sq_singularValues_sub_le
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) {k j : ℕ} {δ γ κ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hhead : ∀ i < k, (1 + 1 / (2 * p.toReal)) * singularValues A k < singularValues A i →
      singularValues A i ^ 2 - δ * singularValues A k ^ 2 ≤ singularValues (P * A) i ^ 2)
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - A * Q) ≤
      (2 * k * Real.sqrt (2 * (p.toReal + 1) * δ) +
        (1 + Real.exp 1 * (p.toReal / 2) * k * γ * κ ^ p.toReal / ((j : ℝ) + 1)) ^ p.toReal⁻¹) *
        schattenNorm p (A - truncatedSVD A k) := sorry

/-! ## Wave 2: singular values of filtered sketches and of RBKI -/

-- RZ1
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rsvd_cfc
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {t : ℕ}
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {i : ℕ} (hi : i < t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |g x| ≤ a) :
    singularValues A i ^ 2 -
        (a / c) ^ 2 * specNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := sorry

-- RZ2
theorem HasOrthonormalCols.sq_sub_le_sq_singularValues_rsvd_cfc
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {i : ℕ}
    (hAZ : truncatedSVD A (i + 1) * Z * Zᴴ = truncatedSVD A (i + 1)) {c a τ : ℝ} (hc : 0 < c)
    (hτ : 0 ≤ τ) (hτi : τ ≤ singularValues A i)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (τ ^ 2), |g x| ≤ a) :
    τ ^ 2 - (a / c) ^ 2 * specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := sorry

-- RZ3
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {k : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A k) {q : ℕ}
    (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) {i : ℕ} (hi : i < k) :
    singularValues A i ^ 2 - γ * singularValues A k ^ 2 -
        4 * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rbki A Ω q) i ^ 2 := sorry

-- RZ4
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki_singularGapRatio
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {q : ℕ} (hq : 1 ≤ q) {i : ℕ} (hi : i < r) :
    singularValues A i ^ 2 -
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          specNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rbki A Ω q) i ^ 2 := sorry

-- RZ5
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {k : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A k) {q : ℕ}
    (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    frobNorm (A - truncatedSVD (rbki A Ω q) k) ^ 2 ≤
      frobNorm (A - truncatedSVD A k) ^ 2 + k * γ * singularValues A k ^ 2 +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2 := sorry

/-! ## Wave 3: the sum of two block Krylov spaces -/

/-- RBKI on the sum of two block Krylov spaces. -/
noncomputable def rbkiSum (A : Matrix m n 𝕜) (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜)
    (q₁ q₂ : ℕ) : Matrix m n 𝕜 :=
  rsvd A (Matrix.fromCols (blockKrylovMatrix (Aᴴ * A) Ω₁ q₁) (blockKrylovMatrix (Aᴴ * A) Ω₂ q₂))

-- TS0
theorem rbkiSum_def (A : Matrix m n 𝕜) (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜) (q₁ q₂ : ℕ) :
    rbkiSum A Ω₁ Ω₂ q₁ q₂ = rsvd A (Matrix.fromCols (blockKrylovMatrix (Aᴴ * A) Ω₁ q₁)
      (blockKrylovMatrix (Aᴴ * A) Ω₂ q₂)) := rfl

theorem rbkiSum_eq_rangeProjector (A : Matrix m n 𝕜) (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜)
    (q₁ q₂ : ℕ) :
    rbkiSum A Ω₁ Ω₂ q₁ q₂ = rangeProjector (Matrix.fromCols
      (blockKrylovMatrix (A * Aᴴ) (A * Ω₁) q₁) (blockKrylovMatrix (A * Aᴴ) (A * Ω₂) q₂)) * A :=
  sorry

-- TS1
theorem singularValues_rbki_le_singularValues_rbkiSum_left (A : Matrix m n 𝕜)
    (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜) (q₁ q₂ i : ℕ) :
    singularValues (rbki A Ω₁ q₁) i ≤ singularValues (rbkiSum A Ω₁ Ω₂ q₁ q₂) i := sorry

theorem singularValues_rbki_le_singularValues_rbkiSum_right (A : Matrix m n 𝕜)
    (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜) (q₁ q₂ i : ℕ) :
    singularValues (rbki A Ω₂ q₂) i ≤ singularValues (rbkiSum A Ω₁ Ω₂ q₁ q₂) i := sorry

-- TS2
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbkiSum_sq_le
    {A : Matrix m n 𝕜} {Ω₁ : Matrix n l₁ 𝕜} {Ω₂ : Matrix n l₂ 𝕜} {Z₁ : Matrix n s₁ 𝕜}
    {Z₂ : Matrix n s₂ 𝕜} (hZ₁ : HasOrthonormalCols Z₁) (hZ₂ : HasOrthonormalCols Z₂)
    (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank) (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j : ℕ} (hk : 0 < k)
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    frobNorm (A - truncatedSVD (rbkiSum A Ω₁ Ω₂ q₁ q₂) k) ^ 2 ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1)) * frobNorm (A - truncatedSVD A k) ^ 2 +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 +
        4 * k * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          specNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2 := sorry

-- TS2m
theorem HasOrthonormalCols.min_frobNorm_sub_truncatedSVD_rbki_sq_le
    {A : Matrix m n 𝕜} {Ω₁ : Matrix n l₁ 𝕜} {Ω₂ : Matrix n l₂ 𝕜} {Z₁ : Matrix n s₁ 𝕜}
    {Z₂ : Matrix n s₂ 𝕜} (hZ₁ : HasOrthonormalCols Z₁) (hZ₂ : HasOrthonormalCols Z₂)
    (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank) (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j : ℕ} (hk : 0 < k)
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    min (frobNorm (A - truncatedSVD (rbki A Ω₁ q₁) k) ^ 2)
        (frobNorm (A - truncatedSVD (rbki A Ω₂ q₂) k) ^ 2) ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1)) * frobNorm (A - truncatedSVD A k) ^ 2 +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 +
        4 * k * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          specNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2 := sorry

-- TS3
theorem HasOrthonormalCols.schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {A : Matrix m n 𝕜} {Ω₁ : Matrix n l₁ 𝕜} {Ω₂ : Matrix n l₂ 𝕜} {Z₁ : Matrix n s₁ 𝕜}
    {Z₂ : Matrix n s₂ 𝕜} (hZ₁ : HasOrthonormalCols Z₁) (hZ₂ : HasOrthonormalCols Z₂)
    (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank) (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j : ℕ} (hk : 0 < k)
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    schattenNorm p (A - A * rangeProjector (truncatedSVD (rbkiSum A Ω₁ Ω₂ q₁ q₂) k)ᴴ) ^ p.toReal ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1)) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        4 * k * singularValues A k ^ (p.toReal - 2) *
          (Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
              specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 +
            Real.exp (-3 * ((q₂ : ℝ) - 1)) *
              specNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2) := sorry

end Det

/-! ## Wave 4: Gaussian start blocks -/

section Gaussian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l₁ l₂ : Type*} [Fintype m]
  [Fintype n] [Fintype l₁] [Fintype l₂] [DecidableEq m] [DecidableEq n]
  {X₁ : Ω → Matrix n l₁ ℝ} {X₂ : Ω → Matrix n l₂ ℝ}

-- GI1
theorem integrable_frobNorm_sub_truncatedSVD_rbkiSum_sq [IsFiniteMeasure μ] (A : Matrix m n ℝ)
    (hX₁ : AEMeasurable X₁ μ) (hX₂ : AEMeasurable X₂ μ) (k q₁ q₂ : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2) μ :=
  sorry

theorem integrable_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (A : Matrix m n ℝ) (hX₁ : AEMeasurable X₁ μ) (hX₂ : AEMeasurable X₂ μ)
    (k q₁ q₂ : ℕ) :
    Integrable (fun ω => schattenNorm p (A - A * rangeProjector
      (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal) μ := sorry

-- GA0 (by-product: per-rank Frobenius bound for one RBKI run)
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X₁ (gaussianMatrix n l₁) μ) {k q : ℕ}
    (hk : k + 2 ≤ Fintype.card l₁) (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X₁ ω) q) k) ^ 2 ∂μ ≤
      (1 + 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1))) * frobNorm (A - truncatedSVD A k) ^ 2 +
        k * γ * singularValues A k ^ 2 := sorry

-- GA1 (general, Frobenius, expectation)
theorem integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ} (hk : 0 < k)
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2 ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * k * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- GA1p (general, Schatten 1 ≤ p ≤ 2, expectation)
theorem integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ} (hk : 0 < k)
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * k * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- GA3 (tail form, 2 ≤ p < ∞)
theorem measureReal_schattenNorm_sub_mul_rangeProjector_rbkiSum_gt_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ} (hk : 0 < k)
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hj : Real.exp 2 * k / (ε * p.toReal) ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + (p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) + Real.sqrt (4 * p.toReal + 1) / 8) *
      Real.log (256 * k ^ 3 * (p.toReal + 1) * Fintype.card n / (ε ^ 2 * δ)) ≤ q₁)
    (hq₂ : 1 + Real.sqrt (4 * p.toReal + 1) / 8 *
      Real.log (256 * k ^ 2 * ((k : ℝ) + j) * (p.toReal + 1) * Fintype.card n / (ε ^ 2 * δ)) ≤
        q₂) :
    μ.real {ω | (1 + ε) * schattenNorm p (A - truncatedSVD A k) <
      schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ)} ≤ δ := sorry

end Gaussian

/-! ## Headlines at natural-number sizes -/

-- GA2 (headline, Frobenius)
theorem integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n k j q₁ q₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) {X₁ : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (2 * (k + j) + 1)) ℝ}
    (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (2 * (k + j) + 1))) μ) (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hj : 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + Real.log (12 * k / ε) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + Real.log (12 * k / ε) / 3 ≤ q₂) :
    ∫ ω, frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- GA2p (headline, Schatten 1 ≤ p ≤ 2)
theorem
    integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n k j q₁ q₂ : ℕ} {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : Matrix (Fin m) (Fin n) ℝ) {X₁ : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (2 * (k + j) + 1)) ℝ}
    (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (2 * (k + j) + 1))) μ) (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hj : 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + Real.log (12 * k / ε) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + Real.log (12 * k / ε) / 3 ≤ q₂) :
    ∫ ω, schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- GA4 (asymptotic form, Frobenius)
theorem exists_forall_integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l₁ l₂ : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq n] [Fintype l₁] [Fintype l₂] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X₁ : Ω → Matrix n l₁ ℝ) (X₂ : Ω → Matrix n l₂ ℝ) (k q₁ q₂ : ℕ) (ε : ℝ),
      HasLaw X₁ (gaussianMatrix n l₁) μ → HasLaw X₂ (gaussianMatrix n l₂) μ → 0 < k → 0 < ε →
      ε ≤ ε₀ → 2 * k + 1 ≤ Fintype.card l₁ → C * (k / ε ^ (3 : ℝ)⁻¹) ≤ Fintype.card l₂ →
      C * (Real.log (k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁ → C * Real.log (k / ε) ≤ q₂ →
      ∫ ω, frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- GA4p (asymptotic form, Schatten 1 ≤ p ≤ 2)
theorem
    exists_forall_integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l₁ l₂ : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq m] [DecidableEq n] [Fintype l₁] [Fintype l₂] (μ : Measure Ω)
      (A : Matrix m n ℝ) (X₁ : Ω → Matrix n l₁ ℝ) (X₂ : Ω → Matrix n l₂ ℝ) (k q₁ q₂ : ℕ) (ε : ℝ)
      (p : ℝ≥0∞),
      HasLaw X₁ (gaussianMatrix n l₁) μ → HasLaw X₂ (gaussianMatrix n l₂) μ → 1 ≤ p → p ≤ 2 →
      0 < k → 0 < ε → ε ≤ ε₀ → 2 * k + 1 ≤ Fintype.card l₁ →
      C * (k / ε ^ (3 : ℝ)⁻¹) ≤ Fintype.card l₂ →
      C * (Real.log (k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁ → C * Real.log (k / ε) ≤ q₂ →
      ∫ ω, schattenNorm p (A - A * rangeProjector
          (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
        (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

end NLAlib
```
