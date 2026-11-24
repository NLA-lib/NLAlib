# Low-rank approximation with $\varepsilon^{-1/3}$ products: two block Krylov spaces

2026-11-20. Design note; **status: design only, revised after one independent review (§11),
awaiting the maintainer's decisions (§9). Nothing is proved and there is no skeleton.** Branch `design/lra-cube-root` from `origin/main` @
`edb7e0ee`. Stage LRA-CUBE-ROOT, board card T150. Targets: harness
`pilot/lra-cube-root-targets.json`. Decision sheet: harness `state/decisions/LRA-CUBE-ROOT.json`
(ids below); review: harness `reports/Review-Fable-LRA-CUBE-ROOT-Design.md`. Every Lean
statement in Appendix A elaborated, with `sorry` proofs, against the
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
  general theorems are stated for any sketch whose range contains the two Krylov sketches, and
  `rbkiSum` is an instance. The paper's choose-one form is kept as a corollary with `min`
  (decision SELECT).
* **Layering, as for RBKI** (§2). (1) Matrix analysis for a pair of projectors
  $\mathbf P,\mathbf Q$ with $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$: error of
  $\mathbf A\mathbf Q$ from the *singular value deficits*
  $\sigma_i(\mathbf A)^2-\sigma_i(\mathbf P\mathbf A)^2$, $i<k$, absolute errors $\beta_i$
  and a count of tail singular values; for $p\ge2$ the same for the usual one-sided output
  $\mathbf P\mathbf A$, with no $\mathbf Q$. No Krylov space, no randomness; any sketch can
  plug in. (2) Deterministic bounds for
  the deficits of a filtered sketch and of `rbki`, in terms of the library's sketch residual
  $(\mathbf A-\llbracket\mathbf A\rrbracket_t)\mathbf\Omega(\mathbf Z^{\mathsf H}\mathbf\Omega)^+$.
  (3) Gaussian start blocks.
* **The needed black box is not in the library.** The library has no bound on individual
  singular values of `rbki` (Musco–Musco's per-vector guarantee) and no gapless Frobenius bound
  for truncated RBKI. §2.3 plans the deficit bound directly (targets RZ1–RZ4, RZ4F); it is a
  one-page argument on a Rayleigh quotient and reuses the existing head capture and Chebyshev
  filter. A by-product is a gapless Frobenius bound for one RBKI run (GA0).
* **Headline (planned, Frobenius), constants explicit, no dependence on the dimensions.** For
  Gaussian $\mathbf X_1$ with $2k+1$ columns and $\mathbf X_2$ with $2(k+j)+1$ columns (any
  joint law), $0<\varepsilon\le1$, $j+1\ge 6k\varepsilon^{-1/3}$,
  $q_1\ge1+\log(12k/\varepsilon)/(2\sqrt2\,\varepsilon^{1/3})$ and
  $q_2\ge1+\log(12/\varepsilon)/3$,
  $$\mathbb E\,\|\mathbf A-\llbracket\mathsf{rbkiSum}(\mathbf A,\mathbf X_1,\mathbf X_2,q_1,q_2)
  \rrbracket_k\|_{\mathsf F}^2\le(1+\varepsilon)\,
  \|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2 .$$
  That is $O(k\varepsilon^{-1/3}\log(k/\varepsilon))$ products: the logarithm is of
  $k/\varepsilon$, not of the dimension (BCW have $\log(d/\varepsilon)$; Bakshi–Narayanan
  2023 remove $\log d$ for $k=1$ by a different route). The same statement with the same
  constants holds for $\|\cdot\|_{S_p}^p$, $1\le p\le2$, for the two-sided output
  $\mathbf A\mathbf Q$ (GA2p). For $2\le p<\infty$ the planned form is a tail bound for the
  one-sided output with $\log(\min(m,n)kp/(\varepsilon\delta))$ and BCW's $p^{1/6}$ (GA3).
* **Size.** 52 targets: S 29, M 20, L 3, in waves 0–5 (§6); batch 1 (Frobenius, $p\le2$) 44,
  batch 2 ($p>2$) 8. Waves 0–3 are deterministic. The Frobenius headline needs 17 of them (no
  pinching, no Schatten norm).
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

Also present, and used (the first version of this note missed the first): McCarthy's trace
inequality `Matrix.PosSemidef.re_trace_rpow_add_le`; Gu's projected form
`frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`; frames of the top
right singular subspace `exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal`;
`ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix`; `le_singularValues_of_forall_mem`.

**Missing** (each is a target): pinching and orthogonal sums in Schatten norms; lower bounds on
individual singular values of `rsvd`/`rbki`; monotonicity of
$\sigma_i(\mathbf P_{\mathbf Y}\mathbf A)$ in the range of $\mathbf Y$ (the library has it only
for $\mathbf A-\mathbf P_{\mathbf Y}\mathbf A$); a public moment lemma for the sketch residual
against a frame (the library's is private and filter-specific); a Chebyshev filter lemma not
tied to two singular value indices; the Frobenius identity for a general compression.
Search results, library and Mathlib, are in §7.

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
| E7 | Lemma 3.6 | "full-rank $\mathbf A$" not needed; the sentence before it has the roles of $\mathbf W,\mathbf Z$ swapped | not needed (the $p\ge2$ chain is one-sided) |
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

### 2.1 Projectors and Schatten norms (PN1–PN4, ST1, ST2, ST2s, SO1)

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
  $\|\mathbf P\mathbf A\|_p^p+\|(\mathbf I-\mathbf P)\mathbf A\|_p^p\le\|\mathbf A\|_p^p$, from
  McCarthy's inequality, which the library has
  (`Matrix.PosSemidef.re_trace_rpow_add_le`) at
  $\mathbf A^{\mathsf H}\mathbf P\mathbf A+\mathbf A^{\mathsf H}(\mathbf I-\mathbf P)\mathbf A=
  \mathbf A^{\mathsf H}\mathbf A$. It is false for $p<2$.
* **ST1.** If $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$ (the range of $\mathbf Q$
  contains the row space of $\mathbf P\mathbf A$) then
  $\|\mathbf A-\mathbf A\mathbf Q\|_p^p+\|\mathbf P\mathbf A\|_p^p\le\|\mathbf A\|_p^p$,
  $p\ge1$.
* **ST2.** Hence, for every $k$,
  $\|\mathbf A-\mathbf A\mathbf Q\|_p^p\le\mathrm{OPT}_p^p+
  \sum_{i<k}\bigl(\sigma_i(\mathbf A)^p-\sigma_i(\mathbf P\mathbf A)^p\bigr)$.
  **ST2s** (BCW Lemma 3.4 itself): the sum is at most
  $\sum_{i<k}\max(1,\tfrac p2)\,\sigma_i^{p-2}\,(\sigma_i^2-\sigma_i(\mathbf P\mathbf A)^2)$,
  by SC1 ($a^r-b^r\le\max(1,r)a^{r-1}(a-b)$ for $0\le b\le a$). Safe at junk values:
  $\sigma_i=0$ forces a zero deficit.
* **SO1.** If $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$ then
  $\mathbf A-\mathbf A\mathbf Q=(\mathbf A-\mathbf P\mathbf A)(\mathbf I-\mathbf Q)$, so
  $\|\mathbf A-\mathbf A\mathbf Q\|\le\|\mathbf A-\mathbf P\mathbf A\|$ in every unitarily
  invariant norm: the two-sided output is never worse than the one-sided one.
* For $p=2$: $\|\mathbf A-\mathbf P\mathbf A\|_{\mathsf F}^2=\mathrm{OPT}_2^2+
  \sum_{i<k}(\sigma_i^2-\sigma_i(\mathbf P\mathbf A)^2)$ when
  $\operatorname{rank}\mathbf P\le k$ (ST2F), and the same for
  $\mathbf A-\llbracket\mathbf P\mathbf A\rrbracket_k$ (ST2T).

Consequence for the outputs (decision OUTPUT): for $p\ge2$ everything is proved for the usual
output $\llbracket\mathbf P_{\mathcal K}\mathbf A\rrbracket_k$ (PN4), and BCW's two-sided output
inherits it by SO1; for $1\le p<2$ only the two-sided output has a proof (PN3).

The hypothesis of every later structural theorem is a bound on the **deficits**
$d_i=\sigma_i(\mathbf A)^2-\sigma_i(\mathbf P\mathbf A)^2\ge0$, $i<k$. For the top-$k$ Ritz
vectors this is the per-vector guarantee (E6); as a hypothesis on singular values it does not
mention vectors.

### 2.2 The tail-count form (CB1, CB1F, CB2): BCW's case analysis as one inequality

SV3: $(j+1)\,\sigma_{k+j}^p\le\mathrm{OPT}_p^p$.

**CB1** ($1\le p\le2$, two-sided). If $d_i\le\gamma\sigma_k^2+\beta_i$ with $\beta_i\ge0$ for
$i<k$, and $\sigma_k\le\kappa\,\sigma_{k+j}$, then
$$\|\mathbf A-\mathbf A\mathbf Q\|_p^p\le\Bigl(1+\frac{k\gamma\kappa^p}{j+1}\Bigr)
\mathrm{OPT}_p^p+\sigma_k^{p-2}\sum_{i<k}\beta_i .$$
Proof: ST2s with $\sigma_i^{p-2}\le\sigma_k^{p-2}$ ($p\le2$), then SV3. The $\beta_i$ are
*absolute* errors (a sketch residual, a routine's rounding), which a multiple of $\sigma_k^2$
cannot absorb. For $p<2$ the statement needs "$\sigma_k=0\Rightarrow\beta_i=0$": Lean's
$0^{p-2}=0$ would otherwise delete the term while the deficits remain. **CB1F** is the Frobenius
twin for $\mathbf A-\llbracket\mathbf P\mathbf A\rrbracket_k$ (ST2T; no junk hypothesis, no
$\mathbf Q$). At $j=0,\kappa=1,\gamma=0$ CB1 is the plain bound
$\mathrm{OPT}^p+\sigma_k^{p-2}\sum\beta_i$; at $j\approx k\varepsilon^{-1/3}$ it is the
heavy-tail case. The case analysis is then: either $\sigma_k\le\kappa\sigma_{k+j}$ (deep run,
$\gamma=\gamma_1$), or $\sigma_{k+j}<\sigma_k/\kappa$ (a gap; wide run, $\gamma=0$,
$\beta_i=d_i$). **CB2** states it for two candidates produced in any way: the smaller of the two
errors is at most
$(1+k\max(\gamma_1\kappa^p/(j+1),\gamma_2))\mathrm{OPT}_p^p+\sigma_k^{p-2}
\max(\sum\beta^{(1)}_i,\sum\beta^{(2)}_i)$, the second candidate's accuracy being assumed only
under the gap.

### 2.3 Deficits of a filtered sketch and of RBKI (RZ1–RZ5, RZ4F)

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
  \rrbracket_{i+1}\|_2^2$ (min–max `le_singularValues_of_forall_mem` on the top right singular
  subspace), then the existing head capture.
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
  (\mathbf Z^{\mathsf H}\mathbf\Omega)^+\|\|\tilde{\mathbf c}\|$; min–max on this
  $(i+1)$-dimensional subspace of the range of $\mathbf P$.
* **RZ3 (RBKI, no gap).** For $0<\gamma\le1$, $q\ge1$, $i<k$,
  $\mathbf A\mathbf Z\mathbf Z^{\mathsf H}=\llbracket\mathbf A\rrbracket_k$:
  $$\sigma_i(\mathsf{rbki}(\mathbf A,\mathbf\Omega,q))^2\ge\sigma_i^2-\gamma\sigma_k^2-
  4e^{-2\sqrt2(q-1)\sqrt\gamma}\,\|\mathbf M_k\|_2^2 .$$
  If $\sigma_i^2\ge(1+\gamma)\sigma_k^2$: RZ1 at $t=k$ with the Chebyshev filter of $[0,\sigma_k^2]$
  (relative gap $(\sigma_i-\sigma_k)/(\sigma_i+\sigma_k)\ge\gamma/(1+\sqrt2)^2$). Otherwise RZ2
  with $\tau^2=\sigma_i^2-\gamma\sigma_k^2$ and the filter of $[0,\tau^2]$ (relative gap
  $\ge\gamma/8$). The filter depends on $i$; all are in the Krylov space (SV2). This is the
  per-vector guarantee of Musco–Musco Theorem 1 in deterministic form (E15). **Decided by the
  design (was decision RITZ):** the per-index cut is used, not Musco–Musco's induction on the
  rank (their properties 1–3); it gives all $i<k$ at once and reuses the library's head capture
  and residual.
* **RZ4 (RBKI, gap).** Head count $r=h+1\le t$, $i<r$,
  $\mathbf A\mathbf Z\mathbf Z^{\mathsf H}=\llbracket\mathbf A\rrbracket_t$:
  $\sigma_i(\mathsf{rbki})^2\ge\sigma_i^2-4e^{-8(q-1)\sqrt{\gamma_{h,t}}}\|\mathbf M_t\|_2^2$,
  $\gamma_{h,t}$ = `singularGapRatio A h t` (MM Theorem 13; E4, E10).
* **RZ4F (RBKI, gap, all deficits at once).**
  $\sum_{i<r}d_i\le4e^{-8(q-1)\sqrt{\gamma_{h,t}}}\|\mathbf M_t\|_{\mathsf F}^2$: ST2T, the
  library's Gu projected form
  (`frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`:
  $\sum_{i<r}d_i\le\|(\mathbf I-\mathbf P)\llbracket\mathbf A\rrbracket_r\|_{\mathsf F}^2$) and
  head capture in the Frobenius norm. This is the deterministic content of the merged
  `integral_frobNorm_sub_truncatedSVD_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`;
  summing RZ4 over $i$ would be weaker by a factor $k$.
* **RZ5.** $\|\mathbf A-\llbracket\mathsf{rbki}\rrbracket_k\|_{\mathsf F}^2\le\mathrm{OPT}_2^2+
  k\gamma\sigma_k^2+4ke^{-2\sqrt2(q-1)\sqrt\gamma}\|\mathbf M_k\|_2^2$ (ST2T + RZ3).

The residual $\mathbf M_t$ is the library's: for a Gaussian block with $\ell\ge t+2$ columns,
$\mathbb E\|\mathbf M_t\|_{\mathsf F}^2=\frac{t}{\ell-t-1}\|\mathbf A-\llbracket\mathbf A
\rrbracket_t\|_{\mathsf F}^2$ (GR1). That is why the Frobenius headline has no dimension in it.

### 2.4 Large singular values, $p\ge2$, one-sided (HD1, HD2, ST3, ST4, CB3)

For $p\ge2$ the chain is one-sided (PN4): there is no $\mathbf Q$ and no hypothesis
$\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$.

* **HD1** (BCW Lemma 3.5, frame form). $\mathbf W$ with at most $L$ orthonormal columns,
  $\|\mathbf A^{\mathsf H}\mathbf W\|_{\mathsf F}^2\ge\sum_{i<L}\sigma_i^2-\eta$,
  $\sigma_L^2\le(1-\theta)\sigma_{L-1}^2$, $\theta\le1$:
  $\theta\,\|(\mathbf I-\mathbf W\mathbf W^{\mathsf H})\llbracket\mathbf A\rrbracket_L
  \|_{\mathsf F}^2\le\eta$. ($\theta\le1$ is needed: for $\theta>1$ the gap forces
  $\sigma_{L-1}=0$ and the conclusion would be scaled by $\theta$.)
* **HD2.** For every projector $\mathbf P$:
  $\theta\,\|(\mathbf I-\mathbf P)\llbracket\mathbf A\rrbracket_L\|_{\mathsf F}^2\le
  \sum_{i<L}d_i$, by HD1 at a frame of the column space of
  $\llbracket\mathbf P\mathbf A\rrbracket_L$ (inside the range of $\mathbf P$).
* **ST3 (head split).** For every $L\le k$ and $p\ge2$:
  $$\|\mathbf A-\mathbf P\mathbf A\|_p\le\|(\mathbf I-\mathbf P)\llbracket\mathbf A\rrbracket_L
  \|_p+\Bigl(\mathrm{OPT}_p^p+\sum_{L\le i<k}\bigl(\sigma_i^p-\sigma_i(\mathbf P\mathbf A)^p
  \bigr)\Bigr)^{1/p}.$$
  Proof: triangle inequality; PN4 on $\mathbf A-\mathbf A_L$; Weyl
  $\sigma_j(\mathbf P(\mathbf A-\mathbf A_L))\ge\sigma_{j+L}(\mathbf P\mathbf A)$.
  The deficits enter in absolute form, which is what a routine's errors need for $p>2$.
* **ST4** = ST3 + HD2 + SC1, with head deficits $\delta\sigma_k^2$, middle deficits
  $\gamma\sigma_k^2$, $\sigma_L\le\kappa\sigma_k$, $0<\theta\le1$:
  $\|\mathbf A-\mathbf P\mathbf A\|_p\le\sqrt{L\delta/\theta}\,\sigma_k+
  (\mathrm{OPT}_p^p+\tfrac p2\kappa^{p-2}(k-L)\gamma\sigma_k^p)^{1/p}$.
* **CB3** = ST4 + SP1 (§2.5) + SV3: with head deficits $\delta\sigma_k^2$ at the indices with
  $\sigma_i>(1+\frac1{2p})\sigma_k$, all deficits $\le\gamma\sigma_k^2$ and
  $\sigma_k\le\kappa\sigma_{k+j}$:
  $$\|\mathbf A-\mathbf P\mathbf A\|_p\le\Bigl(k\sqrt{2(p+1)\delta}+
  \bigl(1+\tfrac{e\,p\,k\gamma\kappa^p}{2(j+1)}\bigr)^{1/p}\Bigr)\mathrm{OPT}_p .$$

### 2.5 The head index (SP1; repair of E9)

**SP1.** For every $\mathbf A$, $k$ and real $p\ge1$ there is $L\le k$ with
$\sigma_L\le(1+\frac1p)\sigma_k$ and, if $L>0$,
$\sigma_{L-1}>(1+\frac1{2p})\sigma_k$ and
$\sigma_L^2\le(1-\frac1{2k(p+1)})\sigma_{L-1}^2$.
Proof: let $L=i+1$ for the largest $i<k$ with $\sigma_i>(1+\frac1{2p})\sigma_k$ and
$\sigma_i/\sigma_{i+1}\ge\rho:=(1+\frac1{2p+1})^{1/k}$, and $L=0$ if there is none. From $L$ on,
every ratio at an index above the threshold is less than $\rho$, so
$\sigma_L<\rho^k(1+\frac1{2p})\sigma_k=(1+\frac1p)\sigma_k$ (no existence argument is needed);
and $1-\rho^{-2}\ge\frac{9}{16k(p+1)}$. The case $\sigma_k=0$ is separate. The relative gap is
$1/(kp)$ instead of the paper's $\varepsilon/d$; it enters ST4 through
$\sqrt{L\delta/\theta}\le k\sqrt{2(p+1)\delta}$ and costs $\log(kp)$ in the depth.

### 2.6 Two block Krylov spaces in one sketch (TS0–TS3)

The sum-space theorems are stated for **any** sketch $\mathbf Y$ whose image under $\mathbf A$
contains the images of the two block Krylov matrices,
$$\operatorname{range}(\mathbf A\mathbf K_{q_j}(\mathbf H,\mathbf\Omega_j))\subseteq
\operatorname{range}(\mathbf A\mathbf Y),\qquad j=1,2,$$
as the library does for `rbki` (`singularValues_sub_rbki_le_of_range_le`). By SV2 the singular
values of $\mathsf{rsvd}(\mathbf A,\mathbf Y)$ dominate those of both runs, so RZ3 for
$(\mathbf\Omega_1,q_1)$ and RZ4F for $(\mathbf\Omega_2,q_2)$ hold for the one projector, and
CB1F applies with no selection. The named instance is
`rbkiSum A Ω₁ Ω₂ q₁ q₂ := rsvd A (fromCols (blockKrylovMatrix (Aᴴ * A) Ω₁ q₁)
(blockKrylovMatrix (Aᴴ * A) Ω₂ q₂))` (TS0, TS1); a single deeper run, a basis with extra
directions, or whatever space a routine actually built are other instances.

**TS2 (Frobenius, deterministic).** With $t=k+j$, frames $\mathbf Z_1,\mathbf Z_2$ of the row
spaces of $\llbracket\mathbf A\rrbracket_k$, $\llbracket\mathbf A\rrbracket_t$, $0<\gamma\le1$:
$$\|\mathbf A-\llbracket\mathsf{rsvd}(\mathbf A,\mathbf Y)\rrbracket_k\|_{\mathsf F}^2\le
\Bigl(1+\frac{2k\gamma}{j+1}\Bigr)\mathrm{OPT}_2^2+
4k\,e^{-2\sqrt2(q_1-1)\sqrt\gamma}\,\|\mathbf M^{(1)}_k\|_2^2+
4\,e^{-3(q_2-1)}\,\|\mathbf M^{(2)}_{t}\|_{\mathsf F}^2 .$$
Case $\sigma_t^2\le\sigma_k^2/2$: CB1F at $j=0$, $\gamma=0$, $\beta_i=d_i$, and RZ4F with gap
ratio $\ge3-2\sqrt2$, so $8\sqrt{\gamma_{h,t}}\ge8(\sqrt2-1)>3$. Case $\sigma_k^2<2\sigma_t^2$:
CB1F with $\kappa^2=2$ and RZ3. **TS2c** is the instance `rbkiSum`. **TS3**, **TS3c** are the
same for $\|\cdot\|_{S_p}^p$, $1\le p\le2$, for the output $\mathbf A\mathbf Q$, $\mathbf Q$
the projector onto the row space of $\llbracket\mathsf{rsvd}(\mathbf A,\mathbf Y)\rrbracket_k$,
with the two residual terms multiplied by $\sigma_k^{p-2}$ (CB1; when $\sigma_k=0$ both
residuals vanish). **TS2m** is the choose-one form: the smaller of the errors of the two
separate runs has the same bound; for the Frobenius norm the better run is the one with the
larger $\|\llbracket\mathsf{rbki}\rrbracket_k\|_{\mathsf F}$ (ST2T), which a routine has for
free.

What this is relative to the paper (to be said in the docstrings of GA2, GA2p, GA3; decision
ATTRIBUTION):

* It is a variant of BCW's algorithm. BCW select one of two runs from estimated singular
  values, use blocks of exactly $k$ and $s$ columns, and state probability $9/10$. Here one
  Rayleigh–Ritz step is taken on the sum of the two Krylov spaces, the blocks are oversampled
  ($2k+1$ and $2(k+j)+1$ columns), and the bound is in expectation.
* A tail bound follows from the expectation by Markov's inequality on the nonnegative excess
  error, at the price $\varepsilon\to\varepsilon\delta$.
* The product count is the same, $2(\ell_1q_1+\ell_2q_2)$ in Tropp and Webber's count (plus
  $k$ for $\mathbf A\mathbf Q$). What is lost is the block-bidiagonal structure of a single
  run and, for $p\ne2$, any computable choose-one rule.
* When $2(k+j)+1\ge n$ the statement holds but uses more than $n$ products; the known lower
  bound has $\min\{N,k\varepsilon^{-1/3}\}$ for the same reason.
* The two start blocks need not be independent: only linearity of expectation (or a union
  bound) is used, so $\mathbf X_1$ may be a sub-block of $\mathbf X_2$.

### 2.7 Gaussian start blocks (GR1, GR2, GI1, GA0–GA4)

**GR1** (the residual of a Gaussian block against a frame; the library has it only inside the
private `exists_filter_residual`). For $\mathbf Z$ with $s$ orthonormal columns and a Gaussian
block with $\ell\ge s+2$ columns,
$\|(\mathbf A-\mathbf A\mathbf Z\mathbf Z^{\mathsf H})\mathbf X(\mathbf Z^{\mathsf H}\mathbf X)^+
\|_{\mathsf F}^2$ is integrable with expectation
$\|\mathbf A-\mathbf A\mathbf Z\mathbf Z^{\mathsf H}\|_{\mathsf F}^2\,s/(\ell-s-1)$; from
`integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix` at
$\mathbf S=(\mathbf A-\mathbf A\mathbf Z\mathbf Z^{\mathsf H})\mathbf V$, $\mathbf V$ a frame of
the complement. **GR2**: its Markov tail. The frame with
$\mathbf A\mathbf Z\mathbf Z^{\mathsf H}=\llbracket\mathbf A\rrbracket_t$ is the library's
`exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal`
($t\le\lvert n\rvert$; for $t>\lvert n\rvert$, $\llbracket\mathbf A\rrbracket_t=\mathbf A$), and
the almost sure rank condition is `ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix`.

**GA1** (any $\mathbf Y$ as in §2.6, $\ell_1\ge k+2$, $\ell_2\ge k+j+2$) and **GA1c**
(`rbkiSum`):
$$\mathbb E\,\|\mathbf A-\llbracket\mathsf{rbkiSum}\rrbracket_k\|_{\mathsf F}^2\le
\Bigl(1+\frac{2k\gamma}{j+1}+4k\,e^{-2\sqrt2(q_1-1)\sqrt\gamma}\frac{k}{\ell_1-k-1}+
4\,e^{-3(q_2-1)}\frac{k+j}{\ell_2-k-j-1}\Bigr)\mathrm{OPT}_2^2 ,$$
from TS2, $\|\cdot\|_2\le\|\cdot\|_{\mathsf F}$, GR1 and
$\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{\mathsf F}\le\mathrm{OPT}_2$. **GA2** (headline,
`Fin` sizes): $\ell_1=2k+1$, $\ell_2=2(k+j)+1$, $\gamma=\varepsilon^{2/3}$,
$j+1\ge6k\varepsilon^{-1/3}$, $q_1\ge1+\log(12k/\varepsilon)/(2\sqrt2\varepsilon^{1/3})$,
$q_2\ge1+\log(12/\varepsilon)/3$: each of the three terms is at most $\varepsilon/3$
($2k\varepsilon^{2/3}/(6k\varepsilon^{-1/3})$; $4k\cdot\varepsilon/(12k)$;
$4\cdot\varepsilon/12$). **GA1p, GA1pc, GA2p**: the same for $1\le p\le2$, two-sided output;
SV4 ($\sigma_k^{p-2}\|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2\le
\mathrm{OPT}_p^p$) removes the factor $\sigma_k^{p-2}$. **GA4, GA4p**: asymptotic forms,
"$O(k\varepsilon^{-1/3})$ columns and depths $O(\varepsilon^{-1/3}\log(k/\varepsilon))$,
$O(\log(1/\varepsilon))$ suffice". **GA0**: one run,
$\mathbb E\|\mathbf A-\llbracket\mathsf{rbki}\rrbracket_k\|_{\mathsf F}^2\le
(1+4ke^{-2\sqrt2(q-1)\sqrt\gamma}\frac k{\ell-k-1})\mathrm{OPT}_2^2+k\gamma\sigma_k^2$.

**GA3** ($2\le p<\infty$, tail form, one-sided output). With probability at least $1-\delta$,
$\|\mathbf A-\llbracket\mathsf{rbkiSum}\rrbracket_k\|_{S_p}\le(1+\varepsilon)\mathrm{OPT}_p$,
when $j+1\ge e^2k(\varepsilon p)^{-1/3}$,
$q_1\ge1+\bigl(\frac{p^{1/6}}{2\varepsilon^{1/3}}+\frac{\sqrt{4p+1}}8\bigr)\Lambda_1$,
$q_2\ge1+\frac{\sqrt{4p+1}}8\Lambda_2$, with
$\Lambda_1=\log\frac{256k^3(p+1)N}{\varepsilon^2\delta}$,
$\Lambda_2=\log\frac{256k^2(k+j)(p+1)N}{\varepsilon^2\delta}$, $N=\min(m,n)$. Derivation
(from CB3, TS1, RZ3, RZ4, GR2; no intermediate deterministic theorem): on the events
$\|\mathbf M^{(1)}_k\|_{\mathsf F}^2\le\frac{2kN}{\delta}\sigma_k^2$ and
$\|\mathbf M^{(2)}_t\|_{\mathsf F}^2\le\frac{2tN}{\delta}\sigma_t^2$ (GR2 and
$\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{\mathsf F}^2\le N\sigma_t^2$), CB3 with
$\delta_{\mathrm{head}}=\varepsilon^2/(32k^2(p+1))$ and either $\kappa=1+\frac1p$,
$\gamma=\varepsilon^{2/3}p^{-1/3}$ (no gap; RZ3 at $\gamma/2$) or $j=0$, $\kappa=1$,
$\gamma=\varepsilon/(ek)$ (gap $\sigma_{k+j}<\sigma_k/(1+\frac1p)$; RZ4 with gap ratio
$\ge1/(2p+1)$); head deficits from RZ4 at $t=k$ with gap ratio $\ge1/(4p+1)$. The head term is
then $\varepsilon/4$ and the other $(1+p\varepsilon/2)^{1/p}\le1+\varepsilon/2$: the thresholds
have slack. Here the dimension enters, because for $p>2$ the Frobenius norm of the tail is not
controlled by $\mathrm{OPT}_p$ (decision P-LARGE). **GA3a** is its asymptotic form.

## 3. Objects, interfaces, statement shapes (items 1–3)

**Objects.** One definition:

| Notion | NLAlib | Bridge |
|---|---|---|
| RBKI on the sum of two block Krylov spaces, $\mathsf{rbkiSum}(\mathbf A,\mathbf\Omega_1,\mathbf\Omega_2,q_1,q_2)$ | `rbkiSum A Ω₁ Ω₂ q₁ q₂ := rsvd A (fromCols (blockKrylovMatrix (Aᴴ * A) Ω₁ q₁) (blockKrylovMatrix (Aᴴ * A) Ω₂ q₂))`; deterministic; `Algorithm: rbki-sum` | `rbkiSum_def`, `rbkiSum_eq_rangeProjector`, `singularValues_rbki_le_singularValues_rbkiSum_left/right`; Mathlib has none |

It is a thin definition: every theorem about it is an instance of a theorem about `rsvd A Y`
under range inclusion. Used directly: `schattenNorm`, `frobNorm`, `specNorm`, `singularValues`,
`truncatedSVD`, `rangeProjector`, `rsvd`, `rbki`, `pinv`, `singularGapRatio`,
`HasOrthonormalCols`, `IsStarProjection`, `gaussianMatrix`, `HasLaw`. The two-sided output is
written `A * rangeProjector (truncatedSVD B k)ᴴ`, not named.

**Interfaces.** None introduced. The hypothesis "$\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$"
is an equation between `IsStarProjection`s; deficits are inequalities between `singularValues`.
A predicate bundling "deficits at most $\gamma\sigma_k^2+\beta_i$" was considered and rejected
(one field). The six frame hypotheses of TS2, TS2m, TS3 repeat; after CB1/CB1F those proofs are
short, so no predicate is added for them either.

**Statement shapes.** Appendix A has a signature for every target. Field: `RCLike 𝕜` for waves
0–3; ℝ for the Gaussian wave, as everywhere in `LowRank/Gaussian` (the law `gaussianMatrix` is
real). Index types `Type*` with `Fintype`; the headlines GA2, GA2p instantiate at `Fin`.
Exponent `p : ℝ≥0∞` with `1 ≤ p`, `p ≤ 2` or `2 ≤ p`, `p ≠ ⊤`, powers `^ p.toReal`, as
`schattenNorm_rpow`. **Constants (decided by the design, was decision CONSTANTS):** written out
($4$, $2\sqrt2$, $3$, $e$ in the deterministic bounds; $6$, $12$ in the headline thresholds).
They are Chebyshev values in readable form [B6] and thresholds of one headline; no consumer
inverts them, so no named bound and no registry entry is introduced. Probability: expectations
of squared (or $p$-th power) errors in closed form (GA0, GA1, GA1p), sample-size headlines (GA2,
GA2p), asymptotic forms (GA4, GA4p, GA3a), tail form for $p>2$ (GA3).

## 4. Consumers (item 4)

| Statement | Consumer |
|---|---|
| PN1–PN4 | any analysis of a compression in a Schatten norm; nuclear-norm lower bounds (`LowerBounds/LowRank/NuclearMinimax.lean`); generalized Nyström in Schatten norms |
| ST1, ST2, ST2s, CB1, CB1F, CB2 | any sketch that controls singular values of $\mathbf P\mathbf A$: `rsvd` with a subspace embedding, subspace iteration, Nyström through the Gram correspondence; the routine of §8, whose errors are the absolute $\beta_i$ |
| SV1, SV2 | Ritz-value statements for Lanczos and block Lanczos (`Krylov/`), the eigenvalue accuracy of Nyström |
| RZ1–RZ4, RZ4F | singular value estimation by RBKI (per-vector PCA guarantee, MM Theorem 1 (3)); block-size-aware bounds of `LowRank-BlockLanczos.md` §2.5; BCW's lower-bound reduction uses the case $k=1$ of RZ3 (their Corollary 5.5) |
| RZ5, GA0 | a Frobenius guarantee for the block Golub–Kahan program through `BlockKrylov.integral_comp_storedOutput`, today |
| TS2, TS3, GA1, GA1p (range-inclusion forms) | a routine's actual basis; a single deeper run (decision SINGLE-RUN); deflation and breakdown handling |
| GA2, GA2p | the explorer's pairing with the lower bound $\Omega(k\varepsilon^{-1/3})$ when it lands |
| GR1, GR2 | every later Gaussian bound stated through a frame and the residual $\mathbf M_t$; replaces the private `exists_filter_residual` pattern |
| CH1 | every Chebyshev filter argument whose interval is not $[0,\sigma_t^2]$ (deflation, stopping criteria) |
| SP1, HD1, HD2 | Schatten-$p$ bounds, $p>2$; HD1 is a $\sin\Theta$-type statement from an energy deficit and a gap, usable for eigenvector accuracy from Rayleigh quotients |

## 5. Files and placement (item 5)

New files:

* `NLAlib/Matrix/Norms/SchattenPinching.lean`: PN1, PN2, PN3, PN4.
* `NLAlib/Matrix/Spectral/CompressionSingularValues.lean`: SV1, SV2, ST2F, ST2T, HD1, HD2
  (singular values and Frobenius error of $\mathbf P\mathbf A$).
* `NLAlib/Matrix/Spectral/SingularValueDecay.lean`: SV3, SV4, SP1 (statements about the spectrum
  alone).
* `NLAlib/LowRank/Structural/SingularValueDeficit.lean`: ST1, ST2, ST2s, SO1, CB1, CB1F, CB2,
  ST3, ST4, CB3.
* `NLAlib/LowRank/Structural/RitzValues.lean`: RZ1–RZ5, RZ4F.
* `NLAlib/LowRank/Structural/BlockKrylovSum.lean`: `rbkiSum`, TS0–TS3, TS2c, TS2m, TS3c.
* `NLAlib/LowRank/Gaussian/BlockKrylovSum.lean`: GA0–GA4.

Additions to existing files, each with its reason:

* SC1 `Real.rpow_sub_rpow_le_max_mul` → `NLAlib/ForMathlib/Analysis/SpecialFunctions/Pow/Real.lean`
  (a fact about real powers; Mathlib candidate).
* CH1 `exists_degree_lt_div_sq_le_exp_of_le` →
  `NLAlib/ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean` (a statement
  about Chebyshev polynomials and two real numbers; today its content is private inside
  `LowRank/Gaussian/BlockKrylov.lean`).
* GR1, GR2 → `NLAlib/LowRank/Gaussian/RangeFinder.lean` (the Gaussian range finder's residual;
  a probabilistic statement, so not in `Structural/`).
* GI1 → `NLAlib/LowRank/Random/RangeFinder.lean` (next to
  `integrable_frobNorm_sub_truncatedSVD_rsvd_sq`, which already covers the Frobenius errors for
  any measurable sketch); `measurable_rbkiSum` → `NLAlib/Probability/Measurability/Krylov.lean`.
* vocabulary row for `rbkiSum`; `docs/constants.toml` unchanged (no named bound).

**Changes to merged statements** (old → new):

* `exists_degree_lt_div_sq_le_exp_singularGapRatio (A : Matrix m n ℝ) …` →
  `(A : Matrix m n 𝕜) …`, same conclusion, reproved from CH1 (decision CHEB-GENERAL); needed so
  that RZ4, RZ4F are over `𝕜` [T7]. Its call sites pass a real matrix and are unaffected.
* `exists_filter_residual` (private, `LowRank/Gaussian/Filter.lean`): statement unchanged; its
  proof is to be rebased on GR1 when GR1 lands (no public statement changes).

No deviation from Mathlib is introduced.

## 6. Targets

Sizes S/M/L. "Needs" lists targets of this note; library lemmas are named in the outline.
Paper locations are BCW unless marked. Batch 2 is marked (b2).

### Wave 0: matrix analysis (no Krylov, no probability)

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| SC1 | $a^r-b^r\le\max(1,r)a^{r-1}(a-b)$ | S | — | Fact 2.4, E6 | $r\ge1$: `one_add_mul_self_le_rpow_one_add` at $s=b/a-1$; $r<1$: $b^r\ge b\,a^{r-1}$ |
| CH1 | Chebyshev filter for reals $0\le\tau\le s$ | M | — | MM Lemma 5 | move the body of `exp_div_two_le_abs_eval_T_comp`; cases $\tau=0$ ($x^d$), $\tau>0$ ($T_d(2x/\tau^2-1)$, monotone beyond $1$) |
| PN1 | pinching for a projector pair, every `SymmetricGauge` | S | — | Fact 2.9, Lemma 3.3 | $\tfrac12(\mathbf A+\mathbf U\mathbf A\mathbf V)$, `matrixNorm_add_le`, unitary invariance (`matrixNorm_mul_of_mul_mul_conjTranspose_eq`) |
| PN2 | Schatten powers add on orthogonal sums | M | — | Lemma 3.3 (proof) | $(\mathbf X+\mathbf Y)^{\mathsf H}(\mathbf X+\mathbf Y)=\mathbf X^{\mathsf H}\mathbf X+\mathbf Y^{\mathsf H}\mathbf Y$ with orthogonal summands; `PosSemidef.schattenNorm_rpow_eq_re_trace_rpow`; trace of a power of an orthogonal sum (equality case of `re_trace_rpow_add_le`; `IsHermitian.cfc_fromBlocks_zero₁₂_zero₂₁` is the block form) |
| PN3 | $\|\mathbf P\mathbf A\mathbf Q\|_p^p+\|(\mathbf I-\mathbf P)\mathbf A(\mathbf I-\mathbf Q)\|_p^p\le\|\mathbf A\|_p^p$ | S | PN1, PN2 | Lemma 3.3 | `lpGauge_matrixNorm`, monotone `rpow` |
| PN4 | one-sided, $p\ge2$ | S | — | Fact 2.7 (Maher) | `Matrix.PosSemidef.re_trace_rpow_add_le` at $\mathbf A^{\mathsf H}\mathbf P\mathbf A$, $\mathbf A^{\mathsf H}(\mathbf I-\mathbf P)\mathbf A$; `schattenNorm_rpow_eq_re_trace_rpow` |
| SV1 | $\sigma_i(\mathbf P\mathbf A)^2\ge\sigma_i(\mathbf A)^2-\|(\mathbf I-\mathbf P)\llbracket\mathbf A\rrbracket_{i+1}\|_2^2$ | M | — | MM Thm 12 (proof) | `le_singularValues_of_forall_mem` on the row space of $\llbracket\mathbf A\rrbracket_{i+1}$; Pythagoras |
| SV2 | $\sigma_i(\mathbf P_{\mathbf Y'}\mathbf A)\le\sigma_i(\mathbf P_{\mathbf Y}\mathbf A)$ for nested ranges | S | — | — | $\mathbf P_{\mathbf Y'}=\mathbf P_{\mathbf Y'}\mathbf P_{\mathbf Y}$, `IsStarProjection.singularValues_mul_le` |
| SV3 | $(j+1)\sigma_{k+j}^p\le\mathrm{OPT}_p^p$ | S | — | eq. (tradeoff-analysis), E8 | `schattenNorm_rpow`, `singularValues_sub_truncatedSVD`, antitone |
| SV4 | $\sigma_k^{p-2}\|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2\le\mathrm{OPT}_p^p$, $p\le2$ | S | — | — | termwise $\sigma_i^2\sigma_k^{p-2}\le\sigma_i^p$; junk value $0^{p-2}=0$ checked |
| SP1 (b2) | head index with gap $1/(2k(p+1))$ | M | — | proof of Thm 3.1, E9 | §2.5; `Nat.findGreatest`; real-analysis estimate $1-\rho^{-2}\ge9/(16k(p+1))$ |
| ST2F | Frobenius identity for $\mathbf A-\mathbf P\mathbf A$, rank $\le k$ | S | — | eq. (inf_cost_lra) | `IsStarProjection.frobNorm_sq_eq_add`, `frobNorm_sq_eq_sum_range_singularValues_sq`, `frobNorm_sub_truncatedSVD_sq` |
| ST2T | the same for $\mathbf A-\llbracket\mathbf P\mathbf A\rrbracket_k$ | S | ST2F | MM Def. 8 | $\llbracket\mathbf P\mathbf A\rrbracket_k=\mathbf\Pi\mathbf A$, $\mathbf\Pi\le\mathbf P$ (`rangeProjector_truncatedSVD_mul`) |
| HD1 (b2) | energy deficit and gap give head capture, frame form | M | — | Lemma 3.5, E11 | §2.4; rows of $\mathbf U_L^{\mathsf H}\mathbf W$ have norm $\le1$; $\theta\le1$ |

### Wave 1: structural theorems for projectors

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| ST1 | $\|\mathbf A-\mathbf A\mathbf Q\|_p^p+\|\mathbf P\mathbf A\|_p^p\le\|\mathbf A\|_p^p$ | S | PN3 | eq. (upper-bound-cost-sp-intro); BN Lemma 4.4 | algebra from $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$ |
| ST2 | error $\le\mathrm{OPT}_p^p+\sum_{i<k}$ deficits in $p$-th powers | S | ST1 | Lemma 3.4 | split $\|\mathbf A\|_p^p$ at $k$; drop $\sigma_i(\mathbf P\mathbf A)$, $i\ge k$ |
| ST2s | the same with $\max(1,\frac p2)\sigma_i^{p-2}d_i$ | S | ST2, SC1 | Lemma 3.4 | termwise SC1 |
| SO1 | two-sided error $\le$ one-sided error | S | — | — | $\mathbf A-\mathbf A\mathbf Q=(\mathbf A-\mathbf P\mathbf A)(\mathbf I-\mathbf Q)$, `matrixNorm_mul_le_mul_specNorm` |
| CB1 | tail-count form with absolute errors, $1\le p\le2$ | M | ST2s, SV3 | Thm 3.1 proof, case 1 | §2.2 |
| CB1F | Frobenius twin, one-sided | S | ST2T, SV3 | Thm 3.1 at $p=2$ | §2.2 |
| CB2 | two candidates, `min` | S | CB1 | Algorithm 3.2 | case split on $\kappa\sigma_{k+j}<\sigma_k$ |
| HD2 (b2) | head capture for a projector | M | HD1, ST2T | Cor. 3.7 | frame of the column space of $\llbracket\mathbf P\mathbf A\rrbracket_L$ |
| ST3 (b2) | head split, one-sided, $p\ge2$ | M | PN4 | eq. (tri_ineq)–(tail-bound-projection-sp) | §2.4; `singularValues_le_singularValues_add_of_rank_le` |
| ST4 (b2) | ST3 with deficits | M | ST3, HD2, SC1 | Thm 3.1 proof, case 2 | `schattenNorm_anti` ($\|\cdot\|_p\le\|\cdot\|_{\mathsf F}$) |
| CB3 (b2) | tail-count form, $2\le p<\infty$ | L | ST4, SP1, SV3 | Thm 3.1 proof | §2.4; arithmetic with $(1+\frac1p)^{p}\le e$ |

### Wave 2: singular values of sketches

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| RZ1 | filtered sketch, gap form | M | SV1 | MM Lemma 9 property 1 | head capture `singularValues_one_sub_rangeProjector_mul_mul_le` at the frame of $\llbracket\mathbf A\rrbracket_{i+1}$; $\|\mathbf M\|\le a\|\mathbf M_t\|$ by functional calculus on the tail |
| RZ2 | filtered sketch, cut form | L | — | MM Lemma 9 property 2 (eq. good_k_subspace) | §2.3; spectral projector of $\mathbf A\mathbf A^{\mathsf H}$ at $\tau^2$; min–max |
| RZ3 | RBKI deficits, no gap | M | RZ1, RZ2, CH1, SV2 | Lemma 3.1, MM Thm 12, E15 | two cases on $\sigma_i^2\ge(1+\gamma)\sigma_k^2$ |
| RZ4 | RBKI deficits, gap, per index | S | RZ1, SV2 | Lemma 3.2, MM Thm 13, E4, E10 | `exists_degree_lt_div_sq_le_exp_singularGapRatio` |
| RZ4F | RBKI deficits, gap, summed | S | ST2T, SV2 | MM Lemma 9 property 1 | Gu's projected form + `matrixNorm_one_sub_rangeProjector_mul_mul_le` at the Frobenius gauge |
| RZ5 | Frobenius error of one truncated run | S | RZ3, ST2T | — | sum over $i<k$ |

### Wave 3: two Krylov spaces in one sketch (deterministic)

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| TS0 | `rbkiSum`, `rbkiSum_def`, `rbkiSum_eq_rangeProjector`, `measurable_rbkiSum` | S | — | abstract ("multiple Krylov subspaces") | definitions; `measurable_rsvd` |
| TS1 | the two range inclusions for `fromCols`; $\sigma_i(\mathsf{rbki})\le\sigma_i(\mathsf{rbkiSum})$ | S | TS0, SV2 | — | `Matrix.fromCols` range |
| TS2 | Frobenius, any $\mathbf Y$ containing both Krylov sketches | M | RZ3, RZ4F, SV2, CB1F | Thm 3.1 at $p=2$ | §2.6 |
| TS2c | TS2 for `rbkiSum` | S | TS2, TS1 | — | instance |
| TS2m | `min` over the two runs, Frobenius | S | RZ3, RZ4F, CB1F | Algorithm 1.2 (sketch) | same case split, each case one run |
| TS3 | Schatten $1\le p\le2$, two-sided output, any $\mathbf Y$ | M | RZ3, RZ4F, SV2, CB1 | Thm 3.1, $p\le2$ | $\mathbf P$ = range projector of $\llbracket\mathsf{rsvd}(\mathbf A,\mathbf Y)\rrbracket_k$; `hβ0` from $\mathbf M=\mathbf 0$ when $\sigma_k=0$ |
| TS3c | TS3 for `rbkiSum` | S | TS3, TS1 | — | instance |

### Wave 4: Gaussian start blocks

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| GR1 | residual of a Gaussian block against a frame: integrable, expectation | M | — | HMT Thm 10.5 (proof) | §2.7 |
| GR2 | its Markov tail | S | GR1 | — | `mul_meas_ge_le_integral_of_nonneg` |
| GI1 | integrability of the two-sided Schatten error of `rsvd A Y` | M | — | — | bounded by $\|\mathbf A\|_p^p$; `measurable_truncatedSVD`, `measurable_rangeProjector`, `measurable_rsvd` |
| GA0 | one run, expectation | S | RZ5, GR1 | MM Thm 12 | frame from the library; a.s. rank from `ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix` |
| GA1 | Frobenius, expectation, any $\mathbf Y$ | M | TS2, GR1 | Thm 3.1 at $p=2$ | linearity; $t>\lvert n\rvert$ separately |
| GA1c | GA1 for `rbkiSum` | S | GA1, TS1 | — | instance |
| GA1p | Schatten $1\le p\le2$, expectation, any $\mathbf Y$ | M | TS3, SV4, GR1, GI1 | Thm 3.1, $p\le2$ | as GA1 |
| GA1pc | GA1p for `rbkiSum` | S | GA1p, TS1 | — | instance |
| GA3 (b2) | Schatten $2\le p<\infty$, tail, one-sided | L | CB3, TS1, RZ3, RZ4, GR2 | Thm 3.1 | §2.7 |

### Wave 5: headlines and asymptotic forms

| Id | Statement | Size | Needs | Formalizes | Outline |
|---|---|---|---|---|---|
| GA2 | Frobenius headline at `Fin` sizes | M | GA1c | Thm 1.1 at $p=2$ | three terms $\le\varepsilon/3$; `Real.log`/`rpow` arithmetic |
| GA2p | Schatten $1\le p\le2$ headline | S | GA1pc | Thm 1.1 | same arithmetic |
| GA4 | asymptotic form, Frobenius | M | GA1c | Thm 1.1 | `exists_forall_`; $j$ chosen inside the proof from $\lvert l_2\rvert$ |
| GA4p | asymptotic form, $1\le p\le2$ | S | GA1pc | Thm 1.1 | as GA4 |
| GA3a (b2) | asymptotic form of GA3 | M | GA3 | Thm 1.1 | $j=\lvert l_2\rvert-k-2$; threshold $kp^{1/6}\varepsilon^{-1/3}\log(\cdot)$ |

Counts: S 29, M 20, L 3 (52). By wave: 0: 14, 1: 11, 2: 6, 3: 7, 4: 9, 5: 5. Batch 1 is 44
targets; batch 2 ($p>2$: SP1, HD1, HD2, ST3, ST4, CB3, GA3, GA3a) is 8. The Frobenius headline
GA2 is itself plus 17 targets, with no PN, SC or HD: CH1, SV1, SV2, SV3, ST2F, ST2T, CB1F, RZ1,
RZ2, RZ3, RZ4F, TS0, TS1, TS2, GR1, GA1, GA1c.

## 7. Shared proof machinery (item 7)

| Argument repeated | Handled by |
|---|---|
| unitary invariance of a gauge under $2\mathbf P-\mathbf I$ | existing `SymmetricGauge.matrixNorm_mul_of_mul_mul_conjTranspose_eq` and `matrixNorm_mul_left_of_hasOrthonormalCols`; PN1 is proved once and never unfolded again |
| $p$-th powers of Schatten norms as sums over a range | existing `schattenNorm_rpow` with `N` at least the rank; SV3, SV4 package the two tail estimates so that no later proof manipulates the sums |
| "deficit in squares to deficit in $p$-th powers" | SC1 inside ST2s, once |
| the case split "gap or heavy tail" | CB1 / CB1F, once; TS2, TS2m, TS3 instantiate |
| Chebyshev value to $4e^{-8d\sqrt\gamma}$ | CH1, once; the constants $2\sqrt2$ and $3$ are two numeric lemmas next to RZ3 and TS2 ($8/\sqrt8=2\sqrt2$, $8(\sqrt2-1)>3$) |
| "the Krylov space contains the filtered sketch" | existing `range_mul_aeval_mul_le_range_mul_blockKrylovMatrix` + SV2 |
| frame of the row space of $\llbracket\mathbf A\rrbracket_t$ | existing `exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal` (public) |
| full row rank of $\mathbf Z^{\mathsf H}\mathbf X$ almost surely; moments and tail of the residual | existing `ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix`; GR1, GR2, once, before GA0, GA1, GA1p, GA3 |
| threshold arithmetic of the headlines ($\log$, $\varepsilon^{1/3}$) | `NLAlib/ForMathlib/Analysis/SpecialFunctions/Log/Basic.lean` has the pattern for the RBKI asymptotic forms; GA2 and GA2p share one private lemma "the three terms are at most $\varepsilon/3$" |
| measurability and integrability of outputs | Frobenius: existing `integrable_frobNorm_sub_truncatedSVD_rsvd_sq`; Schatten two-sided: GI1, once, before GA1p |

Searches, redone after the review (the first version of this note wrongly recorded McCarthy as
absent). Method: `grep` over `NLAlib/` and the pinned Mathlib for the statement shape and for
the usual names.

| Looked for | Library | Mathlib |
|---|---|---|
| McCarthy $\operatorname{tr}(\mathbf X+\mathbf Y)^p\ge\operatorname{tr}\mathbf X^p+\operatorname{tr}\mathbf Y^p$ | **found**: `Matrix.PosSemidef.re_trace_rpow_add_le` (`Matrix/Functions/TracePowers.lean`) | none |
| pinching in a unitarily invariant norm | none as a statement; the averaging identity with a reflection is a private lemma for block matrices in `Matrix/Functions/OperatorConvex.lean` (`half_smul_add_half_smul_reflection`), used for operator convex functions | none |
| Schatten powers of an orthogonal sum / block diagonal | none (`frobNorm_add_sq_of_conjTranspose_mul_eq_zero` and `specNorm_fromBlocks_zero₁₂_zero₂₁` are the $p=2,\infty$ cases; `IsHermitian.cfc_fromBlocks_zero₁₂_zero₂₁` is the functional-calculus block form) | none |
| Schatten norm | library's own | none |
| lower bounds on $\sigma_i(\mathsf{rsvd})$, $\sigma_i(\mathsf{rbki})$; monotonicity of $\sigma_i(\mathbf P_{\mathbf Y}\mathbf A)$ in the range | none (only for $\mathbf A-\mathbf P_{\mathbf Y}\mathbf A$: `singularValues_one_sub_rangeProjector_mul_le_of_range_le`) | none |
| min–max for singular values | found: `le_singularValues_of_forall_mem` (`Matrix/Spectral/SingularValues.lean`), `Matrix/Spectral/CourantFischer.lean` | none (`Analysis/InnerProductSpace/Rayleigh.lean` has only the extreme eigenvalues) |
| Frobenius error of a truncated compression | found: `frobNorm_sub_truncatedSVD_rsvd_sq`, Gu's projected form (`LowRank/Structural/Truncation.lean`); ST2F/ST2T restate them for a general projector | none |
| deterministic head capture for a block Krylov sketch | found only for the single-vector simulated block (`frobNorm_one_sub_rangeProjector_mul_blockKrylovMatrix_mul_truncatedSVD_sq_le`, `Gaussian/SmallBlock.lean`) and in expectation (`Gaussian/Filter.lean`); RZ4F is the block form | none |
| frame of the top right singular subspace | found: `exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal`, `mul_rangeProjector_conjTranspose_truncatedSVD` | none |
| Gaussian residual moment against a frame | found only as `integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix` (two frames) and inside the private `exists_filter_residual`; GR1 | none |
| Bernoulli for real exponents | — | found: `one_add_mul_self_le_rpow_one_add`, `rpow_one_add_le_one_add_mul_self` |
| Chebyshev growth outside $[-1,1]$ | found: `ForMathlib/.../Chebyshev/Growth.lean` | found: `Polynomial.Chebyshev.one_le_eval_T_real` (no rate) |

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
   proved (the paper's estimated-singular-value test is E2, E8, E14).
3. **One basis for both spaces**: TS2, TS3, GA1, GA1p are stated for any sketch whose range
   contains the two Krylov sketches, so the routine's basis need not be `rbkiSum`'s. The
   existing orthogonalization contract (`LowRank-BlockLanczos.md` §3.1a: extend a stored basis
   by a block) covers it if the second run orthogonalizes against the first run's basis; the
   stored factor is then a general projected matrix $\mathbf Q^{\mathsf H}\mathbf A$, not block
   bidiagonal (decision ROUTINE-FORM).

**Tolerance to inexact steps.** The structural layer is stated so that an inexact inner step
changes hypotheses, not theorems:

* *A larger or different subspace.* Deficits are monotone (SV2) and the sum-space theorems
  take range inclusions: extra directions (breakdown handling, deflation, restart vectors)
  need no new mathematics.
* *An inexact best rank-$k$ within the subspace.* CB1, CB1F (and ST3 for $p>2$) take any
  projector $\mathbf P$ and absolute errors $\beta_i$. A routine's errors are of size
  $u\|\mathbf A\|^2$, not multiples of $\sigma_k^2$: if the small SVD returns $\hat{\mathbf P}$
  with $\sigma_i(\hat{\mathbf P}\mathbf A)^2\ge\sigma_i(\mathbf P_{\mathcal K}\mathbf A)^2-\eta$
  (for instance from Weyl with $\|\hat{\mathbf P}-\mathbf P\|\|\mathbf A\|$), the theorems
  apply with $\beta_i+\eta$. For the Frobenius norm, ST2F holds for every projector of rank at
  most $k$, exact Ritz vectors or not.
* *The two-sided output.* The hypothesis $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$ is
  less restrictive than it looks: for any $\mathbf Q$,
  $\mathbf P:=\mathbf I-\mathbf P_{\mathbf A(\mathbf I-\mathbf Q)}$ satisfies it, and the
  burden is the deficits of that $\mathbf P$. For $p\ge2$ the one-sided form has no
  $\mathbf Q$ at all. For $p<2$ a computed $\hat{\mathbf Q}$ costs
  $\|\mathbf A(\mathbf Q-\hat{\mathbf Q})\|_p$ by the triangle inequality. A perturbed form of
  ST1 is therefore not planned (decision INEXACT).
* *Rounded matrix–vector products and loss of orthogonality* change the Krylov space itself.
  RZ1–RZ4 are for exact filtered sketches of the exact $\mathbf A$; an ill-conditioned basis
  at depth $\varepsilon^{-1/3}\log$ spans a different subspace, and the backward model of the
  block program (a run on $\mathbf A+\mathbf E$) does not cover loss of orthogonality. This is
  the library's existing RBKI obstacle (`LowRank-BlockLanczos.md`, BL8), not a new one; the
  range-inclusion forms are what lets a routine plug in the space it actually built once it
  can bound that space's deficits.
* *Output as a perturbation.* A returned $\mathbf B$ with
  $\|\mathbf B-\llbracket\mathsf{rsvd}(\mathbf A,\mathbf Y)\rrbracket_k\|\le\eta$ costs $\eta$
  by `schattenNorm_add_le`; no statement is needed.

## 9. Risks and open questions (item 8)

### Risks

* **RZ2 is new as a statement** (it is Musco–Musco's property 2 reorganized so that the filter
  cut is a parameter). The proof is short on paper but uses spectral projectors of
  $\mathbf A\mathbf A^{\mathsf H}$ against a frame that is only assumed to contain the top
  $i+1$ right singular vectors; ties $\sigma_{i}=\sigma_{i+1}$ make "the top $i+1$ directions" a
  choice, fixed here by `truncatedSVD`. Size L for that reason. If it fails as stated, the
  fallback hypothesis is $\mathbf A\mathbf Z\mathbf Z^{\mathsf H}=\llbracket\mathbf A\rrbracket_k$
  (which RZ3 has anyway).
* **CB3 and GA3 ($p>2$) are the research-grade part.** The chain SP1 → HD2 → ST4 → CB3
  replaces the paper's argument at E9 and E12. ST3, HD2, SP1 were checked by hand and
  numerically on random instances of size up to $9$; the composite constants of CB3 and GA3
  are hand arithmetic (the reviewer re-derived GA3 independently). What could be false there
  is a constant, not the rate.
* **HD1 uses $\llbracket\mathbf A\rrbracket_L$ on the left.** With a gap at $L$ the best
  rank-$L$ approximation is unique, so the choice inside `truncatedSVD` does not matter; with
  $\theta\le0$ the statement is trivial. The proof must not assume
  $\llbracket\mathbf A^{\mathsf H}\rrbracket_L=\llbracket\mathbf A\rrbracket_L^{\mathsf H}$ in
  general.
* **GA1p integrates a function of `rangeProjector (truncatedSVD ·)ᴴ`.** Measurability is
  available; a Bochner integral of a non-integrable function is $0$, so GA1p without GI1 would
  be vacuous: GI1 is listed before it for that reason.
* **Junk values.** `singularValues A k ^ (p.toReal - 2)` at $\sigma_k=0$, $p<2$ is $0$ in
  Lean: CB1 and CB2 carry the hypothesis `hβ0` for it, TS3 discharges it (when $\sigma_k=0$ the
  residuals vanish), SV4 is true as stated. `Real.log (12 * k / ε)` and `Real.log (12 / ε)` are
  positive for $k\ge1$, $\varepsilon\le1$. `singularGapRatio` is $0$ when $\sigma_h=0$. In GA3,
  $\Lambda_i>0$ needs $N\ge1$ and $\delta\le1$; for $\delta>1$ the statement is trivial and for
  an empty index type the error is $0$.
* **What is not claimed.** No statement for block size $k$ exactly (BCW's block; the square
  Gaussian block has no inverse second moment), none for $p=\infty$ (use
  `BlockKrylovGapless`), none for $p<1$. The bound for $p\in[1,2)$ is for the two-sided output
  only. Musco–Musco's Frobenius theorem at depth $\varepsilon^{-1/2}$ is not a by-product.

### Open questions, with recommendations

| Id | Question | Recommendation |
|---|---|---|
| SCOPE-NORMS | Frobenius only; Schatten $1\le p\le2$; or all $1\le p<\infty$? | Batch 1: Frobenius and $p\le2$ (44 targets, expectation form, dimension-free). Batch 2: $p>2$ (8 targets), subject to P-LARGE |
| P-LARGE | Is a tail bound for $p>2$ with $\log(\min(m,n))$ and $p^{1/6}$ wanted at all? | Yes, as batch 2: it is the paper's main theorem for $p>2$ and the only place SP1/HD1/ST3 are used; but it is the research-grade part and the first to drop |
| SCOPE-LB | Lower bound $\Omega(\varepsilon^{-1/3})$ in this stage? | No. It needs the Wishart smallest-eigenvalue hardness of Braverman et al. (not in the library) and belongs to the lower-bound track, where Zhang et al.'s $\Omega(k\varepsilon^{-1/3})$ is the stronger target |
| SELECT | One projector on the sum of the Krylov spaces, or the paper's choice between two runs? | Sum; `min` forms CB2, TS2m as corollaries |
| HEADLINE-FORM | Headline about the definition `rbkiSum`, or about `rsvd A Y` under range inclusion? | Headline (GA2) for `rbkiSum` at `Fin` sizes; the general theorems (TS2, TS3, GA1, GA1p) by range inclusion |
| OUTPUT | Which output? | $\llbracket\mathsf{rbkiSum}\rrbracket_k$ (one-sided, the usual RBKI output) for $p\ge2$, Frobenius included; BCW's $\mathbf A\mathbf Q$ only for $1\le p<2$, where the one-sided inequality is false. The two-sided output inherits every $p\ge2$ bound by SO1 |
| ATTRIBUTION | How do the docstrings attribute a theorem about a variant of BCW's algorithm (sum space, oversampled blocks, expectation)? | Cite "[BakshiClarksonWoodruff2022, Theorem 3.1]; there for an algorithm that selects one of the two runs, with blocks of $k$ and $s$ columns, probability $9/10$ and unspecified constants; here …", as the RBKI files do for Tropp–Webber |
| PROB-FORM | Expectation of the squared error with oversampled blocks, or BCW's probability $9/10$ with block $k$ and $\log(d/\varepsilon)$? | Expectation, as the RBKI files; tail form only for $p>2$ |
| MM-FROB | Also formalize Musco–Musco's Frobenius bound at depth $O(\log/\sqrt\varepsilon)$ (their Property 3)? | Not in this stage; GA0 is the per-rank form. Record as a candidate |
| CHEB-GENERAL | Generalize `exists_degree_lt_div_sq_le_exp_singularGapRatio` from ℝ to `𝕜` (merged statement) | Yes |
| BLOCK-K | Also cover block size exactly $k$ (and $k+j$)? | Not now |
| SINGLE-RUN | Bakshi–Narayanan's single run (one block, depth $\varepsilon^{-1/3}$, simulated wide block)? | Later: TS2/TS3 apply by range inclusion (`rbki_blockKrylovMatrix`); the missing input is the conditioning of the simulated block |
| NAME | `rbkiSum`, $\mathsf{rbkiSum}$ | Accept, or give the name you want |
| INEXACT | Perturbed form of ST1 ($\|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|\le\eta$)? | No: absolute errors $\beta_i$ are in CB1/CB1F now; an inexact $\mathbf Q$ is an output perturbation |
| ROUTINE-FORM | Routine as two runs and a choice (Frobenius), or one basis for both spaces? | Decide at the routine stage; both are covered |

Decided by the design, not asked: RITZ (§2.3), CONSTANTS (§3), FIELD (`RCLike 𝕜` for waves 0–3,
ℝ for the Gaussian wave, the library convention), CORANGE-NAME (the two-sided output is not
named), ONE-SIDED (PN4 is in batch 1; it is one application of a library lemma).

## 10. Material (item 6)

Read: the three papers of §1; library files of §0; `LowRank-BlockLanczos.md`,
`Matrix-GaugeAndSchattenNorms.md`, `Headline-Statements.md`. Reused as mathematics: BCW Lemma
3.3 (generalized), Lemma 3.5 (as HD1), the head/tail split; Musco–Musco Lemma 9 properties 1
and 2 (as RZ1, RZ4F, RZ2), Theorem 13 (RZ4). Reused as proof material: the library's head
capture, Gu's projected form, McCarthy's inequality and Chebyshev growth. Deliberately not
reproduced: BCW's rotation-to-block-matrix proof of Lemma 3.3 (PN1 is two lines without bases);
Lemma 3.4's use of Ritz vectors (hypotheses are on singular values); Lemma 3.6 and Corollary 3.7
(the $p\ge2$ chain is one-sided); the singular value estimates and the selection rule of
Algorithm 3.2 (E2, E14); `transpose` twins (BCW run Krylov on $\mathbf A^{\mathsf T}$; the
library's `rbki` already projects on the left).

## 11. Changes after review

Independent review: harness `reports/Review-Fable-LRA-CUBE-ROOT-Design.md` (verdict: revise,
then approve). Each fix was re-derived, and the matrix-level ones checked numerically (random
instances; sanity checks only), before being adopted.

| Item | Outcome | What changed |
|---|---|---|
| B1 (TS3 does not follow from CB1) | agreed | CB1 and CB2 take absolute errors $\beta_i$ (a function of the index, so that the gap case can use the *sum* of the deficits) and need `hβ0` for $p<2$; ST2s (BCW Lemma 3.4) and the Frobenius twin CB1F added; TS2, TS2m, TS3 are now instantiations. GA2's three terms re-checked: each $\le\varepsilon/3$ |
| B2 (HD1, HD2 false for $\theta>1$) | agreed (the counterexample is correct) | `θ ≤ 1` added to HD1, HD2, ST4; CB3 unaffected |
| B3 (TS4, GA3a unstated) | agreed | TS4 deleted; GA3 depends on CB3, TS1, RZ3, RZ4, GR2; GA3a now has a statement |
| S1 (hidden Gaussian residual lemma) | agreed | GR1, GR2 added in `LowRank/Gaussian/RangeFinder.lean`; the frame and the a.s. rank are existing public lemmas; the private `exists_filter_residual` keeps its statement |
| S2 (McCarthy is in the library) | agreed; the first search was wrong | PN4 is S, batch 1. For $p\ge2$ the chain HD1, HD2, ST3, ST4, CB3, GA3 is now one-sided (factor $1$ instead of $2$ in ST3; checked numerically), the two-sided forms of these are dropped and recovered by SO1. All "searched, none" entries redone (§7) |
| S3 (range-inclusion generality) | agreed | TS2, TS3, GA1, GA1p are for `rsvd A Y`; TS2c, TS3c, GA1c, GA1pc are the `rbkiSum` instances |
| S4 (avoidable factor $k$) | agreed | RZ4F added (Gu's projected form); the gap term of TS2/TS3/GA1 is $4e^{-3(q_2-1)}\|\mathbf M\|_{\mathsf F}^2$; GA2 needs $q_2\ge1+\log(12/\varepsilon)/3$ |
| S5 (what is given up) | agreed | §2.6 list; decision ATTRIBUTION |
| S6 (small points) | agreed | `hk` dropped from TS2, TS2m, TS3; GA3 uses $\min(m,n)$; RZ2, CB1, CB3 renamed; SP1's outline no longer cites the pigeonhole principle; no frame predicate |
| Decision sheet | agreed | RITZ, CONSTANTS, FIELD, CORANGE-NAME, ONE-SIDED decided in the note; P-LARGE, HEADLINE-FORM, ATTRIBUTION added; OUTPUT, INEXACT, SELECT, SINGLE-RUN updated |

One point where the reviewer's proposal was changed rather than taken as written: B1 proposed a
single absolute $\beta$; with S4 the gap case bounds the sum of the deficits, not each one, so
CB1 takes $\beta_i$ and concludes with $\sum_{i<k}\beta_i$.

## Appendix A. Lean statements

### A.0 Check

The file below was elaborated with `lake env lean` against the build of `origin/main` @
`edb7e0ee` (toolchain `leanprover/lean4:v4.33.1`) on 2026-11-20, after the revision of §11: no
error; every declaration reports only "declaration uses `sorry`" (and one
unused-section-variable linter note on `rbkiSum_def`). It lives in an untracked `scratch/`
directory of the worktree and is reproduced here verbatim; it adds nothing under `NLAlib/`.
Comments `-- ID` give the target ids of §6; every target has a statement
(`measurable_rbkiSum` of TS0 is the only declaration named in §6 and not stated here).
Elaboration means the statements typecheck, nothing more. Names are to be reviewed with the
skeleton; implicit instance arguments will be trimmed per declaration (`omit … in`) there.

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
theorem HasOrthonormalCols.mul_frobNorm_truncatedSVD_sub_mul_sq_le {W : Matrix m s 𝕜}
    (hW : HasOrthonormalCols W) (A : Matrix m n 𝕜) {h L : ℕ} (hL : h + 1 = L)
    (hcard : Fintype.card s ≤ L) {θ η : ℝ} (hθ : θ ≤ 1)
    (hgap : singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hη : ∑ i ∈ Finset.range L, singularValues A i ^ 2 - η ≤ frobNorm (Aᴴ * W) ^ 2) :
    θ * frobNorm (truncatedSVD A L - W * Wᴴ * truncatedSVD A L) ^ 2 ≤ η := sorry

-- HD2
theorem _root_.IsStarProjection.mul_frobNorm_truncatedSVD_sub_mul_sq_le {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (A : Matrix m n 𝕜) {h L : ℕ} (hL : h + 1 = L) {θ : ℝ}
    (hθ : θ ≤ 1) (hgap : singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2) :
    θ * frobNorm (truncatedSVD A L - P * truncatedSVD A L) ^ 2 ≤
      ∑ i ∈ Finset.range L, (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

/-! ## Wave 1: structural theorems for projectors -/

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

-- ST2s
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_add_sum_mul {p : ℝ≥0∞}
    (hp1 : 1 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} (hPAQ : P * A * Q = P * A) (k : ℕ) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤ schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
      ∑ i ∈ Finset.range k, max 1 (p.toReal / 2) * singularValues A i ^ (p.toReal - 2) *
        (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

-- SO1
theorem _root_.IsStarProjection.matrixNorm_sub_mul_le_matrixNorm_sub_mul (Φ : SymmetricGauge)
    {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜} (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) :
    Φ.matrixNorm (A - A * Q) ≤ Φ.matrixNorm (A - P * A) := sorry

-- CB1 (tail-count form, 1 ≤ p ≤ 2, two-sided)
theorem _root_.IsStarProjection.schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {A : Matrix m n 𝕜}
    (hPAQ : P * A * Q = P * A) {k j : ℕ} {γ κ : ℝ} {β : ℕ → ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (hβ : ∀ i < k, 0 ≤ β i) (hβ0 : singularValues A k = 0 → ∀ i < k, β i = 0)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 - β i ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - A * Q) ^ p.toReal ≤
      (1 + k * γ * κ ^ p.toReal / ((j : ℝ) + 1)) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) * ∑ i ∈ Finset.range k, β i := sorry

-- CB1F (tail-count form, Frobenius, one-sided)
theorem _root_.IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq_le_of_singularValues_le_mul
    {P : Matrix m m 𝕜} (hP : IsStarProjection P) {A : Matrix m n 𝕜} {k j : ℕ} {γ κ : ℝ}
    {β : ℕ → ℝ} (hγ : 0 ≤ γ) (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 - β i ≤
      singularValues (P * A) i ^ 2) :
    frobNorm (A - truncatedSVD (P * A) k) ^ 2 ≤
      (1 + k * γ * κ ^ 2 / ((j : ℝ) + 1)) * frobNorm (A - truncatedSVD A k) ^ 2 +
        ∑ i ∈ Finset.range k, β i := sorry

-- CB2 (two candidates, 1 ≤ p ≤ 2)
theorem min_schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P₁ P₂ : Matrix m m 𝕜} {Q₁ Q₂ : Matrix n n 𝕜}
    (hP₁ : IsStarProjection P₁) (hQ₁ : IsStarProjection Q₁) (hP₂ : IsStarProjection P₂)
    (hQ₂ : IsStarProjection Q₂) {A : Matrix m n 𝕜} (h₁ : P₁ * A * Q₁ = P₁ * A)
    (h₂ : P₂ * A * Q₂ = P₂ * A) {k j : ℕ} {γ₁ γ₂ κ : ℝ} {β₁ β₂ : ℕ → ℝ} (hγ₁ : 0 ≤ γ₁)
    (hγ₂ : 0 ≤ γ₂) (hκ : 0 ≤ κ) (hβ₁ : ∀ i < k, 0 ≤ β₁ i) (hβ₂ : ∀ i < k, 0 ≤ β₂ i)
    (hβ0 : singularValues A k = 0 → ∀ i < k, β₁ i = 0 ∧ β₂ i = 0)
    (hritz₁ : ∀ i < k, singularValues A i ^ 2 - γ₁ * singularValues A k ^ 2 - β₁ i ≤
      singularValues (P₁ * A) i ^ 2)
    (hritz₂ : κ * singularValues A (k + j) < singularValues A k →
      ∀ i < k, singularValues A i ^ 2 - γ₂ * singularValues A k ^ 2 - β₂ i ≤
        singularValues (P₂ * A) i ^ 2) :
    min (schattenNorm p (A - A * Q₁) ^ p.toReal) (schattenNorm p (A - A * Q₂) ^ p.toReal) ≤
      (1 + k * max (γ₁ * κ ^ p.toReal / ((j : ℝ) + 1)) γ₂) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) *
          max (∑ i ∈ Finset.range k, β₁ i) (∑ i ∈ Finset.range k, β₂ i) := sorry

-- ST3 (head split, one-sided, 2 ≤ p)
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_add_rpow {p : ℝ≥0∞}
    (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P) (A : Matrix m n 𝕜)
    {L k : ℕ} (hLk : L ≤ k) :
    schattenNorm p (A - P * A) ≤
      schattenNorm p (truncatedSVD A L - P * truncatedSVD A L) +
        (schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
          ∑ i ∈ Finset.Ico L k,
            (singularValues A i ^ p.toReal - singularValues (P * A) i ^ p.toReal)) ^
          p.toReal⁻¹ := sorry

-- ST4
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_of_sq_singularValues_sub_le
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {A : Matrix m n 𝕜} {L k : ℕ} (hLk : L ≤ k) {δ γ θ κ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hκ : 1 ≤ κ)
    (hgap : ∀ h, h + 1 = L → singularValues A L ^ 2 ≤ (1 - θ) * singularValues A h ^ 2)
    (hflat : singularValues A L ≤ κ * singularValues A k)
    (hhead : ∀ i < L, singularValues A i ^ 2 - δ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2)
    (hmid : ∀ i, L ≤ i → i < k → singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - P * A) ≤
      Real.sqrt (L * δ / θ) * singularValues A k +
        (schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
          p.toReal / 2 * κ ^ (p.toReal - 2) * ((k : ℝ) - L) * γ *
            singularValues A k ^ p.toReal) ^ p.toReal⁻¹ := sorry

-- CB3 (tail-count form, 2 ≤ p < ∞, one-sided)
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_mul_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    {A : Matrix m n 𝕜} {k j : ℕ} {δ γ κ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hκ : 0 ≤ κ)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hhead : ∀ i < k, (1 + 1 / (2 * p.toReal)) * singularValues A k < singularValues A i →
      singularValues A i ^ 2 - δ * singularValues A k ^ 2 ≤ singularValues (P * A) i ^ 2)
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 ≤
      singularValues (P * A) i ^ 2) :
    schattenNorm p (A - P * A) ≤
      (k * Real.sqrt (2 * (p.toReal + 1) * δ) +
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
theorem HasOrthonormalCols.sq_sub_le_sq_singularValues_rsvd_cfc_of_le_singularValues
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

-- RZ4F
theorem HasOrthonormalCols.sum_sq_singularValues_sub_sq_singularValues_rbki_le
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {q : ℕ} (hq : 1 ≤ q) :
    ∑ i ∈ Finset.range r, (singularValues A i ^ 2 - singularValues (rbki A Ω q) i ^ 2) ≤
      4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
        frobNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 := sorry

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
theorem range_mul_blockKrylovMatrix_le_range_mul_fromCols_left (A : Matrix m n 𝕜)
    (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜) (q₁ q₂ : ℕ) :
    LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) Ω₁ q₁).mulVecLin ≤
      LinearMap.range (A * Matrix.fromCols (blockKrylovMatrix (Aᴴ * A) Ω₁ q₁)
        (blockKrylovMatrix (Aᴴ * A) Ω₂ q₂)).mulVecLin := sorry

theorem range_mul_blockKrylovMatrix_le_range_mul_fromCols_right (A : Matrix m n 𝕜)
    (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜) (q₁ q₂ : ℕ) :
    LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) Ω₂ q₂).mulVecLin ≤
      LinearMap.range (A * Matrix.fromCols (blockKrylovMatrix (Aᴴ * A) Ω₁ q₁)
        (blockKrylovMatrix (Aᴴ * A) Ω₂ q₂)).mulVecLin := sorry

theorem singularValues_rbki_le_singularValues_rbkiSum_left (A : Matrix m n 𝕜)
    (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜) (q₁ q₂ i : ℕ) :
    singularValues (rbki A Ω₁ q₁) i ≤ singularValues (rbkiSum A Ω₁ Ω₂ q₁ q₂) i := sorry

theorem singularValues_rbki_le_singularValues_rbkiSum_right (A : Matrix m n 𝕜)
    (Ω₁ : Matrix n l₁ 𝕜) (Ω₂ : Matrix n l₂ 𝕜) (q₁ q₂ i : ℕ) :
    singularValues (rbki A Ω₂ q₂) i ≤ singularValues (rbkiSum A Ω₁ Ω₂ q₁ q₂) i := sorry

-- TS2 (Frobenius, any sketch whose range contains both Krylov sketches)
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le
    {A : Matrix m n 𝕜} {Ω₁ : Matrix n l₁ 𝕜} {Ω₂ : Matrix n l₂ 𝕜} {Z₁ : Matrix n s₁ 𝕜}
    {Z₂ : Matrix n s₂ 𝕜} (hZ₁ : HasOrthonormalCols Z₁) (hZ₂ : HasOrthonormalCols Z₂)
    (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank) (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j : ℕ}
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {Y : Matrix n l 𝕜}
    (h₁ : LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) Ω₁ q₁).mulVecLin ≤
      LinearMap.range (A * Y).mulVecLin)
    (h₂ : LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) Ω₂ q₂).mulVecLin ≤
      LinearMap.range (A * Y).mulVecLin) :
    frobNorm (A - truncatedSVD (rsvd A Y) k) ^ 2 ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1)) * frobNorm (A - truncatedSVD A k) ^ 2 +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          frobNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2 := sorry

-- TS2c
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbkiSum_sq_le
    {A : Matrix m n 𝕜} {Ω₁ : Matrix n l₁ 𝕜} {Ω₂ : Matrix n l₂ 𝕜} {Z₁ : Matrix n s₁ 𝕜}
    {Z₂ : Matrix n s₂ 𝕜} (hZ₁ : HasOrthonormalCols Z₁) (hZ₂ : HasOrthonormalCols Z₂)
    (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank) (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j : ℕ}
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    frobNorm (A - truncatedSVD (rbkiSum A Ω₁ Ω₂ q₁ q₂) k) ^ 2 ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1)) * frobNorm (A - truncatedSVD A k) ^ 2 +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          frobNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2 := sorry

-- TS2m
theorem HasOrthonormalCols.min_frobNorm_sub_truncatedSVD_rbki_sq_le
    {A : Matrix m n 𝕜} {Ω₁ : Matrix n l₁ 𝕜} {Ω₂ : Matrix n l₂ 𝕜} {Z₁ : Matrix n s₁ 𝕜}
    {Z₂ : Matrix n s₂ 𝕜} (hZ₁ : HasOrthonormalCols Z₁) (hZ₂ : HasOrthonormalCols Z₂)
    (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank) (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j : ℕ}
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    min (frobNorm (A - truncatedSVD (rbki A Ω₁ q₁) k) ^ 2)
        (frobNorm (A - truncatedSVD (rbki A Ω₂ q₂) k) ^ 2) ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1)) * frobNorm (A - truncatedSVD A k) ^ 2 +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          frobNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2 := sorry

-- TS3 (Schatten 1 ≤ p ≤ 2, two-sided output, any sketch containing both Krylov sketches)
theorem HasOrthonormalCols.schattenNorm_sub_mul_rangeProjector_rsvd_rpow_le_of_range_le
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {A : Matrix m n 𝕜} {Ω₁ : Matrix n l₁ 𝕜} {Ω₂ : Matrix n l₂ 𝕜} {Z₁ : Matrix n s₁ 𝕜}
    {Z₂ : Matrix n s₂ 𝕜} (hZ₁ : HasOrthonormalCols Z₁) (hZ₂ : HasOrthonormalCols Z₂)
    (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank) (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j : ℕ}
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {Y : Matrix n l 𝕜}
    (h₁ : LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) Ω₁ q₁).mulVecLin ≤
      LinearMap.range (A * Y).mulVecLin)
    (h₂ : LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) Ω₂ q₂).mulVecLin ≤
      LinearMap.range (A * Y).mulVecLin) :
    schattenNorm p (A - A * rangeProjector (truncatedSVD (rsvd A Y) k)ᴴ) ^ p.toReal ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1)) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) *
          (4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
              specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 +
            4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
              frobNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2) := sorry

-- TS3c
theorem HasOrthonormalCols.schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    {A : Matrix m n 𝕜} {Ω₁ : Matrix n l₁ 𝕜} {Ω₂ : Matrix n l₂ 𝕜} {Z₁ : Matrix n s₁ 𝕜}
    {Z₂ : Matrix n s₂ 𝕜} (hZ₁ : HasOrthonormalCols Z₁) (hZ₂ : HasOrthonormalCols Z₂)
    (hΩ₁ : (Ω₁ᴴ * Z₁).rank = Z₁.rank) (hΩ₂ : (Ω₂ᴴ * Z₂).rank = Z₂.rank) {k j : ℕ}
    (hAZ₁ : A * Z₁ * Z₁ᴴ = truncatedSVD A k) (hAZ₂ : A * Z₂ * Z₂ᴴ = truncatedSVD A (k + j))
    {q₁ q₂ : ℕ} (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    schattenNorm p (A - A * rangeProjector (truncatedSVD (rbkiSum A Ω₁ Ω₂ q₁ q₂) k)ᴴ) ^ p.toReal ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1)) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) *
          (4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
              specNorm ((A - truncatedSVD A k) * Ω₁ * pinv (Z₁ᴴ * Ω₁)) ^ 2 +
            4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
              frobNorm ((A - truncatedSVD A (k + j)) * Ω₂ * pinv (Z₂ᴴ * Ω₂)) ^ 2) := sorry

end Det

/-! ## Wave 4: Gaussian start blocks -/

section Gaussian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l m n l₁ l₂ s : Type*}
  [Fintype l] [Fintype m] [Fintype n] [Fintype l₁] [Fintype l₂] [Fintype s] [DecidableEq m]
  [DecidableEq n] [DecidableEq s] {X₁ : Ω → Matrix n l₁ ℝ} {X₂ : Ω → Matrix n l₂ ℝ}

-- GR1 (the sketch residual of a Gaussian block against a frame)
theorem integrable_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X₁ (gaussianMatrix n l₁) μ) {Z : Matrix n s ℝ} (hZ : HasOrthonormalCols Z)
    (hs : Fintype.card s + 2 ≤ Fintype.card l₁) :
    Integrable (fun ω => frobNorm ((A - A * Z * Zᴴ) * X₁ ω * pinv (Zᴴ * X₁ ω)) ^ 2) μ := sorry

theorem integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X₁ (gaussianMatrix n l₁) μ) {Z : Matrix n s ℝ} (hZ : HasOrthonormalCols Z)
    (hs : Fintype.card s + 2 ≤ Fintype.card l₁) :
    ∫ ω, frobNorm ((A - A * Z * Zᴴ) * X₁ ω * pinv (Zᴴ * X₁ ω)) ^ 2 ∂μ =
      frobNorm (A - A * Z * Zᴴ) ^ 2 * Fintype.card s /
        ((Fintype.card l₁ : ℝ) - Fintype.card s - 1) := sorry

-- GR2 (tail twin)
theorem measureReal_frobNorm_sub_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X₁ (gaussianMatrix n l₁) μ) {Z : Matrix n s ℝ}
    (hZ : HasOrthonormalCols Z) (hs : Fintype.card s + 2 ≤ Fintype.card l₁) {τ : ℝ}
    (hτ : 0 < τ) :
    μ.real {ω | τ * (frobNorm (A - A * Z * Zᴴ) ^ 2 * Fintype.card s /
        ((Fintype.card l₁ : ℝ) - Fintype.card s - 1)) <
      frobNorm ((A - A * Z * Zᴴ) * X₁ ω * pinv (Zᴴ * X₁ ω)) ^ 2} ≤ τ⁻¹ := sorry

-- GI1
theorem integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (A : Matrix m n ℝ) {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ) (k : ℕ) :
    Integrable (fun ω => schattenNorm p (A - A * rangeProjector
      (truncatedSVD (rsvd A (Y ω)) k)ᴴ) ^ p.toReal) μ := sorry

-- GA0 (by-product: per-rank Frobenius bound for one RBKI run)
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X₁ (gaussianMatrix n l₁) μ) {k q : ℕ}
    (hk : k + 2 ≤ Fintype.card l₁) (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X₁ ω) q) k) ^ 2 ∂μ ≤
      (1 + 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1))) * frobNorm (A - truncatedSVD A k) ^ 2 +
        k * γ * singularValues A k ^ 2 := sorry

-- GA1 (general, Frobenius, expectation, any sketch containing both Krylov sketches)
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ}
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (h₁ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₁ ω) q₁).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin)
    (h₂ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₂ ω) q₂).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (Y ω)) k) ^ 2 ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- GA1c
theorem integral_frobNorm_sub_truncatedSVD_rbkiSum_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ}
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2 ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- GA1p (general, Schatten 1 ≤ p ≤ 2, expectation)
theorem
    integral_schattenNorm_sub_mul_rangeProjector_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ}
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (h₁ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₁ ω) q₁).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin)
    (h₂ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₂ ω) q₂).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rsvd A (Y ω)) k)ᴴ) ^ p.toReal ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- GA1pc
theorem integral_schattenNorm_sub_mul_rangeProjector_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ}
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) (hq₁ : 1 ≤ q₁)
    (hq₂ : 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∫ ω, schattenNorm p (A - A * rangeProjector
        (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q₂ : ℝ) - 1)) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1))) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- GA3 (tail form, 2 ≤ p < ∞, one-sided output)
theorem measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤)
    (A : Matrix m n ℝ) (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ) {k j q₁ q₂ : ℕ} (hk : 0 < k)
    (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂) {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hj : Real.exp 2 * k / (ε * p.toReal) ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + (p.toReal ^ (6 : ℝ)⁻¹ / (2 * ε ^ (3 : ℝ)⁻¹) + Real.sqrt (4 * p.toReal + 1) / 8) *
      Real.log (256 * k ^ 3 * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤ q₁)
    (hq₂ : 1 + Real.sqrt (4 * p.toReal + 1) / 8 *
      Real.log (256 * k ^ 2 * ((k : ℝ) + j) * (p.toReal + 1) *
        (min (Fintype.card m) (Fintype.card n) : ℕ) / (ε ^ 2 * δ)) ≤ q₂) :
    μ.real {ω | (1 + ε) * schattenNorm p (A - truncatedSVD A k) <
      schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)} ≤ δ := sorry

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
    (hq₂ : 1 + Real.log (12 / ε) / 3 ≤ q₂) :
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
    (hq₂ : 1 + Real.log (12 / ε) / 3 ≤ q₂) :
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
      C * (Real.log (k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁ → C * Real.log (1 / ε) ≤ q₂ →
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
      C * (Real.log (k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁ → C * Real.log (1 / ε) ≤ q₂ →
      ∫ ω, schattenNorm p (A - A * rangeProjector
          (truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)ᴴ) ^ p.toReal ∂μ ≤
        (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- GA3a (asymptotic form of GA3)
theorem
    exists_forall_measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l₁ l₂ : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq m] [DecidableEq n] [Fintype l₁] [Fintype l₂] (μ : Measure Ω)
      (A : Matrix m n ℝ) (X₁ : Ω → Matrix n l₁ ℝ) (X₂ : Ω → Matrix n l₂ ℝ) (k q₁ q₂ : ℕ)
      (ε δ : ℝ) (p : ℝ≥0∞),
      HasLaw X₁ (gaussianMatrix n l₁) μ → HasLaw X₂ (gaussianMatrix n l₂) μ → 2 ≤ p → p ≠ ⊤ →
      0 < k → 0 < ε → ε ≤ ε₀ → 0 < δ → k + 2 ≤ Fintype.card l₁ →
      C * (k + k / (ε * p.toReal) ^ (3 : ℝ)⁻¹) ≤ Fintype.card l₂ →
      C * ((p.toReal ^ (6 : ℝ)⁻¹ / ε ^ (3 : ℝ)⁻¹ + Real.sqrt p.toReal) *
        Real.log (Fintype.card l₂ * p.toReal * Fintype.card n / (ε * δ))) ≤ q₁ →
      C * (Real.sqrt p.toReal *
        Real.log (Fintype.card l₂ * p.toReal * Fintype.card n / (ε * δ))) ≤ q₂ →
      μ.real {ω | (1 + ε) * schattenNorm p (A - truncatedSVD A k) <
        schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k)} ≤ δ := sorry

end NLAlib
```
