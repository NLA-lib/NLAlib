# Low-rank approximation with $\varepsilon^{-1/3}$ products: the optional items

2026-11-24. Design note; **status: design only, revised after one independent review (§10; harness copy of the review:
`scratch/Review-LRA-OPTIONAL-Design.md` in the worktree), awaiting the maintainer's decisions (§8). Nothing
is proved and there is no skeleton.** Branch `design/lra-optional` from `cleanup/lra-cube-root`
@ `1bed77c6`. Stage LRA-OPTIONAL, board card T152. Targets: harness
`pilot/lra-optional-targets.json`. Decision sheet: harness `state/decisions/LRA-OPTIONAL.json`.
Every Lean statement of Appendix A elaborated with `sorry` proofs against the build at `1bed77c6`
(scratch file outside `NLAlib/`, not committed; §A.0).

The maintainer asked (2026-11-24): "do the optional stuff", that is the items that
`LowRank-CubeRootBlockKrylov.md` (stage 1, fully proved) deferred: MM-FROB, BLOCK-K, SINGLE-RUN,
INEXACT, P-LARGE (c). No lower bounds of any kind. Then: "they are in the library, right?" —
every item was checked against the library first (§0); what is there is reused, never re-proved.

Conventions as in stage 1: singular values indexed from $0$,
$\mathrm{OPT}_p = \|\mathbf A - \llbracket\mathbf A\rrbracket_k\|_{S_p}$,
$\mathbf H = \mathbf A^{\mathsf H}\mathbf A$,
$\mathbf M_t = (\mathbf A - \llbracket\mathbf A\rrbracket_t)\mathbf\Omega(\mathbf Z^{\mathsf H}\mathbf\Omega)^+$
for a frame $\mathbf Z$ with $\mathbf A\mathbf Z\mathbf Z^{\mathsf H} = \llbracket\mathbf A\rrbracket_t$.
**Known** = published, **planned** = proposed here with an outline, **checked** = derived by hand
for this note; the headline threshold chains were re-derived and checked numerically on grids
by the independent review (pure Python), the per-index lemmas by hand only (§8 Risks).

## Summary

| Item | Finding | Plan | Targets | Risk | Recommendation |
|---|---|---|---|---|---|
| MM-FROB | **Already in the library as an instance**: the proved range-inclusion theorem GA1 (`integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix`) with $\mathbf X_1 = \mathbf X_2 = \mathbf X$, $\mathbf Y = \mathbf K_q(\mathbf H, \mathbf X)$, $j = k-1$ is Musco–Musco's single-run $(1+\varepsilon)$ Frobenius bound for a block of $\ge 2k+1$ columns, with $\log(k/\varepsilon)$. Musco–Musco's Property 3 (the rank argument) is needed only for blocks of exactly $k$ | name the instance (headline, $p \le 2$ twin, asymptotic form) | 3 (S1 M2) | low | include (named statement; nothing new to prove) |
| BLOCK-K | **Blocks $k+2$ and $k+j+2$ are already covered** by GA1/GA1p ($\ell_1 \ge k+2$, $\ell_2 \ge k+j+2$; factors $k$, $k+j$ inside the logarithms). Exactly $k$ needs a small-ball bound for the least singular value of a square **real** Gaussian matrix: not in the library (the complex one is) | real square small ball; residual tail; tail headline with $\log(k^5/(\varepsilon\delta^3))$ (no dimension) | 3 (M3) | low–medium | **drop** (saves 2 columns per block) |
| SINGLE-RUN | The simulation identity `rbki_blockKrylovMatrix` and the single-vector simulated-block residual (`frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le`) are in the library, so the stage-1 range-inclusion theorems apply to one run **by composition only**, with the gap factor $\Delta^{-2(t-1)}$ on the top $t=k+j\approx6k\varepsilon^{-1/3}$ singular values: this is the route of Meyer–Musco–Musco 2024 (single vector matches BCW up to $\log(1/\text{gap})$; gap removable by a small random perturbation of the input). **BN23's proof is not a simulation**: it is a filter with roots at the intermediate singular values. That argument generalizes to rank $k$ and is gap-free: one run, block $2k+1$, depth $2(k/\varepsilon)^{1/3}\log(16k/\varepsilon)$, i.e. $O(k^{4/3}\varepsilon^{-1/3}\log(k/\varepsilon))$ products, dimension-free; rank 1 from a single vector in tail form (BN's setting) | root filter; per-index light-tail deficits; one-run Frobenius theorem; Gaussian; headline; asymptotic; single-vector rank-1 | 8 (S2 M5 L1) | medium (new as a statement for $k>1$; re-derived by the review) | include route (b); route (a) as an option (decision SR-RATE) |
| INEXACT | exact pinching for any pair (`IsStarProjection.schattenNorm_mul_mul_rpow_add_le`) and the Gram-defect-to-projector distance (`specNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect`) are in the library; missing is the final combination step without $\mathbf P\mathbf A\mathbf Q = \mathbf P\mathbf A$. **Scope:** only that step; it does not cover a rounded Krylov range (which does not contain the exact one) and still needs exact projectors and a Schatten-$p$ bound on $\mathbf P\mathbf A(\mathbf I-\mathbf Q)$ (§2.4) | perturbed pairing; tail-count form with $\|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|_2\le\eta$, $\|\cdot\|_{S_p}\le\eta_p$ | 2 (S1 M1) | low | include, knowing the scope (weakest batch) |
| P-LARGE (c) | **Achievable with known ingredients, for every $k$, in expectation**: BN23's weight (here $x^r$, $r=\lceil(p-2)/4\rceil$) in the filter makes the filtered tail energy a Schatten-$p$ quantity, so the $\log\min(m,n)$ of the proved GA3 disappears; the head split (SP1–CB3) is not needed | weighted filter lemmas, weighted per-index Gaussian deficits, $p \ge 2$ expectation theorem, headline, asymptotic form, tail form with $\log(1/\delta)$ | 13 (S5 M5 L3) | medium–high: for $k>1$ the statement is new (BN: rank 1; BCW: $\log d$); hand-checked, re-derived by the review | include |

Total **29 targets** (S 9, M 16, L 4), every one with an elaborated statement (Appendix A); 26
if BLOCK-K is dropped as recommended. **Prerequisites (not targets)**, being made by the
LRA-CUBE-ROOT cleanup: `exists_frame_residual` public (SR4, PL1, PL2) and RZ2's two private scalar
lemmas public (CR2); public names TBD by the cleanup. No new definition, interface, vocabulary row, named bound or
Mathlib deviation.

Headlines (planned; constants explicit; no dimension anywhere):

* **MM-FROB.** Gaussian $\mathbf X$ with $\ell \ge 2k+1$ columns, $0<\varepsilon\le1$,
  $q \ge 1 + \sqrt3\,\log(24k/\varepsilon)/(2\sqrt\varepsilon)$:
  $\mathbb E\|\mathbf A - \llbracket\mathsf{rbki}(\mathbf A,\mathbf X,q)\rrbracket_k\|_{\mathsf F}^2
  \le (1+\varepsilon)\mathrm{OPT}_2^2$.
* **SINGLE-RUN.** Same, with $q \ge 1 + 2(k/\varepsilon)^{1/3}\log(16k/\varepsilon)$. For one
  Gaussian start vector and $k=1$:
  $\mathbb P[\|\mathbf A - \llbracket\mathsf{rbki}(\mathbf A,\mathbf x,q)\rrbracket_1\|_{\mathsf F}^2
  > (1+\varepsilon)\mathrm{OPT}_2^2] \le \delta$ for
  $q \ge 1 + 2\varepsilon^{-1/3}\log(128/(\varepsilon\delta^3))$.
* **P-LARGE.** $2\le p<\infty$, blocks $2k+1$, $2(k+j)+1$, $r=\lceil(p-2)/4\rceil$,
  $j+1 \ge 2ek\varepsilon^{-1/3}$,
  $q_1 \ge 1 + r + \sqrt p\,\log(14pk/\varepsilon)/(2\varepsilon^{1/3})$,
  $q_2 \ge 1 + r + \sqrt p\,\log(8pk/\varepsilon)/2$:
  $\mathbb E\|\mathbf A - \llbracket\mathsf{rbkiSum}(\mathbf A,\mathbf X_1,\mathbf X_2,q_1,q_2)\rrbracket_k\|_{S_p}^p
  \le (1+\varepsilon)\mathrm{OPT}_p^p$. With $\varepsilon = p\varepsilon'$ (accuracy $\varepsilon'$
  in the norm) the depths are $p^{1/6}\varepsilon'^{-1/3}\log$ and the wide block
  $k(p\varepsilon')^{-1/3}$: BCW's rate, without their $\log d$.
* **INEXACT.** $\|\mathbf A - \mathbf A\mathbf Q\|_{S_p} \le \|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|_{S_p}
  + \bigl(\|\mathbf A\|_{S_p}^p - \|\mathbf P\mathbf A\mathbf Q\|_{S_p}^p\bigr)^{1/p}$ for every
  pair of orthogonal projectors.

## 0. Library check (what is already there)

Method: `grep` over `NLAlib/` (statement shapes and names) and the pinned Mathlib, after reading
the files named in the brief. Names may move under the concurrent cleanup of `cleanup/lra-cube-root`
(helper moves, the split of `Gaussian/BlockKrylovSum.lean` into `…Sum` and `…SumTail`, and the
rename of `exists_degree_lt_div_sq_le_exp_singularGapRatio'` to the unprimed name); the
mathematics does not depend on them.

| Needed | Found | Consequence |
|---|---|---|
| one run as a two-run instance | GA1 `integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix`, GA1p `integral_schattenNorm_sub_mul_rangeProjector_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix` (any $\mathbf Y$, any joint law, $\ell_1 \ge k+2$, $\ell_2\ge k+j+2$) | MM-FROB with $\ell \ge 2k+1$ is an instance |
| gapless Frobenius for one run | only GA0 `integral_frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul_of_hasLaw_gaussianMatrix` ($\mathrm{OPT}^2 + k\gamma\sigma_k^2$); `BlockKrylovGapless.lean` is spectral only | MM1 is a new *statement*, not new mathematics |
| blocks $k+2$ | GA1, GA1p, GA3 (`measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_gt_le_of_hasLaw_gaussianMatrix`) take $\ell_1 \ge k+2$ | BLOCK-K's gain is two columns |
| square Gaussian least singular value | complex only: `measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix` ($r^2x^2$), `RandomMatrix/Gaussian/Complex/LeastSingularValue.lean`; real: Gordon's `measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix` (useless when square), `measureReal_specNorm_pinv_gt_le_of_hasLaw_gaussianMatrix` needs $\lvert r\rvert<\lvert k\rvert$; deterministic step `exists_iInf_norm_mulVec_le_of_singularValues_le` | BK1 is new (real twin of the complex probe argument) |
| simulation | `rbki_blockKrylovMatrix` (Result rbki-simulated-block), `singularValues_sub_rbki_le_of_range_le`, `singularValues_sub_rbki_le_of_degree_lt_of_add_le` | SINGLE-RUN route (a) is composition |
| simulated-block residual | `frobNorm_sub_mul_mul_blockKrylovMatrix_mul_pinv_sq_le` (one vector, gap $\Delta$, factor $\Delta^{-2(t-1)}$); Gaussian/SmallBlock tail bounds | route (a) inherits $\Delta$; for a block of $b>1$ vectors there is none (block Vandermonde) |
| filters at the squared singular values | RZ1 `HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rsvd_cfc`, RZ2 `HasOrthonormalCols.sq_sub_le_sq_singularValues_rsvd_cfc_of_le_singularValues` (any `g : ℝ → ℝ`, tail bound on an interval), RZ3 `HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki`, `singularValues_rsvd_cfc_le_singularValues_rbki` | SINGLE-RUN reuses them through SR1 (bounds needed only at spectral points) |
| filtered residual (no sup bound) | head capture `HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le` (`Structural/Filter.lean`) already has the residual $(\mathbf A g(\mathbf H) - \mathbf A g(\mathbf H)\mathbf Z\mathbf Z^{\mathsf H})\mathbf\Omega(\mathbf Z^{\mathsf H}\mathbf\Omega)^+$; `IsStarProjection.sq_singularValues_sub_sq_specNorm_le` | CR1 is a two-line composition (S) |
| Gaussian moment of a filtered residual | GR1 `integral_frobNorm_sub_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix` holds for **any** matrix, so at $\mathbf A g(\mathbf H)$ | no Gaussian target for P-LARGE's residual |
| sup-bound tail filter | `specNorm_sub_mul_cfc_mul_mul_le`, `frobNorm_sub_mul_cfc_mul_mul_le` | CT1 is the weighted twin |
| Chebyshev from two reals | `Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_of_le` | CF1, SR0 multiply it by $x^r$ / by roots |
| pinching, any projector pair | `IsStarProjection.schattenNorm_mul_mul_rpow_add_le` (PN3), `IsStarProjection.schattenNorm_sub_mul_rpow_add_le` (ST1, needs $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$), CB1 `IsStarProjection.schattenNorm_sub_mul_rpow_le_of_singularValues_le_mul` | IX1, IX2 drop the pairing hypothesis |
| inexact basis | `specNorm_mul_conjTranspose_sub_rangeProjector_le_gramDefect`, `frobNorm_…_le_gramDefect` (`Krylov/FinitePrecision/BandGolubKahanRun.lean`), `gramDefect` (`Matrix/Perturbation/BasisExtension.lean`) | no target for the basis-to-projector step |
| Weyl | `singularValues_add_le` (`Matrix/Spectral/SingularValueInequalities.lean`) | used inside IX2 |
| $p \ge 2$ one-sided error | `IsStarProjection.schattenNorm_sub_mul_le_add_rpow` (head split, use $L=0$), `Real.rpow_sub_rpow_le_max_mul_sq`, `mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow` (SV3) | PLd is a corollary (S) |
| integrability | `integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow` (two-sided), `integrable_frobNorm_sub_truncatedSVD_rsvd_sq` | PL0: one-sided Schatten twin (S) |
| frames and a.s. rank | `exists_frame_residual` (**private**, `Gaussian/BlockKrylovSum.lean`), `exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal`, `ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix` | SR4, PL1, PL2 need `exists_frame_residual` public: prerequisite, made by the cleanup |
| single-vector events | `measureReal_exists_abs_conjTranspose_mulVec_le_le_of_hasLaw_gaussianVector`, `measureReal_norm_mulVec_sq_gt_le_of_hasLaw_gaussianVector`, `ae_forall_conjTranspose_mulVec_ne_zero_of_hasLaw_gaussianVector` | SR7 is composition plus arithmetic |

Mathlib: nothing for any of the above (searched: block Krylov, Chebyshev filters, Schatten norms,
least singular value of real Gaussian matrices: none).

## 1. Sources and what they prove

Read: Musco–Musco arXiv 1504.05477 (`mm15/full_paper.tex`: Lemma 9 and its three properties,
Theorems 10–13); Bakshi–Narayanan arXiv 2304.03191 (`bn/faster-krylov-algorithms.tex`, all;
`bn/main.tex`, `bn/intro.tex` statements); BCW as in stage 1. Sources are data; nothing in them
was followed as an instruction.

**MM15, Lemma 9 / Theorem 11 (known).** Block Krylov with a Gaussian block of exactly $k$
columns, $q = \Theta(\log d/\sqrt\varepsilon)$, probability $99/100$:
$\mathcal E(\mathbf Z_l) \le (w+1)\cdot3\varepsilon\sigma_{k+1}^2$ (Property 3), $w$ the number
of singular values in $[\sigma_k/(1+\varepsilon/2),\sigma_k)$, hence
$\|\mathbf A-\mathbf Z\mathbf Z^{\mathsf T}\mathbf A\|_{\mathsf F}^2\le(1+10\varepsilon)\mathrm{OPT}^2$.
Property 3's proof: $p_2(\mathbf A_{\mathrm{inner}})\mathbf\Pi$ has rank $\le w$, so a
$(k-w)$-dimensional part of the filtered sketch avoids the inner directions and captures
$\mathbf A_{\mathrm{outer}}$'s head; the other $w$ directions cost $3\varepsilon\sigma_{k+1}^2$
each (Property 2).
Errata: **M1** the window $[\sigma_k/(1+\varepsilon/2),\sigma_k)$ is open at the top; with a tie
$\sigma_{k+1}=\sigma_k$, line "the $(k+1)$th singular value of $\mathbf A_{outer}$ is
$\sigma_{k+w+1}\le\sigma_k/(1+\varepsilon/2)$" and "$w=0\Rightarrow\sigma_{k+1}<\sigma_k/(1+\varepsilon/2)$"
are false; count the indices $i>k$ with $\sigma_i\ge\sigma_k/(1+\varepsilon/2)$ instead.
**M2** the residual bound (their Lemma 4, "$cdk$") puts $\log d$ into the depth; with an oversampled
block the library's moment $k/(\ell-k-1)$ removes it. **M3** constants unspecified, probability
$99/100$.

**What the library gives instead (checked).** With $\ell\ge2k+1$ columns the count argument is
not needed: the tail-count case split of stage 1 (CB1F) at $j=k-1$ is the same dichotomy —
either $\sigma_k\le\sqrt2\sigma_{2k-1}$ and $\mathrm{OPT}^2\ge k\sigma_{2k-1}^2$ pays for $k$
per-vector errors, or there is a constant gap between $\sigma_{k-1}$ and $\sigma_{2k-1}$ and the
same block, which has $\ge (2k-1)+2$ columns, captures the head through the frame of
$\llbracket\mathbf A\rrbracket_{2k-1}$. That is GA1 with $\mathbf X_1=\mathbf X_2$.

**BN23, Theorem "Sharper Algorithm for LRA" (known).** Rank $1$, $p=O(1)$, one Gaussian start
vector, $O(\log(1/\varepsilon)/\varepsilon^{1/3})$ products, probability $0.99$, Schatten-$p$
in $p$-th powers. Proof: through BCW's pinching (their Lemma "Generalized Pythagorean") it
suffices to find $\mathbf w$ in the Krylov space with
$(\mathbf w^{\mathsf T}\mathbf\Lambda\mathbf w)^{p/2}\ge\lambda_1^{p/2}-\varepsilon\sum_{i\ge2}\lambda_i^{p/2}$;
four cases on $\tau=\sum_{i\ge2}\lambda_i^{p/2}$ (normalized $\lambda_1=1$): $\tau\ge1/\varepsilon$
trivial; many eigenvalues near $1$: Chebyshev with cut $1-\varepsilon^{2/3}/(2p)$; few
($\le\varepsilon^{-1/3}+1$) in $[1-\frac1{2p},1-\frac{\varepsilon}{2p}]$: **the polynomial
$x^{t/2}\prod(x-\lambda_i)$ with roots at those eigenvalues**; $\tau<1/2$: a power. In every case
the filter carries a factor $x^{\lceil p/2\rceil}$ so that
$\mathbb E\sum_{\text{tail}}(\phi(\lambda_i)g_i)^2\le(\varepsilon^4/p^2)\sum\lambda_i^p$, which is
bounded by $\tau$, not by the dimension.
So: **the mechanism is not a simulation of a wide block** (no Vandermonde conditioning appears);
it is (i) roots at the intermediate eigenvalues and (ii) a weight $x^{p/2}$ in the filter.
Errata: **B1** the algorithm box says $t=O(p^{-1}\log(1/\varepsilon)/\varepsilon^{1/3})$, the
lemma needs $t\ge Cp\varepsilon^{-1/3}\log(p/\varepsilon)$; **B2** "$=\sum\hat\phi(\lambda_i)^p$"
should be $^2$; **B3** Case 3 counts "at most $\varepsilon^{-1}+1$ such terms" for
$\varepsilon^{-1/3}+1$; **B4** Case 3's Markov step switches from the window edge
$1-\varepsilon/(2p)$ to $1-\varepsilon$; **B5** Case 4 takes $\hat\phi=x^L$ with
$L=O(\log(p/\varepsilon))$, but $\lambda_i\le1-\frac1{2p}$ needs $L=O(p\log(p/\varepsilon))$;
**B6** the theorem writes $\|\mathbf A(\mathbf I-\mathbf w\mathbf w^{\mathsf T})\|$ with
$\mathbf w$ a left vector; the proof gives $\mathbf A(\mathbf I-\mathbf v\mathbf v^{\mathsf T})$,
$\mathbf v\propto\mathbf A^{\mathsf T}\mathbf w$; **B7** two events of probability $0.99$ give
$0.98$, stated $0.99$; **B8** the authors' own margin notes flag Case 2's normalization and the
existence of the Chebyshev polynomial as unexplained. None affects the rate.

**BCW** as in stage 1 (E1–E16). The p ≥ 2 case there is the source of the $\log d$ (stage 1 E9,
E12; GA3).

## 2. The mathematics, item by item

### 2.1 MM-FROB (MM1–MM3): an instance of GA1

GA1 with $\mathbf X_1=\mathbf X_2=\mathbf X$ ($\ell\ge2k+1$), $q_1=q_2=q$, $j=k-1$,
$\mathbf Y=\mathbf K_q(\mathbf H,\mathbf X)$ (both inclusions are `le_rfl`;
$\mathsf{rsvd}(\mathbf A,\mathbf Y)=\mathsf{rbki}(\mathbf A,\mathbf X,q)$ by `rbki_def`) gives
$$\mathbb E\|\mathbf A-\llbracket\mathsf{rbki}\rrbracket_k\|_{\mathsf F}^2\le
\Bigl(1+2\gamma+4ke^{-2\sqrt2(q-1)\sqrt\gamma}\tfrac{k}{\ell-k-1}+4e^{-3(q-1)}\tfrac{2k-1}{\ell-2k}\Bigr)\mathrm{OPT}^2.$$
**MM1** ($\gamma=\varepsilon/6$, checked): $2\gamma=\varepsilon/3$;
$4ke^{-(2/\sqrt3)(q-1)\sqrt\varepsilon}\le\varepsilon/3$ for
$q-1\ge\sqrt3\log(12k/\varepsilon)/(2\sqrt\varepsilon)$; $4(2k-1)e^{-3(q-1)}\le\varepsilon/3$ for
$q-1\ge\log(24k/\varepsilon)/3$, implied. Threshold
$q\ge1+\sqrt3\log(24k/\varepsilon)/(2\sqrt\varepsilon)$, any $\ell\ge2k+1$. **MM2**: the same from
GA1p, $1\le p\le2$, two-sided output. **MM3**: asymptotic form, "$O(\log(k/\varepsilon)/\sqrt\varepsilon)$
depth suffices".
Product count $2\ell q = O(k\varepsilon^{-1/2}\log(k/\varepsilon))$, as Musco–Musco, without
$\log d$. MM's literal block of $k$ columns (Property 3) is **not planned** (variant of BLOCK-K,
decision MM-FROB).

### 2.2 BLOCK-K (BK1–BK3)

What exactly $k$ needs: for a frame $\mathbf Z$ with $s$ columns and a Gaussian block with $s$
columns, $\mathbf M=\mathbf S\mathbf G_2\mathbf G_1^{-1}$ with $\mathbf G_1=\mathbf Z^{\mathsf H}\mathbf X$
square and $\mathbf G_2$ independent. $\mathbb E\|\mathbf G_1^{-1}\|^2=\infty$, so only a tail.
**BK1** (checked): $\mathbb P[\sigma_{\min}(\mathbf G)\le x]\le\lvert r\rvert^{3/2}x$ for an
$r\times r$ real Gaussian: `exists_iInf_norm_mulVec_le_of_singularValues_le` puts a column within
$\sqrt r\,x$ of the span of the others; given the others, that distance is $\lvert g\rvert$,
$g\sim N(0,1)$ (`gaussianReal_abs_le_le`: $\le\sqrt r x$); union bound over $r$ columns. The proof
shape is that of the complex file. **BK2**: with probability $\ge1-\delta$,
$\|\mathbf M\|_{\mathsf F}^2\le8s^4\|\mathbf S\|_{\mathsf F}^2/\delta^3$ (Markov on
$\|\mathbf S\mathbf G_2\|_{\mathsf F}^2$, mean $s\|\mathbf S\|_{\mathsf F}^2$, at $\delta/2$; BK1 at
$\delta/2$). **BK3** (TS2 on the two events, $\delta/2$ each, $\|\mathbf M_t\|^2\le64t^4\mathrm{OPT}^2/\delta^3$):
blocks $k$ and $k+j$, $j+1\ge6k\varepsilon^{-1/3}$,
$q_1\ge1+\log(768k^5/(\varepsilon\delta^3))/(2\sqrt2\varepsilon^{1/3})$,
$q_2\ge1+\log(768(k+j)^4/(\varepsilon\delta^3))/3$ ⟹
$\mathbb P[\|\cdot\|_{\mathsf F}^2>(1+\varepsilon)\mathrm{OPT}^2]\le\delta$. The brief's
"$\log(n/\delta)$" becomes $\log(k/(\varepsilon\delta))$: no dimension.
When $k+j>\lvert n\rvert$ the wide block is wider than the frame (handled as in stage 1, by the
frame of $\min(k+j,\lvert n\rvert)$ columns; the residual vanishes).

### 2.3 SINGLE-RUN (SR0–SR7)

**Route (a), simulation — composition only, gap-dependent (not planned).**
$\mathsf{rbki}(\mathbf A,\mathbf\Omega,q)$ contains $\mathbf K_{q_1}(\mathbf H,\mathbf\Omega)$ and
$\mathbf K_{q_2}(\mathbf H,\mathbf K_s(\mathbf H,\mathbf\Omega))$ for $q_1\le q$, $s+q_2\le q+1$
(`rbki_blockKrylovMatrix`, `singularValues_sub_rbki_le_of_degree_lt_of_add_le`), so TS2 applies
with $\mathbf\Omega_2=\mathbf K_s(\mathbf H,\mathbf\Omega)$. Its residual
$\|(\mathbf A-\llbracket\mathbf A\rrbracket_t)\mathbf K_s(\mathbf Z_t^{\mathsf H}\mathbf K_s)^+\|$
is bounded in the library only for one start vector, by $\Delta^{-2(t-1)}\sum g_i^{-2}\|\cdot\|^2$
under $\sigma_{i+1}^2\le(1-\Delta)\sigma_i^2$ for the top $t=k+j\approx6k\varepsilon^{-1/3}$ values: the
depth then grows by $\approx\frac23 t\log(1/\Delta)$. For a block of $b>1$ vectors the simulated
block is a block Vandermonde matrix; no bound is in the library or in the sources, and it would
need gaps too. For **one start vector** (any $k$) this is the route of Meyer–Musco–Musco
[arXiv 2305.02535, SODA 2024; abstract in harness `research/lra-optional/`]: a single vector run
for $t$ iterations matches block size $\ell\ge k$ run for $O(t/\ell)$ iterations up to a
logarithmic dependence on the smallest gap, which a small random perturbation of the input
removes; they state that this matches BCW for Schatten norms. With the library's pieces it gives
BCW's $k\varepsilon^{-1/3}$ count with an additive $\approx t\log(1/\Delta)$ in the depth, under
the gap hypothesis (decision SR-RATE, option b; about 3 targets, specified at skeleton if chosen).
The perturbation step needs tail bounds for gaps of random-matrix spectra, which the library does
not have (not planned). Chen–Epperly–Meyer–Musco–Rao 2025 (block size) is related; not read.

**Route (b), roots in the filter — gap-free, every $k$ (planned).** Light tail:
$\sqrt2\,\sigma_{k+j}\le\sigma_k$. Let $I=\{k,\dots,k+j-1\}$. For $i<k$ (checked):

* *Degenerate case* $\sigma_k=0$: no roots, $g\equiv1$; then $\mathbf M_k=\mathbf0$ and RZ1 gives
  exact capture.
* *Case A*, $\sigma_i^2\ge(1+\eta)\sigma_k^2$: RZ1 with the frame of $\llbracket\mathbf A\rrbracket_k$
  and $f=\prod_{r\in I}(x-\sigma_r^2)\cdot T$, $T$ Chebyshev for $[0,\sigma_{k+j}^2]$ vs
  $[\sigma_k^2,\infty)$. At the head, each root factor is $\ge\eta\sigma_k^2$; on the spectral
  points of $[0,\sigma_k^2]$ it is either $0$ (a root) or $\le\sigma_k^2$. So
  $(a/c)^2\le\eta^{-2j}\cdot4e^{-8d(\sqrt2-1)}\le\eta^{-2j}4e^{-3d}$, $d=q-1-j$.
* *Case B*, $\sigma_i^2<(1+\eta)\sigma_k^2$: RZ2 (cut form) with cut
  $\tau^2=(1-\eta)\sigma_k^2$, roots at the $r\in I$ with $\sigma_r^2\le\tau^2$ (closed cut: RZ2's
  tail bound is on $[0,\tau^2]$, so a value at $\tau^2$ must be a root; head factors
  $\ge\eta\sigma_k^2$, $\eta\le\frac12$ so $\sigma_{k+j}^2\le\tau^2$). Loss $\sigma_i^2-\tau^2\le2\eta\sigma_k^2$.

Both cases use bounds only at spectral points (T is large on $(\sigma_{k+j}^2,\sigma_k^2)$), so
SR1 is needed in both; RZ1/RZ2 take a function $g:\mathbb R\to\mathbb R$ with a
bound on an interval, and SR1 supplies $g$ equal to $f$ on the spectrum of $\mathbf H$ and $0$
elsewhere (`cfc_congr`; SR1 needs $a\ge0$ for the non-spectral points, B1 of the review). Result **SR2**:
$\sigma_i(\mathsf{rbki}(\mathbf A,\mathbf\Omega,q))^2\ge\sigma_i^2-2\eta\sigma_k^2-4\eta^{-2j}e^{-3(q-1-j)}\|\mathbf M_k\|_2^2$.
**SR3** (Frobenius, one run): case split at $\sigma_k\le\sqrt2\sigma_{k+j}$ — heavy: CB1F with RZ3
(stage 1); light: ST2T with SR2 —
$$\|\mathbf A-\llbracket\mathsf{rbki}\rrbracket_k\|_{\mathsf F}^2\le
\Bigl(1+\tfrac{2k\gamma}{j+1}+2k\eta\Bigr)\mathrm{OPT}^2+4k\bigl(e^{-2\sqrt2(q-1)\sqrt\gamma}+\eta^{-2j}e^{-3(q-1-j)}\bigr)\|\mathbf M_k\|_2^2 .$$
**SR4**: Gaussian, $\mathbb E\|\mathbf M_k\|_2^2\le\frac{k}{\ell-k-1}\mathrm{OPT}^2$ (GR1).
**SR5** (checked): $\ell\ge2k+1$, $u=(k/\varepsilon)^{1/3}$, $j+1=\lceil u\rceil$,
$\eta=\varepsilon/(8k)$, $\gamma=\varepsilon(j+1)/(8k)\le\frac14$, $L=\log(16k/\varepsilon)$: the
four terms are each $\le\varepsilon/4$ when $q-1\ge uL$ (heavy) and
$q-1\ge u(1+L)$ (light; $3(q-1-j)\ge2j\log(8k/\varepsilon)+L$); both follow from
$q\ge1+2uL$. **SR6**: asymptotic form. **SR7** ($k=1$, one vector, BN's setting): on
$\{\lvert\mathbf z^{\mathsf T}\mathbf x\rvert>\delta/2\}\cap\{\|(\mathbf A-\llbracket\mathbf A\rrbracket_1)\mathbf x\|^2\le2\mathrm{OPT}^2/\delta\}$
(SmallBlock's two events) $\|\mathbf M_1\|^2\le8\mathrm{OPT}^2/\delta^3$; SR3 at $k=1$ with
$L'=\log(128/(\varepsilon\delta^3))$ gives $q\ge1+2\varepsilon^{-1/3}L'$.

**Where general $k$ stops (precisely).** One polynomial is applied to all $\ell$ columns, so the
light case spends $j$ degrees on roots, and the balance of the two cases
($j^{3/2}\approx\sqrt{k/\varepsilon}$) is $j\approx(k/\varepsilon)^{1/3}$: one run costs
$O(k^{4/3}\varepsilon^{-1/3}\log(k/\varepsilon))$ products, against BCW's
$O(k\varepsilon^{-1/3}\log)$ for two runs. It beats Musco–Musco's single run
($k\varepsilon^{-1/2}$) iff $k<\varepsilon^{-1/2}$; MM1 covers the other regime. Whether one run
achieves $k\varepsilon^{-1/3}$ without gap hypotheses is **not derived here**; Meyer–Musco–Musco
reach it from one vector with a $\log(1/\text{gap})$ cost, or after a small random perturbation of
the input (route (a) above). For $k=1$ it is BN's theorem (Frobenius; their Schatten-$p$ for $p>2$ would
combine SR with P-LARGE's weight — not planned).

### 2.4 INEXACT (IX1, IX2)

* **IX1** (checked): $\mathbf A-\mathbf A\mathbf Q=\mathbf P\mathbf A(\mathbf I-\mathbf Q)+(\mathbf I-\mathbf P)\mathbf A(\mathbf I-\mathbf Q)$;
  triangle inequality and PN3 give
  $\|\mathbf A-\mathbf A\mathbf Q\|_p\le\|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|_p+(\|\mathbf A\|_p^p-\|\mathbf P\mathbf A\mathbf Q\|_p^p)^{1/p}$,
  any orthogonal projectors, $p\ge1$. At $\mathbf P\mathbf A\mathbf Q=\mathbf P\mathbf A$ it is ST1.
* **IX2**: CB1 with the pairing replaced by $\|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|_2\le\eta$
  and $\|\mathbf P\mathbf A(\mathbf I-\mathbf Q)\|_{S_p}\le\eta_p$ (a program may use
  $\eta_p=\operatorname{rank}(\mathbf P)^{1/p}\eta$): Weyl gives
  $\sigma_i(\mathbf P\mathbf A\mathbf Q)^2\ge\sigma_i(\mathbf P\mathbf A)^2-2\eta\sigma_i(\mathbf A)$
  (also when $\sigma_i(\mathbf P\mathbf A)<\eta$); then IX1, SC1 and CB1's arithmetic: the absolute
  errors become $\beta_i+2\eta\sigma_i$. Junk hypothesis at $\sigma_k=0$, $p<2$: $\eta=0$, $\beta=0$.

**What the batch does NOT give a finite-precision routine.** (1) Only the final combination step
(Rayleigh–Ritz output to the two-sided error) is covered. (2) $\mathbf P$ and $\mathbf Q$ are
exact orthogonal projectors; a computed basis enters through the library's Gram-defect bound and
an output perturbation (triangle inequality), not through a statement here. (The planned IX3,
deficits under a nearby non-projector, had no consumer in the batch and was dropped.) (3) The
deficit hypotheses of $\mathbf P$ are the routine's burden; in floating point the computed Krylov
range does **not** contain the exact Krylov range, so the range-inclusion theorems of stage 1 do
not apply to a rounded run, and nothing here repairs that (the library's RBKI obstacle, stage 1
§8). (4) One-sided outputs ($p\ge2$, Frobenius) need no new statement: they take any projector.
Consumer: the routines stage; a program discharges $\eta$, $\eta_p$ (residual of the small SVD)
and the Gram defect; the theorems stay about abstract projectors (maintainer's preference).

### 2.5 P-LARGE (c) (CF1, CR1, CR2, CT1, PLd, PL0–PL6)

**Answer to (c): achievable with known arguments, for every $k$, in expectation.** Why the
dimension entered GA3: the deficits were bounded by $(a/c)^2\|\mathbf M_t\|^2$ with a sup bound
$a$ of the filter on the tail, and $\mathbb E\|\mathbf M_t\|_{\mathsf F}^2\propto\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{\mathsf F}^2$,
which for $p>2$ is up to $N^{1-2/p}$ times $\sigma_t^{2-p}\mathrm{OPT}_p^p$. Fix (BN's weight):
keep the filtered residual $\mathbf R=(\mathbf B-\mathbf B\mathbf Z\mathbf Z^{\mathsf H})\mathbf X(\mathbf Z^{\mathsf H}\mathbf X)^+$,
$\mathbf B=\mathbf A f(\mathbf H)$, $f=x^r T$, $4r+2\ge p$. GR1 gives
$\mathbb E\|\mathbf R\|_{\mathsf F}^2=\frac{t}{\ell-t-1}\sum_{i\ge t}\sigma_i^2f(\sigma_i^2)^2$
and on the tail $x f(x)^2\le a^2\sigma_t^{4r+2-p}x^{p/2}$, so (CT1)
$\sum_{i\ge t}\sigma_i^2f(\sigma_i^2)^2\le a^2\sigma_t^{4r+2-p}\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{S_p}^p$;
at the head $\lvert f\rvert\ge c\,\sigma_i^{2r}$. Hence (checked)
$$\sigma_i^{p-2}\,\mathbb E\,d_i\le(a/c)^2\Bigl(\tfrac{\sigma_t}{\sigma_i}\Bigr)^{4r+2-p}\tfrac{t}{\ell-t-1}\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{S_p}^p\le(a/c)^2\tfrac{t}{\ell-t-1}\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{S_p}^p,$$
**relative to $\sigma_i$ itself**: large head values need no head split. The p-th power error of
the one-sided output is $\le\mathrm{OPT}^p+\sum_{i<k}\frac p2\sigma_i^{p-2}d_i$ (PLd), and each
index falls in one regime ($\theta=1/p$, $\kappa^2=1+1/p$):

| Regime | Run | Lemma | Contribution to $\mathbb E$ (per index) |
|---|---|---|---|
| I: $\sigma_i^2\ge(1+\frac1p)\sigma_k^2$ | 1, frame $k$ | PL1 ($t=k$), gap ratio $\ge\theta/(1+\sqrt2)^2$, $8\sqrt{\cdot}\ge\frac83\sqrt\theta$ | $2pe^{-\frac83(q_1-1-r)/\sqrt p}\frac{k}{\ell_1-k-1}\mathrm{OPT}^p$ |
| II, heavy ($\sigma_k^2\le(1+\frac1p)\sigma_{k+j}^2$) | 1, frame $k$ | PL2 (weighted RZ3: gap or cut at $\sigma_i^2-\gamma\sigma_k^2$, ratio $\ge\gamma/8$); $\sigma_i^{p-2}\le\sqrt e\sigma_k^{p-2}$; SV3 | $\frac{pe}2\frac{\gamma}{j+1}\mathrm{OPT}^p+2\sqrt e\,pe^{-2\sqrt2(q_1-1-r)\sqrt\gamma}\frac{k}{\ell_1-k-1}\mathrm{OPT}^p$ |
| II, light | 2, frame $k+j$ | PL1 ($t=k+j$; $(1+\frac1p)\sigma_{k+j}^2\le\sigma_i^2$) | $2pe^{-\frac83(q_2-1-r)/\sqrt p}\frac{k+j}{\ell_2-k-j-1}\mathrm{OPT}^p$ |

Summing over $i<k$ gives **PL3** (Appendix A); integrability of each term comes from PL0b
(a squared singular value of the output is bounded by $\sigma_i(\mathbf A)^2$ and measurable). **PL4** (checked; $\gamma=\varepsilon^{2/3}/p$):
the four terms are $\le\varepsilon/4$ under $j+1\ge2ek\varepsilon^{-1/3}$,
$q_1\ge1+r+\sqrt p\log(14pk/\varepsilon)/(2\varepsilon^{1/3})$ (covers
$\sqrt p\log(8\sqrt e\,pk/\varepsilon)/(2\sqrt2\varepsilon^{1/3})$ and
$\frac38\sqrt p\log(8pk/\varepsilon)$), $q_2\ge1+r+\sqrt p\log(8pk/\varepsilon)/2$.
**PL6** (tail, dimension-free, $\delta$ only in logarithms): the deterministic part
$\frac{pe}{2}k\gamma/(j+1)\le\varepsilon/2$ ($j+1\ge ek\varepsilon^{-1/3}$); the random part
$W=\sum_i\frac p2\sigma_i^{p-2}\max(0,d_i-\det_i)$ has $\mathbb EW\le\frac{\varepsilon\delta}2\mathrm{OPT}^p$
(logarithms of $20pk/(\varepsilon\delta)$, $12pk/(\varepsilon\delta)$), Markov. PL2 is stated
with $\max(0,\cdot)$ for that reason. **PL5**: asymptotic form, from PL3 at general sizes (residual factors $\le1$ for
$\ell_1\ge2k+1$, $\ell_2\ge2(k+j)+1$, $j$ chosen in the proof), not from the exact-size PL4. At $p=2$ ($r=0$) PL4 is a
Frobenius bound of the same shape as GA2 with different constants.

**Status of the claim.** For $k=1$ the mechanism is BN's; for $k>1$ the dimension-free
statement is new as a statement (BN: rank 1; BCW and stage 1: $\log d$), checked by hand and
re-derived by the independent review; risk medium–high (a constant could be wrong, the rate was
re-derived twice). Docstrings cite BN and BCW for the method, without "new"/"improved" wording.
**Norm form** (decision P-FORM): with $\varepsilon\le1$ in $p$-th powers, the norm accuracy
$\varepsilon'=\varepsilon/p$ is covered only for $\varepsilon'\le1/p$; the docstring says so.

What remains of the stage-1 chain: GA3 and SP1/HD1/HD2/ST3/ST4/CB3 stay (proved; GA3 is
superseded in rate, not removed). The new statements are about the one-sided output; the
two-sided output inherits them (`schattenNorm_sub_mul_rangeProjector_le_schattenNorm_sub_truncatedSVD_rsvd`).

## 3. Objects, interfaces, statement shapes (design items 1–3)

**Objects.** None new. Used: `rbki`, `rbkiSum`, `rsvd`, `cfc`, `Set.indicator`,
`singularValues`, `truncatedSVD`, `schattenNorm`, `frobNorm`, `specNorm`, `pinv`,
`rangeProjector`, `IsStarProjection`, `HasOrthonormalCols`, `gaussianMatrix`, `gaussianVector`,
`HasLaw`. **Interfaces.** None (a predicate "inexact Rayleigh–Ritz pair" was considered for
INEXACT and rejected: two inequalities, no consumer yet; decide at the routines stage).
**Shapes.** Field `RCLike 𝕜` for deterministic statements (SR1–SR3, CR1, CR2, CT1, PLd, IX1, IX2),
ℝ for Gaussian ones; index types `Type*` + `Fintype`; headlines MM1, SR5 at general `l` with
`2 * k + 1 ≤ Fintype.card l`, PL4/PL6/BK3 at `Fin` sizes as stage 1. Exponents `p : ℝ≥0∞`,
`2 ≤ p`, `p ≠ ⊤`, powers `^ p.toReal`; the weight degree as a hypothesis
`p.toReal ≤ 4 * r + 2` in the general forms and `⌈(p.toReal - 2) / 4⌉₊` in headlines.
**Constants** written out ($4$, $2\sqrt2$, $3$, $8/3$, $e$, $\sqrt e$; thresholds $24$, $16$,
$128$, $14$, $8$, $20$, $12$, $768$): readable forms [B6], no named bound, `docs/constants.toml`
unchanged. Asymptotic forms MM3, SR6, PL5 follow B4/N17 (root namespace, constants first).

## 4. Consumers (item 4)

| Statement | Consumer |
|---|---|
| MM1–MM3 | the certified block Golub–Kahan program today (`BlockKrylov.storedOutput_eq_rbki`, `integral_comp_storedOutput`): a $(1+\varepsilon)$ Frobenius guarantee for the program the library already certifies; explorer pairing with the spectral gapless result |
| SR1 | every filter argument with roots or bounds only on the spectrum (deflation, restarted Krylov) |
| SR2–SR7 | the same program: one run, no second block, no selection; BN's rank-1 setting (SR7) |
| CF1, CR1, CR2, CT1 | every dimension-free bound in a norm stronger than Frobenius on the tail; Nyström in Schatten norms |
| PL0–PL6 | the explorer's $p>2$ entry (replaces GA3's $\log\min(m,n)$); routines for $p>2$ (one-sided output, any projector) |
| IX1, IX2 | the routines stage: the final combination step with a computed row basis $\hat{\mathbf Q}$ |
| BK1 | any square-Gaussian argument (smoothed analysis over ℝ; the complex twin exists) |
| BK2, BK3 | BCW's literal block sizes |

## 5. Files and placement (item 5)

New files:

* `NLAlib/LowRank/Structural/BlockKrylovFrobenius.lean`: SR1, SR2, SR3 (one run, gap-free
  deficits and Frobenius error). SR1's natural home is `LowRank/Structural/RitzValues.lean`
  (filters at the squared singular values); flagged: placed here to keep RitzValues under the
  1000-line warning and out of the concurrent cleanup.
* `NLAlib/LowRank/Gaussian/BlockKrylovFrobenius.lean`: MM1–MM3, SR4–SR7 (one run, Frobenius and
  $p\le2$, Gaussian). Imports `Gaussian/BlockKrylovSum` (MM) and `Gaussian/SmallBlock` (SR7).
* `NLAlib/LowRank/Structural/FilteredResidual.lean`: CR1, CR2, CT1 (deficits with the filtered
  residual; its tail energy).
* `NLAlib/LowRank/Gaussian/BlockKrylovSumSchatten.lean`: PL1–PL6 ($p\ge2$ without the
  dimension). PL1, PL2 are one-run lemmas; flagged: their home would be next to GA0 in
  `Gaussian/BlockKrylovSum.lean`, which the cleanup is splitting.
* `NLAlib/RandomMatrix/Gaussian/LeastSingularValue.lean`: BK1 (real twin of
  `RandomMatrix/Gaussian/Complex/LeastSingularValue.lean`).

Additions to existing files:

* CF1, SR0 → `NLAlib/ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean`,
  next to `exists_degree_lt_div_sq_le_exp_of_le` (statements about polynomials and reals).
* PLd, IX2 → `NLAlib/LowRank/Structural/SingularValueDeficit.lean` (error from deficits).
* IX1 → `NLAlib/Matrix/Norms/SchattenPinching.lean` (pinching for a projector pair).
* PL0, PL0b → `NLAlib/LowRank/Random/RangeFinder.lean`, next to
  `integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow` and
  `integrable_frobNorm_sub_truncatedSVD_rbki_sq`.
* BK2 → `NLAlib/LowRank/Gaussian/RangeFinder.lean`, next to GR1/GR2. BK3 → the tail file of the
  cleanup split (`Gaussian/BlockKrylovSumTail.lean`, or `BlockKrylovSum.lean` if not split).
* **Prerequisites from the LRA-CUBE-ROOT cleanup (not targets):** `exists_frame_residual`
  (private, `Gaussian/BlockKrylovSum.lean`) made public, statement unchanged (SR4, PL1, PL2);
  RZ2's private scalar lemmas `sq_sub_mul_sum_le_sum`,
  `sq_sub_mul_norm_sq_le_norm_conjTranspose_mulVec_sq` (`Structural/RitzValues.lean`) made public
  (CR2). The cleanup agent is making them now; public names TBD there.
* No vocabulary row, no `docs/constants.toml` entry, no Mathlib deviation.

## 6. Targets

Sizes S/M/L. "Uses" names library declarations; "Needs" names targets. Batch = item.

### Wave 0

| Id | Batch | Statement | Size | Needs | Uses / outline |
|---|---|---|---|---|---|
| MM1 | MM-FROB | one run, $\ell\ge2k+1$, $(1+\varepsilon)$ Frobenius | M | — | GA1 at $\mathbf X_1=\mathbf X_2$, $\mathbf Y=\mathbf K_q$, $j=k-1$, $\gamma=\varepsilon/6$; `rbki_def`, `measurable_blockKrylovMatrix`; three terms $\le\varepsilon/3$ |
| MM2 | MM-FROB | the same, Schatten $1\le p\le2$, two-sided | S | — | GA1p; MM1's arithmetic (share a private lemma) |
| BK1 | BLOCK-K | real square least singular value small ball | M | — | `exists_iInf_norm_mulVec_le_of_singularValues_le`, `gaussianReal_abs_le_le`, independence of columns; mirror of the complex probe file |
| SR0 | SINGLE-RUN | Chebyshev times roots | S | — | `exists_degree_lt_div_sq_le_exp_of_le`; $\prod(X-C\rho)$, `Multiset.prod` bounds |
| SR1 | SINGLE-RUN | filter bounds only at squared singular values | S | — | `cfc_congr` on `spectrum ℝ (Aᴴ * A)`; eigenvalues of $\mathbf H$ are $\sigma_i^2$, $i<\lvert n\rvert$ |
| CF1 | P-LARGE | Chebyshev times $x^r$ | S | — | `exists_degree_lt_div_sq_le_exp_of_le`, multiply by $X^r$ |
| CR1 | P-LARGE | gap form, filtered residual | S | — | `IsStarProjection.sq_singularValues_sub_sq_specNorm_le` + `HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le` at `lpGauge ⊤` (RZ1's proof without its last step) |
| CR2 | P-LARGE | cut form, filtered residual below the cut | L | — | RZ2's proof with $\mathbf f=\mathbf A(g\mathbf 1_{<\tau^2})(\mathbf H)(\mathbf I-\mathbf Z\mathbf Z^{\mathsf H})\mathbf\Omega(\mathbf Z^{\mathsf H}\mathbf\Omega)^+\tilde{\mathbf c}$; RZ2's private scalar lemmas (`sq_sub_mul_sum_le_sum`, `sq_sub_mul_norm_sq_le_norm_conjTranspose_mulVec_sq`) to be made public or re-proved |
| CT1 | P-LARGE | filtered tail energy $\le b\,\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{S_p}^p$ | M | — | SVD of $\mathbf A-\llbracket\mathbf A\rrbracket_t$, `frobNorm_sub_mul_cfc_mul_mul_le`'s column argument, `schattenNorm_sub_truncatedSVD_rpow_eq_add_sum` |
| PLd | P-LARGE | one-sided truncated output, $p\ge2$, from squared deficits | S | — | `IsStarProjection.schattenNorm_sub_mul_le_add_rpow` at $L=0$ for $\mathbf\Pi$ with $\mathbf\Pi\mathbf A=\llbracket\mathbf P\mathbf A\rrbracket_k$ (`IsStarProjection.rangeProjector_truncatedSVD_mul_mul`), `Real.rpow_sub_rpow_le_max_mul_sq` |
| PL0 | P-LARGE | integrability, one-sided Schatten $p$-th power | S | — | copy of `integrable_schattenNorm_sub_mul_rangeProjector_rsvd_rpow` |
| IX1 | INEXACT | pinching without the pairing | S | — | `IsStarProjection.schattenNorm_mul_mul_rpow_add_le`, `schattenNorm_add_le` |
| PL0b | P-LARGE | integrability of $\sigma_i(\mathsf{rbki}(\mathbf A,\mathbf X,q))^2$ | S | — | `measurable_singularValues`, `measurable_rsvd`, `measurable_blockKrylovMatrix`; bounded by $\sigma_i(\mathbf A)^2$ |

### Wave 1

| Id | Batch | Statement | Size | Needs | Uses / outline |
|---|---|---|---|---|---|
| MM3 | MM-FROB | asymptotic form | M | MM1 | stage-1 `le_one_and_exists_thresholds` pattern; $C$ absorbs $\sqrt3/2$, $\log24$ |
| BK2 | BLOCK-K | residual tail, square block | M | BK1 | `measureReal_gt_add_mul_le_of_hasLaw_gaussianMatrix_of_indepFun` (BlockTail), Markov, `exists_completion_sub_mul_mul_conjTranspose` |
| SR2 | SINGLE-RUN | per-index deficits, light tail | L | SR0, SR1 | case $\sigma_k=0$ ($g\equiv1$); RZ1 (case A, roots at all $\sigma_r^2$, $k\le r<k+j$), RZ2 (case B, closed cut, roots at $\sigma_r^2\le(1-\eta)\sigma_k^2$), SR1 in both, `singularValues_rsvd_cfc_le_singularValues_rbki` |
| PL1 | P-LARGE | weighted gap form in expectation | M | CF1, CR1, CT1 | `exists_frame_residual` (prerequisite), GR1 at $\mathbf A f(\mathbf H)$, `singularValues_rsvd_cfc_le_singularValues_rbki` |
| PL2 | P-LARGE | weighted cut/gap in expectation, $\max(0,\cdot)$ form | M | CF1, CR1, CR2, CT1 | as RZ3's two cases with weights relative to $\sigma_k$ |
| IX2 | INEXACT | tail-count form with inexact pairing ($\eta$ spectral, $\eta_p$ Schatten) | M | IX1 | CB1's arithmetic (`mul_singularValues_rpow_le_schattenNorm_sub_truncatedSVD_rpow`), `Real.rpow_sub_rpow_le_max_mul_sq` |

### Wave 2

| Id | Batch | Statement | Size | Needs | Uses / outline |
|---|---|---|---|---|---|
| BK3 | BLOCK-K | tail headline, blocks $k$ and $k+j$ | M | BK2 | TS2 (`HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbkiSum_sq_le`), `measureReal_le_add_of_ae_imp` |
| SR3 | SINGLE-RUN | one-run Frobenius, deterministic | M | SR2 | RZ3, CB1F `IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq_le_of_singularValues_le_mul`, ST2T `IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq` |
| PL3 | P-LARGE | $p\ge2$ expectation, any $\mathbf Y$ | L | PL0, PL0b, PLd, PL1, PL2 | regimes of §2.5, `singularValues_rangeProjector_mul_le_of_range_le`, SV3 |
| PL6 | P-LARGE | $p\ge2$ tail, $\log(1/\delta)$ | L | PL0b, PLd, PL1, PL2 | Markov on $W$; `mul_meas_ge_le_integral_of_nonneg` |

### Waves 3–5

| Id | Batch | Statement | Size | Wave | Needs | Uses / outline |
|---|---|---|---|---|---|---|
| SR4 | SINGLE-RUN | one run, Gaussian, expectation | M | 3 | SR3 | `exists_frame_residual`, GR1 |
| SR7 | SINGLE-RUN | rank one, one vector, tail | M | 3 | SR3 | SmallBlock's head-coordinate and tail-energy events, `ae_forall_conjTranspose_mulVec_ne_zero_of_hasLaw_gaussianVector` |
| PL4 | P-LARGE | $p\ge2$ headline | M | 3 | PL3 | arithmetic of §2.5 |
| SR5 | SINGLE-RUN | headline, depth $2(k/\varepsilon)^{1/3}\log(16k/\varepsilon)$ | M | 4 | SR4 | $j=\lceil u\rceil-1$ chosen in the proof; `Nat.ceil` arithmetic |
| PL5 | P-LARGE | asymptotic form | M | 3 | PL3 | general sizes from PL3 (residual factors $\le1$), arithmetic as PL4; pattern of stage-1 GA4p |
| SR6 | SINGLE-RUN | asymptotic form | M | 5 | SR5 | |

Counts: S 9, M 16, L 4 = 29. By batch: MM-FROB 3 (S1 M2), BLOCK-K 3 (M3), SINGLE-RUN 8 (S2 M5
L1), INEXACT 2 (S1 M1), P-LARGE 13 (S5 M5 L3). By wave: 0: 13, 1: 6, 2: 4, 3: 4, 4: 1, 5: 1.
Batches share no target; each depends only on stage 1 and its own targets.

## 7. Shared proof machinery (item 7)

| Repeated argument | Handled by |
|---|---|
| a filter's bounds needed only on the spectrum (roots) | SR1, once |
| filter with roots / with a weight $x^r$ | SR0 / CF1, once each, on top of the existing Chebyshev lemma |
| deficit from a filtered sketch with its own residual | CR1, CR2 (P-LARGE); SINGLE-RUN uses the existing sup-bound RZ1/RZ2 through SR1 |
| filtered tail energy as a Schatten quantity | CT1, once; used by PL1, PL2 |
| Gaussian moment of a residual | existing GR1 at any matrix (no new lemma) |
| frame + a.s. rank + residual integrability | existing `exists_frame_residual` (public: prerequisite from the cleanup); PL0b for the deficits |
| error from deficits, $p\ge2$, one-sided | PLd, once |
| case split heavy/light | stage-1 CB1F (SR3); PL3's three regimes are written once there, PL6 reuses the same per-index lemmas |
| threshold arithmetic ($\log$, cube roots, `Nat.ceil`) | one private lemma per headline file; stage-1 `le_one_and_exists_thresholds` as the pattern for asymptotic forms |
| measurability of `rbki` outputs | existing `measurable_blockKrylovMatrix`, `measurable_rsvd`, `measurable_truncatedSVD` |

## 8. Open questions (item 8) — see the decision sheet

| Id | Question | Recommendation |
|---|---|---|
| MM-FROB | include the named instance? | include (3 targets, nothing new to prove); MM's literal block-$k$ Property 3 dropped |
| BLOCK-K | blocks of exactly $k$? | drop: $k+2$ is in the library; exact $k$ costs 3 M targets for 2 columns per block |
| SINGLE-RUN | gap-free roots route (b), simulation route (a), both, none? | (b) |
| SR-RATE | accept $k^{4/3}\varepsilon^{-1/3}$ (gap-free, derived here), and/or add MMM24's single-vector $k\varepsilon^{-1/3}$ with a gap hypothesis (route (a))? | (b) as the stated result; (a) optional; perturbation route not planned |
| INEXACT | include IX1, IX2 with the stated scope? | include |
| P-LARGE | include the dimension-free $p\ge2$ batch (expectation + tail)? | include; GA3 stays |
| P-FORM | $p$-th powers with $\varepsilon$ in $p$-th powers (as GA2p), or norm form $(1+\varepsilon)\mathrm{OPT}_p$ (as GA3)? | $p$-th powers for the expectation (PL4), tail PL6 in $p$-th powers too; norm forms follow by $(1+\varepsilon/p)^p\le e^{\varepsilon}$ in a docstring note |

### Risks

* **Numerics.** The review checked the headline threshold chains (MM1, SR5, SR7, PL4, PL6) on
  grids (all within about half the budget) and SR2 weakly on random spectra; per-index lemmas
  (CR2, CT1, PL1–PL3, IX1, IX2, BK) are hand-checked only. What could be false is a constant.
* **SR2 (L) and CR2 (L)** reuse RZ2's min–max machinery (made public by the cleanup).
* **PL1/PL2 junk values:** $\sigma_t=0$ gives $0^{4r+2-p}$ and $0^{2-p}$ in `Real.rpow`; the
  statements remain true because the tail vanishes and the block captures the range a.s.
  (`ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`); the proofs must case on it.
* **PL3 regime bookkeeping** (three regimes, two runs, weights) is the longest proof; L.
* **SR5's $(k/\varepsilon)^{1/3}$ and PL3–PL6 for $k>1$ are new as statements** (from BN's root
  filter and weight, BCW's case split, the library's RZ1/RZ2 and GR1); the review re-derived both.
* The `omos` platform was not used (cost 0).

## 9. Material (item 6)

Read: MM15 §4 (Lemma 9, Theorems 10–13); BN23 `faster-krylov-algorithms.tex` (all), statements in
`intro.tex`; the stage-1 note and decision sheet; the files of §0. Reused as mathematics: BN's
root filter (SR2) and weight (CF1, CT1); MM's Theorem 11 as a corollary of BCW's case split (MM1).
Not reproduced: MM's Property 3 rank argument (only needed for block $k$); BN's four-case analysis
(replaced by RZ1/RZ2 + roots, and by PL1/PL2); BN's lower bounds (out of scope); the simulation
route (a) (gap-dependent, dominated by (b)).

## 10. Changes after review

Review: `scratch/Review-LRA-OPTIONAL-Design.md` (verdict: revise, then approve; both new claims
re-derived). Each point verified before adoption; none disputed.

| Item | Outcome |
|---|---|
| B1 SR1 false ($a<0$, vacuous hypothesis) | agreed (counterexample checked); `ha : 0 ≤ a` added; consumer SR2 has $a\ge0$ |
| S1 PL5 needs general sizes | agreed; PL5 depends on PL3 |
| S2 integrability for PL3/PL6 | agreed; PL0b added |
| S3 private-to-public changes | listed as prerequisites from the cleanup (coordinator: being made now), not targets |
| S4 SR-RATE "open" | agreed; MMM24 abstract read (harness `research/lra-optional/`), wording "not derived here", decision options include route (a) |
| S5 SR2 outline | closed cut, $\sigma_k=0$, SR1 in both cases |
| S6 INEXACT scope | IX3 dropped (no consumer); IX2 takes $\eta_p$; scope stated (§2.4) |
| S7 cosmetic | weight written $x^r$; $t=k+j$; P-LARGE risk medium–high |
| S8 P-FORM caveat | added (§2.5) |
| BK1 probe argument | noted: if BLOCK-K is kept, BK1 may use the probe argument ($O(\sqrt r\,x)$); the stated $r^{3/2}x$ is true and suffices |

## Appendix A. Lean statements

### A.0 Check

The file below was elaborated with `lake env lean` against the build of `1bed77c6` on
2026-11-24, again after the review: no error; each of the 29 declarations (revised file, after the review) reports only "declaration uses `sorry`". It
lives in the untracked `scratch/LraOptional.lean` and is reproduced verbatim. Comments `-- ID`
give the target ids. Elaboration means the statements typecheck, nothing more; names and
instance arguments are to be reviewed with the skeleton (asymptotic forms sit where stage 1 put
its own).

```lean
import NLAlib.LowRank.Gaussian.BlockKrylovSum
import NLAlib.LowRank.Gaussian.SmallBlock

/-! Scratch statements for the LRA-OPTIONAL design note. Every proof is `sorry`; this file only
checks that the statements elaborate. Not part of the library. -/

open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix ENNReal

/-! ## P-LARGE: polynomial facts (ForMathlib) -/

-- CF1
theorem Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_mul_pow {s τ : ℝ} (hτ : 0 ≤ τ)
    (hτs : τ ≤ s) (hs : 0 < s) (d r : ℕ) :
    ∃ f : ℝ[X], f.degree < (d + r + 1 : ℕ) ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ x, s ^ 2 ≤ x → c * x ^ r ≤ |f.eval x|) ∧
      (∀ x ∈ Set.Icc 0 (τ ^ 2), |f.eval x| ≤ a * x ^ r) ∧
      (a / c) ^ 2 ≤ 4 * Real.exp (-8 * (d : ℝ) * Real.sqrt ((s - τ) / (s + τ))) := sorry

/-! ## SINGLE-RUN: polynomial facts (ForMathlib) -/

-- SR0
theorem Polynomial.Chebyshev.exists_degree_lt_eval_eq_zero_div_sq_le_exp (R : Multiset ℝ)
    {s τ b h : ℝ} (hτ : 0 ≤ τ) (hτs : τ ≤ s) (hs : 0 < s) (hτb : τ ^ 2 ≤ b) (hh : 0 < h)
    (hR : ∀ x ∈ R, 0 ≤ x ∧ x ≤ b) (d : ℕ) :
    ∃ f : ℝ[X], f.degree < (d + 1 + Multiset.card R : ℕ) ∧ (∀ x ∈ R, f.eval x = 0) ∧
      ∃ c a : ℝ, 0 < c ∧
      (∀ x, s ^ 2 ≤ x → b + h ≤ x → c ≤ |f.eval x|) ∧
      (∀ x ∈ Set.Icc 0 (τ ^ 2), |f.eval x| ≤ a) ∧
      (a / c) ^ 2 ≤ (b / h) ^ (2 * Multiset.card R) *
        (4 * Real.exp (-8 * (d : ℝ) * Real.sqrt ((s - τ) / (s + τ)))) := sorry

namespace NLAlib

section Deterministic

variable {𝕜 : Type*} [RCLike 𝕜] {l m n s : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq s]

/-! ## SINGLE-RUN, deterministic -/

-- SR1: a filter needs its bounds only at the squared singular values
theorem exists_cfc_eq_aeval_and_abs_le_of_forall_singularValues (A : Matrix m n 𝕜) (f : ℝ[X])
    {S : ℝ} {a : ℝ} (ha : 0 ≤ a)
    (htail : ∀ i < Fintype.card n, singularValues A i ^ 2 ≤ S →
      |f.eval (singularValues A i ^ 2)| ≤ a) :
    ∃ g : ℝ → ℝ, cfc g (Aᴴ * A) = cfc (fun x => f.eval x) (Aᴴ * A) ∧
      (∀ i < Fintype.card n, g (singularValues A i ^ 2) = f.eval (singularValues A i ^ 2)) ∧
      ∀ x ∈ Set.Icc 0 S, |g x| ≤ a := sorry

-- SR2: per-index deficits of one run when the tail is light, no gap at k
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki_of_mul_le
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {k j : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A k)
    (hlight : Real.sqrt 2 * singularValues A (k + j) ≤ singularValues A k) {η : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 1 / 2) {q : ℕ} (hq : j + 1 ≤ q) {i : ℕ} (hi : i < k) :
    singularValues A i ^ 2 - 2 * η * singularValues A k ^ 2 -
        4 * η⁻¹ ^ (2 * j) * Real.exp (-3 * ((q : ℝ) - 1 - j)) *
          specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rbki A Ω q) i ^ 2 := sorry

-- SR3: Frobenius error of one run, no gap, cube-root form
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbki_sq_le
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {k j : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A k) {q : ℕ}
    (hq : j + 1 ≤ q) {γ η : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    frobNorm (A - truncatedSVD (rbki A Ω q) k) ^ 2 ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) + 2 * k * η) * frobNorm (A - truncatedSVD A k) ^ 2 +
        4 * k * (Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) +
          η⁻¹ ^ (2 * j) * Real.exp (-3 * ((q : ℝ) - 1 - j))) *
          specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2 := sorry

/-! ## P-LARGE, deterministic -/

-- CR1: gap form with the filtered residual
theorem HasOrthonormalCols.sq_singularValues_sub_inv_sq_mul_le_sq_singularValues_rsvd_cfc
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {t : ℕ}
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {i : ℕ} (hi : i < t) {c : ℝ} (hc : 0 < c)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|) :
    singularValues A i ^ 2 - c⁻¹ ^ 2 *
        specNorm ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := sorry

-- CR2: cut form with the filtered residual below the cut
theorem
    HasOrthonormalCols.sq_sub_inv_sq_mul_le_sq_singularValues_rsvd_cfc_of_le_singularValues
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {i : ℕ}
    (hAZ : truncatedSVD A (i + 1) * Z * Zᴴ = truncatedSVD A (i + 1)) {c τ : ℝ} (hc : 0 < c)
    (hτ : 0 ≤ τ) (hτi : τ ≤ singularValues A i)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|) :
    τ ^ 2 - c⁻¹ ^ 2 * specNorm ((A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) -
        A * cfc (Set.indicator (Set.Iio (τ ^ 2)) g) (Aᴴ * A) * Z * Zᴴ) * Ω *
          pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := sorry

-- CT1: the filtered tail energy against a Schatten norm of the tail
theorem frobNorm_sub_mul_cfc_mul_sq_le_mul_schattenNorm_rpow {A : Matrix m n 𝕜} (g : ℝ → ℝ)
    {Z : Matrix n s 𝕜} {t : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A t) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ⊤) {b : ℝ}
    (hw : ∀ i, t ≤ i → singularValues A i ^ 2 * g (singularValues A i ^ 2) ^ 2 ≤
      b * singularValues A i ^ p.toReal) :
    frobNorm (A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) ^ 2 ≤
      b * schattenNorm p (A - truncatedSVD A t) ^ p.toReal := sorry

-- PLd: one-sided truncated output, p ≥ 2, from the deficits in squares
theorem _root_.IsStarProjection.schattenNorm_sub_truncatedSVD_mul_rpow_le_add_sum_mul
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) (k : ℕ) :
    schattenNorm p (A - truncatedSVD (P * A) k) ^ p.toReal ≤
      schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        ∑ i ∈ Finset.range k, p.toReal / 2 * singularValues A i ^ (p.toReal - 2) *
          (singularValues A i ^ 2 - singularValues (P * A) i ^ 2) := sorry

/-! ## INEXACT, deterministic -/

-- IX1: pinching without the exact pairing P A Q = P A
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_schattenNorm_mul_mul_one_sub_add
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (A : Matrix m n 𝕜) :
    schattenNorm p (A - A * Q) ≤ schattenNorm p (P * A * (1 - Q)) +
      (schattenNorm p A ^ p.toReal - schattenNorm p (P * A * Q) ^ p.toReal) ^ p.toReal⁻¹ :=
  sorry

-- IX2: the tail-count form with an inexact pairing, 1 ≤ p ≤ 2
theorem _root_.IsStarProjection.schattenNorm_sub_mul_le_add_of_singularValues_le_mul
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) {A : Matrix m n 𝕜} {k j : ℕ}
    {γ κ η ηp : ℝ} {β : ℕ → ℝ} (hγ : 0 ≤ γ) (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (hβ0 : singularValues A k = 0 → η = 0 ∧ ∀ i < k, β i = 0)
    (htail : singularValues A k ≤ κ * singularValues A (k + j))
    (hritz : ∀ i < k, singularValues A i ^ 2 - γ * singularValues A k ^ 2 - β i ≤
      singularValues (P * A) i ^ 2)
    (hPAQ : specNorm (P * A * (1 - Q)) ≤ η) (hPAQp : schattenNorm p (P * A * (1 - Q)) ≤ ηp) :
    schattenNorm p (A - A * Q) ≤ ηp +
      ((1 + k * γ * κ ^ p.toReal / ((j : ℝ) + 1)) *
          schattenNorm p (A - truncatedSVD A k) ^ p.toReal +
        singularValues A k ^ (p.toReal - 2) *
          ∑ i ∈ Finset.range k, (β i + 2 * η * singularValues A i)) ^ p.toReal⁻¹ := sorry

end Deterministic

section Gaussian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l m n l₁ l₂ s : Type*}
  [Fintype l] [Fintype m] [Fintype n] [Fintype l₁] [Fintype l₂] [Fintype s] [DecidableEq m]
  [DecidableEq n] [DecidableEq s] {X : Ω → Matrix n l ℝ} {X₁ : Ω → Matrix n l₁ ℝ}
  {X₂ : Ω → Matrix n l₂ ℝ}

/-! ## MM-FROB -/

-- MM1
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k q : ℕ} (hk : 0 < k)
    (hl : 2 * k + 1 ≤ Fintype.card l) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : 1 + Real.sqrt 3 * Real.log (24 * k / ε) / (2 * Real.sqrt ε) ≤ q) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- MM2
theorem
    integral_schattenNorm_sub_mul_rangeProjector_rbki_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k q : ℕ} (hk : 0 < k)
    (hl : 2 * k + 1 ≤ Fintype.card l) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : 1 + Real.sqrt 3 * Real.log (24 * k / ε) / (2 * Real.sqrt ε) ≤ q) :
    ∫ ω, schattenNorm p (A - A * rangeProjector (truncatedSVD (rbki A (X ω) q) k)ᴴ) ^
        p.toReal ∂μ ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

/-! ## SINGLE-RUN, Gaussian -/

-- SR4
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k j q : ℕ}
    (hl : k + 2 ≤ Fintype.card l) (hq : j + 1 ≤ q) {γ η : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2 ∂μ ≤
      (1 + 2 * k * γ / ((j : ℝ) + 1) + 2 * k * η +
        4 * k * (Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) +
          η⁻¹ ^ (2 * j) * Real.exp (-3 * ((q : ℝ) - 1 - j))) *
          ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1))) *
        frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- SR5
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_one_add_mul_of_rpow_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k q : ℕ} (hk : 0 < k)
    (hl : 2 * k + 1 ≤ Fintype.card l) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : 1 + 2 * (k / ε) ^ (3 : ℝ)⁻¹ * Real.log (16 * k / ε) ≤ q) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- SR7: one start vector, rank one, tail form
theorem measureReal_frobNorm_sub_truncatedSVD_rbki_replicateCol_sq_gt_le_of_hasLaw_gaussianVector
    {x : Ω → n → ℝ} (A : Matrix m n ℝ) (hx : HasLaw x (gaussianVector n) μ) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) {q : ℕ}
    (hq : 1 + 2 * Real.log (128 / (ε * δ ^ 3)) / ε ^ (3 : ℝ)⁻¹ ≤ q) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A 1) ^ 2 <
      frobNorm (A - truncatedSVD (rbki A (Matrix.replicateCol Unit (x ω)) q) 1) ^ 2} ≤ δ :=
  sorry

/-! ## BLOCK-K -/

-- BK1: least singular value of a square real Gaussian matrix
theorem measureReal_singularValues_le_le_card_rpow_mul_of_hasLaw_gaussianMatrix {r : Type*}
    [Fintype r] [DecidableEq r] {G : Ω → Matrix r r ℝ} (hG : HasLaw G (gaussianMatrix r r) μ)
    {k : ℕ} (hk : k + 1 = Fintype.card r) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (G ω) k ≤ x} ≤ (Fintype.card r : ℝ) ^ (3 / 2 : ℝ) * x := sorry

-- BK2: residual tail for a block with as many columns as the frame
theorem measureReal_frobNorm_sub_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix_of_card_eq
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {Z : Matrix n s ℝ}
    (hZ : HasOrthonormalCols Z) (hs : Fintype.card s = Fintype.card l) {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | 8 * (Fintype.card s : ℝ) ^ 4 / δ ^ 3 * frobNorm (A - A * Z * Zᴴ) ^ 2 <
      frobNorm ((A - A * Z * Zᴴ) * X ω * pinv (Zᴴ * X ω)) ^ 2} ≤ δ := sorry

-- BK3: blocks of exactly k and k + j columns
theorem measureReal_frobNorm_sub_truncatedSVD_rbkiSum_sq_gt_le_of_hasLaw_gaussianMatrix
    {m n k j q₁ q₂ : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {X₁ : Ω → Matrix (Fin n) (Fin k) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (k + j)) ℝ} (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin k)) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (k + j))) μ) (hk : 0 < k) {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hj : 6 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + Real.log (768 * k ^ 5 / (ε * δ ^ 3)) / (2 * Real.sqrt 2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + Real.log (768 * ((k : ℝ) + j) ^ 4 / (ε * δ ^ 3)) / 3 ≤ q₂) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ 2} ≤ δ := sorry

/-! ## P-LARGE, Gaussian -/

-- PL0
theorem integrable_schattenNorm_sub_truncatedSVD_rsvd_rpow [IsFiniteMeasure μ] (p : ℝ≥0∞)
    (A : Matrix m n ℝ) {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ) (k : ℕ) :
    Integrable (fun ω => schattenNorm p (A - truncatedSVD (rsvd A (Y ω)) k) ^ p.toReal) μ :=
  sorry

-- PL0b: integrability of a squared singular value of the RBKI output
theorem integrable_sq_singularValues_rbki [IsFiniteMeasure μ] (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (q i : ℕ) :
    Integrable (fun ω => singularValues (rbki A (X ω) q) i ^ 2) μ := sorry

-- PL1: weighted gap form in expectation
theorem integral_rpow_mul_sq_singularValues_sub_sq_singularValues_rbki_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {t r q i : ℕ} (hl : t + 2 ≤ Fintype.card l)
    (hr : p.toReal ≤ 4 * r + 2) (hq : r + 1 ≤ q) (hit : i < t) {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hgap : (1 + θ) * singularValues A t ^ 2 ≤ singularValues A i ^ 2) :
    ∫ ω, singularValues A i ^ (p.toReal - 2) *
        (singularValues A i ^ 2 - singularValues (rbki A (X ω) q) i ^ 2) ∂μ ≤
      4 * Real.exp (-(8 / 3) * ((q : ℝ) - 1 - r) * Real.sqrt θ) *
        ((t : ℝ) / ((Fintype.card l : ℝ) - t - 1)) *
        schattenNorm p (A - truncatedSVD A t) ^ p.toReal := sorry

-- PL2: weighted cut form in expectation, excess over γ σ_k²
theorem integral_max_sq_singularValues_sub_sub_sq_singularValues_rbki_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k r q i : ℕ} (hl : k + 2 ≤ Fintype.card l)
    (hr : p.toReal ≤ 4 * r + 2) (hq : r + 1 ≤ q) (hik : i < k) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) :
    ∫ ω, max 0 (singularValues A i ^ 2 - γ * singularValues A k ^ 2 -
        singularValues (rbki A (X ω) q) i ^ 2) ∂μ ≤
      4 * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1 - r) * Real.sqrt γ) *
        ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) * singularValues A k ^ (2 - p.toReal) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- PL3: p ≥ 2, expectation, any sketch containing both Krylov sketches, no dimension
theorem integral_schattenNorm_sub_truncatedSVD_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) (A : Matrix m n ℝ)
    (hX₁ : HasLaw X₁ (gaussianMatrix n l₁) μ) (hX₂ : HasLaw X₂ (gaussianMatrix n l₂) μ)
    {k j r q₁ q₂ : ℕ} (hl₁ : k + 2 ≤ Fintype.card l₁) (hl₂ : k + j + 2 ≤ Fintype.card l₂)
    (hr : p.toReal ≤ 4 * r + 2) (hq₁ : r + 1 ≤ q₁) (hq₂ : r + 1 ≤ q₂) {γ : ℝ} (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) {Y : Ω → Matrix n l ℝ} (hY : AEMeasurable Y μ)
    (h₁ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₁ ω) q₁).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin)
    (h₂ : ∀ ω, LinearMap.range (A * blockKrylovMatrix (Aᴴ * A) (X₂ ω) q₂).mulVecLin ≤
      LinearMap.range (A * Y ω).mulVecLin) :
    ∫ ω, schattenNorm p (A - truncatedSVD (rsvd A (Y ω)) k) ^ p.toReal ∂μ ≤
      (1 + k * p.toReal * (Real.exp 1 * γ / (2 * ((j : ℝ) + 1)) +
        2 * Real.sqrt (Real.exp 1) *
          Real.exp (-2 * Real.sqrt 2 * ((q₁ : ℝ) - 1 - r) * Real.sqrt γ) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        2 * Real.exp (-(8 / 3) * ((q₁ : ℝ) - 1 - r) / Real.sqrt p.toReal) *
          ((k : ℝ) / ((Fintype.card l₁ : ℝ) - k - 1)) +
        2 * Real.exp (-(8 / 3) * ((q₂ : ℝ) - 1 - r) / Real.sqrt p.toReal) *
          (((k : ℝ) + j) / ((Fintype.card l₂ : ℝ) - k - j - 1)))) *
        schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- PL4: headline, p ≥ 2, expectation of the p-th power, dimension-free
theorem integral_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {m n k j q₁ q₂ : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {X₁ : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (2 * (k + j) + 1)) ℝ}
    (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (2 * (k + j) + 1))) μ) (hk : 0 < k) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hj : 2 * Real.exp 1 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + ⌈(p.toReal - 2) / 4⌉₊ + Real.sqrt p.toReal *
      Real.log (14 * p.toReal * k / ε) / (2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + ⌈(p.toReal - 2) / 4⌉₊ + Real.sqrt p.toReal *
      Real.log (8 * p.toReal * k / ε) / 2 ≤ q₂) :
    ∫ ω, schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ p.toReal ∂μ ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

-- PL6: tail form, p ≥ 2, logarithm of 1/δ only
theorem measureReal_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_gt_le_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ⊤) {m n k j q₁ q₂ : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {X₁ : Ω → Matrix (Fin n) (Fin (2 * k + 1)) ℝ}
    {X₂ : Ω → Matrix (Fin n) (Fin (2 * (k + j) + 1)) ℝ}
    (hX₁ : HasLaw X₁ (gaussianMatrix (Fin n) (Fin (2 * k + 1))) μ)
    (hX₂ : HasLaw X₂ (gaussianMatrix (Fin n) (Fin (2 * (k + j) + 1))) μ) (hk : 0 < k)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hj : Real.exp 1 * k / ε ^ (3 : ℝ)⁻¹ ≤ (j : ℝ) + 1)
    (hq₁ : 1 + ⌈(p.toReal - 2) / 4⌉₊ + Real.sqrt p.toReal *
      Real.log (20 * p.toReal * k / (ε * δ)) / (2 * ε ^ (3 : ℝ)⁻¹) ≤ q₁)
    (hq₂ : 1 + ⌈(p.toReal - 2) / 4⌉₊ + Real.sqrt p.toReal *
      Real.log (12 * p.toReal * k / (ε * δ)) / 2 ≤ q₂) :
    μ.real {ω | (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal <
      schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ p.toReal} ≤ δ :=
  sorry

end Gaussian

/-! ## Asymptotic forms (root namespace by rule N17; stated here inside `NLAlib` as in stage 1) -/

-- MM3
theorem exists_forall_integral_frobNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (k q : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < k → 0 < ε → ε ≤ ε₀ →
      2 * k + 1 ≤ Fintype.card l → C * (Real.log (k / ε) / Real.sqrt ε) ≤ q →
      ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- SR6
theorem exists_forall_integral_frobNorm_sub_truncatedSVD_rbki_sq_le_of_rpow_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (k q : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < k → 0 < ε → ε ≤ ε₀ →
      2 * k + 1 ≤ Fintype.card l → C * ((k / ε) ^ (3 : ℝ)⁻¹ * Real.log (k / ε)) ≤ q →
      ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := sorry

-- PL5
theorem exists_forall_integral_schattenNorm_sub_truncatedSVD_rbkiSum_rpow_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l₁ l₂ : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq n] [Fintype l₁] [Fintype l₂] (μ : Measure Ω) (p : ℝ≥0∞)
      (A : Matrix m n ℝ) (X₁ : Ω → Matrix n l₁ ℝ) (X₂ : Ω → Matrix n l₂ ℝ) (k q₁ q₂ : ℕ) (ε : ℝ),
      2 ≤ p → p ≠ ⊤ → HasLaw X₁ (gaussianMatrix n l₁) μ → HasLaw X₂ (gaussianMatrix n l₂) μ →
      0 < k → 0 < ε → ε ≤ ε₀ → 2 * k + 1 ≤ Fintype.card l₁ →
      C * (k / ε ^ (3 : ℝ)⁻¹) ≤ Fintype.card l₂ →
      C * (p.toReal + Real.sqrt p.toReal * Real.log (p.toReal * k / ε) / ε ^ (3 : ℝ)⁻¹) ≤ q₁ →
      C * (p.toReal + Real.sqrt p.toReal * Real.log (p.toReal * k / ε)) ≤ q₂ →
      ∫ ω, schattenNorm p (A - truncatedSVD (rbkiSum A (X₁ ω) (X₂ ω) q₁ q₂) k) ^ p.toReal ∂μ ≤
        (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := sorry

end NLAlib
```
