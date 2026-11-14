# Finite-precision shifted QR on the operation core (SQR-FP)

Stage SQR-FP formalizes [BanksGarzaVargasSrivastava2022] (Part II, arXiv 2205.06810 v1:
"Global convergence of Hessenberg shifted QR II: numerical stability") in floating point. It
builds on the exact shifted QR program on Ops ([Eigensolvers-ShiftedQR-Ops](Eigensolvers-ShiftedQR-Ops.md),
Codex, `origin/feat/ops-exact-shifted-qr` @9765ecf6) and the backward-error layer
([Ops-BackwardError](Ops-BackwardError.md), `origin/feat/ops-backward-step` @d6fdcb74), merged
on `design/sqr-fp` (83e77641). It replaces the plan of §9 of
[Eigensolvers-ShiftedQR](Eigensolvers-ShiftedQR.md) on `main`, which predates both. Requested by
the maintainer (board T137). This note is a design and a sorried skeleton; no proof is written
and no target, check, allowlist, CI file or build pin changes.

## 0. Summary

* **Gap re-check (§2).** All of G8–G17 were re-derived independently from the LaTeX. G8, G9, G10,
  G12, G13 and G16 are confirmed and change statements; G16 is worse than recorded (Lemma 3.6 is
  false under the paper's $\nu\boldsymbol{u} \le 1/4$; $m\nu\boldsymbol{u} \le 1/4$ suffices). New: Definition 3.4's bound relative to
  $\|\mathbf{H} - s\|$ cannot hold in floating point; Lemma 3.7's bound on $\mathbf{R}$ needs
  $\|\mathbf{E}\|_{\mathsf F}$; the computed $\mathbf{R}_{nn}$ is complex (a phase is needed before
  Sun's theorem applies); Lemma 6.1 is used outside its hypothesis (G18); `Exc`'s radius bound
  omits $2^{1/k}$; `Deflate` cuts $k-1$ subdiagonals while the loop tests $k$; Theorem 1.4's
  bit count is not scale invariant. Lemma 2.1 ($k$-th roots by Newton) is unnecessary: $k = 2^m$.
* **Layers (§4).** L1 deterministic backward error (rounded Givens sweep, weakened contracts,
  worklist by composition); L2 rounded convergence mathematics; L3 randomness; L4 the headline
  theorems. L1 lands first, on its own.
* **Skeleton.** 10 new files, 39 sorried statements,
  full `lake build` (5071 jobs), `check_rules` 0 errors. 21 more statements (the rounded programs
  and the headlines) are specified here and skeletonized with their programs (§4).
* **Model (§3).** Real words, `Machine ℝ` with `StdModel u id M` (it has a rounded square root);
  complex numbers as word pairs (the exact development's storage); disk samples from the tape,
  exact (as the paper) behind a sampler contract; `SmallEig` a randomized kernel with a forward
  contract on a good set of tapes. No Newton routine, no exact $\psi_k^k$.

## 1. Maintainer rules this design follows

Ground rule 10 (a library, not a list of results): the rounded Givens lemma, the pair relation,
QR perturbation, disk sampling and the measurable adaptive union bound are general, public, in
their topic files, and planned before the results that use them (§6). Codex's files are not
edited; every change they would need is listed in §7.4. Checks, targets, allowlists, CI and pins
are untouched.

## 2. Paper gaps, re-derived (proven / known / conjectured)

Two independent re-derivations (§§2–3 + appendix; §§4–6), pen and paper; numerics (pure Python)
only to check closed forms. "Statement" = a hypothesis or conclusion we formalize changes.

| id | where | verdict | fix and corrected constant | changes |
|---|---|---|---|---|
| G8 | L3.8 forward error | confirmed (proven) | $\boldsymbol{u} \le (8\kappa\nu)^{-1}(d/((2+2C)\|\mathbf{H}\|))^k$ (the $(2+2C)^{-k}$ was missing); $\widehat{\mathbf{H}}$ bound omits the backward term: $33$ for $32$; "2(·)^k" is a typo for 4 | statement |
| G8' (new) | L3.8 | proven | $\widehat{\mathbf{R}}_{nn}$ is complex after the last rotation; compare $\widehat{\mathbf{Q}}\mathbf{D}$, $\mathbf{D}^{\mathsf H}\widehat{\mathbf{R}}$ with a diagonal phase $\mathbf{D}$; subdiagonal moduli unchanged | statement |
| G9 | L3.9 comptau | confirmed (proven) | paper's route needs $\kappa^2$ and $24000$; the direct route $\mathbf{R}_{nn} = \|\mathbf{e}_n^{\mathsf T}\mathbf{M}^{-1}\|^{-1}$ needs only $(8004\kappa\nu)^{-1}(d/((2+2C)\|\mathbf{H}\|))^k$ and avoids L3.7; output is $\mathrm{fl}(\prod\lvert(\widehat{\mathbf{R}}_\ell)_{nn}\rvert)$ | statement |
| G10 | Thm 4.1 / L4.6 | confirmed (proven) | constant $\tfrac12 k^{-1/(2k)} \ge 0.416$, not $\tfrac12$; Regularize then reaches $1.1\omega$; fix $\beta := \omega^2/(20\cdot101\,\Sigma)$ (bound $\ge 2.08/\omega$), $\eta_1 = \omega^2\sqrt\varphi/(40\cdot101\,\Sigma\sqrt{2k})$ | statement |
| G10b | Thm 4.1 | confirmed | strict $\beta/\mathrm{gap} < c$ (Regularize has $1/4040 < 1/200$) | statement (dichotomy) |
| G11 | L4.6 proof | confirmed | $\psi_k \ge \omega$ ($\omega$-unreduced), sign typo | proof |
| G12 | L5.2 | confirmed, worse (proven) | product **and case split** over the last $k$ subdiagonals; otherwise "some subdiagonal $<\omega$" is not a bottom decoupling and Lemma 6.4 neither terminates nor progresses; factor $1.001001 \le 1.0011$ | statement |
| G13 | L5.3 Exc | (i),(ii),(iv) confirmed; (iii) partial | rounding $\le 0.005\varepsilon\tilde R$; cover $\mathbb{D}(r,(1+\varepsilon)\tilde R)$, so $\lvert r\rvert + (1+\varepsilon)\tilde R \le C\|\mathbf{H}\|$; points of a $0.99\varepsilon\tilde R$-separated net near an eigenvalue: $\le 7$ (attained; Pirl 1969, known), $3$ only for the triangular lattice; we use the packing bound $11$ (elementary); lower bound $1.998^{1/k}\theta\alpha B^{1/k}\psi$ | statement |
| G13v (new) | L5.3 | proven | $\tilde R \le 1.001\cdot 2^{1/k}\theta\alpha B^{1/k}\psi$ ($2^{1/k}$ omitted); constant $13$ survives; $\lvert S\rvert \le 9/\varepsilon^2$ needs $\varepsilon \le 1/2$ (true: $B \ge 2 \Rightarrow k \ge 32 \Rightarrow \varepsilon \le 0.47$) | statement |
| G13vi (new) | L5.3 | proven | rounding of the translate must be $\le \eta/2$ for the probability argument; forward stability at $\eta/2$ | precision only |
| G14 | Sh | confirmed, harmless | line 4 outputs iqr; $\xi = 0.999(1-\gamma)$ valid; decrease factors $1.0016$, $1.0011 \le 1.002$ for $k \ge 2$ ($k = 1$ gives $1.0021$); Requires lacks $\|\mathbf{H}\| \le \Sigma$; no accepted $s$: return a fail flag | statement (Requires) |
| G15 | L6.2 | proof gap only | the Cholesky/normal-block argument (already machine-checked in the exact development) | none |
| G16 | L3.6 appendix | confirmed, **worse** (proven) | the norms grow and $\Delta_\ell$ accumulates: false under the paper's $x = \nu\boldsymbol{u} \le 1/4$ (scalar example $\mathbf{H} = 1$, $s_\ell = -C$: $m = 10$, $C = 1$: $16.6 > 7.0$ and $2.2\cdot10^8 > 1.05\cdot10^6$); correct first part $(1+C)\|\mathbf{H}\|((1+x)^m - 1)$; both stated bounds hold under $m x \le 1/4$ (review: $\le 0.231\cdot4(2\Lambda)^m x$, checked to $m = 200$). The first draft's $m^2 x \le 1/4$ was sufficient, not minimal | statement |
| G17 | L2.5 | confirmed | Part I's $\theta \ge 1$ form; `eqn:jstag-alt` inequality reversed ($\tau \ge (1-\gamma)\psi$) | statement (typo) |
| G18 (new) | L6.1 | proven | the working accuracy $\omega \approx \Gamma/(32n^3B^2)$ violates $\|\mathbf{E}\| \le \mathrm{gap}/(8n^2\kappa^3)$ for $B > 4n$; the proof needs only $\|\mathbf{E}\| \le \mathrm{gap}/(8n^2\kappa^2)$. We instead reuse the exact development's $\|\mathbf{E}\| \le g/(16NB) \Rightarrow \kappa \le 2B$ plus Bauer–Fike for the gap | statement (lemma), none (Thm 6.3) |
| D3.4 (new) | Def 3.4 / L3.5 | proven | adding back the shift rounds the diagonal by $\boldsymbol{u}\lvert s\rvert$, so $\|\widehat{\mathbf{H}}' - \widehat{\mathbf{Q}}^{\mathsf H}\mathbf{H}\widehat{\mathbf{Q}}\| \le \nu\boldsymbol{u}\|\mathbf{H}-s\|$ is false ($\mathbf{H} = s + \delta\mathbf{N}$, $\delta \to 0$). Base $\|\mathbf{H}\| + \lvert s\rvert$ (all uses bound by $(1+C)\|\mathbf{H}\|$); L3.5's $\boldsymbol{u} \le \log 2/(8n^{5/2})$ is not implied by $\nu\boldsymbol{u} \le 1/4$; entry count $8\sqrt{2n}$ (proof). Our round-by-round analysis gives $O(n)$, not $32n^{3/2}$ | statement |
| L3.7 (new) | Sun 1991 | confirmed; constants verified | $\|\Delta\mathbf{R}\|_2 \le 3\|\mathbf{M}^{-1}\|\|\mathbf{R}\|\|\mathbf{E}\|_2$ is false for large $n$ (triangular truncation, norm $\sim(\log n)/\pi$); use $\|\mathbf{E}\|_{\mathsf F}$. At $\eta \le 1/4$ the constants are $7.02$ ($\mathbf{Q}$) and $3.64$ ($\mathbf{R}$) by an elementary proof (review §4): $\mathbf{T} = \mathbf{R}'\mathbf{R}^{-1}$, $\mathbf{T}^{\mathsf H}\mathbf{T} = \mathbf{I} + \widehat{\mathbf{H}}$, $\|\mathbf{T} - \mathbf{I}\|_{\mathsf F}^2 = 2n + \mathrm{tr}\,\widehat{\mathbf{H}} - 2\,\mathrm{tr}\,\mathbf{T}$, AM–GM on the diagonal and $\log\det$ by Taylor: $\|\mathbf{T} - \mathbf{I}\|_{\mathsf F} \le \|\widehat{\mathbf{H}}\|_{\mathsf F}/(\sqrt2(1-\epsilon))$; the stated $8$ holds (D7 resolved) | statement |
| L2.1 | $k$-th roots | conjectured / under-specified | "any $a$" needs range reduction not in the model. Not needed: $k = 2^m$, $m$ rounded square roots have relative error $\le 3\boldsymbol{u}$ (`Ops.StdModel.abs_sqrtIter_sub_le`); $\psi_k^k$ need not be exact either. Caveat: $\varepsilon = (\cdot)^{k/(k-1)}$ of Exc needs a $(k-1)$-th root; it (like the exact development's grid size $M$) is global data supplied as an input word | removes an assumption |
| L6.4 | while loop | partial | $\lfloor N_{\mathrm{dec}}\rfloor + 1$ iterations; backward constant $1.4(1+C) = 7.7$ for $C = 4.5$ (survives); shift moduli $4.07\|\mathbf{H}''\|$, $C$: $3 \to 4.1$; **Deflate must cut the bottom $k$ subdiagonals with "$\le \omega$"** (else a block can recurse forever) | statement |
| T6.3 | backward | correct | per tree level errors on disjoint blocks combine by max; $2(n-1)\omega \le \delta/2$; forward ⇒ backward for SmallEig by Schur (known) | none |
| T6.3 prob | union bound | valid by first failure | before the first failure at most $n(N_{\mathrm{dec}}+1)$ calls; fresh randomness per call suffices; no cross-call independence needed. Running time holds only w.p. $1-\varphi$ unless capped: we cap | statement (cap) |
| T1.4 | bits | proven | $O(k\log(n B\|\mathbf{H}\|/(\delta\Gamma\varphi)))$: $\Gamma$ is absolute, $\|\mathbf{H}\|$ (or $\Sigma$) must appear | statement |
| L3.10 | regularization | confirmed | correct; $\eta_2 \ge \eta_1$ unnecessary | none |
| L5.1 | Find | confirmed | constants hold ($0.9978^2 \ge 2/2.02$); Requires $\kappa_V \le B$; $\log = \log_2$ | Requires |

Net effect on precision: $\log(1/\boldsymbol{u})$ changes by $O(k\log(2+2C) + \log\kappa)$; the
asymptotics $O(k\log(n\Sigma B/(\delta\Gamma\varphi)))$ stand, constants grow.

### 2.1 Corrections after review (Fable, Review-Fable-SQR-FP-Design.md)

Statement changes made on the skeleton:

* **S3** gains `IsUpperHessenberg H` (without it false: $3\times3$ counterexample, review §2 B1)
  and concludes $(2/\omega)^k$, which the exact dichotomy's constant $\tfrac25$ delivers with
  $\beta = \omega^2/(20\cdot101\Sigma)$; enough, because $\tau \le \omega/2$ plus the forward error
  $\omega/2$ reaches the threshold $\le\omega$. $2.08/\omega$ would need the sharp dichotomy constant
  (an extra M target, not planned).
* **Q4** constant $66 \to 66 + 2C$: false for $C > 130$ ($\mathbf{H} = -\mathbf{I}_2$, $s = 200$,
  $m = 1$). Chosen over the hypothesis $d \le \|\mathbf{H}\|$ because it keeps the statement valid
  for every shift and costs only a constant factor in $\boldsymbol{u}$ (all uses have $C \le 4.5$).
* **S5** `hRhi`: $1.001\cdot2^{1/k} \to 2.002^{1/k}$, i.e. $\tilde\psi$ within $0.001/k$ as the paper's
  (eq:boundonpottilde); with a flat $1.001$ the constant $13$ fails for $k \ge 60$. P6 accordingly.
* **Q3** `hm`: $m^2 x \le 1/4 \to m x \le 1/4$ (sufficient and minimal; G16 row).
* Labels: R1/R2 H → L (elementary proof); E2 L → H (needs Codex's matching).
* **R4** lower bound $(1 + \eta)^{-1}\mathbf{R}_{nn} \le |\widehat{\mathbf{R}}_{nn}| \to
  (1 - \eta)\mathbf{R}_{nn} \le |\widehat{\mathbf{R}}_{nn}|$: false as first stated ($n = 0$,
  $\mathbf{M} = 1$, $\mathbf{E} = -1/2$: $2/3 \le 1/2$ fails; still false at $\eta \le 1/4$ with
  $\mathbf{E} = -1/4$). The review's interval for $\|\mathbf{e}_n^{\mathsf T}(\mathbf{M} +
  \mathbf{E})^{-1}\|$ is right; its inversion to $\widehat{\mathbf{R}}_{nn}$ swapped the ends. Q5
  only needs $|\text{ratio} - 1| \le \eta/(1 - \eta)$, which the corrected R3/R4 give. Proved.
* **R1/R2** constants: proved as $16/3$ and $3$ (not $7.02$, $3.64$) by a shorter route than the
  review's det/AM–GM: $\mathbf{T} = \widehat{\mathbf{R}}\mathbf{R}^{-1}$ has
  $\|\mathbf{T} - \mathbf{I}\|_{\mathsf F} \le \|\mathbf{T} - \mathbf{T}^{-\mathsf H}\|_{\mathsf F}
  \le \|\mathbf{T}^{-1}\|_2\|\mathbf{T}^{\mathsf H}\mathbf{T} - \mathbf{I}\|_{\mathsf F}
  \le 3\|\mathbf{M}^{-1}\|\|\mathbf{E}\|_{\mathsf F}$, and
  $(\widehat{\mathbf{Q}} - \mathbf{Q})\mathbf{T} = \mathbf{E}\mathbf{M}^{-1}\mathbf{Q} -
  \mathbf{Q}(\mathbf{T} - \mathbf{I})$ with $\|\mathbf{T}^{-1}\|_2 \le 4/3$.

Confirmed paper errors (both passes and the review agree): G8 (+ phase G8'), G9, G10, G10b,
G11, G12, G13 (i)–(iv), G13v, G13vi, G14 ($k \ge 2$), G16 (fix $m x \le 1/4$), G17, G18
(threshold $B > 4n$), D3.4, L3.7 (Frobenius), L6.4 (bottom $k$, cap $\lfloor N_{\mathrm{dec}}\rfloor + 1$),
Theorem 1.4 scale. G15 is a proof gap only; L3.10 and L5.1 are correct.

## 3. Arithmetic and randomness model (decision D1)

* **Words and machine.** `Machine ℝ`, decoding `id`, `StdModel u id M`
  (`Ops/Catalog/Scalar.lean`): $+,-,\times,\div$ (nonzero divisor), $\sqrt{}$ (nonnegative),
  literals, each with relative error $\boldsymbol{u}$; negation exact; no under/overflow (Part II's
  model, Higham Ch. 2). `MixedModel` (absolute floor) is the follow-up for range safety, as in
  Ops-Finite-Arithmetic; not this stage. The exact development's programs are generic over `M`
  (they take `ExactModel id M` only in their proofs), so the **same programs** are analysed.
* **Complex numbers** are word pairs, column-major, as the exact development stores them;
  complex products and combinations are `Ops.Pair.linearWords`
  (`Ops.StdModel.norm_linearWords_sub_le`: $5\boldsymbol{u}$). No complex machine.
* **Square root** exists in `StdModel`; it gives the Givens radius and all $k$-th roots ($k = 2^m$).
* **Disk samples.** One uniform sample on $\mathbb{D}(0,R)$ per regularized shift, read from a
  fresh tape window. As in the paper, the sample is exact (`diskUniform`, Lebesgue conditioned on
  the disk); a rounded sampler is a coupling within $O(\boldsymbol{u}R)$, absorbed in the
  $\eta/2$ slack of G13vi (decision D1c).
* **SmallEig** is a kernel (oracle) with a forward contract on a set of tapes of probability
  $\ge 1-\varphi$ (Definition 1.2); Part III's algorithm is out of scope.
* **Ritz.** Part II computes Ritz values by `SmallEig` on the trailing $k\times k$ block plus
  `Optimal`; the exact development's `ritz` kernel (θ-optimal by assumption) is not used in the
  rounded algorithm.

## 4. Layers, statements and sizes

Difficulty S/M/L/H as in the harness. "Skel" = in the skeleton now; "plan" = specified here,
skeletonized with its program.

### L1 — deterministic backward error (first landing, decision D3)

| id | statement (Lean name) | where | diff | status |
|---|---|---|---|---|
| B1–B5 | `IsPerturbedUnitaryPair` refl, trans, mono, `isPerturbedUnitarySimilar_snd`, `exists_specNorm_sub_mul_le` | Matrix/Perturbation/UnitaryPair | S,M,S,S,S | skel |
| B6 | `isBackwardErrorRel_isPerturbedUnitaryPair` | same | S | skel |
| G1 | `Ops.StdModel.norm_roundedGivensCoeffs_sub_le` ($4\boldsymbol{u}$, relative) | Matrix/FinitePrecision/GivensRounded | M | skel |
| G2 | `Ops.StdModel.norm_linearWords_sub_le` ($5\boldsymbol{u}$) | same | M | skel |
| G3, G4 | `IsRoundedRowRotation.specNorm_sub_le`, `IsRoundedColRotation.specNorm_sub_le` ($2\eta\|\mathbf{A}\|$) | same | M, S | skel |
| G5 | `Ops.StdModel.norm_rotatePair_sub_le` ($12\boldsymbol{u}$) | same | M | skel |
| Q1 | `IsStableQRStep.isPerturbedUnitarySimilar` | Matrix/QRIteration/StableStep | S | skel |
| Q2 | `IsStableQRChain.isPerturbedUnitarySimilar` (G16 corrected) | same | M | skel |
| E1 | `IsEigenvalueListing.exists_specNorm_sub_le` (forward ⇒ backward, Schur) | Matrix/Perturbation/EigenvalueBackward | M | skel |
| C1, C2 | `IterationContract.backward`, `DecouplingContract.backward` (ν = 0 bridges) | Eigensolvers/ShiftedQR/Backward | S, S | skel |
| C3 | `shiftedStep_isPerturbedUnitarySimilar` (rounded step, $50(n+1)\boldsymbol{u}\|\mathbf{H}\|$) | same | L | skel |
| C4 | `solve_backward` (worklist with a backward decoupling implementation) | same | H | skel |
| P1 | `stepWithDiag` program + `IsStableQRStep` theorem (both inequalities, outputs $\widehat{\mathbf{R}}_{nn}$; base $\|\mathbf{H}\|+\lvert s\rvert$; zeroes structural fill so the output is Hessenberg) | Eigensolvers/ShiftedQR/StableStep (new) | L | plan |
| P2 | `multiStepStable`: the repeated step as an `IsStableQRChain` (via `BackwardStep.loop`) | same | M | plan |
| P3 | `solveRounded`: worklist with rounded threshold and scan, fail flag, bottom-$k$ deflation; `solveRounded_backward` | Eigensolvers/ShiftedQR/RoundedSolve (new) | H | plan |

The backward half of Theorem 6.3 is **composition**: per round `IsPerturbedUnitaryPair` from G3–G5
by `of_near_unitary`-free exact rotations (the computed coefficients are compared with the exact
unitary Givens rotation of the computed column entries), $n$ rounds by
`BackwardStep.loop_rel` with the size $\max(\|\mathbf{W}\|/a, \|\mathbf{Z}\|/b)$, degree $k$ by
`loop`, iterations by `whileFuel`, blocks lifted by `exists_submatrix`, deflations by
`sub_single`. No error invariant is threaded by hand.

Assumed in L1: nothing but `StdModel`; `SmallEig` enters only through E1 (any listing within
$\beta$). The worklist's scalar arithmetic is exact in C4 and rounded in P3.

### L2 — rounded convergence mathematics

| id | statement | where | diff | status |
|---|---|---|---|---|
| R1–R4 | QR perturbation: `IsQR.frobNorm_sub_le_of_add`, `IsQR.frobNorm_sub_triangular_le_of_add` ($\|\mathbf{E}\|_{\mathsf F}$; proved through $\|\widehat{\mathbf{R}}\mathbf{R}^{-1} - \mathbf{I}\|_{\mathsf F} \le 3\|\mathbf{M}^{-1}\|\|\mathbf{E}\|_{\mathsf F}$, constants $16/3$ and $3 \le 8$), `IsQR.last_le_of_add`, `IsQR.le_last_of_add` ($\mathbf{R}_{nn}$ ratio in $[1 - \eta, (1 - \eta)^{-1}]$; R4 corrected) | Matrix/Perturbation/QRFactorization | L, L, M, M | skel |
| Q3 | `IsStableQRChain.exists_specNorm_aeval_sub_le` (L3.6 second part, $mx \le 1/4$) | StableStep | L | skel |
| Q4 | `IsStableQRChain.exists_frobNorm_conj_sub_le` (L3.8 corrected, phase $\mathbf{D}$, constant $66 + 2C$) | same | L | skel |
| Q5 | `IsStableQRChain.abs_prod_last_sub_le` (L3.9 corrected, 8004, $0.0006$) | same | M | skel |
| Q6 | `potential_le_or_exists_lt_of_sub_le` (L5.2, bottom $k$) | same | S | skel |
| S1, S2 | `isOptimalRitzValues_of_lt`, `not_isOptimalRitzValues_of_le` (Optimal) | Matrix/QRIteration/RoundedStrategy | S, S | skel |
| S3 | `exists_mem_le_norm_inv_pow_of_not_isOptimalRitzValues` (Regularize core, G10 fixed; upper Hessenberg; $(2/\omega)^k$ from the exact dichotomy's $\tfrac25$) | same | L | skel |
| S4 | `isPromisingRitzValue_findRitzWith` (Find, L5.1) | same | M | skel |
| S5 | `exists_mem_le_norm_inv_pow_of_covers` (Exc core, G13 fixed; $\tilde R \le 2.002^{1/k}\theta\alpha B^{1/k}\psi$) | same | L | skel |
| S6 | `exists_decoupled_of_contract` (L6.4 abstract while loop) | same | M | skel |
| E2 | `exists_pseudoConditionNumber_le_and_le_norm_sub` (κ and gap after perturbation, G18); H as outlined: Bauer–Fike alone does not give the gap, it needs the eigenvalue matching that Codex's `exists_pseudoConditionNumber_add_le` proves but does not export (S/M once exported, §7.4 item 5) | EigenvalueBackward | H | skel |
| K1 | `Ops.StdModel.abs_sqrtIter_sub_le` ($k$-th root, $3\boldsymbol{u}$) | Matrix/FinitePrecision/RootsRounded | S | skel |
| P4 | Optimal program: rounded $\mathbf{e}_n^{\mathsf T}p(\mathbf{H})$ recurrence within $0.0009(\theta\psi)^k$ under $\boldsymbol{u}_{\mathrm{Optimal}}$ | Eigensolvers/ShiftedQR/RoundedRitz (new) | M | plan |
| P5 | comptau program: $\mathrm{fl}(\prod\lvert\widehat{\mathbf{R}}_{nn}\rvert)$ within $0.001$ | RoundedRitz | M | plan |
| P6 | rounded potential: $\tilde\psi_k$ within $0.001\psi_k/k$, the paper's (eq:boundonpottilde) (moduli, product, `sqrtIter`) | RoundedRitz | S | plan |
| P7 | Find program meets S4's hypothesis | RoundedFind (new) | M | plan |
| P8 | Exc program: net of $\mathbb{D}(r,(1+\varepsilon)\tilde R)$, translate, rounding $\le \min(0.005\varepsilon\tilde R, \eta/2)$ | RoundedExc (new) | L | plan |
| P9 | Sh iteration (one call of Find, comptau, Exc, trials): decoupled at the bottom or $\psi_k$ contracted by $1.002(1-\gamma)$ on the good event | RoundedIteration (new) | L | plan |
| P10 | Regularize program: SmallEig + samples + Optimal + decoupling trials | RoundedRegularize (new) | L | plan |
| P11 | rounded while loop: $\le \lfloor N_{\mathrm{dec}}\rfloor+1$ iterations, error $\le \omega$ (L6.4) | RoundedDecouple (new) | L | plan |
| P12 | preservation along the tree: norm $\le \Sigma$, $\kappa \le B$, gap $\ge \Gamma$ for every block | RoundedSolve | M | plan |

### L3 — randomness

| id | statement | where | diff | status |
|---|---|---|---|---|
| D1, D2 | `isProbabilityMeasure_diskUniform`, `measureReal_diskUniform_closedBall_le` | Probability/Distributions/DiskUniform | S, M | skel |
| D3 | `measureReal_exists_norm_add_sub_lt_le` (L3.10) | same | M | skel |
| D4 | `measureReal_exists_norm_add_sub_lt_le_of_separated` (Exc translate, 11) | same | M | skel |
| U1 | `measureReal_exists_lt_mem_le` (adaptive union bound, measurable states) | Probability/AdaptiveUnionBoundMeasurable | M | skel |
| P13 | tape coupling: disk sampler and SmallEig as tape-window functions; independence of a call's window from its input state (`IsTapeLaw.integral_future`) | Eigensolvers/ShiftedQR/RoundedProbability (new) | M | plan |
| P14 | Regularize failure $\le \varphi$ (SmallEig $\varphi/2$ + D3 $\varphi/2$) | same | M | plan |
| P15 | Sh failure $\le \varphi$ (D4 with $\eta = \varepsilon\tilde R\sqrt{\varphi/(11n)}$) | same | S | plan |
| P16 | global failure $\le \phi$ by U1 over $\le n(N_{\mathrm{dec}}+1)$ call slots and $n$ leaves | same | L | plan |

### L4 — headline theorems

| id | statement | diff | status |
|---|---|---|---|
| T1 | **Theorem 6.3** as an Ops `Algorithm` (`roundedAlgorithm`): total run, cap; with probability $\ge 1-\phi$ (Specification.Accepts on a tape law) the stored multiset is the spectrum of $\mathbf{H}+\mathbf{E}$, $\|\mathbf{E}\| \le \delta$; under $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ (closed form, corrected) | H | plan |
| T2 | **precision theorem** (Thm 1.4): $\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}}) \le c\,k\log_2(nB\Sigma/(\delta\Gamma\phi))$ with explicit $c$ | L | plan |
| T3 | relative form ($\delta\|\mathbf{H}\|$, $\Sigma$ computed as $2\|\mathbf{H}\|_{\mathsf F}$) | M | plan |
| T4 | Hermitian corollary (Remark 1.7, $k = 2$, $B = 1$; optional) | L | plan |
| T5 | work bound of `roundedAlgorithm` (as `exactAlgorithmWithPolynomialWork`, `Ops-PolynomialWork`) | M | plan |

### Totals

| layer | skel | plan | S | M | L | H |
|---|---|---|---|---|---|---|
| L1 | 18 | 3 | 9 | 8 | 2 | 2 |
| L2 | 16 | 9 | 5 | 9 | 10 | 1 |
| L3 | 5 | 4 | 2 | 6 | 1 | 0 |
| L4 | 0 | 5 | 0 | 2 | 2 | 1 |
| **all** | **39** | **21** | 16 | 25 | 15 | 4 |

Skeleton alone: S 14, M 16, L 7, H 2 (`~/nlalib-harness/pilot/sqr-fp-targets.json`). Sixty
statements in all, matching the stage-1 estimate (S 12, M 25, L 16, H 6).

Waves: 0 = B1–B6, G1–G5, K1, D1–D2, Q1 (library, no dependencies); 1 = Q2, E1, R3–R4, C1–C2,
D3–D4, U1, S1–S2; 2 = C3, Q3, R1–R2, Q5, Q6, S4, S6, E2; 3 = C4, Q4, S3, S5 (+P1–P3: the L1
landing); 4 = P4–P12; 5 = P13–P16, T1–T5.

## 5. Interfaces, files and placement

### 5.1 Objects (vocabulary rows to add)

| object | meaning | Mathlib bridge |
|---|---|---|
| `IsPerturbedUnitaryPair a b ε P P'` | one unitary acting on the left of `P.1`, by similarity on `P.2`, errors $\varepsilon a$, $\varepsilon b$ | none (searched); projects to `IsPerturbedUnitarySimilar` |
| `IsStableQRStep ε H s H' R` | Def 3.4, absolute error | `IsQR` |
| `IsStableQRChain x H ss H' Rs` | degree $m$ step as a chain | `multiShiftedQRStep` at $x = 0$ |
| `roundedGivensCoeffs M u v` | machine coefficients in program order | `givensCoeffs` |
| `IsRoundedRowRotation`, `IsRoundedColRotation` | pairwise-relative rotation error | `givens` |
| `sqrtIter M m a` | $m$ machine square roots | `Real.rpow` |
| `diskUniform c R` | `ProbabilityTheory.cond volume (closedBall c R)` (an abbreviation, no deviation) | Mathlib `cond` |
| `findRitzWith t m e ss` | Find with supplied comparison values | `findRitz` |
| `BackwardIterationContract ν`, `BackwardDecouplingContract θ ε` | weakened Codex contracts | `IterationContract`, `DecouplingContract` |

### 5.2 Files of the skeleton

| file | declarations |
|---|---|
| `Matrix/Perturbation/UnitaryPair.lean` (new) | B1–B6 |
| `Matrix/Perturbation/QRFactorization.lean` (new) | R1–R4 |
| `Matrix/Perturbation/EigenvalueBackward.lean` (new) | E1, E2 |
| `Matrix/FinitePrecision/GivensRounded.lean` (new) | G1–G5, defs |
| `Matrix/FinitePrecision/RootsRounded.lean` (new) | K1, `sqrtIter` |
| `Matrix/QRIteration/StableStep.lean` (new) | Q1–Q6, defs |
| `Matrix/QRIteration/RoundedStrategy.lean` (new) | S1–S6, `findRitzWith` |
| `Probability/Distributions/DiskUniform.lean` (new) | D1–D4 |
| `Probability/AdaptiveUnionBoundMeasurable.lean` (new) | U1 (a separate file so that the proved countable-state lemma stays sorry-free) |
| `Eigensolvers/ShiftedQR/Backward.lean` (new, Codex's folder) | C1–C4, contracts |
| `docs/references.bib` | Sun1991, BauerFike1960, ChangPaigeStewart1997 |

Placement: perturbation theory under `Matrix/Perturbation`, machine-word error lemmas under
`Matrix/FinitePrecision` (they import Ops, as `OpsUnitarySimilarity` does), strategy mathematics
next to `Strategy.lean`/`Dichotomy.lean`, the disk law under `Probability/Distributions`, program
statements in the exact development's folder. `IsBackwardErrorRel` for the pair lives with the
pair (one bridge line; the single-matrix bridge is in `OpsUnitarySimilarity`, kept as is).

### 5.3 Consumers

B*, G* → C3, P1 (sweep), later any Givens/Householder unitary algorithm (Hessenberg reduction,
QZ, rounded Lanczos tridiagonal QR). R1–R4 → Q4, Q5; also rounded QR/Cholesky elsewhere. Q* → S*,
P9–P11. D*, U1 → P13–P16; U1 replaces HDIAG's countable-state requirement for real-word states.
E1 → T1 leaves; E2 → P12. C4 → P3 → T1.

## 6. Shared proof machinery (rule 10)

| repeated argument | handled by | status |
|---|---|---|
| perturbed similarity of a whole step from a sequence of rounded kernels | `BackwardStep.seq/loop/loop_rel/whileFuel/ite` with `IsPerturbedUnitarySimilar` | exists (d6fdcb74) |
| the factorization and the similarity with **one** unitary (Def 3.4's two inequalities) | `IsPerturbedUnitaryPair` + its `IsBackwardErrorRel`; dimensionless budget, `loop_rel` size $\max(\|\mathbf{W}\|/a, \|\mathbf{Z}\|/b)$ | new (B1–B6) |
| per-pair rounding error → spectral-norm error of a rotation | `IsRoundedRowRotation.specNorm_sub_le` (reusable rounded-kernel lemma) | new (G3–G4) |
| complex products on word pairs | `Ops.StdModel.norm_linearWords_sub_le` | new (G2) |
| Givens coefficients from rounded data | G1, G5 | new |
| word-level program theorems for a generic machine (exact as a special case) | the `ScalarProducts.writes_*_word` pattern (Ops-Scalar-Rounded): `*_writes_word` versions of Codex's Coefficients/Rotation/Sweep, exact theorems as corollaries | to add (§7.4) |
| relative budgets | `loop_rel` (worked lemma) | exists |
| block embedding of a step on a deflated block | `exists_submatrix`, `sub_single`, `exists_fromBlocks₁₁/₂₂` | exists |
| forward-from-backward of a degree $k$ step | Q4 (one lemma, used by Regularize, Sh, Exc) | new |
| decisions from computed quantities | "computed within relative error" hypotheses in S1–S5 (not re-derived per subroutine) | new |
| QR perturbation | R1–R4 in `Matrix/Perturbation` | new |
| geometric probability on a disk | D2 → D3, D4 | new |
| adaptive union bound with real-word states | U1 | new |
| fresh tape window independent of the past | `IsTapeLaw.integral_future`, `indepFun_of_measurable` (Ops/TapeLaw) | exists |
| κ after perturbation | `exists_pseudoConditionNumber_add_le` (Codex) | exists |
| eigenvalue listing / Schur | `IsEigenvalueListing.exists_hasOrthonormalCols_isUpperTriangular` | exists |

Mathlib searched (v4.33.1): no perturbed similarity, no QR perturbation, no Givens rounding, no
uniform law on a disk (but `ProbabilityTheory.cond`, used), no measurable adaptive union bound.

## 7. Reuse of the exact development

### 7.1 Reused unchanged

All programs that are not convergence decisions: `coefficients`, `rotateRows/Columns`, `round`,
`sweep`, `shiftedStep`, `repeatedStep`/`multiStep`, `scan`, `BlockCopy`, the worklist
(`worklistLoop`, `writeAndSplit`, `processRange`, `solve`), `Output`, `Storage`, `Kernels`'
`smallEig` call shape. Mathematics: `DeflationInv` (its witness is `IsPerturbedUnitarySimilar`
verbatim), `DeflationConditioning` (G15, κ bound), `ShiftSearch`, `Strategy`, `Dichotomy`.

### 7.2 Weakened (contracts)

`IterationContract`, `DecouplingContract` → `BackwardIterationContract`,
`BackwardDecouplingContract` (C1, C2: exact is error $0$). `DecoupleInv` → its `H = UᴴH₀U` becomes
`IsPerturbedUnitarySimilar H₀ H e` (a new invariant in the rounded decouple file, not an edit).

### 7.3 Re-proved

Every `*_writes` that uses `ExactModel` to name the stored values (Coefficients, Rotation,
Sweep, Step, MultiStep, Potential, Radius, Scan thresholds) must be re-proved word-level. The
footprint/frame half of each proof is reusable as is if the theorems are split into
`*_writes_word` (machine-generic, value = machine evaluation) + exact corollary.

The convergence programs are **new**, not re-proved: Part II's algorithm differs from the exact
one (Regularize with SmallEig and random perturbation instead of the θ-optimal `ritz` kernel;
Find by comptau on $\widehat{\mathbf{R}}_{nn}$ instead of `RowSolve`; Exc as a disk net with a
random translate instead of the square grid). Codex's `RowSolve`/`HalfNorm` path has no
floating-point analysis in the paper and is not used.

### 7.4 Changes needed in Codex's files (not made here)

1. Split `coefficientsWithScratch_writes`, `writes_rotateLeft/RightWithScratch`,
   `rotateRows/Columns_writes`, `round_writes`, `sweep_writes` into a machine-generic `_word`
   theorem and the exact corollary (rule 10; avoids a second memory proof in P1).
2. Expose the triangular factor's last diagonal word from the sweep (or accept a wrapper P1).
3. Rotation loops restricted to the Hessenberg profile, or a zeroing pass (output Hessenberg in
   floating point).
5. (review) Export the eigenvalue matching $\lvert d'_i - d_i\rvert < g/8$ proved inside
   `exists_pseudoConditionNumber_add_le` (E2 becomes S/M), and the bottom-$k$ "$\le \omega$" scan.
4. Bottom-$k$ deflation threshold "$\le \omega$" and a fail word in the worklist (P3), or a new
   worklist round in our files reusing `writeAndSplit`.

## 8. Assumed kernels and oracles

| item | status in this design |
|---|---|
| `SmallEig` (Def 1.2) | randomized kernel: forward accuracy $\beta$ on a tape set of probability $\ge 1-\varphi$; at the leaves enters by E1. Part III not formalized |
| disk sampler | exact uniform sample from a tape window (paper's assumption); rounding coupling as an option |
| $k$-th roots (L2.1) | **not assumed**: `sqrtIter`; the $(k-1)$-th root in Exc's $\varepsilon$ is an input word (global data, as $M$) |
| $\psi_k^k$ exact (paper §5) | **not assumed**: computed, $O(k\boldsymbol{u})$ then $1/k$ by the root |
| iqr step | **computed** (Givens program, C3/P1), not a kernel; a kernel meeting `IsStableQRStep` is a drop-in |
| Ritz values | computed as SmallEig of the trailing block + Optimal (Part II), not the θ-optimal oracle |
| Hessenberg reduction | out of scope (input is Hessenberg) |

## 9. Open questions (recommendations in bold; the decision sheet has them)

1. **D1 model**: **(a) `StdModel` relative error on real words, sqrt included, complex pairs**,
   exact disk samples; (b) `MixedModel` now; (c) a complex machine.
2. **D2 kernel vs computed**: **iqr computed (C3/P1); $k$-th roots computed (`sqrtIter`);
   SmallEig a randomized kernel; Ritz = SmallEig + Optimal**; alternative: iqr as a kernel contract
   (`IsStableQRStep`) first.
3. **D3 landing** (after review): **batch 1 = waves 0–2 now** (B1–B6, G1–G5, K1, Q1–Q3, Q5,
   Q6, R1–R4, E1, D1–D4, U1, S1, S2, S4, S6, C1–C3; E2 waits for Codex's export); **batch 2 =
   C4, P1–P3** after `BackwardDecouplingContract` gains the failure disjunct
   (`IsDecoupledAbs τ H' ∨ failWord`, D5) and Codex's word-level split (§7.4 item 1) is in; Q4, S3,
   S5 (wave 3) with batch 1 once their edits are approved. Earlier recommendation: L1 first as its own landing (waves 0–3 + P1–P3); then
   L2–L4.
4. **D4 gap fixes that change statements**: **adopt all of §2** (G8/G8', G9 direct route, G10 via
   $\beta \to \beta/1.25$, G12 bottom-$k$, G13 cover + 11, G13v, G16 $m\nu\boldsymbol{u} \le 1/4$,
   D3.4 base, L3.7 Frobenius, G18 via Codex's κ lemma, deflate bottom $k$, Thm 1.4 with $\Sigma$).
5. **D5 failure semantics**: **fail word + cap** (total program, `Specification.Accepts` fails on
   the bad event) vs forced deflation.
6. **D6 Codex coordination**: **ask Codex for §7.4 item 1 (word-level split)** before P1, else
   duplicate frame proofs.
7. **D7 QR perturbation constants** (resolved by review: $7.02$, $3.64 \le 8$ by the elementary
   proof): **state 8 at $\eta \le 1/4$**; originally: verify against Sun 1991 /
   Chang–Paige–Stewart at proof time**; only Q4 depends on it (Q5 avoids it).

## 10. Risks

* R1–R2 (QR perturbation) constants unverified against the source; the statements are loose on
  purpose (D7).
* S3, S5 inherit Part I's machinery (Lemma 2.8, the dichotomy); constants were checked by hand,
  not machine-checked; a reviewer should re-check S5's hypothesis list.
* C4 depends on Codex's preservation proofs adapted to a nonzero backward error.
* Program-side effort: the exact development's program proofs are ~13k lines; the rounded
  programs (P4–P12) are new; without §7.4 item 1 the frame proofs repeat.
* The paper's Thm 1.4 asymptotics stand, but the explicit $\boldsymbol{u}_{\mathrm{ShQR}}$ is
  long; T2 is L only if the closed form is assembled once (as a definition) and bounded once.

## 11. Material

Part II LaTeX (`src2/*.tex`), Part I (`src1/exactqr.tex`), the stage-1 note §§9–10, the reviews
Review-Fable-Ops-ShiftedQR and Review-Fable-Ops-BackwardError, Paper-Gap-G15, Higham 2002
(Ch. 2, 3, 19), Sun 1991, Chang–Paige–Stewart 1997, Bauer–Fike 1960, Pirl 1969 (packing; not
cited in Lean, the bound 11 is elementary).

## 12. Checks run on the skeleton

`lake build` (full): 5071 jobs, success. `check_rules --files` on the 10 new Lean files and
`NLAlib.lean`: 0 errors, 0 warnings. 39 `sorry`s, all in theorem statements.

`scripts/stage_check.sh`: exit 1, at the strict kernel replay only. Before it: 1343 proved
modules build with `--wfail` (0 warnings), axiom audit 0 violations, 14 linters 0 errors,
`mk_all --check` current, freshness current. The replay reports 39 violations, exactly the 39
skeleton sorries (strict on `NLAlib`). The house practice is a scaffold library, which needs a
`lakefile.toml` edit this design may not make (decision D8). The steps after the replay (fixtures,
program checks, references, constants, rules extraction) did not run.

**Scaffold patch (D8, not applied).** `~/nlalib-harness/reports/sqr-fp-scaffold.patch` moves the
ten skeleton files to `NLAlibScaffold/` (module names `NLAlibScaffold.*`), drops them from
`NLAlib.lean`, adds the root `NLAlibScaffold.lean` and the `NLAlibScaffold` `lean_lib` to
`lakefile.toml` (the SHIFTED-QR pattern, 55eebad2; removed again as in a7085789/bde2a77a). Apply
with `git apply` after the maintainer approves the lakefile edit; then `stage_check` replays
only sorry-free `NLAlib`. A file moves back into `NLAlib` when its statements are proved.
