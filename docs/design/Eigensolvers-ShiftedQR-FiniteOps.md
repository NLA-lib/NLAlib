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
* **Q4** gains `IsUpperHessenberg H` (found at proof time): `multiShiftedQRStep` is Givens QR,
  which is a QR factorization of $p(\mathbf{H})$ only for Hessenberg $\mathbf{H}$. Without it false:
  $3\times3$, $m = 1$, $s = C = 0$, the chain the exact QR step truncated to Hessenberg form,
  $\mathbf{H}$ close to rank one with $\mathbf{H}_{31} \approx 6\cdot10^{-8}$ (data and an 80-digit
  check in `~/nlalib-harness/pilot/q4-counterexample/`): hypotheses hold ($x = 1.4\cdot10^{-14}$,
  bound $1.3\cdot10^{-9}$, $\kappa \le 3.44$, $d = 2.9\cdot10^{-7}$), but every phase $\mathbf{D}$
  leaves error $\ge 0.251$ against the bound $1.5\cdot10^{-4}$. Every use applies Q4 to a
  Hessenberg iterate.
* **S5** `hRhi`: $1.001\cdot2^{1/k} \to 2.002^{1/k}$; with a flat $1.001$ the constant $13$ fails for
  $k \ge 60$. The paper's (eq:boundonpottilde), $\tilde\psi$ within $0.001/k$, is not quite enough
  (second-order slip, Fable review of the agent statements): with the radius word
  $\mathrm{fl}(2^{1/k}\theta\alpha B^{1/k}\tilde\psi)$ the upper end needs
  $(1 + 0.001/k)(1 + \boldsymbol{u}) \le 1.001^{1/k}$, false for every $k \ge 2$. P6 therefore exposes
  $\lvert\tilde\psi - \psi_k\rvert \le 20\boldsymbol{u}\psi_k$; P9 takes $10^5k\boldsymbol{u} \le 1$
  ($\tilde\psi$ within $0.0002/k$), which fits both ends for every $k \ge 1$.
* **C1** `BackwardIterationContract ν` → `BackwardIterationContract θ ν` (θ a parameter, as in
  `BackwardDecouplingContract θ ε`). With θ quantified inside, C1 is false: let `Iter'` test the
  stored θ word against θ₀ and run `iteration` (meets `IterationContract θ₀`) or `abort`; at the
  word θ₀ + 1 with $m = 0$, $n = 1$, $\mathbf{H} = 0$ every hypothesis holds ($k = 1$ gives
  `exceptionalSpacing = 1`, $M = 2$) and `abort` fails `Writes .total`. No consumer changes: C4/P3
  use only `BackwardDecouplingContract θ`, and a rounded decoupling loop calls the iteration at its
  own fixed θ.
* **S5** gains `hd`, no shift of `ss` an eigenvalue (as the exact Exc lemma has it). Without it
  false: an eigenvalue $r$ makes the stagnation hypothesis vacuous (Lean's inverse is $0$).
  $n = k = 2$, $\mathbf{H} = \mathbf{I} - uu^{\mathsf T}$, $u = (0.006, 0.006, \sqrt{1 - 7.2\cdot10^{-5}})$
  (eigenvalues $0, 1, 1$, $\kappa = 1$, $\psi \approx 4.65\cdot10^{-4}$), `ss` $= [0, 0]$, $r = 0$,
  $B = \alpha = 1$, $\gamma = 1/2$, $\theta = 1/(4.2\psi)$, $\varepsilon = 1/2$, $S$ an offset square
  grid of spacing $0.7\tilde R$: every $s \in S$ is $\ge 0.166$ from the spectrum, so
  $\|\mathbf{e}_n^{\mathsf T}(\mathbf{H} - s)^{-2}\| \le 36 < ((1-\gamma)\psi)^{-2}$. P9 supplies `hd`
  as it supplies S4's `hne` (same `ss`): the Ritz shifts are tried first, and an eigenvalue shift
  is accepted (exactly: `det_sub_smul_one_ne_zero_of_find_none`). `hkn`, `hγ`, `hε2` are unused.
* **E1** gains `hβ0 : 0 ≤ β`. Without it false at $m = 0$: with $\beta = -1$ the forward
  hypothesis is vacuous, but every $0\times0$ $\mathbf{L}'$ has $\|\mathbf{L}' - \mathbf{L}\|_2 = 0 > \beta$.
  A skeleton gap, not a paper error; T1 supplies it (an error bound, $\beta \ge 0$). Proved.
* **RandomDecouplingContract** gains outer bounds `nmax` (order) and `Nmax` (norm), with the
  hypotheses $n \le n_{\max}$, $N \le N_{\max}$ (found while proving P11p; maintainer approved).
  As first stated, with $n$ and $N$ quantified inside while $\boldsymbol{u}$, the cap $F$, $\varphi$
  and the parameter words are fixed, it is unprovable for the Lemma 6.4 loop: the precision and the
  cap the loop needs grow with the block's order and norm ($F \approx \log(N/\omega)/\gamma$, the
  iteration's $\boldsymbol{u}$ bound decreases in $n$ and $N$), so no fixed choice serves every
  block. The change only weakens what a decoupler must deliver, so C4p becomes stronger; C4p and
  T1 instantiate `nmax := n`, `Nmax := N₀` (every block they hand to D has order $\le n + 1$ and
  norm $\le N_0$); no other hypothesis changes. Signature:
  `RandomDecouplingContract law B g φ k F nmax Nmax ps ω ε D I`.
* **P11p: the loop's scan has its own threshold.** The iteration's outcome certifies only
  $(1 - \boldsymbol{u})^2|h|^2 \le t$; a rounded `bottomScan` with the same $t$ fails whenever
  $t < (1 + \boldsymbol{u})^2|h|^2$, so the single threshold of the review (Statements3, item 3)
  can let a decoupled iterate through. `roundedDecouple` scans with the first parameter word
  $t_L$, $(1 + \boldsymbol{u})^2 t \le (1 - \boldsymbol{u})^2 t_L$, and certifies
  $|h| \le \omega_D$ from $t_L \le (1 - \boldsymbol{u})^2\omega_D^2$. The cap is stated as
  $(1 + \boldsymbol{u})^2((1.002(1-\gamma))^F N_{\max})^2 \le t_L$ (via
  `exists_norm_subdiag_le_hessenbergPotential`), the iterate norms as $N_{\max} + FE \le S$, the
  class as $FE \le (g/2)/(16(n_{\max}+1)2B)$. $F$ is a runtime dimension (no literal); $m$ and
  $n_0$ are read from the parameter words by `bindIdx`.
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
| E1 | `IsEigenvalueListing.exists_specNorm_sub_le` (forward ⇒ backward, Schur; $\beta \ge 0$) | Matrix/Perturbation/EigenvalueBackward | M | skel |
| C1, C2 | `IterationContract.backward`, `DecouplingContract.backward` (ν = 0 bridges) | Eigensolvers/ShiftedQR/Backward | S, S | skel |
| C3 | `shiftedStep_isPerturbedUnitarySimilar` (rounded step, $50(n+1)\boldsymbol{u}\|\mathbf{H}\|$) | same | L | skel |
| C4 | `solveRounded_backward` (the rounded worklist, fail disjunct; replaces the exact-worklist `solve_backward`, §13) | Eigensolvers/ShiftedQR/RoundedSolve | M (given C4a) | skel (batch 2) |
| C4a | `roundedWorklistRound_backwardStep` (one round as a `BackwardStep`) | same | H | skel (batch 2) |
| P1 | `stepWithDiag` program + `stepWithDiag_isStableQRStep` (both inequalities, outputs $\widehat{\mathbf{R}}_{nn}$; base $\|\mathbf{H}\|+\lvert s\rvert$; Hessenberg output; $300(n+1)^2\boldsymbol{u}$) | Eigensolvers/ShiftedQR/StableStep (new) | L | skel (batch 2) |
| P2 | `multiStepStable` + `multiStepStable_isStableQRChain` | same | M | skel (batch 2) |
| P3 | `bottomScan` + `bottomScan_writes` (the rounded bottom-$k$ decision of `Deflate`) | Eigensolvers/ShiftedQR/RoundedSolve (new) | M | skel (batch 2) |

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
| Q4 | `IsStableQRChain.exists_frobNorm_conj_sub_le` (L3.8 corrected, Hessenberg $\mathbf{H}$, phase $\mathbf{D}$, constant $66 + 2C$) | same | L | skel |
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
| P6 | rounded potential: $\tilde\psi_k$ within $20\boldsymbol{u}\psi_k$ (at least the paper's (eq:boundonpottilde), $0.001\psi_k/k$; moduli, product, `sqrtIter`) | RoundedRitz | S | plan |
| P7 | Find program meets S4's hypothesis | RoundedFind (new) | M | plan |
| P7b | `comptauHalf_isHalfTau`: the concrete comparison routine (copy, the half $l$ repeated $e$ times, `multiStepStable` P2 + `comptau` P5) meets `IsHalfTau`, P7's routine contract; bridge `shiftPoly_flatten_replicate` ($p_{l^e} = p_l^{\,e}$) | RoundedFind | M | plan |
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

### 7.4 Changes needed in Codex's files

**Item 1 is DONE on our side** (prove/sqrfp-compose), in Codex's merged files, exact theorems kept
as one-line corollaries with unchanged statements; Codex should take these changes, not redo them:
`Rotation` (`linearComplex`, `writes_rotate{Left,Right}WithScratch_word`), `RotationLoops`
(`machineRowRotation`, `machineColRotation`, their `_apply_*`/`_eq` lemmas,
`rotate{Rows,Columns}[WithScratch]_writes_word`), `Coefficients` (`coefficientRadius`,
`roundedGivensCoeffs` + `_eq`, `coefficients[WithScratch]_writes_word`), `Round`
(`round_writes_word`), `Shift` (`machineShiftedPrefix` + lemmas, `shiftDiagonal_writes_word`,
`initializeState_writes_word`), `Step` (`shiftedStep_writes_of_sweep`). C3 is proved on them by
`BackwardStep.loop_rel`.

Rule candidates found by C3 (not added): `BackwardStep.in_frame` (a framed body had to be unfolded
by hand); a `BackwardStep` rule through allocation (so no per-program "step from sweep" frame
lemma); a standard frame-state predicate for `loop_rel` (position, live views, scratch room; C3
defines a private `SweepState`). The program's coefficients are `NLAlib.roundedGivensCoeffs`
(`ShiftedQR.roundedGivensCoeffs_eq_ite`); the former `ShiftedQR.coefficientWords` was merged into it.

Original list:


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
6. (batch-2 review, Fable §4) **DONE on our side** (prove/sqrfp-b2work), hypotheses only, exact
   theorems kept as one-line corollaries with unchanged names and statements: the stack/scan memory
   lemmas assumed `ExactModel id M` but used only exact natural literals, so they could not be
   applied under `StdModel u` with `u > 0`. New machine-generic forms:
   `Worklist` (`rangePush_writes_of_isExactNatLit`, `rangePop_writes_of_isExactNatLit`,
   `stackInit_writes_of_isExactNatLit`), `Deflation` (`splitPush_writes_of_isExactNatLit`),
   `RangeSplit` (`writeAndSplit_writes_of_isExactNatLit`, `IsExactNatLit id M (n+1)`), each taking
   `IsExactNatLit id M B` and bounds of the literals written. `scanRound_writes` also used exact
   arithmetic (its squared modulus), not only literals: it now derives from
   `Scan.scanRound_writes_word` (any scalar machine, `IsExactNatLit id M n`; the stored word is
   `subdiagonalSqWord M H k`, bounded by `subdiagonalSqWord_bounds` under `StdModel`), on
   `PairScalar.normSq_writes_word` and `StdModel.add_mul_self_bounds` (`Ops/Blas/NormSq`). The
   exact `scanLoop`/`scan_writes` are unchanged.

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

## 13. Batch 2: the rounded worklist, C4, P1–P3 (skeleton)

Branch `prove/sqrfp-batch2` (from `integrate/sqrfp` @60ab60ad). Codex's exact worklist, scan
and `DecouplingContract` are untouched (§7.4 item 4 is ours: a new worklist in our files).
Statements and programs are in `NLAlibScaffold`; three declarations are proved (trivial glue:
RF1, DP1, LB1), seven are `sorry` (DP2, DP3, P3, C4a, C4, P1, P2).

### 13.1 The rounded worklist (`RoundedSolve.lean`)

`solveRounded D L : [N, k, np] (A, Thr, P) → (Out, Fl)` allocates the stack, a work matrix and
five scan registers and runs `roundedWorklist`: `Fl := 0`, `stackInit`, then
`while j < 2N, isPos St { roundedWorklistRound } then { if isPos St { roundedAbort } }`.
A round pops $(lo, d)$ (`rangePop`, bounded reads), copies the block (`copyToWork`), and

* $d \le k$: runs the leaf routine `L` into `Out[2 lo]`;
* $d > k$: runs `D [d, k, np] (W, P) → (W, Fl)`; if `Fl > 0` → `roundedAbort` (writes `Fl := 1`,
  stack count $0$); else `bottomScan [d, k] (W, Thr) → (R)`; if the flag `R[3]` is set,
  `writeAndSplit` at the index `R[4]` (reused as is: copy back, push both children), else abort.

Reused unchanged: `rangePop`, `stackInit`, `copyToWork`, `writeAndSplit` (`copyToGlobal`,
`splitPush`), `scanRound` (the visit of Codex's scan), `whileFuel`. New: `bottomScan` (the visits
$N-1-k+j$, $j<k$, i.e. exactly the bottom $k$ subdiagonals), `roundedAbort`, the three wrappers.
Footprints: a round writes `A, St, Out, W, R, Fl` (`roundedWorklistFp`); `Thr` and `P` are
read-only. The run is total: the fuel $2N$ is the cap (the exact progress measure
$2|\mathrm{done}| + |\mathrm{active}|$ shows it is never reached by a successful run); a decoupler
failure, an empty scan and work left at the cap each write the failure word.

**Contracts.** `RoundedDecouplingContract fails k ps ω ε D I` (the review's "fail disjunct"): from
a Hessenberg block of order $n + 1 \ge k + 1$, norm $\le N$, with the parameter words `ps`, `D` is
total, writes only the block and `Fl`, and either `Fl = 1` (only if `fails`), or `Fl = 0` and the
block is an upper Hessenberg perturbed unitary similarity with error $\varepsilon(N)$ having a
bottom-$k$ subdiagonal entry of modulus $\le \omega$. No precondition on $\kappa_V$, gap or
convergence: backward error does not need them, and a capped Lemma 6.4 loop that fails when its
cap is exhausted meets the contract with `fails` true for every tape. `BackwardLeafContract β L
I`: a leaf returns an eigenvalue listing of $\mathbf{B} + \mathbf{F}$, $\|\mathbf{F}\|_2 \le \beta$
(exact kernel: LB1, $\beta = 0$; SmallEig with forward error via E1). The old
`BackwardDecouplingContract θ ε` (Codex's parameter layout, no failure) stays only for C2; the
old `solve_backward` (Codex's exact worklist with a backward decoupler) is removed: that worklist
cannot take a failing decoupler, and Part II's decoupler has other parameters (review §6).

### 13.2 Statements and rationale

| id | statement | rationale |
|---|---|---|
| RF1 | `BackwardStep.in_frame` (proved) | rule candidate from C3; C4 composes framed rounds with it |
| DP1 | `DeflationInv.exists_isPerturbedUnitarySimilar_rebase` (proved) | turns an accumulated invariant into one `IsPerturbedUnitarySimilar` step + invariant at error $0$: what makes a round a `BackwardStep` |
| DP2 | `DeflationInv.setSubBlock_of_isPerturbedUnitarySimilar` | perturbed similarity of an active block (via `exists_submatrix`) |
| DP3 | `DeflationInv.finish_of_specNorm_le` | a leaf with backward error $\beta$ |
| LB1 | `IsEigenvalueKernels.backwardLeafContract` (proved) | exact kernel is a leaf with $\beta = 0$ |
| P3 | `bottomScan_writes` | flag $1$ ⇒ an index $i$, $n \le i + k$, $(1-\boldsymbol{u})^2\lvert h_{i+1,i}\rvert^2 \le t$; flag $0$ ⇒ every bottom-$k$ entry has $t < (1+\boldsymbol{u})^2\lvert h\rvert^2$ |
| C4a | `roundedWorklistRound_backwardStep` | one round, relation `IsPerturbedUnitarySimilar`, error $e \ge c + \varepsilon(N_0) + \beta$, state `RoundedWorklistState` (geometry + read-only words + failed-or-invariant at error $0$ for the current $\mathbf{M}$, $\|\mathbf{M}\|_2 \le \|\mathbf{H}_0\|_2 + je$) |
| C4 | `solveRounded_backward` | `(fails ∧ Fl = 1) ∨ (Fl = 0 ∧ Out = spectrum of H + E, ‖E‖₂ ≤ 2(n+1)(c + ε(N₀) + β))` |
| P1 | `stepWithDiag_isStableQRStep` | Definition 3.4 (corrected base) with $300(n+1)^2\boldsymbol{u}(\|\mathbf{H}\|_2 + \lvert s\rvert)$ and the stored $\widehat{\mathbf{R}}_{nn}$ |
| P2 | `multiStepStable_isStableQRChain` | the degree-$k$ step is `IsStableQRChain (300(n+1)^2 u)`, Hessenberg output, the $k$ stored $\widehat{\mathbf{R}}_{nn}$ |

Hypotheses pinned (C4/C4a): `StdModel u id`, $0 \le \boldsymbol{u} < 1$; `IsExactNatLit id Mch (n+1)`
(**found while writing**: index literals are `M.lit n`, exact under `StdModel` only for $0$; the
stack, flags and indices are such literals, so without it the count words are rounded and the
statement is false); $\mathbf{H}$ upper Hessenberg; threshold word $t$ with
$(1+\boldsymbol{u})^2\omega^2 \le t$ (an entry $\le \omega$ always passes the rounded test, so a
successful decoupler never leads to an abort) and $t \le (1-\boldsymbol{u})^2c^2$, $c \ge 0$ (each
cut $\le c$; Part II: $t = 2\omega^2$, $c = 2\omega$ for $\boldsymbol{u} \le 0.29$); $\beta \ge 0$;
$\varepsilon(N_0) \ge 0$; $\|\mathbf{H}\|_2 + 2(n+1)(c + \varepsilon(N_0) + \beta) \le N_0$ (every
block the decoupler sees has norm $\le N_0$; replaces the old $2\|\mathbf{H}\|$ device, which was
vacuous at $\mathbf{H} = 0$). Fuel/cap: $2(n+1)$ rounds. Not needed and not assumed: $k = 2^m$
(any $k$; the algorithm instantiates $2^m$), $n \ge 1$, $\omega > 0$, monotone $\varepsilon$,
$B \ge 1$ and the Lemma 6.1 threshold $B > 4n$ (both are convergence/preservation, P11/P12,
not backward error). P1/P2: Hessenberg input (Givens QR is a QR factorization only then, as Q4),
$(n+1)\boldsymbol{u} \le 1/2500$ (C3's), $\boldsymbol{u} \ge 0$; any shift.

The error bound $2(n+1)e$ is uniform per round because `BackwardStep.whileFuel` charges a fixed
$\varepsilon_i$ per round; the outcome-sharp $n(c+\varepsilon) + (n+1)\beta$ would need an
outcome-dependent rule. A factor $\le 2$; irrelevant for the precision theorem.

### 13.3 Edge cases checked

* **C4/C4a.** $n = 0$ ($1\times1$; with $k \ge 1$ one leaf, error $\beta$; with $k = 0$ the block
  goes to `D`, whose success branch needs an index in `Fin 0`, so `D` must fail: the conclusion
  is the fail disjunct, and with `fails` false the contract is unsatisfiable — consistent);
  $\mathbf{H} = 0$ (no vacuity, unlike the old $\le\|\mathbf{H}\|$ hypothesis); $\varepsilon(N_0)<0$
  (excluded: else $e < \beta$ and a single leaf violates the bound); $\omega < 0$ (success
  impossible, harmless); `ps = []`; a failure at the first call; work left at the cap (impossible
  for a successful run: the state at $j = 2(n+1)$ forces $2|\mathrm{done}| \ge 2n+3$); scan finds
  an index other than the decoupler's (fine: every passing index has $\lvert h\rvert \le c$);
  scan finds none after a successful decoupler (impossible by $(1+\boldsymbol{u})^2\omega^2 \le t$);
  children nonempty ($i < d - 1$); stack capacity after a push (from `length_le` after the split);
  $\boldsymbol{u} = 1$ (excluded: the cut bound needs $(1-\boldsymbol{u})^2 > 0$).
* **P3.** $k = 0$ (no visit, flag $0$, vacuous ∀); $k = n$ (all subdiagonals); $n = 0$;
  $\boldsymbol{u} \le 1$ needed for $\mathrm{fl}(x^2) \ge 0$; index literal exactness.
* **P1.** $n = 0$ (no rotation: $\widehat{\mathbf{R}} = \mathrm{fl}(h - s)$, error $\le \boldsymbol{u}\lvert h-s\rvert$);
  $\mathbf{H} = 0, s = 0$ (all zeros exact); non-Hessenberg $\mathbf{H}$ (excluded, false as for Q4);
  zeroing pass needs `M.lit 0 = 0` (true under `StdModel`); constant: $171(n+1)^{3/2} \le 300(n+1)^2$
  (similarity, the zeroed part costs $\sqrt{n+1}$), $72(n+1)$ (factorization).
* **P2.** $k = 0$ (nil chain, `readBlock` of $0$ words); output Hessenberg stated separately (the
  chain gives it only for $k \ge 1$); shift and diagonal views disjoint from the matrix (the
  in-place copy would overwrite them).
* **DP2/DP3.** $e < 0$ or $\beta < 0$ (hypotheses unsatisfiable, vacuous); ranges clamped by
  `blockIndex` (in range by the partition).

### 13.4 Notes for the reviewer

* The caller's gloss "P1 = rounded decoupling round, P2 = Lemma 6.4 loop, P3 = deflate" differs
  from §4 (P1 step, P2 degree-$k$ step, P3 worklist). This batch follows §4, with P3 narrowed to
  the deflation decision (`bottomScan`) and the worklist itself as C4/C4a. The Lemma 6.4 loop is
  P11 (L2): it is the `D` that meets `RoundedDecouplingContract`.
* Rule candidates: `BackwardStep.in_frame` added (RF1). Not added: a `BackwardStep` rule through
  allocation (C4 allocates only at the top, where `writes_allocs_preserving_post` suffices); a
  `whileFuel` with outcome-dependent errors (see 13.2); a standard frame-state predicate (C4a's
  `RoundedWorklistState` carries `RoundedGeometry`, the worklist's own).
* Risk: C4a is the bulk (a replay of Codex's `processRange`/`worklistRound` memory proofs with
  the new branches); P1 needs a pair version of C3's sweep lemma and the residual bookkeeping of
  the triangular factor.

## 14. Toward the headline: L2–L4 (batch 3 onward)

Branch `design/sqrfp-headline` (from `integrate/sqrfp` @f9679b04). Maintainer (2026-11-14): "lets
work on the next bits to get a true headline theorem. some of L2 might belong in its own place."
State on entry: L1 and batches 1–2 proved with standard axioms (C4 `solveRounded_backward`, P1–P3,
R1–R4, Q1–Q6, S1–S6, D1–D4, U1, E1–E2, K1, DP1–DP3, B*, G*, C1–C3). This section fixes the
headline, works backwards to those results, places every new result, and settles the C4
interface for the probability layer. The general probability layer has its own note,
[Ops-Probabilistic-Specs](Ops-Probabilistic-Specs.md).

### 14.1 The headline

**T1c (Theorem 6.3 with Theorem 1.4's quantifiers, corrected; constants revised in §14.11).** Let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$
with $\kappa(\mathbf{V}) \le B$, eigenvalues separated by $\Gamma > 0$, $\|\mathbf{H}\|_2 \le
\Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$, and $k = 2^m$ chosen from $B$ as in
(eqn:setk) (so $B^{2/k} \le 2$). On a machine with `StdModel u id`, Borel operations, exact natural
literals up to $n + 1$, a tape whose stream $s_U$ is uniform on $[0, 1]$, an exact polar disk
sampler and a `SmallEig` kernel meeting Definition 1.2 (forward error $\beta_{\mathrm{se}}$,
failure $\varphi_{\mathrm{se}}$ on a bad window), with the parameter words set by
`shqrParams n k B Γ Σ δ φ` and

$$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}(n, k, B, \Gamma, \Sigma, \delta, \varphi),$$

the program `roundedShQR` run on the stored $\mathbf{H}$ **always terminates** (every tape;
capped, C4), and with probability at least $1 - \varphi$ it sets the failure word to $0$ and stores
all eigenvalues, with multiplicity, of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le \delta$. Lean form (planned, with the programs of wave 9). It takes
`hI : I.IsMeasurable` and `hloc` as C4p does. The earlier `hMeas : Mch.IsMeasurable` does not
give `hI`: the contracts leave `I` free off their operands (Fable review of the PROB-LOGIC
drafts, item 1). PL4 instead shows that a measurable interpretation meeting the contracts
exists. In T1c, `0 ≤ φse` follows from `IsRandomSmallEig` at any Hessenberg input, or is added
next to `hφse`.

```lean
theorem roundedShQR_measureReal_not_spectrum_le … (hM : StdModel u id Mch)
    (hI : I.IsMeasurable) (hloc : ∀ o, I.TapeLocal o (win o))
    (hNat : IsExactNatLit id Mch (n + 1)) (hSE : IsRandomSmallEig law sU βse φse I)
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * diagonal d)
    (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ) (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖)
    (hΣ : specNorm H ≤ Σ) (hδ : 0 < δ) (hδΣ : δ ≤ Σ) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hk : k = shqrDegree (4 * B)) (hpar : … stored params = shqrParams n k B Γ Σ δ φ)
    (hse : βse ≤ shqrSmallEigAccuracy n k B Γ Σ δ) (hφse : φse ≤ shqrSmallEigFailure n k B Γ Σ δ φ)
    (hu : u ≤ uShQR n k B Γ Σ δ φ) … (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (roundedShQR …) env F
      (fun μ' => Fl = 0 ∧ ∃ roots E, HoldsMatrix out roots μ'.store ∧ specNorm E ≤ δ ∧
        (H + E).charpoly.roots = List.ofFn roots) μ} ≤ φ
```

**T1 (in the skeleton, the worklist level).** `NLAlib.ShiftedQR.solveRounded_measureReal_not_spectrum_le`
(`NLAlibScaffold/Eigensolvers/ShiftedQR/RoundedHeadline.lean`, **proved** from C4p
`solveRounded_pwrites`): the same program `solveRounded D L` as C4, with a decoupler meeting
`RandomDecouplingContract law (2B) (g/2) φ_D …` (a probabilistic block specification on the class:
Hessenberg, norm $\le N$, condition $\le 2B$, separation $\ge g/2$) and a leaf meeting
`RandomLeafContract law β φ_L`, fails to store the spectrum of some $\mathbf{H} + \mathbf{E}$,
$\|\mathbf{E}\|_2 \le 2(n+1)(c + \varepsilon(N_0) + \beta)$, with probability at most
$2(n + 1)(\varphi_D + \varphi_L)$, provided $2(n+1)(c + \varepsilon(N_0) + \beta) \le
g/(16(n+1)B)$ (class preservation, via `DeflationInv.exists_pseudoConditionNumber_subBlock_le`
and the new P12a). T1c is T1 with $D$ = the Lemma 6.4 loop of `Regularize` + $\mathrm{Sh}_{k,B}$
(P11p: $\varphi_D = F\varphi_{\mathrm{it}}$, $\varepsilon(N) = F\varepsilon_{\mathrm{it}}(N)$),
$L$ = `SmallEig` + E1, and the parameter arithmetic PAR1. Why the split: the iteration programs
(P4–P10) do not exist yet, and the headline's shape must not wait for them; T1 is a real theorem
about the C4 program now, and T1c's statement is fixed here.

**T2 (bits).** $\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}}) \le c_1 k \log_2(n B \Sigma/(\delta\Gamma\varphi)) + c_2$
with explicit $c_1, c_2$; $\Sigma$ appears (errata N8). `uShQR` is one closed-form definition
(min of the loop budget, $\boldsymbol{u}_{\mathrm{Regularize}}$, $\boldsymbol{u}_{\mathrm{Sh}}$
with the corrected G8/G9/G13/G16 forms), bounded once. **T3**: relative form $\delta\|\mathbf{H}\|_2$
with $\Sigma$ an input word, $\|\mathbf{H}\|_2 \le \Sigma \le c\|\mathbf{H}\|_2$ (or $\Sigma$
computed as a rounded $2\|\mathbf{H}\|_{\mathsf F}$). **T5**: work bound on every tape (the cap
makes it deterministic; the paper's holds only w.p. $1-\varphi$, errata N10).

**Hypotheses and why each is honest.** Hessenberg input (Givens QR is a QR factorization only
then; Q4, S3); $\kappa$ and gap as data of an explicit diagonalization (the paper's
$B \ge 2\kappa_V$, $\Gamma \le \mathrm{gap}/2$ with the factor 2 moved into the contract classes);
$\Sigma \ge \|\mathbf{H}\|$; `StdModel` (no under/overflow, Part II's model); Borel machine
operations (needed: the failure event of a call is a function of the computed input block, and
with non-measurable rounding the adaptive union bound fails); exact literals for the index words;
exact polar sampler (decision D1c; a rounded sampler is a coupling within $O(\boldsymbol{u}R)$,
absorbed in G13vi's slack — not formalized); `SmallEig` an oracle with a bad-window contract
(Part III out of scope; its precision is not counted); parameter words exact (the $(k-1)$-th root
in Exc's $\varepsilon$, the cap $F$, $k$, the thresholds are supplied, computed outside the model).

**What it does not claim.** No Hessenberg reduction or random preprocessing of a general matrix
(Remark 1.3); no statement about `SmallEig`'s own cost or precision; no running-time bound beyond
T5's count of operations; no forward error for eigenvalues; no rounded disk sampler; nothing for
$\kappa_V = \infty$ or repeated eigenvalues ($\Gamma > 0$ is a hypothesis). Modelling choices that are stronger than
the paper: `SmallEig`'s randomness is a fixed window of the uniform stream, and the parameter
words are exact reals, not floats (§14.11).

### 14.2 Backwards from the headline

`✓` = proved on `integrate/sqrfp`; `skel` = sorried here; `plan` = specified, skeletonized with
its program. Gen = general library (own topic file, stage-free docstring), Stg = this algorithm.

| id | statement | place | G/S | diff | status | wave |
|---|---|---|---|---|---|---|
| T1c | `roundedShQR_measureReal_not_spectrum_le` | Eigensolvers/ShiftedQR/RoundedHeadline | Stg | M | plan | 10 |
| T2, T3, T5 | bits; relative form; work bound | same | Stg | L, M, M | plan | 10 |
| T4 | Hermitian corollary ($k = 2$, $B = 1$; optional) | same | Stg | L | plan | 10 |
| PAR1 | `shqrParams`/`uShQR` meet T1's and P11p's hypotheses (ω, $c$, threshold word, budget, $\varphi$ split $\varphi/(4(n+1))$ each) | same | Stg | L | plan | 9 |
| PAR1p | positivity under T1c's hypotheses: `0 < uShQR …`, `0 < shqrSmallEigAccuracy …`, `0 < shqrSmallEigFailure …` (else T1c is vacuous through $0 \le u \le$ `uShQR` and T2's $\log$ is junk); review B1 | same | Stg | M | plan | 9 |
| PAR1k | `2 ≤ shqrDegree B` and $B^{2/k} \le 2$ (N11, S3's `hBk`) | same | Stg | S | plan | 9 |
| T1d | the all-tape statement for `roundedShQR`: on every tape the run is total, writes only $\mathbf{A}$, `Out`, `Fl`, and `Fl = 0` implies the spectrum of some $\mathbf{H}+\mathbf{E}$, $\|\mathbf{E}\|_2 \le \delta$ (C4 with `fails := True` + P11d + the leaf's all-tape contract) | RoundedHeadline | Stg | S | plan | 10 |
| T1 | `solveRounded_measureReal_not_spectrum_le` | RoundedHeadline | Stg | S | **proved** (from C4p) | — |
| C4p | `solveRounded_pwrites` (worklist as `PWrites`; class preservation; rounds add) | RoundedHeadline | Stg | H | skel | 7 |
| C4cap | D interface `[n+1, k, np, F]`, `F` an outer parameter of both decoupling contracts (§14.4, §14.11 B4); **before C4p** | RoundedSolve | Stg | S | plan | 6 |
| P12a | `DeflationInv.exists_pseudoConditionNumber_subBlock_le_and_le_norm_sub` (active blocks: condition $2B$, separation $g/2$) | Matrix/QRIteration/DeflationPerturbed | Gen | M | skel | 5 |
| P12b | iterate class: a perturbed unitary similarity within $g/(16NB)$ of a block with condition $\le 2B$, separation $\ge g/2$ has condition $\le 4B$, separation $\ge g/4$ (from E2; §14.11 B3) | Matrix/Perturbation/EigenvalueBackward | Gen | S | plan | 5 |
| LF1 | `SmallEig` kernel (`IsRandomSmallEig`: forward $\beta$ off a bad window) meets `RandomLeafContract` (E1) | Eigensolvers/ShiftedQR/RoundedKernels | Stg | M | plan | 7 |
| P11d | `roundedDecouple` (Lemma 6.4 loop: bottom scan P3, iteration, cap $F$) meets `RoundedDecouplingContract True` | Eigensolvers/ShiftedQR/RoundedDecouple | Stg | M | plan | 9 |
| P11p | `roundedDecouple_randomDecouplingContract`: `roundedDecouple` meets `RandomDecouplingContract` at $(2B, g/2)$, orders $\le n_{\max}+1$, norms $\le N_{\max}$ ($\varphi_D = F\varphi_{\mathrm{it}}$, error $F(1+C)S((1+300(n_{\max}+1)^2\boldsymbol{u})^k-1)$; iterates at $(B_i \ge 4B, g/4)$, norm $S$) by P10b + PL5 (`whileFuel`) + P12b | RoundedDecouple | Stg | L | **proved** | 9 |
| P10b | `shIteration` = Regularize; Sh: `ShIterationContract` (decoupled at the bottom, or $\psi_k$ contracted by $1.002(1-\gamma)$; error $\varepsilon_{\mathrm{it}}$; failure $\varphi_{\mathrm{it}}$) | Eigensolvers/ShiftedQR/RoundedIteration | Stg | M | plan | 9 |
| P10 | `regularize` program (SmallEig of the trailing block, $k$ disk draws, Optimal, $\le k$ trials) — PWrites from S1–S3 ✓, RZ1, D3 ✓, Q4 ✓ | Eigensolvers/ShiftedQR/RoundedRegularize | Stg | L | plan | 8 |
| P9 | `shStep` program (Find, comptau test, Exc, trials, fail word) — PWrites from S4 ✓, S5 ✓, Q5 ✓, Q6 ✓, D4 ✓ | Eigensolvers/ShiftedQR/RoundedSh | Stg | L | plan | 8 |
| P14 | Regularize's failure $\le \varphi$: SmallEig $\varphi/2$ + D3 ✓ $\varphi/2$, by PL3b on the joint window | RoundedRegularize | Stg | M | plan | 7 |
| P15 | Exc translate failure (D4 ✓, $\eta = \varepsilon\tilde R\sqrt{\varphi/(11n)}$), PL3b | Eigensolvers/ShiftedQR/RoundedExc | Stg | S | plan | 7 |
| P8 | `excShifts` program (net of $\mathbb{D}(r, (1+\varepsilon)\tilde R)$, translate, rounding $\le \min(0.005\varepsilon\tilde R, \eta/2)$) meets S5's cover/card and D4's separation | RoundedExc | Stg | L | plan | 8 |
| P7b | `comptauHalf` (copy $\mathbf{H}$, `repeatBlock` $l^e$, `stepComptau` = `multiStepStable` P2 ✓ + `comptau` P5 ✓) meets `IsHalfTau` ($0.0011$) under $300(n+1)^2\boldsymbol{u} \le (8004B)^{-1}(d/((2+2C)\|\mathbf{H}\|))^{k/2}$, $30000(k/2+1)\boldsymbol{u} \le 1$, $(n+1)\boldsymbol{u} \le 1/2500$; P9 passes it to P7 | Eigensolvers/ShiftedQR/RoundedFind | Stg | M | plan | 8 |
| P7 | `findRounded` program (halving with comptau of half-products via P2 ✓) meets S4's hypothesis | Eigensolvers/ShiftedQR/RoundedFind | Stg | M | plan | 8 |
| P6 | `roundedPotential` (bottom product + `sqrtIter` K1 ✓, FP1): $\tilde\psi$ within $20\boldsymbol{u}\psi$ (under $20000k\boldsymbol{u} \le 1$; P9 takes $10^5k\boldsymbol{u} \le 1$) | Eigensolvers/ShiftedQR/RoundedRitz | Stg | S | plan | 7 |
| P5 | `comptau` ($\mathrm{fl}\prod\lvert\widehat{\mathbf{R}}_{nn}\rvert$ from P2 ✓; Q5 ✓ + FP1) | RoundedRitz | Stg | S | plan | 7 |
| P4 | `optimalTest` program ($\widehat{\mathbf{v}}_k$ recurrence; FP2) meets S1/S2's $0.0009$ hypothesis | RoundedRitz | Stg | M | plan | 7 |
| FP2 | rounded $\mathbf{e}_n^{\mathsf T}p(\mathbf{H})$ by the recurrence $\widehat{\mathbf{v}}_{j+1} = \mathrm{fl}((\mathbf{H} - s_{j+1})^{\mathsf H}\widehat{\mathbf{v}}_j)$: error $\le 2(n+1)^2(2+2C)^k\|\mathbf{H}\|^k\boldsymbol{u}$ (Lemma 4.5) | Matrix/FinitePrecision/HessenbergRowPoly | Gen | M | plan | 6 |
| FP1 | rounded product of $k$ words: relative error $(1+\boldsymbol{u})^{k-1} - 1$ | Matrix/FinitePrecision/ProductRounded | Gen | S | plan | 5 |
| GR1 | main's `squareGrid c R ε`, filtered to $\mathbb{D}(c, (1+\varepsilon)R)$: still covers $\mathbb{D}(c,R)$ at $\varepsilon R$ (a covering point is within $\varepsilon R$; `exists_mem_squareGrid_norm_sub_le` reused), is $0.99\varepsilon R$-separated (spacing $2\varepsilon R/(\sqrt2+\varepsilon)$, $\varepsilon \le 1/2$), and has $\le 9/\varepsilon^2$ points (S5's count; the unfiltered `length_squareGrid_le` gives only $12/\varepsilon^2$). Two lemmas `squareGrid_pairwise_separated`, `card_filter_squareGrid_le`; no new net | Matrix/QRIteration/Strategy | Gen | M | plan | 5 |
| RZ1 | `exists_perm_forall₂_ritzValues` (a forward-accurate listing of the trailing block, reordered, is entrywise within $\beta$ of `ritzValues`) | Matrix/QRIteration/Ritz | Gen | S | skel | 5 |
| D5 | `map_polarDisk_eq_diskUniform` (two uniform draws → the uniform disk law) | Probability/Distributions/DiskUniform | Gen | M | skel | 5 |
| PL0–PL6 | **stage PROB-LOGIC** ([Ops-Probabilistic-Specs](Ops-Probabilistic-Specs.md), own targets file): run measurability, strong Markov at stopping times, `PWrites` rules, measurable catalog, `PBackwardStep.whileFuel`, bridge to `Ops/Law` | Ops/Logic/Probabilistic, Ops/TapeStopping | Gen | — | separate stage | PROB-LOGIC 1–3 |

Proved and used unchanged: C4, C4a and their sublemmas (deterministic skeleton of C4p),
P1–P3, Q1–Q6, R1–R4, S1–S6, D1–D4, E1, E2, K1, DP1–DP3, B*, G*. U1 is no longer on the critical
path (`PWrites.seq` subsumes the adaptive union bound); it stays as a law-level lemma.

**Counts (revised, §14.11).** SQR-FP: skeleton 4 sorried (S 1, M 2, H 1: RZ1, D5, P12a, C4p)
+ T1 proved; planned 30 (S 10, M 13, L 7). PROB-LOGIC (its own stage, PL0–PL6): skeleton 6
sorried (M 3, L 2, H 1) + 3 proved; planned 7 (S 2, M 4, L 1).

### 14.3 Placement (the maintainer's point)

**General, own topic files, docstrings without this stage:** the Ops probability layer PL0–PL6
as the separate stage PROB-LOGIC (`Ops/Logic/Probabilistic`, `Ops/TapeStopping`,
`Ops/Catalog/ScalarMeasurable`); the polar sampler
D5 (`Probability/Distributions/DiskUniform`); approximate Ritz values RZ1
(`Matrix/QRIteration/Ritz`); class preservation P12a/P12b (`DeflationPerturbed`,
`EigenvalueBackward`); rounded products FP1 and the rounded last-row polynomial FP2
(`Matrix/FinitePrecision/*`); the separation of main's square grid GR1 (`Matrix/QRIteration/Strategy`, next to its covering and
count; no new net). Already general and proved: perturbation of the Hessenberg
potential (Q6), optimal Ritz values under perturbation (S1–S3), Find with computed values (S4),
Exc's covering argument (S5), the abstract while loop (S6), disk regularization (D3, D4), the
measurable union bound (U1).

**Stage-specific (`Eigensolvers/ShiftedQR/…`):** the programs and their contracts (P4–P11,
LF1, P14, P15), C4p, PAR1, the headlines.

Earliest waves are the general ones (5–6); the stage programs follow (7–9); assembly last (9–10).

### 14.4 The C4 interface change (decision C4-CHANGE)

The watch item (batch-2 review §3): `fails : Prop` is global, so C4 does not expose which call
failed. The suggested `fails : ℕ → Prop` with `∃ pos, fails pos ∧ Fl = 1` **does not suffice**:
the contract quantifies the tape inside, so for a randomized decoupler (which fails on some tape
at every start position) `fails pos` must be true for every `pos` — no information. A usable
per-call event must depend on the tape and the call's input block,
`fails : (m : ℕ) → Matrix (Fin (m+1)) (Fin (m+1)) ℂ → Tape ℝ → ℕ → Prop`, and C4's fail branch
would expose `∃ j < 2(n+1), ∃ p Hⱼ, (Hⱼ an active block …) ∧ fails Hⱼ τ p ∧ Fl = 1`.

Options:

* **(a, recommended) Keep C4 and C4a as proved; add C4p.** The per-call failure event lives in
  each call's good set (`PWrites`), and the union bound is `PWrites.seq`/`whileFuel` (PL3, PL5).
  C4 stays the all-tapes backward statement (instantiated with `fails := True` for a randomized
  decoupler); C4p replays C4a's round with PWrites rules, reusing its deterministic sublemmas
  (`roundedRange_writes`, `roundedLarge_writes`, `roundedCut_core`, `RoundedGeometry.*`) for the
  branches without random calls. Re-proof of C4/C4a: **0 lines**. New: C4p (H, ~400 lines, mostly
  PWrites bookkeeping over existing sublemmas). One small edit is needed anyway (**C4cap**, S,
  ~20–40 lines): the decoupler's interface gains the cap dimension `F`
  (`[n+1, k, np, F] (W, P) → (W, Fl)`, as Codex's exact `decouple` has `[N, m, k, F, M]`), so that
  `roundedDecouple` is one program term with the cap as runtime data (a Lean constant could be a
  loop bound through `IExp.const`, but that makes a family of programs, one per $F$; review
  §4). `F` is an outer parameter of `RoundedDecouplingContract`/`RandomDecouplingContract`, like
  `k`, never quantified inside (the C1 lesson): $\varphi_D = F\varphi_{\mathrm{it}}$ depends on it. It changes `RoundedDecouplingContract`,
  `roundedProcessLarge` (one `run` line), `solveRounded`'s interface and the frames in C4a/C4.
* (b) Restate C4 with the tape-indexed per-call event above. Re-proof: `RoundedWorklistState`'s
  fail branch carries the witness, C4a's fail branch builds it from the popped block (M, ~150
  lines). But the union bound then needs the call positions and input blocks as **random
  variables** identified with C4's existential witness — a call-trace semantics for Ops that does
  not exist (H, specific to this proof). Not recommended.
* (c) `fails : ℕ → Prop`: insufficient (above).

### 14.5 Shared machinery and rule candidates (planned as early waves)

From batch 2 (RoundedSolve, program:math ≈ 816:94):

| candidate | where it goes | status |
|---|---|---|
| `DeflationInv.of_isPerturbedUnitarySimilar`, `DeflationInv.exists_isPerturbedUnitarySimilar_finish/_split`, `IsEigenvalueListing.charpoly_roots_eq_ofFn` (stated in `RoundedSolve`, general) | move to `Matrix/QRIteration/DeflationPerturbed`, `Matrix/Spectral/EigenvalueListing` | wave 5 (move only) |
| `writeAndSplit_writes_mem` (machine-generic split) | Codex's `RangeSplit` (with §7.4 item 6) | wave 5 (move) |
| witness-exposing `IsPerturbedUnitaryPair.exists_witness` (U, E, F as data for consumers that re-embed) | `Matrix/Perturbation/UnitaryPair` | wave 5, S |
| allocation geometry: `RoundedGeometry`/`WorklistGeometry` are the same structure (views live, room, pairwise apart) with the same six lemmas (`of_eqOff`, `live_of_subset`, `disj`, `disj_scratch`, `allocated`) | `Ops/Logic/Geometry` (`Ops.Geometry views lens μ`) | wave 5, M |
| `BackwardStep` through allocation (C4 used `writes_allocs_preserving_post` by hand) | `Ops/Logic/Backward` | wave 6, S |
| `PWrites` rules mirroring `Writes` 1:1 (seq/ite/loop/whileFuel/bindIdx/allocs/in_frame) | PL3 | wave 6 |
| `PBackwardStep.whileFuel` (backward error and failure add per round) — makes C4p, P11p and the Sh trial loops procedural | PL5 | wave 6 |
| a random-call rule from a kernel's bad-window contract (`PWrites.of_window` + frame) | PL3b | wave 6 |

New programs reuse: `multiStepStable` (P2) for every trial step, `bottomScan` (P3) for every
decoupling test, Codex's `BlockCopy`/`copyToWork` for trial copies, `sqrtIter` (K1) for roots.

### 14.6 Edge cases checked (per new statement)

* **C4p / T1.** $n = 0$: one leaf, D never called, bound $2\varphi_L$; $k = 0$: D gets
  $1\times1$ blocks, its success needs an index in `Fin 0`, so `RandomDecouplingContract` forces
  $\varphi_D \ge 1$ and the bound is trivial; $n + 1 \le k$: leaves only; $\varphi_D < 0$ or
  $\varphi_L < 0$: the contract is false under a genuine tape law (some instance has a satisfiable
  precondition), so no vacuous success; $B$: $\kappa \ge 1$ gives $B \ge 1$, no division by $0$ in
  `hsmall`; $g > 0$ assumed (else separation is empty and the class has no content); $\beta < 0$,
  $\varepsilon(N_0) < 0$ excluded (as C4); $\omega < 0$: D's success impossible, forces
  $\varphi_D \ge 1$; the classes are $2B$, $g/2$ (P12a needs total error $\le g/(16(n+1)B)$, and
  $2B\cdot g/(16(n+1)B) \le g/2$); the norm class $N_0$ covers every block (C4's `hN₀`).
* **P12a.** $r.2 = 0$ (empty block: vacuous); $\varepsilon < 0$ (invariant unsatisfiable);
  separation inherited only because the block's eigenvalues are a sub-multiset of those of
  $\mathbf{H} + \mathbf{E}$ (injective there) — stated with $\forall i \ne j$ on the block's own
  listing.
* **RZ1.** $k = 0$ (both lists empty); $\beta < 0$ (hypothesis unsatisfiable for $k \ge 1$); the
  order of `ritzValues` is `Multiset.toList` (arbitrary), hence the existential reorder.
* **D5.** $R > 0$ assumed ($R = 0$ makes `diskUniform` the conditional law on a null set, $0$);
  the image of $[0,1]^2$ is the closed disk; boundary null.
* **PL0–PL3, PL2.** See [Ops-Probabilistic-Specs](Ops-Probabilistic-Specs.md) §4 ($\varphi < 0$,
  $\varphi \ge 1$, `DeterminedFrom`, `W = 0`, test failure, `N = 0`, stopping positions that
  peek).
* **Junk values to watch in the planned statements.** P4/P9/P10: shifts equal to eigenvalues
  (Lean's inverse is $0$) — carried as `hne`/`hd` from D3/D4's distance $> 0$, as S3/S5 require;
  P6: $\psi = 0$ (an exactly decoupled block: the loop exits before Sh, so P9 assumes
  $\omega < $ every bottom subdiagonal); P8: $\varepsilon$ is an input word, $\varepsilon \le 1/2$
  checked (G13v); P7: $k = 2^m$, $m = 0$ (Find returns the single shift); P11p: $F = 0$ (the
  contract then requires the input already decoupled — false in general, so PAR1 must give
  $F \ge 1$); PAR1: $\log$ of ratios $\le 1$ ($\delta \le \Sigma$, $\varphi \le 1$ needed for the
  bit count to be nonnegative).

### 14.7 Skeleton and checks

New files: `NLAlibScaffold/Ops/TapeStopping.lean` (PL2), `NLAlibScaffold/Ops/Logic/Probabilistic.lean`
(PL0, PL1, PL3a–e; both stage PROB-LOGIC), `NLAlibScaffold/Matrix/QRIteration/Ritz.lean` (RZ1; lands in main's `Ritz.lean`),
`NLAlibScaffold/Eigensolvers/ShiftedQR/RoundedHeadline.lean` (contracts, C4p, T1). Added to
existing scaffold files: D5 (`DiskUniform`), P12a (`DeflationPerturbed`). No proved statement
changed. `lake build NLAlib NLAlibScaffold` and `check_rules` results: §14.10.

### 14.8 Batches

* **PROB-LOGIC (separate stage, first):** waves P1–P3 of its own note; must be on main before
  SQR-FP wave 7.
* **Batch 3 (general library, waves 5–6):** wave 5: D5, RZ1, P12a, P12b, FP1, GR1, RC1–RC3 and the
  batch-2 moves; wave 6: FP2, **C4cap** (before C4p).
* **Batch 4 (stage programs, waves 7–8):** wave 7: C4p, LF1, P4–P6, P14, P15; wave 8: P7–P10.
* **Batch 5 (assembly, waves 9–10):** wave 9: P10b, P11d, P11p, PAR1, PAR1p, PAR1k; wave 10:
  T1c, T1d, T2, T3, T5 (T4 optional).

### 14.9 Risks

* PL1 (run measurability) is new Ops infrastructure by induction over `Stmt` with fuel; the only
  H in the general layer. Fallback: state PL3c with measurability of the intermediate memory as a
  hypothesis and discharge it per program (costly; not recommended).
* C4p is a replay of C4a's round in PWrites form; without PL5 it repeats the per-round state
  bookkeeping (H rather than L).
* The iteration programs (P7–P10) are the bulk of the program side (Find's half-products, Exc's
  net and trials); their contracts are fixed by S1–S6, so the risk is volume, not truth.
* `uShQR` assembles many corrected constants; T2 is L only if PAR1 defines it once.
* Measurable machine operations are a new hypothesis of the headline (honest, and true for any
  rounding to a discrete format), but a reviewer should confirm it is acceptable.

### 14.10 Checks run

`lake build NLAlib NLAlibScaffold`: 5090 jobs, success. `check_rules --files` on the changed and
new files: 0 errors, 0 warnings. `scripts/stage_check.sh`: exit 0 (1351 proved modules, axiom
audit 0 violations, 14 linters 0 errors, strict replay of `NLAlib` 0 violations; the 10 new
`sorry`s are in `NLAlibScaffold` only). Decision sheet:
`~/nlalib-harness/state/decisions/SQR-FP-HEADLINE.json`; targets (batches 3–5, waves 5–10):
`~/nlalib-harness/pilot/sqr-fp-targets.json`.

### 14.11 Revision after review (Fable, `Review-Fable-SQR-FP-Headline.md`; maintainer approved)

* **B1 (positivity).** New targets PAR1p (`0 < uShQR`, `0 < shqrSmallEigAccuracy`,
  `0 < shqrSmallEigFailure` under T1c's hypotheses) and PAR1k (`2 ≤ shqrDegree B`,
  $B^{2/k} \le 2$). Without PAR1p T1c could be vacuous through $0 \le u \le$ `uShQR`, and T2's
  $\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}})$ would be junk. PAR1 also checks that every natural
  literal the inner programs store (stack counts, trial counters, $k$, $F$) is covered by the
  `IsExactNatLit` bound of T1c (stated for the maximum).
* **B2 (PL2).** Restated with Mathlib's `IsStoppingTime (IsTapeLaw.filtration h) p`,
  `p : Ω → WithTop ℕ`, conclusion on `{p ≠ ⊤}`
  (`IsTapeLaw.measure_inter_shift_mem`); `Tape.IsStoppingPos` removed. A failing run has no end
  position: `PWrites.seq` uses the stopping time "end position on success, `⊤` on failure". The
  clamp to `m.pos` on failure is not a stopping time. PL3b–e still compose: `of_window`, `ite`
  need no stopping time; `seq` uses PL2 as above (or, equivalently, the per-position
  decomposition with `IsTapeLaw.shift` and `integral_future` that the review checked);
  `whileFuel` is `seq`/`ite` by induction. See [Ops-Probabilistic-Specs](Ops-Probabilistic-Specs.md) §2.
* **B3 (class constants, end to end).** One rule: each level hands the next a class with the
  constants doubled once. Input: $\kappa(\mathbf{V}) \le B$, separation $\Gamma$. Worklist (C4p,
  P12a): blocks given to D have condition $\le 2B$, separation $\ge \Gamma/2$, norm $\le N_0$
  (total error $\le \Gamma/(16(n+1)B)$). Inside D (P12b): iterates are perturbed similarities of
  that block within $(\Gamma/2)/(16(n+1)\cdot 2B)$, so they have condition $\le 4B$, separation
  $\ge \Gamma/4$. Sh/Find/Exc/Regularize (P7–P10) are instantiated with $B' = 4B$, $\Gamma' =
  \Gamma/4$: T1c takes `k = shqrDegree (4 * B)`, and `shqrParams`/`uShQR` are written in
  $(4B, \Gamma/4)$. Cost: constants in $\log(1/\boldsymbol{u})$ only (the paper's single factor
  $2$ in $B \ge 2\kappa_V$, $\Gamma \le \mathrm{gap}/2$ becomes $4$; T2's asymptotics unchanged).
  `RandomDecouplingContract` is instantiated at $(2B, \Gamma/2)$ (as in C4p) and the iteration
  contract at $(4B, \Gamma/4)$.
* **B4 (C4cap).** Wave 6, before C4p. Planned signatures after C4cap:
  `RoundedDecouplingContract fails k F ps ω ε D I` and
  `RandomDecouplingContract law B g φ k F ps ω ε D I` (later `… k F nmax Nmax ps …`, §2.1), frame
  `[n + 1, k, ps.length, F]`, with `F`
  fixed outside the `∀`; `solveRounded D L : [N, k, np, F] …`. The skeleton's C4p (frame
  `[n + 1, k, ps.length]`) is restated in the C4cap commit, and only then dispatched. The reason
  given in §14.4 is corrected: `IExp.const` exists; `F` is runtime data so that the decoupler is
  one program.
* **T1d** added (all-tape statement; termination, footprint, backward error when `Fl = 0`).
* **Modelling choices (not paper assumptions), added to the "not claimed" list of §14.1.**
  (a) `SmallEig`'s randomness is a **fixed-length window $W$ of the uniform stream at the call
  position**, wrong only on a bad window (`PWrites.of_window`). This is stronger than Definition
  1.2's black box ("with probability $\ge 1 - \varphi$"); an oracle that draws an adaptive number
  of samples does not fit. Its measurability and tape locality are part of `IsRandomSmallEig`
  (the same for `IsPolarDiskSampler`). (b) Parameter words (Σ, B, Γ, δ, φ, ω, k, F, Exc's
  ε, thresholds) are **arbitrary reals** supplied exactly (`Machine ℝ`, `dec = id`), not
  floating-point numbers.
* **Placement.** GR1 reuses main's `squareGrid` (option (b)): separation and a filtered count in
  `Strategy.lean`, no new net. RZ1 moved to `NLAlibScaffold/Matrix/QRIteration/Ritz.lean`
  (destination main's `Ritz.lean`). PL0–PL6 are the separate stage **PROB-LOGIC** (stage note
  [Ops-Probabilistic-Specs](Ops-Probabilistic-Specs.md), targets
  `~/nlalib-harness/pilot/prob-logic-targets.json`), with a bridge PL6 to `Ops/Law`'s law-level
  shape; PL4 is stated per operation with a sum-type assembly.
* **Proving order.** PROB-LOGIC P1 (PL1, PL2, PL4) → P2 (PL3b–f, PL6) → P3 (PL5), in parallel
  with SQR-FP wave 5 (D5, RZ1, P12a, P12b, FP1, GR1, moves, RC1–RC3) and wave 6 (FP2, C4cap); then
  wave 7 (C4p, LF1, P4–P6, P14, P15) once PROB-LOGIC is on main; waves 8–10 as §14.8.

## 15. The headline statements (wave 10, phase 1: statements only)

File `NLAlibScaffold/Eigensolvers/ShiftedQR/RoundedTheorems.lean` (it imports P11p's
`RoundedDecouple` and PAR1's `RoundedPrecision`, which `RoundedHeadline` cannot). Six sorried
statements; every block they use is proved.

### 15.1 The program and its words

* `roundedShQR := solveRounded roundedDecouple smallEigLeaf`, interface
  `[N, k, np, F] (A, Thr, P) → (Out, Fl)`; dimensions `shqrDims = [n + 1, k, np, shqrCap …]`.
* `shqrParams n k B Γ Σ δ φ := roundedDecoupleParams tL R tv 0.2 (4B) (shqrAlpha k (4B))
  (shqrEps k (4B)) k (Nat.log 2 k)` with $t_L$ = `shqrLoopThreshold`, $R$ = `shqrRadius`,
  $t$ = `shqrScanThreshold`; the threshold word is `shqrDeflationThreshold`.
* P11p's mapping: $n_{\max} = n$, $N_{\max} = 2\Sigma$, $S = 4\Sigma$, $B_i = 4B$, $g = \Gamma$,
  $\varphi_{\mathrm{it}}$ = `shqrSmallEigFailure`, $\varphi_R$ = `shqrRegularizeFailure`,
  $C$ = `shqrC k (4B)`, $F$ = `shqrCap`.
* **PAR1 adjustment.** P11p needs $(1+\boldsymbol{u})^2 t \le (1-\boldsymbol{u})^2 t_L \le
  (1-\boldsymbol{u})^4\omega_D^2$; the old $\omega_D = (1+v)\omega/(1-v)$ ($v = \boldsymbol{u}_{\mathrm{ShQR}}$)
  cannot meet it (at $u = v > 0$ it needs $(1+v)^2(1-v)^2 \le (1-v)^4$). New:
  $t_L = (1+v)^2 t/(1-v)^2$ (`shqrLoopThreshold`) and $\omega_D = \sqrt{t_L}/(1-v) =
  (1+v)^2\omega/(1-v)^2$ (`shqrDecoupled`); the cut level becomes $(1+v)^3\omega/(1-v)^3 \le 2\omega$
  (`shqrCut_le`, now via $(1+v)^3 \le 2(1-v)^3$ for $v \le 1/10$), so the worklist's budget is
  unchanged. New lemma `shqrLoopThreshold_spec` (P11p's `hthr`, `hcut`). `shqrParams_spec` is
  re-proved unchanged in statement.

### 15.2 Statements

| id | Lean name | informal |
|---|---|---|
| T1c | `roundedShQR_measureReal_not_spectrum_le` | the §14.1 headline: probability $\le \varphi$ of not (footprint, `Fl = 0`, spectrum of $\mathbf{H}+\mathbf{E}$, $\|\mathbf{E}\|_2 \le \delta$) |
| T1d | `roundedShQR_terminates` | on every tape the run succeeds (`Wp .total … (fun _ => True)`); termination only (maintainer: P11d dropped, correctness is the probability statement) |
| T2 | `logb_inv_uShQR_le` | $\exists c_1, c_2$ absolute: $\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}}) \le c_1 k \log_2\frac{4(n+1)B\Sigma^2}{\delta\min(\Gamma,\Sigma)\varphi} + c_2$ |
| T3 | `roundedShQR_relative` | $0 < \Sigma$, $\|\mathbf{H}\|_2 \le \Sigma \le c\|\mathbf{H}\|_2$, $c \ge 1$, $0 < \delta \le 1$: parameters at $\delta\Sigma/c$ give $\|\mathbf{E}\|_2 \le \delta\|\mathbf{H}\|_2$ w.p. $\ge 1-\varphi$ |
| T4 | `roundedShQR_hermitian` | Hermitian Hessenberg input, gap on `hH.eigenvalues`, no $\mathbf{V}$ supplied; $B = 1$, $k$ = `shqrDegree 4` |
| T5 | `roundedShQR_work_le` | $\exists c$: `Count.size (stmtCost roundedShQR [n+1, k, np, F])` $\le c(n+1)^4(k+1)^4(n_p+1)(F+1)$ (static, so on every tape, `exec_within`) |

T1c follows §14.1's Lean text with Fable's fixes (`hI : I.IsMeasurable` with `hloc`;
`IsPolarDiskSampler sU I` and `hU`; `k = shqrDegree (4 * B)`) and the machine hypotheses of T1
(`IsScalar`, `IsIndexLit`, `IsToNat`, `IsCmp`); the memory precondition is bundled as
`ShQRInput`, the success event as `ShQRSpectrum`, the footprint as `shqrFp`. Added next to
`hse`, `hφse`: `hβse0 : 0 ≤ βse`, `hφse0 : 0 ≤ φse` (needed by LF1 and P11p; §14.1 allowed it).
`0 ≤ u` comes from `StdModel`; `1 ≤ B` from $\kappa(\mathbf{V}) \ge 1$.

### 15.3 Edge cases checked

* **Junk values.** $B \ge 1$ (from `one_le_pseudoConditionNumber`), $\Sigma \ge \delta > 0$,
  $n + 1 \ge 1$: no division by $0$ in `shqrBudget`, `shqrOmega`, `shqrRadius`; $1 - v \ge 9/10$
  in `shqrLoopThreshold`, `shqrDecoupled`, `shqrCut`; `Nat.log 2 k = q` at $k = 2^q$; Exc's
  $\varepsilon \le 1/2$ (`shqrEps_le_half`); $\sqrt{\cdot}$ of positive failures; `shqrCap ≥ 1`.
* **$n = 0$, $k$ vs $n$.** $k \ge 2$ (PAR1k), so $n + 1 \le k$ gives leaves only (the decoupler is
  never called; its contract is vacuous at $k > n$); the gap is vacuous at $n = 0$. In T2 this is
  why the argument has $\min(\Gamma, \Sigma)$: at $n = 0$, $\Gamma \to \infty$ leaves
  $\boldsymbol{u}_{\mathrm{ShQR}}$ fixed (budget $= \delta$) while $\log(1/\Gamma) \to -\infty$.
  In T3, $n = 0$ and $\mathbf{H} = 0$ satisfy T1c's hypotheses but $\|\mathbf{E}\|_2 \le 0$ asks
  for exact output, hence `hS0 : 0 < S` (which with $\Sigma \le c\|\mathbf{H}\|_2$ gives
  $\mathbf{H} \ne 0$).
* **$\varphi = 1$**: T1c, T3, T4 are then trivially true but not vacuous elsewhere; all
  failures stay positive. **$\delta = \Sigma$**: allowed (budget $\min(\Sigma,
  \Gamma/(16(n+1)B))$). **$B = 1$**: $k$ = `shqrDegree 4` = $128$ (setk at $4B$; the paper's $k = 2$
  for Hermitian inputs is not claimed in T4).
* **T2's form (counterexample to §14.1's $\log_2(nB\Sigma/(\delta\Gamma\varphi))$).** Every term
  of `uShQR` is a ratio of $\delta$, $\Gamma$, $\Sigma$ (budget/$\Sigma$, $R/\Sigma$, $\eta/\Sigma$,
  $\log(4\Sigma/\omega)$), so $(\Sigma, \delta, \Gamma) \mapsto t(\Sigma, \delta, \Gamma)$ leaves
  it fixed while $\log_2(\Sigma/(\delta\Gamma))$ drops by $\log_2 t$: false for $t$ large, any
  $c_1, c_2$. Fixed with $\Sigma^2/(\delta\Gamma)$ ($\delta$ is absolute in T1c). The factor $4$
  makes the argument $\ge 4$, so the $k\cdot$const terms fit in $c_1$. N14's $\sqrt n$ is
  $\tfrac12\log_2(n+1)$ bits inside $c_1 k\log_2(n+1)$. $c_1, c_2$ are existential before the
  $\forall$ (absolute); explicit numerals are left to the proof.
* **Quantifiers.** $k$, $F$, `shqrParams` and the tape law are fixed outside; `P.real` of the
  failure set (outer measure if not measurable, so the bound is no weaker). T1d **drops** the
  class and precision hypotheses of T1c (a strengthening, decided at proof time): it keeps only
  the machine classes (`IsScalar`, `IsIndexLit`, `IsExactNatLit (n+1)`, `IsToNat`, `IsCmp`), the
  totality of `SmallEig` and of the disk sampler, $k$ = `shqrDegree (4B)` (so $k = 2^q$) and the
  input memory; no `StdModel`, no Hessenberg input. Its route is not C4/P11d but termination-only
  lemmas: `TerminatingDecoupler`/`TerminatingLeaf` (RoundedSolveTermination),
  `solveRounded_terminates` (RoundedWorklistTermination), `roundedDecouple_terminatingDecoupler`
  (RoundedDecoupleTermination), with `multiStepStable_terminates` (StableStep) and
  `findRounded_terminates` (RoundedFind) in the programs' home files.
* **T5.** Static count (bound values, `whileFuel` fuel, `bindIdx` worst value), so it holds on
  every tape (errata N10). Estimate: $2(n+1)$ rounds, $F$ iterations, per iteration
  $O((k^3 + n_p k)(n+1)^2)$ (Find's $\le k$ levels of $\le k^2$ shifted steps, Exc's $\le n_p$
  trials of $k$ steps, Optimal's dense row product $O(n^2)$ per step); the exponents carry
  margin. `SmallEig` counts one per call (its cost is not claimed).
* **Joint satisfiability.** PAR1p: `uShQR`, `shqrSmallEigAccuracy`, `shqrSmallEigFailure` are
  positive, so $0 < \boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ exists; an exact
  `SmallEig` ($\beta = \varphi = 0$, empty bad sets) and the exact polar sampler meet their
  contracts; tape laws exist (product measure). PL4 covers only the catalog's scalar, index and
  comparison meanings: that a measurable interpretation (`I.IsMeasurable`) meets the `SmallEig`
  contract at the same time is **assumed, not exhibited** (it needs a measurable eigenvalue
  listing; `SmallEig` is an oracle, Definition 1.2). A Borel listing exists (lexicographically
  sorted roots), so the hypotheses are not contradictory, but no Lean lemma states it.

### 15.4 Gaps for the proving phase

* **P11p's `hd` is not in PAR1.** P11p feeds Sh the separation $\eta/2$ of Regularize's shifts
  and requires $\eta/2 \le \varepsilon\,c_{\mathrm{lo}}\,\omega\sqrt{\varphi_{\mathrm{it}}/(11(n+1))}/4$
  directly; PAR1's `shqrDist` is the *minimum* of the two, so `shStepHyps_of_le_uShQR` does not
  give it. It holds with a margin of about $10^5$ (numerically $\varepsilon \ge 0.2$,
  $c_{\mathrm{lo}} \ge 1.4$ under setk), but needs a lower bound on `shqrEps` (new PAR1 lemma) or
  a smaller radius $R$.
* P11p's backward error $F(1+C)S(\dots)$ is below `shqrDecoupleError` ($F(3.1+C)4\Sigma(\dots)$):
  monotone, fine. P11p's `hfuel` from `hcap` ($0.8016^F \cdot 4\Sigma < \omega$, $N_{\max} = 2\Sigma$).

### 15.5 The certificate form (audit B1, B4)

File `NLAlibScaffold/Eigensolvers/ShiftedQR/RoundedCertification.lean`. T1c and T5 are about the
same program but not the same run; the headline is restated as a canonical certificate
(`Ops.Algorithm`) and one `Accepts` bound, so cost and correctness hold on one event.

* **Program and problem.** `shqrProgram : Program ShQROp Tst 4 5` frames `roundedShQR` at
  `[d 0 + 1, d 1, d 2, d 3]` = $(n + 1, k, n_p, F)$ on five raw buffers (matrix words, threshold
  word, parameter words, output room, failure word). `shqrProblem Mch admitted`: the data are
  $\mathbf{H}$ and $B, \Gamma, \Sigma, \delta, \varphi$ with $k$ = `shqrDegree (4B)`,
  $n_p$ = `(shqrParams …).length`, $F$ = `shqrCap …`; the admitted sizes (`ShQRSizes`) have exact
  natural literals up to $n + 1$ and **$k \le n$** (B4: the regime $k > n$, a copy and one
  full-size `SmallEig` call, is excluded).
* **Model** (`shqrModel`, confined and uniform, not charged): scalar arithmetic and literals are
  the functions of the machine `Mch`; comparisons and index conversion exact; `SmallEig` meets
  the relational `randomSmallEigRel sU W Bad β` (fixed windows and bad sets, $\beta \ge 0$);
  `Ritz` the exact block function (never called); the polar sampler `polarDiskRel sU`. Realized
  by `shqrInterp` (exact eigenvalues reading and ignoring the window, exact polar sampler).
  `StdModel`, measurability, tape locality and the laws of the bad sets are hypotheses of the
  probability theorem only.
* **Costs** (`shqrResources kw ks kws`): kernels cost the caller's `kw`/`ks`/`kws` at their call
  dimensions (possibly $0$, not bounded by $1$), everything else one unit.
* **Specification** (`shqrSpecification`): budget, scratch, memory manifest (static count;
  per-kind counts are a follow-up), `good` empty (`SmallEig` is relational, so the output is not
  a function of input and tape), and
  $$\mathrm{work} = 196218(n+1)^3(k+1)^3(n_p+1)(F+1) + 8b^4\,\overline{w}_{\mathrm{kw}},\qquad
  \mathrm{span} = \text{the same with } \overline{w}_{\mathrm{ks}},$$
  $b = n + k + n_p + F + 2$ (the constant was $196017$ before the programs became wrappers of
  the `With` programs, SMALLEIG RF7), $\overline{w}$ the largest kernel weight at one dimension
  $\le b^2$ (`spectralWorkEnvelope`). The first term is the monomial bound of the instrumented
  static count (`stmtWorkMono`, kernel-checked), the second the kernel-call polynomial of the
  pruned tree (`Stmt.keepCalls`, coefficient $8$, degree $4$) times the envelope
  (`Program.exec_lift_le_add_selected`, new in `NLAlib/Ops/SelectedWork.lean`).
* **Certificate** `roundedShQRAlgorithm` (hypotheses: `admitted`, measurable `Bad`,
  $\beta \ge 0$, `ks ≤ kw`): termination from T1d through `wp_frame`, work from the run bound.
* **Headline** `roundedShQR_algorithm_measureReal_not_accepts_le`: under T1c's hypotheses, the
  probability that the counted run is not accepted (success, every resource bound, the frame
  `shqrFp`, `ShQRSpectrum` with error $\delta$) is $\le \varphi$. The bridge is
  `Algorithm.measureReal_not_accepts_le_of_wp` (new, `NLAlib/Ops/Probability.lean`): a total
  postcondition of the memory semantics of the certified program is a postcondition of the same
  counted run (`exec_mem`), so no `good` that pins the output is needed. The tape law is on the
  whole tape (`IsTapeLaw`), which covers every window the program reads.
* **CI.** `scripts/OpsPrograms.lean` imports `NLAlib` only, so a scaffold certificate is not
  inventoried. On promotion it needs the reviewed line
  `NLAlib.ShiftedQR.roundedShQRAlgorithm hyps=4 uniform=yes confined=yes charged=no
  budget=manifest scratch=manifest`.
