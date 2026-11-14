# Block Lanczos for low-rank approximation: small blocks and certified programs

2026-11-14. Design note; **status: draft for the maintainer, one independent review applied
(§10), nothing proved, no library file changed**. Branch `design/block-lanczos` from
`origin/main` @ `cbf64ea9` (PR #137). Decision sheet: harness
`state/decisions/BLOCK-LANCZOS.json` (ids BL1–BL11 below).

The maintainer asked to "begin thinking about block Lanczos methods for low-rank approximation":
the library has the Tropp–Webber and Musco–Musco analyses of ordinary RBKI; the request is to
(1) consider block sizes below the target rank, and (2) begin building programs for these methods,
with full reorthogonalization, "where we get some kinds of complete guarantees".

Label convention (as in `Krylov-LanczosReorth.md`): **known** is a published result (with
citation; "locator to verify" when the theorem number was read from an arXiv HTML rendering and
not from the published version); **planned** is a statement this note proposes to prove, with a
proof sketch; **conjectured** has no proof route yet. Sizes are S/M/L/H. Singular values are
indexed from $0$ as in the library: $\sigma_0\ge\sigma_1\ge\cdots$, the head of a rank-$r$ problem
is the indices $i<r$, and the optimal spectral error is $\sigma_r$. Throughout
$\mathbf H=\mathbf A^{\mathsf H}\mathbf A$, $\lambda_i=\sigma_i^2$, $b$ is the block size
(`Fintype.card l`) and $q$ the number of blocks, so `rbki A Ω q` uses $2qb$ products.

## Summary

* **What exists.** `rbki`, `nystromBKI` and their analyses are complete for block size
  $b\ge t+2$, $t\ge r$: gapped (Tropp–Webber), gapless in Tropp–Webber's form, gapless in
  Musco–Musco's $(1+\varepsilon)$ form, truncated and untruncated, with Nyström twins (§0). Every
  theorem assumes $t+2\le b$ or $r+2\le b$. Nothing covers $b<r$. There is no program for any
  low-rank method.
* **Small blocks need little new structure.** The deterministic filter bound
  (`SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le`) takes an arbitrary test
  matrix with an arbitrary column type, and `rbki A Ω q` is `rbki` of the *simulated block*
  $[\mathbf\Omega,\mathbf H\mathbf\Omega,\dots,\mathbf H^{s-1}\mathbf\Omega]$ at depth $q-s+1$.
  So the existing chain applies with $\mathbf\Omega$ replaced by the simulated block, and the
  block-size condition $b\ge t+2$ (which enters only through the Gaussian inverse moment
  `integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`) is replaced by a conditioning bound for a
  Krylov–Vandermonde matrix. That bound is the only new probabilistic input.
* **Single vector, explicit** (planned, §2). For $b=1$ the conditioning factor has a closed form
  (Lagrange basis polynomials on the head eigenvalues), which gives, for a Gaussian vector and
  with probability at least $1-\delta$,
  $$\|\mathbf A-\mathsf{rbki}(\mathbf A,\mathbf x,q)\|_2^2\le\sigma_r^2+
  32\,e^{-8(q-t)\sqrt\gamma}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
  \|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{\mathsf F}^2,$$
  with $\gamma$ the relative gap between $\sigma_{r-1}$ and $\sigma_t$ and $\Delta$ the smallest
  relative gap among $\lambda_0,\dots,\lambda_{t-1}$. This is Meyer–Musco–Musco's single-vector
  theorem in substance, with their depth $q=t+O((t\log(1/\Delta)+\log(n/\delta\varepsilon))/\sqrt\gamma)$,
  and the $(1+\varepsilon)$ gapless form follows from the existing case split. By monotonicity in
  the block it holds for **every** block size at the same depth, which is a complete (if
  wasteful for $1<b<t$) guarantee for all $b$ in the first stage.
* **Block-size-aware bounds** for $1<b<r$ (Meyer–Musco–Musco's $b$-th order gap; Chen, Epperly,
  Meyer, Musco and Rao's $\tilde O(k/\sqrt\varepsilon)$ for every $b$) are **known** and are a
  second stage: the deterministic interface is planned here, the probabilistic input (their
  Theorem 4.1) is an H-size formalization on its own (§2.5).
* **Program** (§3): one fixed `Ops.Program`, a *column-queue Golub–Kahan process with full
  reorthogonalization*. Every new vector is orthogonalized against **all** stored vectors of its
  side by the certified `cgs2Impl`, one column at a time; the block size only decides which
  stored vector is multiplied next. With full reorthogonalization this is block Lanczos
  bidiagonalization, it reuses the single-vector orthogonalization and its column-wise
  loss-of-orthogonality lemma unchanged, and in exact arithmetic its output factors satisfy
  $\mathbf U\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}=\mathsf{rbki}(\mathbf A,\mathbf\Omega,q)$
  for every input, including rank-deficient blocks and breakdown. Nearly dependent columns are
  deflated by a threshold test inside the fixed program (§3.5, BL11), so that for $b>1$ the
  rounded guarantees cover all returned columns and not only a prefix.
* **Guarantee ladder** (§4). G1 exact certificate plus Gaussian tape: every exact theorem,
  old and new, holds for the stored output of the same counted run (the Hutch++ pattern). G2
  rounded total execution with the executed local-error history (the `Lanczos.Reorth` pattern).
  G3 orthogonality of both bases, residual relations, and a forward
  bound for the returned factors against the projection onto the computed range. G4 a backward
  model: the computed range contains the exact block Krylov image for $\mathbf A+\mathbf E$ and a
  nearby start block. G5 the end-to-end rounded accuracy theorem. G1–G4 are planned. **G5 has a
  real obstacle**: $\mathbf E$ depends on the random start, so the exact probabilistic theorems
  cannot be applied to $\mathbf A+\mathbf E$; they have to be made uniform in $\mathbf E$ (§4.5).
  This is the research content of "complete guarantees" and is put to the maintainer as BL8.
* **First stage** proposed: 28 statements (S 10, M 15, L 3), §5; G4–G5 and the block-size-aware
  probability are later stages.

## 0. What main already has (reused, not re-derived)

| Piece | Where (`origin/main` @ `cbf64ea9`) | Used for |
|---|---|---|
| `rbki A Ω q := rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q)`, `nystromBKI`, `rsvd A Ω := rangeProjector (A * Ω) * A`; `Ω : Matrix n l 𝕜`, `l` any `Fintype` | `LowRank/Structural/BlockKrylov.lean`, `Matrix/Factorizations/SketchedLowRank.lean` | the specification of the program; the object of every bound |
| `singularValues_sub_rbki_le_of_degree_lt` (RBKI beats every filter of degree $<q$, singular value by singular value) | `LowRank/Structural/BlockKrylov.lean` | generalized in A4 |
| Deterministic filter bound: frames `Z`, `W` with `hΩ : (Ωᴴ * Z).rank = Z.rank`, residual $(\mathbf B-\mathbf B\mathbf Z\mathbf Z^{\mathsf H})\mathbf\Omega(\mathbf Z^{\mathsf H}\mathbf\Omega)^{+}$ | `LowRank/Structural/Filter.lean:187` (gauge form), `:261`, `:292` | applied at the simulated block (A5) |
| Gaussian filter bound, gapped RBKI/RSI, gapless $(1+\varepsilon)$ and Tropp–Webber forms, Nyström twins, asymptotic forms | `LowRank/Gaussian/{Filter,BlockKrylov,BlockKrylovGapless,NystromBlockKrylov}.lean` | the $b\ge t+2$ regime; transported to the program in G1 |
| Chebyshev filter `exists_rbki_filter` (private): degree $<q$, ratio $(a/c)^2\le 4e^{-8(q-1)\sqrt\gamma}$ | `LowRank/Gaussian/BlockKrylov.lean:248` | needed at degree $q-t$; made public with the degree as parameter (A8) |
| Musco–Musco case split `singularValues_zero_le_or_exists_singularGapRatio` (private) | `LowRank/Gaussian/BlockKrylovGapless.lean` | gapless single-vector form (A11) |
| `blockKrylovMatrix`, `blockKrylovSpace`, `blockKrylovSpace_le_of_range_le`, `mem_blockKrylovSpace_iff`, `blockKrylovMatrix_replicateCol`, `rank_blockKrylovMatrix_le` | `Krylov/Basic/BlockSpace.lean` | A1–A3 |
| `krylovGrade`, `rank_krylovMatrix`, `krylovMatrix_mulVec_injective_iff` | `Krylov/Basic/Grade.lean` | almost-sure rank of the single-vector simulated block |
| Gaussian small ball $\mathbb P[\lvert g\rvert\le a]\le a$ (`gaussianReal_abs_le_le`, **private**, stated on the measure) | `Probability/Distributions/GaussianLogOverlap.lean` | the head coordinates (A9); has to be made public, with a `HasLaw` form |
| `singularValues_one_sub_rangeProjector_mul_le_of_range_le` and its gauge, spectral and Frobenius forms | `Matrix/Spectral/SingularValueInequalities.lean:465`, `Matrix/Norms/Projector.lean` | monotonicity in the range (A3, G4) |
| Operation core: `Ops.Program`, `Algorithm`, `AccessModel`, `Specification`, `Algorithm.ofWp`, `Algorithm.link`, `Writes`, loop and allocation rules | `NLAlib/Ops/` | the program and its certificate |
| `OperatorOp.matvec` with `IsExactMatvec` and normwise `IsMatvec dec A delta I`; stored rectangular `StoredOperatorOp.matvec` with dense and COO lowerings | `Ops/Catalog/{Operator,StoredOperator}.lean`, `Ops/Profiles/Stored*.lean` | products with $\mathbf A$; **no adjoint operation exists** (§3.2) |
| `cgs2Impl`, `cgs2_spec`, `TwoPassOut`, `twoPassRel`: two classical passes against the stored columns, sequential dot/axpy error envelope | `Krylov/Lanczos/Reorth/TwoPass*.lean` | every orthogonalization of the program, unchanged |
| `Lanczos.Reorth.solve`, `runs_solve`, `Rounded.History`, admissible prefix `reorthSteps`, `Output.exists_run_prefix`, `Output.exists_spectral_prefix`, canonical certificates (`Reorth/Certificate.lean`, `RoundedStoredCertificate.lean`) | `Krylov/Lanczos/Reorth/` | the template for G2–G3; guarded normalization, saved raw norms, prefix selection |
| `IsOrthErr`, `frobNorm_transpose_mul_self_sub_one_le_of_columns` ($\|\mathbf V^{\mathsf T}\mathbf V-\mathbf I\|_{\mathsf F}\le\sqrt{3m}\,\mu$ from per-column bounds), `hasOrthonormalCols_polarFactor`, `frobNorm_polarFactor_sub_le`, `HasOrthonormalCols.exists_transpose_eq_mul_eq_neg` | `Matrix/Perturbation/{OrthErr,SymmetricBackward}.lean` | G3 orthogonality (verbatim), G4 backward construction |
| Rank-revealing MGS and Hutch++: Gaussian block from the tape (`HutchPlusPlus/Samples.lean`), batches of operator applications, `Algorithm.measureReal_failure_le`, `measureReal_not_accepts_le_of_hasLaw_gaussianMatrix` | `Matrix/Factorizations/MGS/`, `Estimation/Trace/HutchPlusPlus/` | the template for the Gaussian start block and the probability transfer (G1) |

Not on main: a multi-column product contract with rounding, an adjoint product, a block
orthogonalization routine, any SVD or small symmetric eigensolver *operation* with a contract
(`SpectralBisection` is a whole program; shifted QR is on `feat/ops-exact-shifted-qr`, unmerged),
Vandermonde or Krylov conditioning facts, anything on block size below rank.
`Implementation-Coverage.md:208` lists RBKI/NysBKI as P2 with "orthonormalized block iteration,
rank decisions, storage and rounded recurrence" missing; this note is that item.

## 1. Literature

Statements were read from the arXiv HTML renderings; numbering is that of the arXiv versions
(locators to verify against the published versions before any docstring cites them).

| Source | Result | Block size | Status here |
|---|---|---|---|
| Musco–Musco 2015 (arXiv 1504.05477), Thm 1, Thm 13 | $(1+\varepsilon)$ spectral, Frobenius, per-vector at $q=\Theta(\log d/\sqrt\varepsilon)$; gap-dependent form | $b\ge k$ | on main (spectral, Frobenius) |
| Tropp–Webber 2023 (arXiv 2306.12418), Thms 9.1/9.2 (Thms 14/15 in the ar5iv numbering) | gapless and gapped expectation bounds | $b\ge r+2$ | on main |
| Meyer–Musco–Musco 2024 (arXiv 2305.02535v3), Thm 1, Thm 3, Thm 6 | single vector: $t=O((k/\sqrt\varepsilon)\log(1/g_{\min})+(1/\sqrt\varepsilon)\log(n/\varepsilon\delta))$; the simulated start block $[\mathbf g,\mathbf A^2\mathbf g,\dots]$ is $(k,L)$-good with $L=cnk^3\log(n/\delta)/(\delta^2g_{\min}^{4k})$; gap-dependent form with $\ell\ge k$ | $b=1$ | **planned** in substance, §2 (own constants) |
| ibid., Def. 2, Thm 10, Thm 11 | $b$-th order gap $g_{\min,b}$; $O((b(k-b)/\sqrt\varepsilon)\log(1/g_{\min,b})+(b/\sqrt\varepsilon)\log(n/\delta\varepsilon))$ products | $1\le b\le k$ | known; stage 2 |
| Chen–Epperly–Meyer–Musco–Rao 2025 (arXiv 2508.06486v2), Thm 1.3 (informal, $\tilde O(k/\sqrt\varepsilon)$), the formal statement of §3.3, Thm 3.8, Thm 4.1 | every $b$: $bq=O((k/\sqrt\varepsilon)\log(\kappa_{k'}/\Delta_{k'})+(b/\sqrt\varepsilon)\log(n/\delta\varepsilon))$; $\sigma_{\min}([\mathbf H,\mathbf C\mathbf H,\dots,\mathbf C^{t-1}\mathbf H])\ge C\,(\delta^5/k^{15})(\Delta_k/6\kappa_k)^{6(t-1)}$ with probability $1-\delta$ | $1\le b\le k$ | known; stage 2 (H) |
| Yuan–Gu–Li 2018 (arXiv 1808.06287), Thm III.1 | singular-value bounds for $b$ above the cluster size, constant not explicit | any | not planned |
| Tropp–Webber 2023, §6.1 and the remark after Thm 15 | "it is impossible to establish any gapless error bounds in the case $k<r$" | $b<r$ | lower-bound statement A13 planned |
| Barlow–Smoktunowicz 2013; Carson–Lund–Rozložník–Thomas 2022, Table 3 | BCGSI+ (block CGS2): loss of orthogonality $O(u)$ under $O(u)\kappa(\mathbf X)<1$ | — | not used (BL7) |
| Simon–Zha 2000; Barlow 2013 | one-sided reorthogonalization in Lanczos bidiagonalization for low-rank approximation (Simon–Zha); backward-stability analysis of reorthogonalized Golub–Kahan–Lanczos (Barlow) | $b=1$ | related to G4; both from memory, **locators to verify** |
| Ruhe 1979 | band Lanczos: block Lanczos run one vector at a time | any | the queue form of §3.1; from memory, **locator to verify** |

Finite precision is open in both small-block papers. Chen et al. §5: "we believe there are many
interesting questions regarding the behavior of block Krylov subspace methods in
finite-precision arithmetic … we are optimistic that our results could transfer to that setting
with enough care"; their experiments use "block-Lanczos … that performs full reorthogonalization
at each iteration". No backward-stability theorem for block Lanczos with full
reorthogonalization or for RBKI in floating point was found.

Two source inconsistencies to keep in mind when citing: Meyer–Musco–Musco define $g_{\min}$
with denominator $\sigma_i$ in Theorem 1 and $\sigma_{i+1}$ in Theorems 3, 6, 7; Chen et al.
Theorem 4.1 prints $k^{15}$ and its use in §3.3 quotes $k^{14}$.

## 2. Small blocks in exact arithmetic

### 2.1 The simulated block (deterministic, planned, S)

For $s,q\ge0$,
$\mathcal K_{q+1}(\mathbf H,\mathbf K_{s+1}(\mathbf H,\mathbf\Omega))=\mathcal K_{s+q+1}(\mathbf H,\mathbf\Omega)$
(Chen et al. Observation 3.3, Meyer–Musco–Musco §3.1), by `mem_blockKrylovSpace_iff` or directly
from `blockKrylovSpace_succ`. Since `rsvd` depends on its test matrix only through
$\operatorname{range}(\mathbf A\mathbf\Omega)$:

```lean
theorem blockKrylovSpace_blockKrylovMatrix (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (s q : ℕ) :
    blockKrylovSpace A (blockKrylovMatrix A B (s + 1)) (q + 1) = blockKrylovSpace A B (s + q + 1)

theorem rbki_blockKrylovMatrix (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (s q : ℕ) :
    rbki A (blockKrylovMatrix (Aᴴ * A) Ω (s + 1)) (q + 1) = rbki A Ω (s + q + 1)

theorem singularValues_sub_rbki_le_of_range_le (A : Matrix m n 𝕜) {Ω : Matrix n l 𝕜}
    {Ω' : Matrix n l' 𝕜} (h : LinearMap.range Ω'.mulVecLin ≤ LinearMap.range Ω.mulVecLin)
    (q i : ℕ) : singularValues (A - rbki A Ω q) i ≤ singularValues (A - rbki A Ω' q) i

theorem singularValues_sub_rbki_le_of_degree_lt_of_add_le {R : Type*} [CommSemiring R]
    [Algebra R 𝕜] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) {q s d : ℕ} {f : R[X]}
    (hf : f.degree < d) (hsd : s + d ≤ q + 1) (i : ℕ) :
    singularValues (A - rbki A Ω q) i ≤
      singularValues (A - rsvd A (aeval (Aᴴ * A) f * blockKrylovMatrix (Aᴴ * A) Ω s)) i
```

The last one is `singularValues_sub_rbki_le_of_degree_lt` at $s=1$, $d=q$, up to the
reindexing of `Fin 1 × l`. The third gives the block monotonicity used in §2.4: a block does at
least as well as any of its sub-blocks, column combinations included, at the same depth. For
positive semidefinite $\mathbf H$, `nystromBKI` gets the same four through the Gram
correspondence already on main.

### 2.2 The single-vector starting-block factor (planned, M)

Take $b=1$, start vector $\mathbf x$, the simulated block
$\mathbf K=[\mathbf x,\mathbf H\mathbf x,\dots,\mathbf H^{t-1}\mathbf x]$, $\mathbf Z$ the frame
of the top $t$ right singular vectors, $\mathbf V_\perp$ a complementary frame, and
$g_i$ the coordinates of $\mathbf x$ in the right singular basis. Then
$\mathbf Z^{\mathsf H}\mathbf K=\operatorname{diag}(g_i)_{i<t}\,\mathbf W$ with $\mathbf W$ the
Vandermonde matrix of $\lambda_0,\dots,\lambda_{t-1}$ (Mathlib's `Matrix.vandermonde`), which is
invertible exactly when the head eigenvalues are distinct and every $g_i\ne0$, and
$$\bigl[(\mathbf V_\perp^{\mathsf H}\mathbf K)(\mathbf Z^{\mathsf H}\mathbf K)^{-1}\bigr]_{ji}
=\frac{g_j}{g_i}\,\ell_i(\lambda_j),\qquad
\ell_i(x)=\prod_{k<t,\,k\ne i}\frac{x-\lambda_k}{\lambda_i-\lambda_k},\qquad j\ge t,\ i<t,$$
because the row $(1,x,\dots,x^{t-1})$ is $\sum_i\ell_i(x)$ times the rows of $\mathbf W$
(Mathlib's `Lagrange.basis`, `Lagrange.eq_interpolate`). The residual of the filter bound at the
filter $f$ therefore has
$$\|\mathbf M\|_{\mathsf F}^2=\sum_{j\ge t}\sum_{i<t}
\sigma_j^2 f(\lambda_j)^2\,\frac{\lvert g_j\rvert^2}{\lvert g_i\rvert^2}\,\ell_i(\lambda_j)^2 .$$
With $\Delta\le(\lambda_k-\lambda_{k+1})/\lambda_k$ for $k+1<t$ and $0\le x\le\lambda_{t-1}$,
every factor of $\ell_i(x)$ is at most $1/\Delta$ (for $k<i$:
$\lvert x-\lambda_k\rvert\le\lambda_k$ and $\lambda_k-\lambda_i\ge\Delta\lambda_k$; for $k>i$:
$\lvert x-\lambda_k\rvert\le\lambda_k\le\lambda_{k-1}$ and
$\lambda_i-\lambda_k\ge\lambda_{k-1}-\lambda_k\ge\Delta\lambda_{k-1}$), so
$\lvert\ell_i(x)\rvert\le\Delta^{-(t-1)}$ and, for $\lvert f\rvert\le a$ on $[0,\lambda_t]$,
$$\|\mathbf M\|_{\mathsf F}^2\le a^2\,\Delta^{-2(t-1)}\Bigl(\sum_{i<t}\lvert g_i\rvert^{-2}\Bigr)
\|(\mathbf A-\llbracket\mathbf A\rrbracket_t)\mathbf x\|_2^2 .$$

Deterministic statement (planned, M; the frame is a hypothesis, as in the existing structural
theorems, since statements do not quantify over `eigenvectorBasis`):

```lean
theorem specNorm_sub_rbki_replicateCol_sq_le {t : ℕ} (A : Matrix m n 𝕜) (x : n → 𝕜)
    {Z : Matrix n (Fin t) 𝕜} (hZ : HasOrthonormalCols Z)
    (hAZ : Aᴴ * A * Z = Z * Matrix.diagonal fun i => ((singularValues A i ^ 2 : ℝ) : 𝕜))
    {Δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q d r : ℕ} {f : ℝ[X]} (hf : f.degree < d)
    (hd : t + d ≤ q + 1) (hr : r ≤ t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ a) :
    specNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      singularValues A r ^ 2 +
        (a / c) ^ 2 * Δ⁻¹ ^ (2 * t) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2
```

Four points about this statement, all found in review:

* `hΔ1 : Δ ≤ 1` is needed. The exponent is written $2t$ instead of $2(t-1)$ to avoid a
  truncated subtraction [V2], and at $t=1$ `hgap` is vacuous, so without `hΔ1` the factor
  $\Delta^{-2}$ could be made small and the statement would be false (take
  $\mathbf A=\operatorname{diag}(2,1)$, $t=r=q=1$, $f=1$). BL2 asks whether the sharp exponent
  $2(t-1)$ is wanted instead.
* `hpos` is needed: `hgap` also holds when $\sigma_i=\sigma_{i+1}=0$, and then the Vandermonde
  matrix is singular. The case $\operatorname{rank}\mathbf A<t$ is separate and easy (the
  Krylov space is invariant once $q$ reaches the rank, so the error is zero); planned, S.
* The tail is $(\mathbf A-\mathbf A\mathbf Z\mathbf Z^{\mathsf H})\mathbf x$ for the frame of
  the hypothesis, not `(A - truncatedSVD A t) *ᵥ x`: `hgap` gives no gap between
  $\sigma_{t-1}$ and $\sigma_t$, and when they coincide the two differ. Their Frobenius norms
  agree, which is all §2.3 uses.
* The head frame $\mathbf W$ of the structural theorem is the first $r$ columns of
  $\mathbf Z$.

The Frobenius twin has
$\|\mathbf A-\llbracket\mathbf A\rrbracket_r\|_{\mathsf F}^2$ in place of $\sigma_r^2$, and the
late-truncated twin follows from the existing reverse Eckart–Young step. A numerical check of
the identity for $\mathbf M$, of the inequality, and of the crude bound on five instances agreed
to rounding; this is a check of closed forms, not rate evidence.

### 2.3 Gaussian start vector (planned, M)

For a standard Gaussian $\mathbf x$ the coordinates $g_i$ are independent standard normals.
$\mathbb P[\min_{i<t}\lvert g_i\rvert\le\delta/2t]\le\delta/2$ by the small-ball bound and a
union bound, so $\sum_{i<t}g_i^{-2}\le4t^3/\delta^2$ off that event; and
$\mathbb E\|(\mathbf A-\llbracket\mathbf A\rrbracket_t)\mathbf x\|^2=
\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{\mathsf F}^2$, so Markov gives a factor $2/\delta$
off an event of probability $\delta/2$. With the Chebyshev filter of degree $q-t$:

```lean
theorem measureReal_lt_specNorm_sub_rbki_sq_le_of_hasLaw_gaussianVector (A : Matrix m n ℝ)
    (hx : HasLaw x (gaussianVector n) μ) {h r t q : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * t) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
        specNorm (A - rbki A (Matrix.replicateCol Unit (x ω)) q) ^ 2} ≤ δ
```

(name to be fixed against [N14], [N15] in the skeleton; no `hpos` here, the rank-deficient case
being covered separately). The error itself is at most $\|\mathbf A\|_2^2$, so its expectation
is finite; but the expectation of this *bound* is not, since $\mathbb E\,g_i^{-2}=\infty$, so
the route gives no expectation bound of the shape of the existing $b\ge t+2$ theorems. Hence
the tail form. BL3 offers the truncated-expectation form (expectation on the event
$\{\min_i\lvert g_i\rvert>\delta/t\}$, which uses the independence of head and tail coordinates
and loses only $t^3/\delta^2$) as an addition; integrating the tail against the cap
$\|\mathbf A\|_2^2$ would give a full expectation bound at a worse rate, not proposed.

**Rate.** $q\ge t+\dfrac{1}{8\sqrt\gamma}\Bigl(2t\log\dfrac1\Delta+
\log\dfrac{32\,t^3\,\|\mathbf A-\llbracket\mathbf A\rrbracket_t\|_{\mathsf F}^2}
{\delta^3\,\varepsilon\,\sigma_r^2}\Bigr)$ gives $\sigma_r^2(1+\varepsilon)$: Meyer–Musco–Musco's
Theorem 6 shape, $O((t/\sqrt\gamma)\log(1/\Delta)+(1/\sqrt\gamma)\log(n/\delta\varepsilon))$. The
gapless $(1+\varepsilon)$ form (their Theorem 1) comes from the existing Musco–Musco case split at
$t=r$, depth $r+O((r\log(1/\Delta)+\log(n/\delta\varepsilon))/\sqrt\varepsilon)$, for the truncated
output $\llbracket\mathsf{rbki}(\mathbf A,\mathbf x,q)\rrbracket_r$. Asymptotic forms follow [B5].

Almost-sure applicability: `hx` holds almost surely; `hΩ` of the structural theorem is
$\operatorname{rank}(\mathbf Z^{\mathsf H}\mathbf K)=t$, which is the Vandermonde determinant
being nonzero. If two positive head singular values coincide no $\Delta>0$ is admissible and no
bound is claimed. Some gap hypothesis is unavoidable when the coincidence is above $\sigma_r$
(A13); whether gaps among the indices in $[r,t)$ or at $\sigma_{r-1}=\sigma_r$ are needed is
not settled by A13.

### 2.4 Every block size at once (planned, S)

A column of a Gaussian $n\times b$ matrix is a Gaussian vector, and
`singularValues_sub_rbki_le_of_range_le` compares the block with that column. So the bound of
§2.3 holds verbatim for `rbki A (X ω) q` with $\mathbf X$ Gaussian $n\times b$, any $b\ge1$. In
products this costs $b$ times the single-vector count, which is the wrong dependence on $b$ for
$1<b<t$ but is a correct theorem for every block size, next to the existing $b\ge t+2$ theorems.

### 2.5 Block-size-aware bounds (stage 2; interface planned, probability known)

For general $b$ and $s$ with $sb\ge t$ the head matrix is the block Krylov–Vandermonde matrix
$\mathbf Z^{\mathsf H}\mathbf K_s=[\mathbf G,\mathbf\Lambda\mathbf G,\dots,\mathbf\Lambda^{s-1}\mathbf G]$,
$\mathbf G=\mathbf Z^{\mathsf H}\mathbf\Omega$ Gaussian $t\times b$. Three layers:

1. **Deterministic interface** (planned, M): the filter bound at the simulated block, in terms
   of $\|(\mathbf Z^{\mathsf H}\mathbf K_s)^{+}\|_2$ and the tail energy of $\mathbf K_s$, with
   $\mathbf H$ scaled by $\lambda_0$ so that the tail columns are bounded by
   $\|(\mathbf A-\llbracket\mathbf A\rrbracket_t)\mathbf\Omega\|$. Every probabilistic input plugs
   into this one theorem; §2.2 is its $b=1$ instance with the pseudoinverse computed exactly.
2. **Almost-sure rank** (planned, M): $\operatorname{rank}(\mathbf Z^{\mathsf H}\mathbf K_s)=t$
   almost surely when every head eigenvalue has multiplicity at most $b$ and $sb\ge t$ (a
   $t\times t$ minor is a nonzero polynomial in $\mathbf G$: take $\mathbf G$ with one column
   per group of a partition of the head into $b$ groups of at most $s$ distinct eigenvalues
   each). This shows where larger blocks
   help: multiplicities up to $b$ are harmless.
3. **Quantitative conditioning** (known): Meyer–Musco–Musco Theorem 10 ($b$-th order gap,
   $b(k-b)$ products) and Chen et al. Theorem 4.1 (every $b$, $\tilde O(k/\sqrt\varepsilon)$
   products, through Nie's matrix anti-concentration and Gautschi's Vandermonde bound). Both are
   H-size formalizations with no existing infrastructure; neither is needed for the programs.
   Chen et al. conjecture the $b$-th order gap suffices with $\kappa_k$ removed; open.

### 2.6 Necessity of the gap (planned, S/M)

If some head eigenvalue $\lambda=\sigma_i^2$, $i<r$, has multiplicity larger than $b$, then the
projection of $\mathcal K_q(\mathbf H,\mathbf\Omega)$ onto its eigenspace is spanned by the $b$
projected columns of $\mathbf\Omega$, for every $q$. So there is a unit eigenvector $\mathbf w$
orthogonal to $\mathcal K_q$; $\mathbf A\mathbf w$ is orthogonal to $\mathbf A\,\mathcal K_q$
(as $\langle\mathbf A\mathbf w,\mathbf A\mathbf k\rangle=\lambda\langle\mathbf w,\mathbf k\rangle$),
and $\|\mathbf A-\mathsf{rbki}(\mathbf A,\mathbf\Omega,q)\|_2\ge\|\mathbf A\mathbf w\|=\sigma_i$
for every $q$ and every $\mathbf\Omega$. This shows suboptimality only when
$\sigma_i>\sigma_r$ (for $\mathbf A=\mathbf I$ every block size is optimal), and A13 is stated
with that hypothesis. It is the content of Tropp–Webber's remark that gapless bounds are
impossible for block size below rank (quote read from the ar5iv rendering; locator to verify),
and it goes in `LowerBounds/LowRank`.

## 3. The program

### 3.1 Which process (BL4, BL5, BL7)

With full reorthogonalization the block structure does not enter the orthogonalization: each
new vector is reduced against every stored vector of its side. The block size only fixes the
order in which stored vectors are multiplied. Written as a queue over columns (band Lanczos in
the sense of Ruhe 1979, applied to Golub–Kahan bidiagonalization), with $N=qb$:

```
append(Q, k, w):                       -- one procedure, used three times (§6)
    ν₀ := ‖w‖                          -- saved raw norm
    (h, w') := cgs2(Q[0..k), w)        -- two classical passes against all k stored columns
    β := ‖w'‖
    if β ≤ τ·ν₀ then q_k := 0, β := 0 else q_k := w'/β      -- deflation test (§3.5)
    return (h, β, ν₀)

for c in 0 .. b-1:   R₀[0..c, c], R₀[c, c] := append(V, c, Ω e_c)
for i in 0 .. N-1:
    R[0..i, i],   R[i, i]   := append(U, i,   A v_i)        -- matvec
    S[0..i+b, i], S[i+b, i] := append(V, i+b, Aᴴ u_i)       -- adjoint matvec
output U (m × N), S ((N+b) × N), V₊ (n × (N+b)), R₀ (b × b), the saved raw norms
```

$\tau\ge0$ is an input word. At $\tau=0$ the test is $\beta=0$, the exact zero guard of the
rank-revealing MGS and of `Lanczos.Reorth` on main.

It uses $N$ products with $\mathbf A$ and $N$ with $\mathbf A^{\mathsf H}$, Tropp–Webber's
$m=2q$ block products. In exact arithmetic at $\tau=0$ (planned, M, P1–P3 of §5):

* $\operatorname{range}\mathbf V_{[0,jb)}=\mathcal K_j(\mathbf H,\mathbf\Omega)$ and
  $\operatorname{range}\mathbf U_{[0,jb)}=\mathbf A\,\mathcal K_j(\mathbf H,\mathbf\Omega)$, the
  nonzero columns orthonormal;
* $\mathbf U\mathbf U^{\mathsf H}=\texttt{rangeProjector}(\mathbf A\,\mathbf K_q)$ and
  $\mathbf A^{\mathsf H}\mathbf U=\mathbf V_+\mathbf S$, hence
  $$\mathbf U\,\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}=\mathsf{rbki}(\mathbf A,\mathbf\Omega,q)$$
  for **every** $\mathbf A$, $\mathbf\Omega$, $q$: dependent start columns, rank-deficient
  $\mathbf A$ and breakdown inside the run included, with the zero-column convention of the
  rank-revealing MGS on main (a zero residual stays zero);
* $\mathbf S^{\mathsf H}$ is zero outside the band $0\le\text{col}-\text{row}\le b$, and
  $\mathbf R=\mathbf S_{[0,N)}^{\mathsf H}$; for $b=1$ this is Golub–Kahan–Lanczos
  bidiagonalization.

A direct numerical run of this recurrence for $b=1,2,3,4$, a dependent start block and a
rank-deficient matrix reproduced `rbki` to $10^{-14}$; again a check of the identity only.

Why this form, against the alternatives:

* **Against block Lanczos on $\mathbf A^{\mathsf H}\mathbf A$** (Chen et al.'s Algorithm 1 is
  stated with the Krylov space of $\mathbf A\mathbf A^{\mathsf T}$, the transposed convention):
  it yields $\mathbf V$ and the block tridiagonal
  $\mathbf V^{\mathsf H}\mathbf H\mathbf V$, but `rbki` needs an orthonormal basis of
  $\mathbf A\,\mathcal K_q$ and $\mathbf U^{\mathsf H}\mathbf A$, so a second orthogonalization
  and more products, or a squared condition number. The two-sided recurrence produces both bases
  and the small factor with the same $2N$ products.
* **Against a block routine (BCGS2/BCGSI+)**: the known result needs
  $O(u)\kappa(\mathbf X)<1$ for the block being orthogonalized, and Krylov blocks lose rank
  routinely; an intra-block rank decision is then part of the contract. Column by column, the
  rank decision is one scalar test per column (§3.5), and `cgs2Impl`, `TwoPassOut` and
  `frobNorm_transpose_mul_self_sub_one_le_of_columns` apply without change. Cost: no level-3
  kernels; the model of computation does not reward them today.
* **Full coefficient columns are stored** (BL5), not only the band. In exact arithmetic the
  entries outside the band vanish; in rounded arithmetic they are the reorthogonalization
  corrections. Keeping them makes the residual relations
  $\mathbf A\bar{\mathbf V}=\bar{\mathbf U}\bar{\mathbf R}+\mathbf F_1$,
  $\mathbf A^{\mathsf H}\bar{\mathbf U}=\bar{\mathbf V}_+\bar{\mathbf S}+\mathbf F_2$ hold column by
  column from the representation clause of the two-pass contract alone, with no induction and
  no use of symmetry. `Lanczos.Reorth` discards them and bounds them by an induction that uses
  symmetry; that argument has no direct two-sided analogue. Storage $N(N+b)$ words, negligible
  against the $(m+n)N$ of the bases.

The Hermitian twin (the same queue on one basis, $\mathbf H\mathbf V=\mathbf V_+\mathbf T$,
$N$ products, block Lanczos proper, output a factored `nystromBKI`) shares the append step and
is a later stage; it needs a small solve with $\mathbf T$ for the Nyström form.

### 3.2 Objects

| Object | Kind | Home | Mathlib |
|---|---|---|---|
| `bandGolubKahanState A Ω i` (a `structure` with `U`, `V`, `R`, `S`): the exact queue recurrence with the zero-column convention | pure definition, RCLike | `Krylov/Processes/BandGolubKahan.lean` | searched: no bidiagonalization, no block Krylov process; none |
| `OperatorPairOp` with `matvec`, `rmatvec`; `IsExactMatvecPair dec A I`, `IsMatvecPair dec A δ δ' I` (normwise, for $\mathbf A$ and $\mathbf A^{\mathsf H}$) | operation signature and contracts | `Ops/Catalog/OperatorPair.lean` | none |
| stored adjoint: `StoredOperatorOp` lowering of `rmatvec` for dense (transposed traversal of the same words) and COO | profile | `Ops/Profiles/StoredDense.lean`, `StoredCOO.lean` | none |
| `appendOrth`: the `append` procedure of §3.1 | `Impl`, shared | `Krylov/Processes/AppendOrth.lean` (§6) | none |
| `BandGolubKahan.solve`: the fixed program | `Ops.Program` | `Krylov/GolubKahan/Band/Alg.lean` | none |

Shapes, to be fixed against the Ops API in the skeleton (the contracts follow
`IsExactMatvec`/`IsMatvec` in `Ops/Catalog/Operator.lean` field by field):

```lean
structure BandGolubKahanState (m n N b : ℕ) (𝕜 : Type*) where
  U : Matrix (Fin m) (Fin N) 𝕜
  V : Matrix (Fin n) (Fin (N + b)) 𝕜
  R : Matrix (Fin N) (Fin N) 𝕜
  S : Matrix (Fin (N + b)) (Fin N) 𝕜

/-- P2, stated below the LowRank layer: `rbki` is the corollary `rbki_eq_…` in LowRank. -/
theorem bandGolubKahan_U_mul_conjTranspose_mul (A : Matrix (Fin m) (Fin n) 𝕜)
    (Ω : Matrix (Fin n) (Fin b) 𝕜) (q : ℕ) :
    (bandGolubKahan A Ω q).U * (bandGolubKahan A Ω q).Sᴴ * (bandGolubKahan A Ω q).Vᴴ =
      rsvd A (blockKrylovMatrix (Aᴴ * A) Ω q)

def IsExactMatvecPair (dec : K → 𝕜) (A : Matrix (Fin m) (Fin n) 𝕜) (I : Interp Op Tst K) : Prop :=
  IsExactMatvec dec A (I.restrict OperatorPairOp.matvec) ∧
    IsExactMatvec dec Aᴴ (I.restrict OperatorPairOp.rmatvec)

def IsMatvecPair (dec : K → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (δ δ' : ℝ)
    (I : Interp Op Tst K) : Prop :=
  IsMatvec dec A δ (I.restrict OperatorPairOp.matvec) ∧
    IsMatvec dec Aᵀ δ' (I.restrict OperatorPairOp.rmatvec)
```

The raw-condition constructors are the two existing ones for one product, applied to
$\mathbf A$ and to $\mathbf A^{\mathsf H}$: an oracle pair, and stored dense or COO words with
the adjoint lowering (O2, O3). `I.restrict` stands for whatever the core uses to view one
operation of a signature; the signature of the certificate (Q2, Q3) is the Hutch++ one
(`Estimation/Trace/HutchPlusPlus/{Specification,Certification}.lean`) with three output
buffers and is written in the skeleton, not here.

A separate `OperatorPairOp` signature is proposed, not a new constructor of `OperatorOp`, so
that no existing model, profile or certificate changes (BL9). No new hypothesis predicate is
needed for the theory part: the gap is a hypothesis with a free $\Delta$ (BL2).

### 3.3 Operation model

BLAS level, as `Lanczos.Reorth`: `Blas1Op` (dot, axpy, nrm2, scal, copy), scalar comparison for
the guard, `OperatorPairOp`, sampling for the start block. Exact model over `RCLike 𝕜`
(`RCLikeBlas`); rounded model over $\mathbb R$ with `StdModel u id M` and the sequential
dot/axpy envelope, as every rounded certificate on main. Linking to scalar arithmetic and to
stored dense/COO data reuses the existing tables plus the adjoint lowering. The start block is
read from the Gaussian stream in one window of $nb$ words (the Hutch++ sample layout).

### 3.4 Output and truncation (BL6)

The program returns $(\mathbf U,\mathbf S,\mathbf V_+)$, a factored form of `rbki A Ω q` of
rank at most $N$. Every untruncated theorem applies to it. The $(1+\varepsilon)$ theorems for a
target rank $r$ are about `truncatedSVD (rbki A Ω q) r`
$=\mathbf U\llbracket\mathbf S^{\mathsf H}\rrbracket_r\mathbf V_+^{\mathsf H}$, which needs the
SVD of the $N\times(N+b)$ band matrix. Main has no SVD or small symmetric eigensolver as an
operation with a contract. The proposal is to return the untruncated factors now and add the
truncation when a small-SVD endpoint exists (the shared "QR/triangular/SVD/small-eigensolver
endpoints" item, `Implementation-Coverage.md:330`), either as a declared primitive with a
functional and an error contract or by linking a certified solver.

### 3.5 Deflation (BL11)

In rounded arithmetic an exact zero test almost never fires, and a nearly dependent column is
the normal case: a start block with close columns, or $N$ beyond the numerical rank, which is
what low-rank approximation is for. `Lanczos.Reorth` on main keeps the exact guard, never
deflates, and proves its strong results on the longest prefix passing $\tau\nu<\beta$. For
$b=1$ the first failure is the end of the useful run. For $b>1$ it is not: the other columns
of the queue are still good, and a guarantee that ends at the first failed column would cover
only a prefix of the returned factors.

So the test is part of the fixed program, with the threshold $\tau$ an input: a column with
$\beta\le\tau\nu_0$ is stored as zero and the run continues. Consequences:

* Every nonzero stored column passes the admissibility test by construction, so the
  orthogonality bound of §4.3 covers all nonzero columns of the returned factors, not a prefix.
* A deflated column leaves a residual of size at most $\tau\nu_0\le\tau\|\mathbf A\|_2$ in the
  relation it belongs to, in place of a rounding-level one. The bounds of §4.3–4.4 get a term
  $\tau\sqrt{D}\,\|\mathbf A\|_2$, $D$ the number of deflated columns; the admissible window for
  $\tau$ is the one of `RoundedSpectral` (bounded below by a multiple of the rounding level).
* A zero column has zero descendants along $i\mapsto i+b$, in exact and in rounded arithmetic
  ($\mathbf A\mathbf 0=\mathbf 0$ has $\nu_0=0$ and deflates for every $\tau\ge0$), so the block
  width shrinks without any change of the tree: no `bindIdx` on a shrinking width is needed.
* At $\tau=0$ in exact arithmetic the output is exactly `rbki` (§3.1). At $\tau>0$ in exact
  arithmetic it is `rsvd` at a subspace of the Krylov space; no exact theorem is proposed for
  that case, the rounded analysis covers it through the residual term.

The alternative is the `Lanczos.Reorth` convention (exact guard, analysis on a prefix); it
keeps the exact identity for all inputs and makes the rounded guarantee end at the first
numerical deflation.

## 4. Guarantees

### 4.1 G1: exact certificate and Gaussian tape (planned, L for the execution proof)

`Algorithm` for the exact BLAS model at $\tau=0$: for every admitted $(m,n,b,q)$, every input
and tape, the canonical run succeeds, the three output buffers decode to matrices with
$\mathbf U\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}=\mathsf{rbki}(\mathbf A,\mathbf\Omega,q)$,
$\mathbf\Omega$ the decoded tape window, scratch is released, exactly $nb$ samples are consumed,
and the counts are $N$ `matvec`, $N$ `rmatvec`, with work, span and storage bounds. Then, as
for Hutch++, `Algorithm.measureReal_failure_le` transfers any exact tail bound for `rbki` under
`HasLaw X (gaussianMatrix n l) μ` to the stored output of the same counted run. Expectation
bounds (the form of all existing RBKI theorems) transfer as integrals of the decoded output;
whether the core has an expectation transfer next to the failure-probability transfer has to be
checked in the skeleton (open item O1).

This is already a complete guarantee in the exact model for every block size: existing theorems
for $b\ge t+2$, §2.3–2.4 for the rest.

### 4.2 G2: rounded total execution (planned, L)

The `runs_solve` shape of `Lanczos.Reorth`: under `StdModel`, `IsBlas1`, normwise
`IsMatvecPair`, exact comparison and a size-only precision envelope, the run succeeds for every
input with no orthogonality, rank or nonbreakdown hypothesis, and the output carries the
executed history: for every appended column its raw vector, both passes (`TwoPassOut`), saved
raw norm, deflation test, normalization, and the decoded stored entries.

### 4.3 G3: orthogonality, residuals, forward bound (planned, M each)

With the deflation of §3.5 (BL11 a) the statements are about all nonzero stored columns, and
$D$ is the number of deflated ones; with the exact guard (BL11 b) they hold on the longest
column prefix passing the saved test and $D=0$. On each side:

* $\|\bar{\mathbf U}^{\mathsf T}\bar{\mathbf U}-\mathbf I\|_{\mathsf F}\le\sqrt{3N}\,\mu$ on the
  nonzero columns, and the same for $\bar{\mathbf V}_+$, with
  $\mu=2(2c+2(\eta+c)^2/\tau+E)$ as in `RoundedSpectral`; this is
  `frobNorm_transpose_mul_self_sub_one_le_of_columns` applied to the column sequence, with the
  same fixed-point window. In particular the number of nonzero columns is at most $m$,
  respectively $n$.
* Residual relations $\|\mathbf A\bar{\mathbf V}-\bar{\mathbf U}\bar{\mathbf R}\|_{\mathsf F}$,
  $\|\mathbf A^{\mathsf T}\bar{\mathbf U}-\bar{\mathbf V}_+\bar{\mathbf S}\|_{\mathsf F}\le
  \bigl(c'\sqrt N\,(\varepsilon_{\rm mv}+\varepsilon_2)+\tau\sqrt D\bigr)\|\mathbf A\|_2$.
* **Forward bound for the returned factors**:
  $$\|\mathbf A-\bar{\mathbf U}\bar{\mathbf S}^{\mathsf T}\bar{\mathbf V}_+^{\mathsf T}\|\le
  \|(\mathbf I-\mathbf P_{\bar{\mathbf U}})\mathbf A\|+
  \bigl(c''\sqrt N\,(\mu+\varepsilon_{\rm mv}+\varepsilon_2)+\tau\sqrt D\bigr)\|\mathbf A\|_2,$$
  $\mathbf P_{\bar{\mathbf U}}$ the orthogonal projector onto the computed range, in the spectral
  and Frobenius norms. This says the returned factors are as good as projecting $\mathbf A$ onto
  the computed left basis; it needs nothing about Krylov spaces.

The constants $c,c',c''$ are fixed by the proofs and go to `docs/constants.toml`.

### 4.4 G4: backward model (planned, L; sketch)

Restrict to the nonzero columns (a zero column has only zero descendants, so the restricted
queue has the same shape with a smaller width). Let $\mathbf Q_U$ and $\mathbf Q_{V_+}$ be the
polar factors of the computed bases (`hasOrthonormalCols_polarFactor`, distance
$\le\sqrt{3N}\mu$), and $\mathbf Q_V$ the first $N$ columns of $\mathbf Q_{V_+}$. Let $\mathbf R'$ be the band
part of $\bar{\mathbf R}$ (entries with $0\le\text{col}-\text{row}\le b$) and $\mathbf S'$ the
matrix with $\mathbf S'_{[0,N)}=\mathbf R'^{\mathsf T}$ and the last $b$ rows of $\bar{\mathbf S}$.
Both changes are $O(\sqrt N\mu\|\mathbf A\|)$ per column, $O(N\mu\|\mathbf A\|)$ in Frobenius
norm: $\bar{\mathbf R}$ and
$\bar{\mathbf S}_{[0,N)}^{\mathsf T}$ both approximate $\bar{\mathbf U}^{\mathsf T}\mathbf A\bar{\mathbf V}$,
and an entry of $\bar{\mathbf R}$ above the band is
$\bar{\mathbf u}_j^{\mathsf T}\mathbf A\bar{\mathbf v}_i=(\mathbf A^{\mathsf T}\bar{\mathbf u}_j)^{\mathsf T}\bar{\mathbf v}_i
=\sum_{k\le j+b}\bar S_{kj}\,\bar{\mathbf v}_k^{\mathsf T}\bar{\mathbf v}_i+O(\varepsilon)$ with
$i>j+b\ge k$, which is small by the near-orthogonality of $\bar{\mathbf V}_+$. This is the
"discarded coefficients are small" step of `Lanczos.Reorth`, here without induction because
both residual relations are available (BL5). Put
$\mathbf D_1=\mathbf Q_U\mathbf R'-\mathbf A\mathbf Q_V$,
$\mathbf D_2=\mathbf Q_{V_+}\mathbf S'-\mathbf A^{\mathsf T}\mathbf Q_U$. The two conditions
$\mathbf E\mathbf Q_V=\mathbf D_1$, $\mathbf E^{\mathsf T}\mathbf Q_U=\mathbf D_2$ are compatible
exactly when $\mathbf S'_{[0,N)}=\mathbf R'^{\mathsf T}$, which together with the supports
(column $i$ of $\mathbf S'$ in rows $\le i+b$, $\mathbf R'$ upper triangular) forces the band
shape chosen above, and
$\mathbf E=\mathbf D_1\mathbf Q_V^{\mathsf T}+\mathbf Q_U\mathbf D_2^{\mathsf T}(\mathbf I-\mathbf Q_V\mathbf Q_V^{\mathsf T})$
satisfies them with $\|\mathbf E\|_{\mathsf F}\le\|\mathbf D_1\|_{\mathsf F}+\|\mathbf D_2\|_{\mathsf F}=
O((N\mu+\tau\sqrt D)\|\mathbf A\|_2)$. Then $(\mathbf A+\mathbf E)\mathbf Q_V=\mathbf Q_U\mathbf R'$ and
$(\mathbf A+\mathbf E)^{\mathsf T}\mathbf Q_U=\mathbf Q_{V_+}\mathbf S'$ hold exactly, and by
induction on blocks, using only the triangular shapes,
$$\operatorname{range}\mathbf Q_U\supseteq(\mathbf A+\mathbf E)\,
\mathcal K_q\bigl((\mathbf A+\mathbf E)^{\mathsf T}(\mathbf A+\mathbf E),\tilde{\mathbf\Omega}\bigr),
\qquad\tilde{\mathbf\Omega}=\mathbf Q_{V,[0,b)}\mathbf R_0 .$$
Here $\mathbf R_0$ is the stored start-block coefficient matrix, so that
$\tilde{\mathbf\Omega}-\mathbf\Omega$ is the representation error of the start block plus the
polar correction. Only the inclusion is needed (no dimension count, so no nonbreakdown
hypothesis), and by `singularValues_one_sub_rangeProjector_mul_le_of_range_le` and Weyl
$$\sigma_i(\mathbf A-\mathbf P_{\bar{\mathbf U}}\mathbf A)\le
\sigma_i\bigl((\mathbf A+\mathbf E)-\mathsf{rbki}(\mathbf A+\mathbf E,\tilde{\mathbf\Omega},q)\bigr)+\|\mathbf E\|_2 .$$
With G3 this bounds the error of the stored factors by the exact RBKI error of a nearby matrix
and a nearby start block. Related work for $b=1$: Simon–Zha 2000 propose one-sided
reorthogonalization for low-rank approximation by Lanczos bidiagonalization; the
backward-stability analysis of reorthogonalized Golub–Kahan–Lanczos is Barlow 2013 (both from
memory, locators to verify). A block statement in this form was not found.

### 4.5 G5: end to end, and the obstacle (BL8)

$\mathbf E$ and $\tilde{\mathbf\Omega}$ are functions of the random start block. The exact
theorems are "for fixed $\mathbf A$, Gaussian $\mathbf\Omega$", so they do not apply to
$(\mathbf A+\mathbf E,\tilde{\mathbf\Omega})$. Three routes:

* **(a) Uniform deterministic bounds through a gap** (recommended to try first). The
  deterministic structural bounds hold for every pair. For $\mathbf A+\mathbf E$ they involve its
  own singular frame $\tilde{\mathbf Z}$; with a gap at the cut, Wedin's theorem gives
  $\|\sin\Theta(\mathbf Z,\tilde{\mathbf Z})\|\le\|\mathbf E\|/(\text{gap}-\|\mathbf E\|)$, and for
  large blocks $\sigma_{\min}(\tilde{\mathbf Z}^{\mathsf T}\tilde{\mathbf\Omega})$ is within
  $(\|\sin\Theta\|+\|\tilde{\mathbf\Omega}-\mathbf\Omega\|/\|\mathbf\Omega\|)\|\mathbf\Omega\|$ of
  $\sigma_{\min}(\mathbf Z^{\mathsf T}\mathbf\Omega)$. The result is a bound for all
  $\|\mathbf E\|\le e$ in terms of quantities of the original pair, which is then integrated.
  For small blocks the quantity to control is the Vandermonde factor of §2.2, not
  $\sigma_{\min}$: the hypothesis $\Delta>0$ is already present and gives stability of each
  $\lambda_i$ and of each head coordinate $g_i$, but through the absolute gap
  $\Delta\lambda_{t-1}$, so the rounded single-vector theorem would need roughly
  $u\cdot\mathrm{poly}(n,N)\cdot(\sigma_0/\sigma_{t-1})^2\ll\Delta\,\delta/t$: roundoff below the
  gap scale, with a condition number of the head. This is the natural first target. Gapless
  large-block theorems need a cut with a gap chosen by pigeonhole, or route (b). Size L–H;
  **conjectured** as stated, no worked proof.
* **(b) Perturbation of the filter**: compare $(\mathbf A+\mathbf E)f(\tilde{\mathbf H})\tilde{\mathbf\Omega}$
  with $\mathbf Af(\mathbf H)\mathbf\Omega$ directly (Musco–Musco–Sidford-style polynomial
  perturbation). No gap needed, but the Chebyshev filter is large on the head, so the admissible
  $u$ shrinks exponentially in the degree unless the argument is relative. Conjectured.
* **(c) A posteriori**: G3's forward bound plus a computable estimate of
  $\|(\mathbf I-\mathbf P_{\bar{\mathbf U}})\mathbf A\|$. A complete guarantee of a different kind
  (certifies the run, predicts nothing).

## 5. Statements of the first stage

| # | Result | Status | Size | Reuses |
|---|---|---|---|---|
| A1 | `blockKrylovSpace_blockKrylovMatrix` | planned | S | `blockKrylovSpace_succ` |
| A2 | `rbki_blockKrylovMatrix`, `nystromBKI_blockKrylovMatrix` | planned | S | A1 |
| A3 | `singularValues_sub_rbki_le_of_range_le` and gauge form | planned | S | `blockKrylovSpace_le_of_range_le`, range monotonicity |
| A4 | `singularValues_sub_rbki_le_of_degree_lt_of_add_le` | planned | S | A2, existing degree lemma |
| A5 | Krylov matrix of a diagonalized pair is `diagonal g * vandermonde λ`; Lagrange form of $(\mathbf V_\perp^{\mathsf H}\mathbf K)(\mathbf Z^{\mathsf H}\mathbf K)^{-1}$ | planned | M | `Matrix.vandermonde`, `Lagrange.basis` |
| A6 | $\lvert\ell_i(x)\rvert\le\Delta^{-(t-1)}$ on $[0,\lambda_{t-1}]$ under the relative gap | planned | S | — |
| A7 | `specNorm_sub_rbki_replicateCol_sq_le` and Frobenius, truncated twins; the case $\operatorname{rank}\mathbf A<t$ | planned | M | structural filter bound, A4–A6 |
| A8 | public Chebyshev filter with degree parameter (generalizes `exists_rbki_filter`) | planned | S | existing proof |
| A9 | Gaussian head/tail event: $\sum g_i^{-2}\le4t^3/\delta^2$, tail energy by Markov; public small-ball lemma | planned | S | small ball, rotation invariance |
| A10 | single-vector gapped tail bound (§2.3), spectral and Frobenius | planned | M | A7–A9 |
| A11 | single-vector gapless $(1+\varepsilon)$ tail bound for the truncated output | planned | M | A10, case split |
| A12 | every block size (§2.4): A10, A11 for a Gaussian block; asymptotic forms | planned | S | A3 |
| A13 | necessity: multiplicity above $b$ at some $\sigma_i>\sigma_r$ gives error $\ge\sigma_i$ for every $q$ (§2.6) | planned | M (S if the eigenspace projection lemma exists) | `blockKrylovSpace_eq_iSup_krylovSpace`, grade |
| P1 | `bandGolubKahanState`: ranges are the block Krylov spaces, nonzero columns orthonormal | planned | M | `blockKrylovSpace_succ`, MGS facts |
| P2 | $\mathbf U\mathbf U^{\mathsf H}=$ `rangeProjector (A * K_q)`; $\mathbf A^{\mathsf H}\mathbf U=\mathbf V_+\mathbf S$; $\mathbf U\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}=$ `rsvd A K_q` (in `Krylov`), `= rbki A Ω q` (corollary in `LowRank`) | planned | M | P1, `rbki_eq_rangeProjector` |
| P3 | band structure, $\mathbf R=\mathbf S^{\mathsf H}_{[0,N)}$; $b=1$ is Golub–Kahan | planned | S | P1 |
| O1–O3 | `OperatorPairOp`, exact and normwise contracts, joint realization; dense and COO adjoint lowerings | planned | S, M, M | `Operator`, `StoredOperator` |
| Q1 | `appendOrth` exact and rounded `Writes` specifications, cost and peak | planned | M | `cgs2_spec`, `Reorth.advance` proofs |
| Q2 | `BandGolubKahan.solve`: total exact `Writes` theorem, output $=$ P1 state | planned | L | Q1, loop and archive rules |
| Q3 | canonical exact certificate with counts ($N$ + $N$ products, $nb$ samples), work, span, storage | planned | M | `Algorithm.ofWp`, static manifests |
| Q4 | Gaussian tape: transfer of the existing gapped and gapless bounds and of A10–A12 to the stored output | planned | M | Hutch++ `Samples`, `Probability` |
| R1 | rounded total execution with history (G2) | planned | L | Q1 rounded, `Rounded.History` pattern |
| R2 | orthogonality of both bases on the nonzero columns (G3) | planned | M | column lemma; `reorthSteps` API under BL11 b |
| R3 | residual relations (G3) | planned | M | `TwoPassOut.norm_sub_sub_sum_le` |
| R4 | forward bound for the returned factors (G3) | planned | M | R2, R3 |
| R5 | rounded canonical certificate, scalar-linked and stored | planned | L | `RoundedStoredCertificate` pattern |

Totals: 28 rows, twins counted with their row (S 10, M 15, L 3). Later stages: G4 backward
model (L), G5 (BL8), truncation (BL6), block-size-aware probability (§2.5), Hermitian twin and
`nystromBKI` program, odd product counts.

## 6. Shared proof machinery (planned first)

* **`appendOrth`**: one procedure and one pair of specifications (exact, rounded) for "reduce
  against the first $k$ stored columns, save the raw norm, normalize with the zero guard, append
  the column and its coefficients". The program calls it three times (start block, left step,
  right step). `Lanczos.Reorth.advance` is the same step specialized to the three-term update;
  whether to restate it through `appendOrth` is not part of this stage, but the new proofs
  should be written so that it can be.
* **Column-queue archive invariant**: stored prefix of a basis buffer plus an upper-triangular
  coefficient buffer, with a source index $i\mapsto i+b$. One loop rule instance, used for both
  bases.
* **Adjoint operator**: contracts and lowerings once, for every later two-sided algorithm
  (RSVD, generalized Nyström, LSQR, GK-based SVD).
* **Two-basis backward construction** (G4): a pure `Matrix/Perturbation` lemma, the rectangular
  companion of `HasOrthonormalCols.exists_transpose_eq_mul_eq_neg`.
* **Vandermonde and Lagrange for Krylov matrices** (A5, A6): `Matrix/Structured` and
  `Krylov/Basic`, reusable for quadrature and for the stage-2 block Vandermonde.

## 6a. Consumers

| Statement or interface | Consumer |
|---|---|
| A1–A4 (simulated block, monotonicity) | A7, the stage-2 interface of §2.5, any later restarted or deflated block method |
| A5, A6 (Vandermonde, Lagrange bound) | A7; stage 2; Gauss quadrature and Krylov conditioning statements |
| A7 (deterministic single vector) | A10–A12; the uniform-in-$\mathbf E$ version of §4.5 (a) |
| A8 (public Chebyshev filter) | A10; existing gapped theorems (unchanged) |
| A10–A12 | Q4 (transport to the program); the Rates page |
| A13 | documentation of why A10 has a gap hypothesis; `LowerBounds/LowRank` |
| P1–P3 | Q2 (specification of the program), G4 (shape of the backward relation) |
| `OperatorPairOp`, adjoint lowerings | this program; RSVD, generalized Nyström, LSQR, any two-sided method |
| `appendOrth` | this program three times; the Hermitian twin; optionally `Lanczos.Reorth` |
| Q2–Q4, R1–R5 | the algorithm page for RBKI; G4–G5; the truncation stage |

## 7. Files and placement

| File | Contents | New/edit |
|---|---|---|
| `Krylov/Basic/BlockSpace.lean` | A1 | edit: statement about `blockKrylovSpace` |
| `LowRank/Structural/BlockKrylov.lean` | A2–A4 | edit: structural facts about `rbki` |
| `Matrix/Structured/Vandermonde.lean` | A5 (matrix part) | new; general matrix facts |
| `Polynomial/Interpolation/LagrangeBound.lean` | A6 | new; a scalar fact about Lagrange basis polynomials |
| `Probability/Distributions/GaussianLogOverlap.lean` | small-ball lemma made public (A9) | edit |
| `Krylov/Basic/KrylovVandermonde.lean` | A5 (Krylov matrix of a diagonalized pair) | new |
| `LowRank/Structural/SmallBlock.lean` | A7 | new |
| `LowRank/Gaussian/BlockKrylov.lean` | A8 | edit: private lemma made public and generalized |
| `LowRank/Gaussian/SmallBlock.lean` | A9–A12 | new |
| `LowerBounds/LowRank/BlockSize.lean` | A13 | new |
| `Krylov/Processes/BandGolubKahan.lean` | P1–P3, stated with `rsvd`, `rangeProjector`, `blockKrylovMatrix` (all below `LowRank`) | new |
| `Ops/Catalog/OperatorPair.lean`, `Ops/Profiles/StoredDense.lean`, `StoredCOO.lean` | O1–O3 | new; two edits |
| `Krylov/Processes/AppendOrth.lean` | Q1 | new |
| `Krylov/GolubKahan/Band/{Alg,Solve,Certification}.lean` | Q2, Q3: the program is a Krylov process, next to `Krylov/Lanczos/Reorth/` | new |
| `Krylov/GolubKahan/Band/{Rounded,RoundedOutput,RoundedCertificate}.lean`, `Krylov/FinitePrecision/BandGolubKahanRun.lean` | R1–R5 | new |
| `LowRank/BlockKrylov/{Samples,Probability}.lean` | the `rbki` corollary of P2, Q4 | new, after `Estimation/Trace/HutchPlusPlus/` |

`Krylov` cannot import `Probability` [P1] and `rbki` is a `LowRank` definition: the process,
the program and its rounded run analysis are in `Krylov` and speak of `rsvd` at the block
Krylov matrix; everything with a law or with `rbki` is in `LowRank`. `Krylov` may import `Ops`
and `Matrix`. No Mathlib deviation is introduced. Bibliography
entries to add before any docstring cites them: `MeyerMuscoMusco2024`,
`ChenEpperlyMeyerMuscoRao2025`; `Ruhe1979`, `SimonZha2000`, `Barlow2013`,
`BarlowSmoktunowicz2013`, `CarsonLundRozloznikThomas2022` only if cited.

## 8. Material

Read: the five `LowRank` block Krylov files and their private lemmas, `BlockSpace.lean`,
`Ops/README.md`, `docs/contributing/programs.md`, `Ops-Lanczos-Reorth-Rounded.md`,
`Ops-Lanczos-Rounded-Spectral.md`, `Ops-HutchPlusPlus*.md`, `Ops-Spectral-Bisection.md`,
`Krylov-LanczosReorth.md`, `Implementation-Coverage.md`; the papers of §1 in their arXiv HTML
renderings. Reused as mathematics: the simulated-block observation and the shape of the
single-vector theorems (Meyer–Musco–Musco). Not reproduced: their $(k,L)$-good interface and
the black-box use of Musco–Musco's Theorem 1 (the library's filter bound does that job with
explicit constants), their per-vector guarantee (not on main for large blocks either), the
perturbation argument for gap-free statements (their Corollaries 14, 16), Schatten-$p$ rates.
The retired routine-certificate program proofs of `Krylov-LanczosReorth.md` are not used;
`IsOrthErr` and the column lemma are, as pure mathematics.

## 9. Open questions

| id | question | options | recommendation | why |
|---|---|---|---|---|
| APPROVE | approve the scope and the first stage (§5) | **a approve** / b revise | a | — |
| BL1 | scope of the small-block theory in stage 1 | **a deterministic reduction, single vector with explicit constants, every $b$ by monotonicity; block-size-aware bounds in stage 2** / b go directly to Chen et al. Thm 4.1 / c deterministic interface only | a | (a) is elementary, reuses the filter chain, and already gives a theorem for every $b$; Thm 4.1 needs Nie's anti-concentration and has no infrastructure |
| BL2 | gap parameter and exponent | **a hypothesis with a free $\Delta\le1$ on squared singular values (Chen et al.'s $\Delta_k$), exponent $2t$** / b the same with the sharp exponent $2(t-1)$ (a natural-number subtraction in the statement; the reviewer prefers this) / c a named `minSingularGapRatio` / d Meyer–Musco–Musco's $g_{\min}$ on $\sigma$ | a | no new vocabulary, no subtraction; matches the stage-2 source; (b) gains one factor $\Delta^{-2}$ |
| BL3 | headline shape for $b=1$ | **a tail bound, failure probability $\le\delta$** / b truncated expectation only / c both | c if cheap, else a | this route bounds the error by a quantity with infinite mean, so there is no expectation bound of the existing shape; the truncated expectation is stronger than the tail and composes with Markov |
| BL4 | which process | **a two-sided column-queue Golub–Kahan, full reorthogonalization on both bases** / b block Lanczos on $\mathbf A^{\mathsf H}\mathbf A$ plus a projection step / c Hermitian block Lanczos and `nystromBKI` first | a | returns `rbki` exactly with $2qb$ products and both bases; (c) is the twin and shares the append step |
| BL5 | coefficients | **a store full coefficient columns** / b band only, corrections bounded by induction | a | residual relations without symmetry or induction; $N(N+b)$ words |
| BL6 | output | **a untruncated factors $(\mathbf U,\mathbf S,\mathbf V_+)$ now, truncation when a small-SVD endpoint exists** / b add a small-SVD primitive with a contract now / c return $(\mathbf U,\mathbf A^{\mathsf H}\mathbf U)$ | a | the untruncated theorems apply at once; the SVD endpoint is a shared item with its own design |
| BL7 | intra-block orthogonalization | **a column by column with `cgs2Impl`** / b a BCGS2 block routine with a new contract | a | reuses the certified routine and the column lemma; the rank decision is one scalar test per column (BL11) instead of a block condition |
| BL11 | deflation | **a threshold test $\beta\le\tau\nu_0$ in the fixed program, $\tau$ an input; rounded guarantees over all nonzero columns with a $\tau\sqrt D\|\mathbf A\|$ term; exact identity at $\tau=0$** / b exact zero guard only, as `Lanczos.Reorth`; rounded guarantees end at the first inadmissible column | a | for $b>1$ one nearly dependent column would otherwise void the guarantee for everything after it; the cost is that the rounded output is no longer analyzed as a prefix of one fixed process |
| BL8 | route to the rounded end-to-end theorem | **a backward model (G4) then gap-based uniform bounds, single vector first** / b filter perturbation / c a posteriori only / d stop at G4 for now | a, as a research branch | $\mathbf E$ depends on the start block; (a) uses the gap the small-block theorems already assume |
| BL9 | adjoint product | **a new `OperatorPairOp` signature** / b add `rmatvec` to `OperatorOp` | a | no existing model or certificate changes |
| BL10 | scalars | **a exact program over `RCLike`, rounded analysis over $\mathbb R$** / b real only | a | as every rounded certificate on main |

Open items for the skeleton, not decisions: (O1) whether the core has an expectation transfer
for tape laws or only `measureReal_failure_le`; (O2) the admitted dimensions ($q\ge1$, $b\ge1$,
$N+b\le n$ or not: the zero-column convention makes $N>\operatorname{rank}$ harmless in the
exact certificate, and in the rounded analysis the nonzero columns number at most $m$ and $n$
by near-orthogonality, so no bound is proposed); (O3) exact names against [N13]–[N15].

## 10. Review record

One independent review of the first draft, 2026-11-14 (a fresh agent given the note and the
library, not the author's reasoning). It re-derived §2.1–§2.4, §3.1 and §4.4 and checked the
attributions against the arXiv renderings and the cited identifiers against the worktree.
Findings applied:

* two false statements: the single-vector theorems at $t=1$ without $\Delta\le1$ (now `hΔ1`),
  and "the expectation of the error does not exist" (it is the bound whose mean is infinite);
* A13 shows necessity only for a coincidence above $\sigma_r$ (restated);
* the single-vector statement needed positive head singular values and the tail of its own
  frame (`hpos`, `A - A * Z * Zᴴ`);
* numerical deflation was not designed (new §3.5, BL11; §4.3–4.4 restated);
* placement: the program and P2 moved to `Krylov`, A6 to `Polynomial`;
* missing shapes for the program half and the Consumers table (§3.2, §6a);
* corrections to the backward-model sketch (definition of $\mathbf Q_V$, $\mathbf R_0$ stored,
  the Frobenius order), to §4.5 (a) (condition number of the head), to three attributions and
  to four library facts (`Lagrange.eq_interpolate`, the private small-ball lemma, a name that
  no longer exists, the positive-semidefinite hypothesis of the Nyström twins).

Not re-reviewed after these changes: §3.5 and the $\tau\sqrt D$ terms are new text and have had
no independent check. The reviewer could not run numerics and could not confirm the
Tropp–Webber quotation; line-number locators in §0 were not checked.
