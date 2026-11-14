# Block Lanczos for low-rank approximation: small blocks and certified programs

2026-11-14. Design note; **status: approved by the maintainer with two changes (§9, §10):
sharp statements with clean corollaries, and orthogonalization as an abstract contract with a
concrete scheme substituted. Two independent reviews applied (first draft; then the contract
of §3.1a). Nothing proved; the Lean skeleton is in progress on this branch.** Branch
`design/block-lanczos` from `origin/main` @ `cbf64ea9` (PR #137). Decision sheet: harness
`state/decisions/BLOCK-LANCZOS.json` (ids BL1–BL12 below, all decided).

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
* **Program** (§3): one fixed `Ops.Program`, *block Golub–Kahan bidiagonalization with full
  reorthogonalization*, written against an **abstract orthogonalization operation**: extend
  the stored basis of one side by a block, with a contract in three parameters
  $(\eta_0,\mu,\varepsilon)$ (§3.1a). Every driver theorem depends on the scheme only through
  the contract. In exact arithmetic, for every scheme meeting the exact contract, the output
  factors satisfy
  $\mathbf U\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}=\mathsf{rbki}(\mathbf A,\mathbf\Omega,q)$
  for every input, including rank-deficient blocks and breakdown. The first concrete scheme,
  substituted by linking, is column-wise CGS2 (the certified `cgs2Impl`) with a threshold
  deflation test (§3.5); the rank decision belongs to the scheme, so the rounded guarantees
  cover all returned columns and not only a prefix.
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
* **First stage**: 32 statements (S 12, M 17, L 3), §5, the contract and its generic
  consequences first; G4–G5 and the block-size-aware
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
    {Δ : ℝ} (hΔ : 0 < Δ) (hpos : ∀ i < t, 0 < singularValues A i)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2)
    (hx : ∀ i, (Zᴴ *ᵥ x) i ≠ 0) {q d r : ℕ} {f : ℝ[X]} (hf : f.degree < d)
    (hd : t + d ≤ q + 1) (hr : r ≤ t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|)
    (htail : ∀ y ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval y| ≤ a) :
    specNorm (A - rbki A (Matrix.replicateCol Unit x) q) ^ 2 ≤
      singularValues A r ^ 2 +
        (a / c) ^ 2 * Δ⁻¹ ^ (2 * (t - 1)) * (∑ i, ‖(Zᴴ *ᵥ x) i‖⁻¹ ^ 2) *
          ‖WithLp.toLp 2 ((A - A * Z * Zᴴ) *ᵥ x)‖ ^ 2
```

**Decided (maintainer, 2026-11-14): the mathematical statements may be messy; clean
corollaries are stated on top.** So this theorem and those of §2.3 carry the sharp factors,
and the readable forms (the rate of §2.3, the asymptotic forms, a version with
$\Delta^{-2t}$ and rounded constants) are separate corollaries (A12).

Four points about this statement, all found in review:

* The exponent is the sharp $2(t-1)$ (BL2 b). A draft with $2t$ and no further hypothesis was
  false at $t=1$, where `hgap` is vacuous (take $\mathbf A=\operatorname{diag}(2,1)$,
  $t=r=q=1$, $f=1$); any corollary with the exponent $2t$ needs $\Delta\le1$. The subtraction
  is harmless: $t=0$ forces $r=0$ and an empty sum.
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
    (hq : t ≤ q) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t → singularValues A (i + 1) ^ 2 ≤ (1 - Δ) * singularValues A i ^ 2) :
    μ.real {ω | singularValues A r ^ 2 +
        32 * Real.exp (-8 * ((q : ℝ) - t) * Real.sqrt (singularGapRatio A h t)) *
          Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) * frobNorm (A - truncatedSVD A t) ^ 2 <
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

**Rate.** $q\ge t+\dfrac{1}{8\sqrt\gamma}\Bigl(2(t-1)\log\dfrac1\Delta+
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

**Decided (maintainer, 2026-11-14): the orthogonalization is an abstraction.** The driver is
written against one operation, *extend a stored basis by a block*, with a contract (§3.1a). It
knows nothing about how the extension is computed. A concrete scheme is proved against the
contract and substituted by linking; column-wise CGS2 with threshold deflation is the first
instance (§3.5), and a block routine (BCGS2, Householder) is a later instance of the same
contract. With $N=qb$:

```
V₀, R₀ := extend(∅, Ω)                       -- start block
for j in 0 .. q-1:
    U_j, R[·, j]     := extend(U_{<j},   A V_j)       -- b products with A
    V_{j+1}, S[·, j] := extend(V_{≤j},   Aᴴ U_j)      -- b products with Aᴴ
output U (m × N), S ((N+b) × N), V₊ (n × (N+b)), R₀ (b × b)
```

`extend(Q, W)` returns the new block $\mathbf Q'$ and the coefficients of $\mathbf W$ against
the old and the new columns (stacked into one block column of $\mathbf R$ or $\mathbf S$).
Full reorthogonalization is the fact that $\mathbf Q$ is *all* stored columns of that side.
This is block Lanczos bidiagonalization; when the scheme works column by column it is the band
form of Ruhe 1979 applied to Golub–Kahan.

It uses $N$ products with $\mathbf A$ and $N$ with $\mathbf A^{\mathsf H}$, Tropp–Webber's
$m=2q$ block products. For every scheme meeting the **exact** contract (planned, M, P1–P3 of
§5):

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

A direct numerical run of this recurrence with column-wise two-pass Gram–Schmidt as the scheme,
for $b=1,2,3,4$, a dependent start block and a rank-deficient matrix, reproduced `rbki` to
$10^{-14}$; again a check of the identity only.

### 3.1a The orthogonalization contract

Two pure predicates on matrices, in `Matrix/Perturbation` next to `IsOrthErr`, and one
operation whose contract is the decoded predicate. The exact one fixes what the scheme
computes up to the freedom every scheme has; the rounded one is the guarantee every stability
theorem of §4 consumes, through its three parameters only. The definitions below are the
second version, after an independent review of the first (§10); they are still unchecked by
Lean until the skeleton compiles.

**Zero columns.** A basis with deflated columns is not near orthonormal as a matrix, so
"orthonormal on the nonzero columns" is expressed without subtypes or reindexing by the
*Gram defect on the support*:

```lean
/-- 0/1 indicator of the nonzero columns. -/
noncomputable def colSupport (Q : Matrix m ι 𝕜) (j : ι) : 𝕜 := if Q.col j = 0 then 0 else 1

/-- `Qᴴ Q - diag(colSupport Q)`: zero iff the nonzero columns are orthonormal. -/
noncomputable def gramDefect (Q : Matrix m ι 𝕜) : Matrix ι ι 𝕜 :=
  Qᴴ * Q - Matrix.diagonal (colSupport Q)
```

Its Frobenius and spectral norms are those of $\mathbf G-\mathbf I$ on the kept columns. One
bridge lemma (compress to the kept columns) connects it to `IsOrthErr`, to the polar factor of
§4.4 and to "the number of kept columns is at most $n$".

```lean
/-- Exact extension of a basis `Q` by a block `W`. -/
structure IsBasisExtension (Q : Matrix (Fin n) (Fin k) 𝕜) (W Q' : Matrix (Fin n) (Fin b) 𝕜)
    (H : Matrix (Fin k) (Fin b) 𝕜) (R : Matrix (Fin b) (Fin b) 𝕜) : Prop where
  repr : W = Q * H + Q' * R
  upper : R.BlockTriangular id
  span : ∃ (M : Matrix (Fin k) (Fin b) 𝕜) (T : Matrix (Fin b) (Fin b) 𝕜), Q' = Q * M + W * T
  zero_col : ∀ c, W.col c = 0 → Q'.col c = 0
  coef_zero_left : ∀ j, Q.col j = 0 → H j = 0
  coef_zero_right : ∀ c, Q'.col c = 0 → R c = 0
  orth : gramDefect Q = 0 → gramDefect (Matrix.fromCols Q Q') = 0

/-- Antecedent of the rounded contract: the basis, extended by `b` more columns each
contributing at most `3 μ²`, stays within `η₀`. -/
def ExtensionWindow (η₀ μ : ℝ) (b : ℕ) (Q : Matrix (Fin n) (Fin k) ℝ) : Prop :=
  Real.sqrt (frobNorm (gramDefect Q) ^ 2 + 3 * b * μ ^ 2) ≤ η₀

/-- Rounded extension with parameters `(η₀, μ, ε)`. -/
structure IsBasisExtensionErr (η₀ μ ε : ℝ) (Q : Matrix (Fin n) (Fin k) ℝ)
    (W Q' : Matrix (Fin n) (Fin b) ℝ) (H : Matrix (Fin k) (Fin b) ℝ)
    (R : Matrix (Fin b) (Fin b) ℝ) : Prop where
  upper : R.BlockTriangular id
  zero_col : ∀ c, W.col c = 0 → Q'.col c = 0
  residual : ExtensionWindow η₀ μ b Q → frobNorm (W - Q * H - Q' * R) ≤ ε * frobNorm W
  column : ExtensionWindow η₀ μ b Q → ∀ c, Q'.col c = 0 ∨
    (|‖WithLp.toLp 2 (Q'.col c)‖ ^ 2 - 1| ≤ μ ∧
      ‖WithLp.toLp 2 (Qᵀ *ᵥ Q'.col c)‖ ^ 2 +
        ∑ c' ∈ Finset.Iio c, (Q'.col c' ⬝ᵥ Q'.col c) ^ 2 ≤ μ ^ 2)
```

Why each clause is there (the first version lacked several; each omission made a claim of
this note false):

* **`span`** (the range is not enlarged): without it $\mathbf W=\mathbf 0$ with an arbitrary
  orthonormal $\mathbf Q'$ would pass. The other inclusion follows from `repr`. Together they
  give the Krylov ranges of P1 for any scheme.
* **`orth` is conditional** on the old basis being orthonormal on its support: two classical
  passes give $\mathbf Q'\perp\mathbf Q$ only then, so an unconditional clause could not be
  proved by the instance. The driver supplies the antecedent by induction.
* **`zero_col`**: a zero input column gives a zero output column. The contract does not imply
  it otherwise ($\mathbf W=[\mathbf 0,\mathbf w]$, $\mathbf Q'=[\mathbf w/\|\mathbf w\|,\mathbf 0]$
  meets every other clause), and §4.4 needs it: a zero basis column has only zero descendants,
  so deleting zero columns keeps the triangular shape.
* **`coef_zero_left`, `coef_zero_right`**: coefficient rows at zero columns are zero. `repr`
  leaves them free, and then $\mathbf S=\mathbf V_+^{\mathsf H}\mathbf A^{\mathsf H}\mathbf U$,
  the band structure and $\mathbf R=\mathbf S^{\mathsf H}_{[0,N)}$ can fail. (The identity
  $\mathbf U\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}=\mathsf{rsvd}$ does not need them.)
* **Both rounded clauses carry the antecedent**, as both clauses of `IsOrthErr` on main do:
  the representation bound of two passes and the normalization term use the near-orthonormal
  basis. Execution (G2) is unaffected, since the antecedent is inside the predicate.
* **The window covers the columns added inside the block.** Column $c$ is reduced against
  $[\mathbf Q,\mathbf Q'_{<c}]$, so a hypothesis on $\mathbf Q$ alone would make $\mu$ depend
  on itself. With `ExtensionWindow` every intermediate basis has spectral defect at most
  $\eta_0$, the single-vector `IsOrthErr` applies at $\eta_0$, $\mu$ is a function of a free
  $\eta_0$, and the window of the whole run is $\sqrt{3(N+b)}\,\mu\le\eta_0$. There is no
  circularity; it is a joint smallness condition (roughly $\tau\gtrsim N(c+E)$ for CGS2).
* **The column clause is absolute** ($\mu$, not
  $\varepsilon_1+\varepsilon_3\|\mathbf w\|/\|\mathbf w'\|$): the scheme owns the rank decision,
  so it can promise $\mu$ for every column it keeps. This is what lets the guarantees cover
  all returned columns for $b>1$.
* **Composition** (E2) is an exact block identity,
  $\|\mathrm{gd}[\mathbf Q,\mathbf Q']\|_{\mathsf F}^2=\|\mathrm{gd}\,\mathbf Q\|_{\mathsf F}^2+
  2\|\mathbf Q^{\mathsf T}\mathbf Q'\|_{\mathsf F}^2+\|\mathrm{gd}\,\mathbf Q'\|_{\mathsf F}^2$,
  plus the column clause: each step adds at most $3b\mu^2$, so
  $\|\mathrm{gd}\,\mathbf V\|_{\mathsf F}\le\sqrt{3N}\,\mu$. It replaces
  `frobNorm_transpose_mul_self_sub_one_le_of_columns`, which needs every column nonzero and
  does not apply here.
* The exact contract implies the rounded one at $(0,0,0)$ only.

Statements planned for `Matrix/Perturbation/BasisExtension.lean` (E1, E2):
`IsBasisExtension.range_eq`, `IsBasisExtension.coef_eq` ($\mathbf H=\mathbf Q^{\mathsf H}\mathbf W$,
$\mathbf R=\mathbf Q'^{\mathsf H}\mathbf W$ under `gramDefect Q = 0`),
`mul_conjTranspose_eq_rangeProjector_of_gramDefect_eq_zero`, `IsBasisExtensionErr.mono`,
`IsBasisExtension.isBasisExtensionErr`, `frobNorm_gramDefect_fromCols_sq`,
`IsBasisExtensionErr.frobNorm_gramDefect_fromCols_sq_le`, `frobNorm_gramDefect_le_of_blocks`,
`specNorm_gramDefect_le_frobNorm`, the compression bridge
`specNorm_submatrix_transpose_mul_self_sub_one_le_gramDefect`, and
`card_filter_col_ne_zero_le`.

The operation and how a scheme is substituted, in the core's existing mechanism (compare
`passRel`, `twoPassRel`, `cgs2_spec` in `Krylov/Lanczos/Reorth/`):

```lean
inductive OrthOp where
  | extend
  -- dims [n, k, b]
  -- ins  [Q (k·n words), W (b·n)]
  -- outs [Q' at (Q.buffer, Q.offset + k·n), W (clobbered), C = [H; R] column-major ((k+b)·b)]

/-- The contract: the decoded blocks satisfy the rounded extension guarantee. -/
def extendRel (dec : K → ℝ) (η₀ μ ε : ℝ) (ok : ℕ → ℕ → ℕ → Prop) : BlockRel K

/-- The exact contract, same operands. -/
def exactExtendRel (dec : K → 𝕜) : BlockRel K

-- every driver theorem takes the contract as a hypothesis on the interpretation:
--   (hO : I.Meets .total (Has.inj OrthOp.extend) ((extendRel dec η₀ μ ε ok).spec ExtendOperands))
-- a scheme is an implementation proved against it:
--   (cgs2ExtendImpl τ).Triple I .total ((extendRel dec η₀ (cgs2Mu …) (cgs2Eps … τ) ok).spec ExtendOperands)
-- and the concrete certified algorithm is `Algorithm.link` with the table sending
-- `OrthOp.extend` to `.inl (cgs2ExtendImpl τ)` and every other operation to `.inr`.
```

Points fixed by the review of the mechanics:

* The new block is written **directly after the stored basis in the same buffer**, so that
  the columns a later column is reduced against form one contiguous block, as `passRel`
  requires; no copy. $\mathbf S$ and $\mathbf R$ are stored packed by block column so that
  $\mathbf C$ is written in place. Whether the admission can express
  "$\mathbf Q'$ starts at $\mathbf Q$'s end in the same buffer" under the frame rules, and
  zero-length blocks at $k=0$, are to be checked first in the skeleton (open item O4).
* $(\eta_0,\mu,\varepsilon)$ are real constants; `ok n k b` bounds the dimensions for which the
  scheme promises them. One $\eta_0$ serves all $k$.
* A relational exact contract suffices for the certificate and for the probability transfer:
  `Specification.good` is a predicate on the final memory, and
  $\mathbf U\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}$ does not depend on the scheme. An
  expectation transfer is available for that product only; the individual factors are not
  measurable functions of the tape under a relational contract.
* The abstract `AccessModel` needs a joint realization, that is at least one scheme: it comes
  from the realized exact BLAS model through `Interp.link_meets` and the exact CGS2 triple (E4),
  which therefore must prove the unconditional clauses for an arbitrary $\mathbf Q$.
* The test signature is fixed across a link, so the abstract driver's signature already
  contains the comparison test the instance uses.

Why the remaining choices, against the alternatives:

* **Against block Lanczos on $\mathbf A^{\mathsf H}\mathbf A$** (Chen et al.'s Algorithm 1 is
  stated with the Krylov space of $\mathbf A\mathbf A^{\mathsf T}$, the transposed convention):
  it yields $\mathbf V$ and the block tridiagonal
  $\mathbf V^{\mathsf H}\mathbf H\mathbf V$, but `rbki` needs an orthonormal basis of
  $\mathbf A\,\mathcal K_q$ and $\mathbf U^{\mathsf H}\mathbf A$, so a second orthogonalization
  and more products, or a squared condition number. The two-sided recurrence produces both bases
  and the small factor with the same $2N$ products.
* **First instance column-wise CGS2, not a block routine (BCGS2/BCGSI+)**: the known block
  result needs $O(u)\kappa(\mathbf X)<1$ for the block being orthogonalized, and Krylov blocks
  lose rank routinely, so a block instance needs its own rank-revealing step before it can meet
  the contract. Column by column, the rank decision is one scalar test per column (§3.5), and
  `cgs2Impl`, `TwoPassOut` and the `IsOrthErr` facts of
  `Matrix/FinitePrecision/ClassicalGramSchmidt.lean` are reused. With the contract in place a
  block instance is an addition, not a redesign.
* **Full coefficient columns are stored** (BL5), not only the band. In exact arithmetic the
  entries outside the band vanish; in rounded arithmetic they are the reorthogonalization
  corrections. Keeping them makes the residual relations
  $\mathbf A\bar{\mathbf V}=\bar{\mathbf U}\bar{\mathbf R}+\mathbf F_1$,
  $\mathbf A^{\mathsf H}\bar{\mathbf U}=\bar{\mathbf V}_+\bar{\mathbf S}+\mathbf F_2$ hold column by
  column from the residual clause of the contract alone, with no induction and no use of
  symmetry. `Lanczos.Reorth` discards them and bounds them by an induction that uses
  symmetry; that argument has no direct two-sided analogue. Storage $N(N+b)$ words, negligible
  against the $(m+n)N$ of the bases.

The Hermitian twin (the same queue on one basis, $\mathbf H\mathbf V=\mathbf V_+\mathbf T$,
$N$ products, block Lanczos proper, output a factored `nystromBKI`) uses the same orthogonalization contract and
is a later stage; it needs a small solve with $\mathbf T$ for the Nyström form.

### 3.2 Objects

| Object | Kind | Home | Mathlib |
|---|---|---|---|
| `bandGolubKahanState A Ω i` (a `structure` with `U`, `V`, `R`, `S`): the exact queue recurrence with the zero-column convention | pure definition, RCLike | `Krylov/Processes/BandGolubKahan.lean` | searched: no bidiagonalization, no block Krylov process; none |
| `OperatorPairOp` with `matvec`, `rmatvec`; `IsExactMatvecPair dec A I`, `IsMatvecPair dec A δ δ' I` (normwise, for $\mathbf A$ and $\mathbf A^{\mathsf H}$) | operation signature and contracts | `Ops/Catalog/OperatorPair.lean` | none |
| stored adjoint: `StoredOperatorOp` lowering of `rmatvec` for dense (transposed traversal of the same words) and COO | profile | `Ops/Profiles/StoredDense.lean`, `StoredCOO.lean` | none |
| `IsBasisExtension`, `IsBasisExtensionErr` (§3.1a) | pure predicates | `Matrix/Perturbation/BasisExtension.lean` | none; `IsOrthErr` is the single-vector, caller-admissibility relative |
| `OrthOp.extend`, `extendRel`, `exactExtendRel` | operation and contracts | `Ops/Catalog/Orth.lean` | none |
| `cgs2ExtendImpl τ`: column-wise `cgs2Impl`, saved raw norm, threshold test, normalization (§3.5) | `Impl`, the first instance | `Matrix/Factorizations/CGS2/Extend.lean` | none |
| `BandGolubKahan.solve`: the fixed program over `OrthOp`, `OperatorPairOp`, sampling | `Ops.Program` | `Krylov/GolubKahan/Band/Alg.lean` | none |

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

The driver's signature is `OrthOp`, `OperatorPairOp`, block copy and sampling: no arithmetic of
its own. The CGS2 instance lowers `OrthOp.extend` to the BLAS level of `Lanczos.Reorth`
(`Blas1Op`: dot, axpy, nrm2, scal, copy; scalar comparison for the test). Exact model over
`RCLike 𝕜` (`RCLikeBlas`); rounded model over $\mathbb R$ with `StdModel u id M` and the
sequential dot/axpy envelope, as every rounded certificate on main. Further linking to scalar
arithmetic and to stored dense/COO data reuses the existing tables plus the adjoint lowering. The start block is
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

### 3.5 The first instance: column-wise CGS2 with threshold deflation (BL11)

```
cgs2Extend τ (Q, W):                   -- for each column c of W, in order
    ν₀ := ‖w_c‖                        -- saved raw norm
    (h₁, w₁) := cgsPass([Q, Q'_{<c}], w_c)     -- one contiguous stored block of k + c columns
    (h₂, w') := cgsPass([Q, Q'_{<c}], w₁)
    h := h₁ + h₂                       -- k + c scalar additions; first k entries to H, last c to R
    β := ‖w'‖
    if β ≤ τ·ν₀ then q'_c := 0, R[c, c] := 0 else q'_c := w'/β, R[c, c] := β
```

It is built from two `cgsPass` calls, not from `cgs2Impl`: `cgs2Impl` on main overwrites and
releases its coefficient buffer (`TwoPassOut` keeps $h_1,h_2$ only as witnesses), while the
contract returns the coefficients. `passRel` already outputs them, and
`isOrthErr_of_two_passes` has the hypothesis for the rounded sum. The two blocks $\mathbf Q$
and $\mathbf Q'_{<c}$ must be swept as one basis; sweeping them one after the other is not
CGS2 and puts a first-order $\eta_0$ term into the orthogonality. $\tau$ is a rational literal
of the implementation (`ScalarOp.lit`), not a run-time word.

In rounded arithmetic an exact zero test almost never fires, and a nearly dependent column is
the normal case: a start block with close columns, or $N$ beyond the numerical rank, which is
what low-rank approximation is for. `Lanczos.Reorth` on main keeps the exact guard, never
deflates, and proves its strong results on the longest prefix passing $\tau\nu<\beta$. For
$b=1$ the first failure is the end of the useful run. For $b>1$ it is not, and a guarantee
that ends at the first failed column would cover only a prefix of the returned factors. Hence
the threshold test, inside the scheme, with $\tau\ge0$ a parameter of the instance.

What the instance proves (E3, E4 of §5):

* **Rounded contract** with $\mu=2(2c+4(\eta_0+c)^2/\tau+E)$ and
  $\varepsilon=3c+2E+2\tau$ (sketch values, to be fixed by the proof), $c$ the one-pass
  coefficient and $E$ the normalization envelope of `RoundedSpectral`, under
  $\eta_0,c\le1/100$, $0<\tau\le1$, $4u\le c$. Every kept column passes the admissibility test
  by construction, which turns `IsOrthErr`'s relative clause into the absolute $\mu$; this
  step is proved on main as `LanczosReorthRun.norm_transpose_mulVec_v_le`, inside the run
  structure, and is extracted as a standalone lemma on `IsOrthErr`. The executed test compares
  the rounded product of the literal $\tau$ with the computed norm, which costs the factors 2
  against the first draft's constants. A kept column has residual
  $\|\mathbf f\|+\|\boldsymbol\delta\|\le3c\|\mathbf w\|+E\|\mathbf w'\|$; a dropped one has
  residual $\mathbf f+\mathbf w'$ with $\|\mathbf w'\|\lesssim\tau\|\mathbf w\|$. Per-column
  bounds give the Frobenius form. The pure part is `IsOrthErr` at the CGS2 constants, already
  on main (`Matrix/FinitePrecision/ClassicalGramSchmidt.lean`).
* **Exact contract** at $\tau=0$ in the exact model: the test is $\beta=0$, the zero guard of
  the rank-revealing MGS on main, and the output is `IsBasisExtension`.

A zero column of $\mathbf V$ gives a zero product, which the `zero_col` clause of the contract
maps to a zero column, so the effective block width shrinks without any change of the tree (no `bindIdx` on a shrinking
width). At $\tau>0$ in exact arithmetic the output is `rsvd` at a subspace of the Krylov
space; no exact theorem is proposed for that case, the rounded analysis covers it through
$\varepsilon$.

## 4. Guarantees

### 4.1 G1: exact certificate and Gaussian tape (planned, L for the execution proof)

First for the abstract driver: under the exact contract for `OrthOp.extend` and the exact
operator pair, then linked with the CGS2 instance at $\tau=0$ into an `Algorithm` for the exact
BLAS model. For every admitted $(m,n,b,q)$, every input and tape, the canonical run succeeds, the three output buffers decode to matrices with
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

For the abstract driver: under the rounded contract `extendRel dec η₀ μ ε` and normwise
`IsMatvecPair` with allowance $\varepsilon_{\rm mv}$, the run succeeds for every input with no
orthogonality, rank or nonbreakdown hypothesis, and the output carries the executed history:
for every block step the decoded product block and the extension relation
`IsBasisExtensionErr` between the stored blocks. The driver does no arithmetic, so this proof
is storage bookkeeping only. Linked with the CGS2 instance it gives the `runs_solve` shape of
`Lanczos.Reorth` under `StdModel`, `IsBlas1`, exact comparison and a size-only precision
envelope.

### 4.3 G3: orthogonality, residuals, forward bound (planned, M each)

All in the contract parameters $(\eta_0,\mu,\varepsilon)$ and $\varepsilon_{\rm mv}$, for every
scheme, under the window $\sqrt{3(N+b)}\,\mu\le\eta_0$; the CGS2 corollaries substitute the
values of §3.5. On each side:

* $\|\bar{\mathbf U}^{\mathsf T}\bar{\mathbf U}-\mathbf I\|_{\mathsf F}\le\sqrt{3N}\,\mu$ on the
  nonzero columns (that is, $\|\mathrm{gd}\,\bar{\mathbf U}\|_{\mathsf F}\le\sqrt{3N}\,\mu$), and
  the same for $\bar{\mathbf V}_+$: the column clause of the contract and the composition
  lemma E2. In particular the number of nonzero columns is at most $m$, respectively $n$.
* Residual relations $\|\mathbf A\bar{\mathbf V}-\bar{\mathbf U}\bar{\mathbf R}\|_{\mathsf F}$,
  $\|\mathbf A^{\mathsf T}\bar{\mathbf U}-\bar{\mathbf V}_+\bar{\mathbf S}\|_{\mathsf F}\le
  c'\sqrt N\,(\varepsilon_{\rm mv}+\varepsilon)\|\mathbf A\|_2$: the residual clause, block by
  block.
* **Forward bound for the returned factors**:
  $$\|\mathbf A-\bar{\mathbf U}\bar{\mathbf S}^{\mathsf T}\bar{\mathbf V}_+^{\mathsf T}\|\le
  \|(\mathbf I-\mathbf P_{\bar{\mathbf U}})\mathbf A\|+
  c''\sqrt N\,(\mu+\varepsilon_{\rm mv}+\varepsilon)\|\mathbf A\|_2,$$
  $\mathbf P_{\bar{\mathbf U}}$ the orthogonal projector onto the computed range, in the spectral
  and Frobenius norms. This says the returned factors are as good as projecting $\mathbf A$ onto
  the computed left basis; it needs nothing about Krylov spaces.

For the CGS2 instance $\varepsilon$ contains the deflation threshold $\tau$, so the price of
deflation is visible as a $\tau\|\mathbf A\|_2$ term in the last two bounds.

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
O(N(\mu+\varepsilon_{\rm mv}+\varepsilon)\|\mathbf A\|_2)$. Then $(\mathbf A+\mathbf E)\mathbf Q_V=\mathbf Q_U\mathbf R'$ and
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
| A12 | every block size (§2.4): A10, A11 for a Gaussian block; the clean corollaries (readable constants, rate, asymptotic forms) | planned | S | A3 |
| A13 | necessity: multiplicity above $b$ at some $\sigma_i>\sigma_r$ gives error $\ge\sigma_i$ for every $q$ (§2.6) | planned | M (S if the eigenspace projection lemma exists) | `blockKrylovSpace_eq_iSup_krylovSpace`, grade |
| E1 | `IsBasisExtension`, `IsBasisExtensionErr`: monotonicity in the parameters, the exact one implies the rounded one at $(\eta_0,0,0)$ | planned | S | — |
| E2 | composition: a sequence of extensions meeting the rounded contract has $\|\mathbf G-\mathbf I\|_{\mathsf F}\le\sqrt{3N}\mu$ on the nonzero columns, under $\sqrt{3N}\mu\le\eta_0$ | planned | S | `frobNorm_transpose_mul_self_sub_one_le_of_columns` |
| E3 | `cgs2Extend_spec`: column-wise CGS2 with threshold $\tau$ meets `extendRel` at the constants of §3.5 | planned | M | `cgs2_spec`, `IsOrthErr` at the CGS2 constants, `Lanczos.Reorth` normalization proofs |
| E4 | the same implementation at $\tau=0$ in the exact model meets `exactExtendRel` | planned | M | rank-revealing MGS facts |
| E5 | linking: the abstract certificates composed with E3/E4 through `Algorithm.link`, costs and storage recomputed | planned | M | `Algorithm.link`, `Profile.Refines` |
| P1 | `bandGolubKahanState`, for any exact extension: ranges are the block Krylov spaces, nonzero columns orthonormal | planned | M | `blockKrylovSpace_succ`, E1 |
| P2 | $\mathbf U\mathbf U^{\mathsf H}=$ `rangeProjector (A * K_q)`; $\mathbf A^{\mathsf H}\mathbf U=\mathbf V_+\mathbf S$; $\mathbf U\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}=$ `rsvd A K_q` (in `Krylov`), `= rbki A Ω q` (corollary in `LowRank`) | planned | M | P1, `rbki_eq_rangeProjector` |
| P3 | band structure, $\mathbf R=\mathbf S^{\mathsf H}_{[0,N)}$; $b=1$ is Golub–Kahan | planned | S | P1 |
| O1–O3 | `OperatorPairOp`, exact and normwise contracts, joint realization; dense and COO adjoint lowerings | planned | S, M, M | `Operator`, `StoredOperator` |
| Q2 | `BandGolubKahan.solve` over the abstract `OrthOp`: total exact `Writes` theorem, output $=$ P1 state | planned | L | `exactExtendRel`, loop and archive rules |
| Q3 | canonical exact certificate with counts ($N$ + $N$ products, $nb$ samples), work, span, storage | planned | M | `Algorithm.ofWp`, static manifests |
| Q4 | Gaussian tape: transfer of the existing gapped and gapless bounds and of A10–A12 to the stored output | planned | M | Hutch++ `Samples`, `Probability` |
| R1 | rounded total execution with history (G2), under `extendRel` | planned | L | `Rounded.History` pattern |
| R2 | orthogonality of both bases on the nonzero columns (G3), in $(\eta_0,\mu)$ | planned | M | E2 |
| R3 | residual relations (G3), in $(\varepsilon,\varepsilon_{\rm mv})$ | planned | M | residual clause |
| R4 | forward bound for the returned factors (G3) | planned | M | R2, R3 |
| R5 | rounded canonical certificate for the CGS2 instance, scalar-linked and stored | planned | L | E3, E5, `RoundedStoredCertificate` pattern |

Totals: 32 rows, twins counted with their row (S 12, M 17, L 3). Order: E1, E2 and the generic
P, Q2–Q3, R1–R4 first (everything in the contract's parameters), then the instance E3–E5 and
the linked certificates Q4, R5. The theory rows A1–A13 are independent of the program rows. Later stages: G4 backward
model (L), G5 (BL8), truncation (BL6), block-size-aware probability (§2.5), Hermitian twin and
`nystromBKI` program, odd product counts.

## 6. Shared proof machinery (planned first)

* **The orthogonalization contract** (§3.1a): `IsBasisExtension`, `IsBasisExtensionErr`,
  `OrthOp.extend`, and the composition lemma E2. Every later method that keeps an orthonormal
  basis (the Hermitian twin, block Arnoldi, a randomized range finder, GMRES) is a consumer,
  and every scheme (CGS2, MGS2, BCGS2, Householder) is an instance proved once. Adding a
  scheme is: implement it, prove its `…_spec` against `extendRel`, link.
  `Lanczos.Reorth.advance` hard-wires CGS2 today; restating it over the contract is not part
  of this stage, but nothing here should prevent it.
* **Block archive invariant**: stored block prefix of a basis buffer plus a block
  upper-triangular coefficient buffer. One loop rule instance, used for both bases.
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
| `IsBasisExtension(Err)`, `OrthOp.extend`, E2 | this program at three call sites; the Hermitian twin; later range finders, block Arnoldi; optionally `Lanczos.Reorth` |
| `cgs2ExtendImpl`, E3–E5 | the concrete certificates Q4, R5; any consumer of the contract that wants CGS2 |
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
| `Matrix/Perturbation/BasisExtension.lean` | E1, E2: the two predicates and the composition lemma, next to `OrthErr.lean` | new |
| `Ops/Catalog/Orth.lean` | `OrthOp`, `extendRel`, `exactExtendRel` | new |
| `Matrix/Factorizations/CGS2/{Extend,ExtendRounded,ExtendExact}.lean` | E3, E4: the scheme is a factorization routine, independent of Krylov | new |
| `Krylov/GolubKahan/Band/{Alg,Solve,Certification}.lean` | Q2, Q3: the abstract program is a Krylov process, next to `Krylov/Lanczos/Reorth/` | new |
| `Krylov/GolubKahan/Band/Linked.lean` | E5 | new |
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

## 9. Decisions and open questions

**Decided by the maintainer, 2026-11-14** ("math statements can be messy, we will have clean
corollaries. otherwise stuff is good. ideally we start with abstractions for how we do
orthogonalization, and then prove a concrete one by subbing something in."):

| id | decision |
|---|---|
| APPROVE | approved with the two changes below |
| BL1 | a: single vector with explicit constants and every block size by monotonicity now; block-size-aware bounds in stage 2 |
| BL2 | b: sharp statements (exponent $2(t-1)$, all factors); clean corollaries on top |
| BL3 | c: tail bound and truncated expectation, the messy forms; clean corollaries on top |
| BL4 | a: two-sided block Golub–Kahan with full reorthogonalization |
| BL5 | a: full coefficient columns |
| BL6 | a: untruncated factors now |
| BL7 | **changed**: neither option; the orthogonalization is an abstract operation with a contract (§3.1a), the driver is proved against it, and column-wise CGS2 is the first scheme substituted |
| BL8 | a: backward model, then uniform bounds through the gap, as a research branch |
| BL9 | a: `OperatorPairOp` |
| BL10 | a: exact over `RCLike`, rounded over $\mathbb R$ |
| BL11 | a, as a property of the CGS2 instance and not of the driver (§3.5) |

| BL12 | a ("yeah a is fine"): block extension with an absolute per-column guarantee, the rank decision owned by the scheme |

BL2 and BL3 are read from "statements can be messy"; BL11 from "otherwise stuff is good".
No decision is open.

BL12 as it was put, raised by the change to BL7:

| id | question | options | recommendation | why |
|---|---|---|---|---|
| BL12 | granularity and shape of the orthogonalization contract | **a block extension with an absolute per-column guarantee $(\eta_0,\mu,\varepsilon)$, the rank decision owned by the scheme (§3.1a)** / b single-vector `IsOrthErr` $(\eta_0,\varepsilon_1,\varepsilon_2,\varepsilon_3)$ with admissibility left to the driver, as in `Krylov-LanczosReorth.md` / c both, with b ⟹ a proved once | a (c if `Lanczos.Reorth` is to be restated over the contract soon) | (a) admits block schemes and makes the driver free of rank logic; (b) is the finer contract and already has its CGS2 constants on main, and "b plus a threshold test ⟹ a" is exactly the instance proof E3 |

The original options, for the record:

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

## 9a. Skeleton record (2026-11-14)

The Lean skeleton of the first stage is on this branch. Every file compiles through the shared
gate (one combined build of all new modules, 3761 jobs), `check_rules` reports 0 errors, and
about 65 statements are `sorry`, each preceded by a proof outline. Nothing is pushed. The
branch is based on `cbf64ea9`; `origin/main` has since moved to PR #138, which changes
`Ops/Catalog/Operator.lean` and `Ops/Logic/Writes.lean`, so a rebase needs a rebuild and a
recheck of `OperatorPair.lean` and `Band/Alg.lean`.

| File | Contents | Proved / sorry |
|---|---|---|
| `Matrix/Perturbation/BasisExtension.lean` | `colSupport`, `gramDefect`, `IsBasisExtension`, `ExtensionWindow`, `IsBasisExtensionErr`, block helpers, E1, E2 | 26 / 4 |
| `Matrix/Perturbation/OrthErr.lean` | admissible-column lemma added | all proved |
| `Matrix/Factorizations/BasisExtensionContract.lean` | `extendRel`, `exactExtendRel` | all proved |
| `Ops/Catalog/Orth.lean`, `OperatorPair.lean` | `OrthOp.extend` with a generic decoded-matrix contract; `OperatorPairOp` | all proved |
| `Krylov/Processes/BandGolubKahan.lean` | `IsBlockGolubKahan`, P1–P3, existence | 4 / 15 |
| `Krylov/FinitePrecision/BandGolubKahanRun.lean` | `IsBlockGolubKahanErr`, R2–R4 | 5 / 8 |
| `Krylov/GolubKahan/Band/Alg.lean` | driver `solve`, `program`, stored-run predicates, Q2, R1 | definitions complete; specifications sorry |
| `Krylov/GolubKahan/Band/Run.lean` | assembly of packed coefficients, bridges to the pure relations, consequences | all proved |
| `Krylov/GolubKahan/Band/Certification.lean`, `Linked.lean` | canonical exact certificate (Q3), scheme-generic linking (E5) | certificates proved from the driver specification; 6 accounting lemmas sorry |
| `Matrix/Factorizations/CGS2/*.lean`, `Krylov/Orthogonalization/CGS2/*.lean` | the CGS2 instance: pure lemmas, `cgs2ExtendImpl`, E3, E4 | definitions complete; 12 sorry |
| `LowRank/BlockKrylov/{Factored,Samples,Probability}.lean` | output equals `rbki`; Gaussian tape; generic transfer and two corollaries (Q4) | all proved |
| `Krylov/Basic/BlockSpace.lean`, `LowRank/Structural/BlockKrylov.lean` | A1–A4 | all proved |
| `ForMathlib/LinearAlgebra/Vandermonde.lean`, `Krylov/Basic/KrylovVandermonde.lean`, `Polynomial/Interpolation/LagrangeBound.lean` | A5, A6 | 8 / 2 |
| `LowRank/Structural/SmallBlock.lean` | A7 and the residual lemma | 0 / 4 |
| `LowRank/Gaussian/BlockKrylov.lean`, `Probability/Distributions/GaussianLogOverlap.lean` | A8, public small-ball lemma | all proved |
| `LowRank/Gaussian/SmallBlock.lean`, `LowerBounds/LowRank/BlockSize.lean` | A9–A13 | 4 / 10 |

Where the skeleton departs from the text above (the Lean files are authoritative):

* **Layering of the contract.** `Ops` is the bottom layer and cannot import `Matrix`, so
  `Ops/Catalog/Orth.lean` holds a contract generic in a predicate on the decoded matrices, and
  the two concrete contracts are in `Matrix/Factorizations/BasisExtensionContract.lean`.
* **Placement of the CGS2 program files.** `cgsPass`, `passRel`, `PassOut` are in
  `Krylov/Lanczos/Reorth/Sweep*.lean`, a layer above `Matrix`, so the instance's program files
  are in `Krylov/Orthogonalization/CGS2/`. Their intended home is
  `Matrix/Factorizations/CGS2/` once the two sweep files move down (they import only `Ops`).
  This touches files on main and is left as a recommendation.
* **Realization of the abstract model.** `AccessModel.realize` is a field, so the abstract
  model needs a witness. It is a choice-based word function built from
  `exists_isBasisExtension`, not the CGS2 triple; the abstract certificate therefore needs no
  scheme, and still quantifies over every interpretation meeting the contract.
* **Expectation transfer (O1).** The core has only a failure-probability transfer. The stored
  product equals `rbki` for every sample, so integrals transfer by equality, with no
  measurability or integrability hypothesis (`integral_comp_storedOutput`).
* **Operand layout (O4).** Adjacency in one buffer is one equation in the admission predicate;
  zero-length blocks need nothing. Coefficients are stored packed by block column.
* **Constants of the CGS2 instance.** $\mu=2\varepsilon_1+4\varepsilon_3/\tau+5E$, that is
  $4c+8(\eta_0+c)^2/\tau+5E$, and $\varepsilon=3c+2E+2\tau$; $\tau\le1$ is not needed. The norm
  clause needs about $4.1E$, so the $2E$ of §3.5 was too small.
* **Zero columns in the instance.** `IsOrthErr`'s antecedent fails on a basis with zero
  columns; the instance uses `IsOrthErrOnSupport` (antecedent on the Gram defect) and a
  compression lemma. No exact-zero assumption on the arithmetic is needed.
* **Product errors** in the rounded relation are column-wise, which gives a zero product for a
  zero column.
* **Theory.** A6 needs no positivity of the nodes. The rank-deficient companion of A7 needs
  distinct singular values ("error zero once $q$ reaches the rank" is false without them). The
  probabilistic statements need no `hpos`. A13 is singular value by singular value and needs no
  positivity. The Nyström twin of A2 needs positive semidefiniteness. A truncated gapped tail
  bound was added because A11 needs it; the truncated block bound is not a comparison of
  outputs and reruns the range-monotone chain.
* **Scalars.** The exact extension contract is generic in the field; the driver's stored-run
  predicates and certificate are over $\mathbb R$ so far (BL10 asked for the exact program over
  `RCLike`; not done).

Not yet stated: the rounded canonical `Algorithm` (R5; only its Triple and counted-run forms),
the clean corollaries of A12 beyond the two transfer corollaries, G4. Missing library facts
found while writing: the spectral and Frobenius error of projecting onto an arbitrary
eigenframe of the top $r$ directions (needed by A7); the Musco–Musco case-split lemma is still
private in `BlockKrylovGapless.lean` (needed by A11); a reindexing lemma for
`blockPrefix (j+1)` as `fromCols` (every block induction goes through it). The hard proofs are
the driver's loop invariant (`solve_writes`), the two CGS2 `Triple`s, the residual lemma of
A7, and `exists_isBasisExtension`.

## 9b. Proof record (2026-11-14)

The branch was rebased onto `origin/main` @ `c74ff06d` (PR #138) with no conflicts, and every
statement of the skeleton is now proved. One combined build of all modules of the branch
(3789 jobs) has no error and no `sorry`; a source scan of the 36 Lean files the branch touches
finds no `sorry`, `admit`, `native_decide` or `maxHeartbeats`; `check_rules` reports 0 errors.
The proving lanes report `#print axioms` giving only `propext`, `Classical.choice`,
`Quot.sound` on their headline theorems. The proved/sorry column of the table in §9a is
superseded: every row is proved. Nothing is pushed. Not run: a whole-library build and
`scripts/stage_check.sh`.

No statement, definition or constant of the skeleton had to change to be proved, with two
exceptions of form only: two internal driver lemmas lost three unused instance arguments, and
one `variable` line was split. No defect was found in the driver or in the CGS2
implementation.

What is certified:

* **Small-block theory** (§2): all of A1–A13, including the Gaussian tail, truncated
  expectation and gapless bounds for a vector and for a block of any size.
* **Abstract driver** (§3, §4.1–4.3): for every input, every tape and every interpretation
  meeting the exact extension contract and the exact operator pair, the program runs within
  its counts ($nb$ samples, $qb$ products with $\mathbf A$, $qb$ with $\mathbf A^{\mathsf H}$,
  $2q+1$ extensions) and scratch bound, and the stored factors satisfy
  $\mathbf U\mathbf S^{\mathsf H}\mathbf V_+^{\mathsf H}=\mathsf{rbki}(\mathbf A,\mathbf\Omega,q)$;
  under the rounded contracts the stored run satisfies the orthogonality, residual and forward
  bounds of §4.3. Any statement about `rbki` under a Gaussian law transfers to the stored
  output, failure probabilities and expectations alike.
* **CGS2 instance** (§3.5): `cgs2ExtendImpl 0` meets the exact contract for an arbitrary
  basis, and `cgs2ExtendImpl τ` meets the rounded contract at
  $\mu=4c+8(\eta_0+c)^2/\tau+5E$, $\varepsilon=3c+2E+2\tau$.
* **Linking** is proved generically in the scheme (`linked_certifies`, `linkedAlgorithm`).

Not yet stated, so not proved:

* the **concrete** linked certificates, that is `linkedAlgorithm` instantiated at
  `cgs2ExtendImpl` over the exact BLAS model and over the rounded model (the generic theorem
  and both instance `Triple`s exist; the instantiation, with its `wellTyped` side condition
  and the recomputed costs, is not written);
* the rounded canonical `Algorithm` (R5), the clean corollaries (A12), G4, G5;
* the driver's certificate over `RCLike` (it is over $\mathbb R$).

Cleanup owed (no mathematical content): about forty block-algebra helpers are private in
`Krylov/Processes/BandGolubKahan.lean` and `Krylov/FinitePrecision/BandGolubKahanRun.lean`,
two of them duplicated (the S5 warnings), and belong as public lemmas in
`Matrix/Perturbation/BasisExtension.lean`, with the generic Gram-defect lemmas of the run
file; `LowRank/Gaussian/SmallBlock.lean` is 1104 lines and its deterministic helpers belong in
`LowRank/Structural/SmallBlock.lean`; `Krylov/Orthogonalization/CGS2/PassSupport.lean` restates
three bounds of `Lanczos/Reorth/RoundedOrthogonality.lean` under a weaker hypothesis and
should replace them there; the sweep files should move to the Matrix layer (§9a); seven
linter warnings (three long docstring lines, three unused hypotheses, one unused instance
argument).

## 9c. Explorer and inventory record (2026-11-14)

The branch was rebased a second time, onto `origin/main` @ `f329b7ff` (PR #145), and the whole
library builds on it (5094 jobs, no error, no `sorry`).

**Library side.** 23 `Result:` ids on 46 theorems, each with a bold name and a citation or
"No printed source."; `Algorithm:` tags `block-golub-kahan` (specification, run model, and the
driver program) and `cgs2-basis-extension` (the implementation); bibliography entries
`MeyerMuscoMusco2023` and `ChenEpperlyMeyerMuscoRao2025`, with the cited labels checked against
the arXiv versions (the locators of §1 for those two papers are thereby verified against
arXiv; the Tropp–Webber remark on block size below rank could not be checked and is not
cited); ten vocabulary rows; the curated page `docs/algorithms/Block-Golub-Kahan.md`.
Program-side theorems carry no result ids, as on main. With an extraction of this branch
(`scripts/explore_data.sh`), `scripts/check_rules.py` runs all 106 rules with 0 errors; the
extraction-tier naming rules had not run before, and found five names, since fixed (two
stored-run predicates restated as `Prop`-valued, one restricted expectation renamed
`integral_setOf_…`, two range lemmas renamed without `mulVecLin`).

**Certificate inventory** (new on main with PRs #143 and #145: `scripts/OpsPrograms.lean`
against `scripts/ops_certificates.txt`). The driver certificate's model is proved confined,
and its specification states a closed-form scratch bound. It is not uniform, because the
matrix-free operator pair is a declared oracle, which the algorithm page and the docstrings
name. Its budget is the full static count, a manifest. The check therefore still asks for a
reviewed line, which is the maintainer's to add:

```
NLAlib.Krylov.GolubKahan.Band.Certification.algorithm hyps=0 uniform=no confined=yes charged=no budget=manifest scratch=closed
```

Until that line is in the registry, `scripts/OpsPrograms.lean` (and so CI and
`scripts/stage_check.sh`) fails on this branch with that one error.

**Site side.** Content pages on the local branch `feat/block-lanczos-explorer` of the site
repository (worktree `~/work/nla-site-block-lanczos`, on the site's main @ `420155a`; content
pages only, not pushed): a new algorithm page for block Golub–Kahan, a page for its driver, a
Gram–Schmidt implementation page for the two-pass basis extension, the RBKI page extended with
the results for block sizes below the target rank, and placements on the Nyström BKI page, two
theory pages and two task pages. Against the extraction of this branch at `37bc6516`: the
site build passes (137 authored pages, 580 result groups), `audit_math.py` reports 0 issues
(580 of 580 result groups curated, 28 of 28 tagged methods placed), `audit_organization.py`
reports 0 issues, and the site's unit tests pass. The site build rejects unknown ids, so the
library branch has to be published before the site branch.

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

Maintainer decisions, 2026-11-14 (§9), applied in a second revision: the single-vector
statements carry the sharp exponent, with clean corollaries planned (A12); §3 is rewritten
around an abstract orthogonalization operation (§3.1a), the driver theorems of §4 are stated in
the contract's parameters, and column-wise CGS2 with threshold deflation is the first instance
(§3.5, E3–E5). The first stage grew from 28 to 32 statements.

Second independent review, 2026-11-14, of §3.1, §3.1a, §3.5 and §4.2–4.4 after that revision
(read against `OrthErr.lean`, `ClassicalGramSchmidt.lean`, `Lanczos/Reorth/`, and the Ops
contract, link and certificate files; nothing compiled). Findings applied in a third revision:

* the exact `orth` clause and the rounded `residual` clause had to be conditional on the old
  basis;
* zero columns: the column lemma on main does not apply to a basis with zero columns; the
  contract is restated with the Gram defect on the support, and E2 is an exact block identity;
* two claims did not follow from the first contract and needed new clauses: the band structure
  and $\mathbf R=\mathbf S^{\mathsf H}$ restricted (`coef_zero_left/right`), and "a zero column
  has zero descendants" (`zero_col`); plus `span` to stop the range growing;
* the window for $b>1$ must cover the columns added inside the block (`ExtensionWindow`);
* `cgs2Impl` discards the coefficients, so the instance is built from two `cgsPass` calls; the
  operand layout puts the new block directly after the stored basis;
* constants of §3.5 corrected for the rounded test.

Still unchecked: none of the Lean in this note has been compiled; the operand admission for
"new block at the end of the basis buffer" and zero-length blocks (O4) are the first things
the skeleton tests. The reviewer could not run numerics and could not confirm the
Tropp–Webber quotation; line-number locators in §0 were not checked.
