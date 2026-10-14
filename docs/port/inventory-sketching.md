# Inventory: prototype `Sketching/` and its consumers

Read-only survey, 2026-10-14, from `atlas/declarations.json`, the Lean files wherever a proof's
organisation is claimed, and the prototype's notes `docs/SKETCH_INTERFACE.md` and
`docs/SPARSE_INTEGRATION.md` (re-checked against today's atlas). Counts are atlas declarations.
Sizes: `Sketching/` 1873 in about 150 files, 31.5k lines; `LowRank/` 315; `Estimation/` 101;
`Solvers/` 69; `Krylov/` 470, none probabilistic.

## 1. Map

| subdirectory | files / lines / decls | mathematics |
|---|---|---|
| `Gaussian/` | 1 / 189 / 2 | Gaussian sketch is a subspace embedding |
| `Properties/SubspaceEmbedding/` | 5 / 320 / 13 | the predicate, Gram and singular-value forms |
| `Properties/JL/` | 1 / 339 / 8 | Johnson-Lindenstrauss, Gaussian sketch only |
| `Properties/ApproxMatrixMultiplication/` | 1 / 268 / 4 | AMM from a second-moment hypothesis |
| `Sampling/` | 13 / 1984 / 96 | leverage scores, row sampling, AMM by sampling, Hoeffding |
| `Structured/` | 5 / 1001 / 48 | SRHT, with and without replacement |
| `Sparse/` | 125 / 27725 / 1702 | CountSketch, SparseStack, OSNAP (section 5) |

How each sketch is defined:

- **Gaussian.** The measure `gaussianMatrix (Fin k) (Fin m)` on `Matrix`; the sketch is
  `(1 / √k) • G`. The embedding theorem is on the canonical space (no `HasLaw`), over `Fin`.
- **CountSketch.** `countSketchMatrix h σ : Matrix ρ ι ℝ`, a function of a hash and signs; law
  `countSketchLaw` on `(ι → ρ) × (ι → ℝ)` (uniform hashes times `rademacherMeasure`).
- **SparseStack, OSNAP.** `sparseStackMatrix Z : Matrix (Fin s × Fin b) (Fin n) ℝ` (entry `± 1/√s`
  at row `(g, hash g i)`) under `sparseStackMeasure s b n hb`; `uniformSparseMatrix X` under
  `uniformSparseMeasure m s n hsm`. Both measures are the `toMeasure` of a proof-internal
  real-weighted `SparseSketch.FiniteLaw`.
- **SRHT.** `srhtSketch H ξ T = √(n/k) • (selectionMatrix _)ᵀ * H * diagonal ξ` under `srhtLaw hk`
  on `(Fin n → ℝ) × ExactRowSubset (Fin n) k`. `H` is a hypothesis (`Hᵀ * H = 1`,
  `H i j ^ 2 = 1 / n`), instantiated by `walshMatrixFin b`. A twin with i.i.d. row labels.
- **Row sampling.** `leverageSamplingSketch p ω : Matrix (Fin k) n ℂ` under
  `Measure.pi fun _ => finiteSamplingLaw p hp`; `p` is data with a domination hypothesis.
- **Sub-Gaussian rows** (`RandomMatrix/SubGaussian/`): no law; a family `A : m → Ω → n → ℝ` with
  `iIndepFun`, a directional `HasSubgaussianMGF` and an isotropy integral.

Headline results (statements and constants in the table of 2.2), by conclusion shape:

- `one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix`: `U` orthonormal with `d` columns,
  `0 < ε ≤ 1`, `0 < δ ≤ 1`, `k ≥ 18 (d + 2 log(2/δ)) / ε²` give `1 − δ ≤ P(IsSubspaceEmbedding)`.
  Success form, sample size only; the tail `2 exp(−t²/2)` stays inside the proof.
- `jl_distributional`, then `jl_lemma` (union over `N²` pairs) and three sample-size corollaries:
  inline event, Gaussian only. `lintegral_frobSq_transpose_mul_sketch_sub_le`: AMM from a
  second-moment hypothesis on any sketch, in lower Lebesgue integrals; no caller.
- `measure_le_norm_leverage_gram_sub_one` (Gram tail over `ℂ`);
  `integral_frobenius_sampled_mul_sub_sq` (exact AMM variance);
  `uniform_subset_average_convex_le_iid`: Hoeffding 1963 Thm 4, sampling without replacement is
  below i.i.d. in convex order (explicit coupling, 44 declarations).
- `measure_srht_gram_failure_le_of_sharp_sample_size` and variants (manuscript bound, capped width,
  Walsh, with replacement, rank zero, full rows). Gram form, sample size only.
- `measure_countSketch_gram_failure_le`, `measure_countSketch_embedding_failure_le_of_rows`,
  `integral_frobSq_countSketch_gram_error_eq`. Failure form on the predicate: the target shape.
- `measure_sparseStack_embedding_success_ge`, `measure_uniformSparse_embedding_success_ge`: section
  5. Success form, sketch size a function of `(d, δ, ε)`.

## 2. The property predicates

### 2.1 What exists

- **`IsSubspaceEmbedding S U ε`** (`Properties/SubspaceEmbedding/Basic.lean`), real only:
  `∀ x, (1 − ε)‖Ux‖² ≤ ‖SUx‖² ∧ ‖SUx‖² ≤ (1 + ε)‖Ux‖²`, norms written `v ⬝ᵥ v`. Deterministic: no
  measure, no failure probability. API: `.mono`, `.mul_right`, `.of_mul_right`, the Gram form
  `isSubspaceEmbedding_iff_specNorm_transpose_mul_self_sub_one_le` (needs `HasOrthonormalCols U`,
  `0 ≤ ε`), `isSubspaceEmbedding_iff_singularValues`, `isSubspaceEmbedding_reindex_iff`.
- **Oblivious subspace embedding**: no predicate. Failure probability and sample size occur only
  inside each distribution's theorem.
- **Johnson-Lindenstrauss**: no predicate; an inline event. **JL moment property**: the inline
  hypothesis `hmom` of the AMM theorem; no theorem concludes it for any distribution.
- **Approximate matrix multiplication**: no predicate; three unrelated statements (table).
- **Isotropy**: inline, three spellings: `hsecond : ∀ k i j, ∫ Z i k * Z j k = if i = j ...`
  (Hutchinson); `(hz : MemLp _ 2) (hind : pairwise IndepFun) (hmean) (hsq)` (diagonal estimator,
  spectral measure); `(hmgf) (hiso)` on rows (sub-Gaussian JL).
- **Isotropic bounded atoms** (matrix Chernoff): inline `hA`,
  `hbound : 0 ≤ lambdaMin (A j) ∧ lambdaMax (A j) ≤ L`, `hmean : (1/N) • Σ A j = 1`. **Limited
  independence**: `SparseSketch.FiniteLaw.MatchesUpTo μ ν k`, internal to the sparse proof.
- **Bundles assumed downstream**: `rsvd_main` takes `hunit` (a.s. `IsUnit (Ω₁ Ω₁ᵀ)`), `hinv` (an
  *equality* `E‖S₂Ω₂Ω₁†‖_F² = k/(t−k−1) ‖S₂‖_F²`), `hXi`, `hZi`; `completion_reduction` takes `hG₁`,
  `hG₂`, `hG₁m`, `hGi`; `SketchProject.expErr_le` takes `hlam : λ‖v‖² ≤ vᵀ W v`.

`IsSubspaceEmbedding` is concluded for Gaussian, CountSketch, SparseStack, OSNAP. It is assumed by
**no theorem outside `Sketching/`**: the only import of `Sketching` by a consumer is
`LowRank/Nystrom/Structural.lean` taking `Sampling/Leverage` for a projector lemma, and
sketch-and-solve, sketch-and-precondition, Nyström PCG are atlas `candidate`s, not formalised.

### 2.2 Sketch family × property

`†`: not stated through the predicate, or in a shape different from its neighbours.

| family | JL, fixed vector | subspace embedding, fixed `U` | AMM or second moment |
|---|---|---|---|
| Gaussian | G1 †: `2exp(−k(ε²/4−ε³/6))` | G2 †: `k ≥ 18(d+2log(2/δ))/ε²` | G3 †: exact |
| sub-Gaussian rows | B1 †: `2exp(−kε²/(256e²K⁴))` | B2 †: singular values only | none |
| CountSketch | none | C1: `(d²+d)/(mε²)`; C2 | C3: exact `E‖G‖_F²` |
| SparseStack | none | P1 †: rounded `s`, `m` | internal `tr G^{2q}` |
| OSNAP | none | P2 †: rounded `s`, `m` | internal `tr G^{2q}` |
| SRHT, distinct rows | none | H1 †: `k ≥ 3Lε⁻²log(4d/δ)` | none |
| SRHT, i.i.d. rows | none | H2 †: same | none |
| leverage sampling | none | L1 †: `2d exp(−βkε²/(3d))`; L2 † | none |
| column-row sampling | none | none | S1 †: `≤ ‖A‖²‖B‖²/(βc)` |
| any, JL second moment | hypothesis | none | A1 †: `ε²‖A‖²‖B‖²` |
| Haar / orthonormal | none | none | none |

G1 `jl_distributional`; G2 `one_sub_le_measure_isSubspaceEmbedding_gaussianMatrix`; G3
`integral_frobSq_mul_gram_mul_transpose_sub` (in `RandomMatrix/`: `(‖M‖²‖N‖² + ‖MNᵀ‖²)/t`); B1
`measure_lt_abs_mulVec_sq_sub_le_of_independent_isotropic_rows`; B2
`measure_extreme_singular_failure_le_of_independent_isotropic_rows` (`√N ± (32eK²√(log 9)√n + t)`,
failure `2exp(−t²/(1024e²K⁴))`); C1 `measure_countSketch_gram_failure_le`; C2
`measure_countSketch_embedding_failure_le_of_rows` (`m ≥ (d²+d)/(δε²)`); C3
`integral_frobSq_countSketch_gram_error_eq`; P1 `measure_sparseStack_embedding_success_ge`; P2
`measure_uniformSparse_embedding_success_ge`; H1
`measure_srht_gram_failure_le_of_sharp_sample_size`; H2
`measure_srhtWithReplacement_gram_failure_le_of_sharp_sample_size`; L1
`measure_le_norm_leverage_gram_sub_one`; L2 `measure_leverage_embedding_failure_le_of_sample_size`
(`k ≥ 3d/(βε²) log(2d/δ)`); S1 `integral_frobenius_sampled_mul_sub_sq_le_of_probability_domination`;
A1 `lintegral_frobSq_transpose_mul_sketch_sub_le`.

### 2.3 The one-offs

The embedding conclusion has five shapes over six families:

1. Gaussian: `1 − δ ≤ μ.real {G | IsSubspaceEmbedding ((1/√k) • G) U ε}`, sample-size form only.
2. CountSketch: `μ.real {z | ¬ IsSubspaceEmbedding (S z) U ε} ≤ δ`, with a Gram tail before it.
3. SparseStack, OSNAP: `1 − δ ≤ μ.real {IsSubspaceEmbedding}` and, separately,
   `μ.real {ε < specNorm (Uᵀ (SᵀS U) − 1)} ≤ δ`, at one prescribed sketch size.
4. SRHT: `(μ {ω | ε < specNorm ((SU)ᵀ(SU) − 1)}).toReal ≤ δ`; never reaches the predicate.
5. Leverage sampling: `(μ {ω | ∃ x, ‖SAx‖² < (1−ε)‖Ax‖² ∨ (1+ε)‖Ax‖² < ‖SAx‖²}).toReal ≤ δ` over
   `ℂ`, on `range A ⊆ range U`, after an operator-norm Gram tail `ε ≤ ‖·‖`.

Also: strict against non-strict events; `μ.real`, `.toReal` and `ENNReal.ofReal` bounds; `ε < 1`
against `ε ≤ 1`; `[NeZero d]` against a separate `d = 0` theorem; `Fin` against `Fintype`. Only
leverage sampling and CountSketch expose an unconditional tail in `ε`. AMM is `∫⁻` in A1, Bochner in
G3 and S1.

## 3. What the consumers actually need

No consumer proof uses a subspace embedding, a JL property, or AMM. The low-rank theorems use
Gaussianity itself; the estimators use moments of probe coordinates; the solvers and the sampling
algorithms carry their own finite laws.

| consumer | law in the statement | what the proof uses |
|---|---|---|
| R1 range finder, Frobenius | `HasLaw Ω gaussianMatrix` | structural bound; block law; `E‖G†‖_F²` |
| R2 range finder, spectral | Gaussian | R1's inputs; Chevet; `E‖G†‖` |
| R3 subspace iteration | Gaussian | R2 on `(AAᵀ)^q A`; power inequality; Jensen |
| R4 truncated RSVD | Gaussian | R1; deterministic truncation |
| R5 Nyström, PSD, trace | Gaussian | R1 applied to `F`, `A = FᵀF` |
| R6 generalized Nyström | Gaussian `Ω ⟂ Ψ` | R1; completion; block law for `Ψ`; Fubini |
| R7 RPCholesky | own adaptive `PMF` | diagonal sampling; trace-drift recursion |
| R8 volume sampling | own determinantal `PMF` | Gram-determinant identities; exact formula |
| R9 polynomial filter | none (deterministic) | right inverse of the leading block of `Ω` |
| E1 Hutchinson, mean | any, second moments | `E[z_i z_j] = δ_ij` only |
| E2 variance; diagonal estimator | any, moment bundle | independent coordinates, 4th moment |
| E3 Hutchinson, tail | independent sub-Gaussian | Hanson-Wright |
| E4 Hutch++, XTrace, mean | isotropic probes | probes independent of `Q(S)`; `Q` orthonormal |
| E5 SLQ | Rademacher (Gaussian for `1/x`) | E3; `‖z‖² = n` a.s.; Gauss quadrature |
| E6 random-start power, Lanczos | Gaussian vector | rotation invariance; log-overlap moments |
| S1 sketch-and-project | any finite sketch `PMF` | `λ • 1 ≤ E[(SᵀA)⁺(SᵀA)]` as hypothesis |
| S2 randomized Kaczmarz | rows `∝ ‖a_i‖²`, own `PMF` | one-step identity; `σ_min` |

R1 `rsvd_main_gaussian`; R2 `integral_specNorm_residual_le_singularValues_of_gaussian`; R3
`integral_specNorm_residual_gram_pow_gaussian_le`; R4 `rsvd_truncated_main_gaussian`; R5
`integrable_and_integral_trace_sub_nystrom_le`; R6 `gn_main_gaussian`; R7
`integral_trace_choleskyHistoryLaw_le_mul_spectralTraceTail`; R8
`integral_frobSq_volumeSamplingResidual_le_mul_bestRankFrobSq`; R9
`residual_sq_le_of_polynomial_filter`; E1 `integral_hutchinsonEstimate_eq_trace`; E2
`variance_quadForm`, `integral_mul_mulVec_apply_eq`; E3
`measureReal_le_abs_hutchinsonEstimate_sub_integral_le`; E4
`integral_deflatedTraceEstimate_comp_eq_trace`; E5
`measureReal_abs_compressionQuadratureEstimate_sub_trace_gt_le_of_hasLaw_rademacherVector`; E6
`integral_powerRayleighRelativeError_gaussianVector_le`; S1
`SketchProject.integral_sqErr_iidPathLaw_le`; S2 `integral_sqErr_kaczmarz_le_frobConditionNumber`.

Read from the proofs:

- **Range finder family (R1-R6).** The deterministic core is HMT Thm 9.1,
  `frobSq_residual_le_of_range_subset` and `specNorm_residual_sq_le_of_range_subset`: for any `Ω`
  with `Ω₁ = V₁ᵀΩ` of full row rank and any orthonormal `Q` with `range (AΩ) ⊆ range Q`,
  `‖(I−QQᵀ)A‖² ≤ ‖Σ₂‖² + ‖Σ₂Ω₂Ω₁†‖²`. It is distribution-free and already takes "any `Q`". The
  probabilistic step uses the block law (`hasLaw_gaussianMatrix_block_of_hasLaw`,
  `gaussianMatrix_indepFun_block_of_hasLaw`: `V₁ᵀΩ`, `V₂ᵀΩ` are independent Gaussians), conditioning
  (`integral_frobSq_mul_block_mul_pinvR_block`), inverse moments
  (`integrable_and_integral_frobSq_pinvR_gaussianMatrix`: `k/(t−k−1)`;
  `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le`: `e√(k+p)/p`), Chevet, and the a.s.
  rank facts `gaussianMatrix_ae_isUnit_mul_transpose`, `ae_rank_mul_gaussian_eq_min`.
- **Statements for a general random matrix.** `rsvd_main` and `gn_main` (a raw bundle whose `hinv`
  is an equality only a Gaussian satisfies); E1 and E3 (hypotheses on entries);
  `SketchProject.expErr_le` (any finite family of sketches with a spectral lower bound on the mean
  projector), the one consumer written against a property rather than a distribution.
- **Not formalised** (atlas `candidate`): `sketch-and-solve-ls`, `sketch-and-precondition`,
  `nystrom-pcg`, `hutchpp` (error bound), `rsvd-tail`, `etrsvd`; `tgn-expected-error` is `assumed`.
  These are the consumers that would take a subspace embedding as a hypothesis.

## 4. Parallel structure of proofs

1. **Gram bound to embedding.** Each family bounds `(SU)ᵀ(SU) − 1` and converts, or does not, by
   hand. Core: `{¬ IsSubspaceEmbedding} ⊆ {ε < specNorm G}`. Hypothesis: `HasOrthonormalCols U`.
2. **Matrix Chernoff through isotropic bounded atoms** (three times): leverage sampling (i.i.d.,
   non-uniform; calls `matrix_chernoff_sampling_lower/upper`), SRHT with replacement
   (`measure_norm_uniform_iid_sub_one_le`, same lemmas), SRHT without replacement
   (`measure_norm_uniform_subset_sub_one_le`, its own Laplace-transform argument after
   `integral_traceExp_uniform_subset_le_iid`). Core: the Gram matrix is an average of `k` rank-one
   atoms `u_j u_jᴴ / p_j`, PSD, mean `1`, `lambdaMax ≤ L`; then
   `P(‖mean − 1‖ ≥ ε) ≤ 2 d exp(−ε² k / (3 L))`. Hypotheses if written once: the atoms, `L`, and
   independence or domination of the trace MGF by the i.i.d. one (what sampling without replacement
   supplies). Leverage is `L = d/β`; SRHT gets `L` from flattening, on an event of probability
   `1 − δ/2`, combined by `measureReal_prod_le_measureReal_add_of_sections_le_of_measurableSet`
   (twice).
3. **Trace-moment Markov** (five times): `FiniteLaw.prob_le_norm_le_expect_trace_pow_div` with
   `sparseStack_ose_failure_tail`, the OSNAP copies in `UniformSparseTail.lean`, two
   limited-independence copies, the `q = 1` Frobenius case inline in `CountSketchTail.lean`. Core:
   `P(¬ embedding) ≤ E tr G^{2q} / ε^{2q}` from `specNorm_pow_two_mul_le_trace_pow`. Hypothesis: a
   bound on `∫ tr (G ω ^ (2q))`.
4. **Convex order through a conditional barycenter** (three times): sampling without replacement
   against i.i.d. (`uniform_subset_average_convex_le_iid`), SparseStack and OSNAP against the i.i.d.
   ternary model (`SparseSketch.unconditional_convex_order` and its `UniformSparse` copy). Core: a
   kernel `κ` with `E[Ψ(Y) | X = x] = Φ(x)` gives `E f(Φ X) ≤ E f(Ψ Y)` for convex `f`. Hypotheses:
   kernel, barycenter identity, convexity.
5. **Hollow Gram identity** (three times): `SparseSketch.gramError_eq_hollow`, the `UniformSparse`
   copy, `mul_countSketchGram_sub_one_mul_apply_eq_quadForm`. Core: unit columns and `UᵀU = 1` give
   `G = Σ_{i≠j} (SᵀS)_{ij} u_i u_jᵀ`.
6. **Quadratic-form concentration.** `hanson_wright_mgf` is already shared (sub-Gaussian JL,
   Hutchinson tail, SLQ through Hutchinson); SRHT flattening uses a sibling, the additive chi-square
   tail for directionally sub-Gaussian vectors. Each user re-derives isotropy from its own bundle.
7. **Gaussian block law plus inverse moment** (R1, R2, R5, R6, completion): re-assembled per file.
   Written once: the joint law of `(V₁ᵀΩ, V₂ᵀΩ)` and the moments of `‖Σ₂ Ω₂ Ω₁†‖`.
8. **Finite path laws** (five times): `kaczmarzRowPathPMF`, `SketchProject.pathPMF` and
   `iidPathPMF`, `choleskyHistoryPMF`, `volumeSamplingPMF`, each with its own integral lemmas.
   Kaczmarz is developed apart from sketch-and-project although it is the instance `S = e_i`.
9. **Twins.** `_of_hasLaw` copies of most headlines; a Gaussian and a Rademacher corollary of every
   estimator result; real and complex copies (RPCholesky, volume sampling, angles).

No net argument occurs in `Sketching/`; the only one is in `RandomMatrix/SubGaussian/` (factor
`9^n`), used by no sketch. Decoupling appears only inside the Hanson-Wright proof.

## 5. The sparse block

**Headline.** For `U` with orthonormal columns (`n × d`), `0 < ε ≤ 1`, `0 < δ ≤ 1`, with
`q = sparseMomentOrder d δ = max 1 ⌈log₂(d/δ)⌉`, `s = sparseColumnSparsity q ε < 1356 q/ε` and
`m = s * sparseBlockRows d q ε < 306456 (d + q)/ε²` (`sparse_embedding_parameters`): SparseStack and
uniform exact-`s` columns are `ε`-subspace embeddings with probability at least `1 − δ`
(`measure_sparseStack_embedding_success_ge`, `measure_uniformSparse_embedding_success_ge`). The
source is a manuscript formalised by an external MIT-licensed Lean project (`SparseFockFormal`),
ported file by file. CountSketch (4 files, 21 declarations) is separate.

**A tail in general parameters exists but is internal**: `SparseSketch.concrete_band_bound_le_beta`
with `SparseSketch.sparseStack_failure_tail_of_band_bounds` gives, for all `s > 0`, `b > 1`,
`q > 0`: `P(¬ embedding) ≤ d (3 c_b² β / ε)^{2q}`, `β = (3+√2)(√(D/m) + D/m + (2q+1)/s)`,
`D = d + 2q + 1`, `m = s b`, `c_b = (1 − (1−1/b)^b)⁻¹ < 1.582`; in `FiniteLaw.prob`, for a `Frame`.

**The chain** (no net, no union bound), with the directory that holds each step:

1. Markov on `E tr G^{2q}`; rounding of `q`, `s`, `b`; the `Frame` representation of `U`; the
   endpoints; two side results (`4q`-wise independent hashes suffice; a random frame independent of
   the sketch). `MomentMethod/`, 17 files, 184 declarations.
2. `E tr G_sparse^{2q} ≤ c^{4q} E tr G_iid^{2q}`, the i.i.d. model having entries in `{0, ±√b}`:
   convex order through a martingale coupling, for both laws. `IIDComparison/`, 18 files, 303.
3. `E tr G_iid^k` is a sum of `d` vacuum matrix elements of a multiplication operator in an
   orthonormal product-polynomial basis. `FockModel/`, 10 files, 288.
4. The operator splits into grade-raising, preserving and lowering bands; a ladder iteration gives
   `d (3β)^{2q}` from band norms `≤ β`; the band norms are bounded sector by sector (`Heavy`,
   `Light`, `Mixed`, `Directional`: 44 files, 616) by `3 + √2`. `Bands/`, 57 files, 725.
5. Substrate: a real-weighted finite law with `expect`, `prob`, products, `MatchesUpTo` and a bridge
   `toMeasure`. `FiniteLaw/`, 7 files, 80.

**Reusable theory against bookkeeping.** `docs/SKETCH_INTERFACE.md` classifies the 115 content
files: 95 (24.5k lines) needed for the headline, 16 (2.7k) representation or side results, 4
CountSketch. Five lemmas are reusable in library vocabulary: the trace-moment Markov step; convexity
of `A ↦ tr A^{2q}` (already in `Matrix/Functions/`); convex order through a barycenter; the ladder
bound for a graded operator; the hollow Gram identity. The 62 `FockModel` and `Bands` files
establish one fact for one law, the trace moment of the i.i.d. ternary model. 1632 of the 1702
declarations are in namespace `NLAlib.SparseSketch`; 70 are public.

**Unproved.** Nothing: no `sorry` in `Sketching/`. Fragile instead: `Fin` indices; `Frame` and
`FiniteLaw` duplicate `HasOrthonormalCols` and `Measure`; the public theorems fix the sketch size
and cannot be applied to a sketch of a given size.

**Recommendation.** Port CountSketch now: short, already in the target shape, the `q = 1` instance
of the moment route. For SparseStack and OSNAP, **scaffold**: the two laws as `PMF`s, the two
headlines in tail form through the trace-moment interface of section 10 with the Markov step proved,
one `sorry` per law for the trace-moment bound, constants behind names. Leave the 95-file machinery
for a later private port. Reasons: no consumer uses a sparse embedding; the machinery serves a
single hypothesis; a faithful port rewrites the `FiniteLaw` substrate (about 37 files, by
`docs/SPARSE_INTEGRATION.md`) against a Probability layer not yet designed; and the
general-parameter tail above is the statement worth having.

## 6. Numerical bounds

| quantity | prototype bound | origin |
|---|---|---|
| Gaussian JL tail | `2exp(−k(ε²/4 − ε³/6))` | source (Dasgupta-Gupta) |
| JL dimension | `(ε²/4−ε³/6)⁻¹ log(2N²/δ)`; `48 log N/ε²` | proof's own |
| sub-Gaussian JL | `2exp(−kε²/(256e²K⁴))` | proof's (its Hanson-Wright constant) |
| Gaussian embedding | `k ≥ 18(d + 2log(2/δ))/ε²` | proof's; source has an unnamed `C` |
| Gaussian `σ_min`, `‖G‖` | `√N ∓ (√n + t)`, `e^{−t²/2}` each | source (Davidson-Szarek) |
| matrix Chernoff, sampling | `d e^{−ε²N/(2L)}` lower, `d e^{−ε²N/(3L)}` upper | source (Tropp) |
| leverage sampling | `2d e^{−βkε²/(3d)}`; `k ≥ 3d/(βε²) log(2d/δ)` | source |
| SRHT | `k ≥ 3Lε⁻² log(4d/δ)`, two values of `L` | see below |
| CountSketch | `(d²+d)/(mε²)`; `m ≥ (d²+d)/(δε²)` | source; second moment exact |
| SparseStack, OSNAP | `s < 1356 q/ε`, `m < 306456(d+q)/ε²`; `c* < 1.582`, `3+√2` | manuscript's |
| RSVD, Frobenius | `(1 + k/(t−k−1)) OPT²` | source (HMT 10.5) |
| RSVD, spectral | `(1+√(k/(p−1)))σ_{k+1} + (e√(k+p)/p)(Σ_{j>k}σ_j²)^{1/2}` | source (HMT 10.6) |
| generalized Nyström | `(1 + t/(s−t−1))(1 + k/(t−k−1))` | source; improved below |
| RPCholesky | `k ≥ r/ε + r log(1/(εη))` pivots, factor `1+ε` | source (CETW) |
| Hutchinson | `m ≥ 256e² ε⁻² log(2/δ)` (Hanson-Wright `1/(256e²)`) | proof's; source `8` |
| SLQ | `m ≥ 1024e² ε⁻² log(2/δ)` | proof's (from Hanson-Wright) |
| power, random start | `min(1, (log(2n)+2)/(2q+1))` | source's rate, proof's constants |
| Lanczos, random start | `4((log(2n)+2+log 2)² + 4)/((log 2)² q²)` | same |

Volume sampling (`(k+1) OPT²`), column-row AMM and Kaczmarz (`1 − κ_F⁻²`) carry the source's
constants. Two bounds for one quantity, and how they were named:

- **SRHT row bound.** `srhtSharpRowBound n d δ = (√d + √(8 log(2n/δ)))²` and
  `srhtManuscriptRowBound n d δ = d + √(a d) + a`, `a = 256e² log(4n/δ)`; the first is smaller
  (`srhtSharpRowBound_le_manuscript`). Each has its own theorems, told apart by suffix
  (`..._of_sharp_sample_size`, `..._of_manuscript_sample_size`), doubled again for replacement,
  Walsh and capped width. One improves the other.
- **Sparse embeddings.** CountSketch (`s = 1`, `m ∼ d²/(δε²)`) and SparseStack (`s ∼ log(d/δ)/ε`,
  `m ∼ (d + log(d/δ))/ε²`) are incomparable. Named by distribution.
- **Gaussian against sub-Gaussian** (extreme singular values, JL): weaker hypotheses, worse
  constants; named by hypothesis (`..._of_independent_isotropic_rows`).
- **Chi-square upper tail.** Chernoff form `measureReal_le_sum_sq_le_gaussianVector`, additive form
  `measureReal_sq_norm_ge_add_two_sqrt_mul_add_le`; incomparable, named by the event.
- **Generalized Nyström.** `gn_main_gaussian` has `1 + t/(s−t−1)`;
  `integrable_and_integral_frobSq_rawGeneralizedNystrom_le_rank_factor_gaussian` improves it to
  `1 + q/(s−q−1)`, `q = min (rank A) t`. Named `_rank_factor`.
- **RSVD.** One bound stated four times by the amount of certificate supplied: `rsvd_main`,
  `rsvd_main_gaussian`, `..._residual_le_bestRankFrobSq_gaussian`, `..._gaussianRangeFrame_...`.

Sample sizes are inline expressions in a hypothesis (`hk`, `hsize`, `hrows`); only the SRHT row
bounds and the sparse parameters are named definitions.

## 7. Orthonormal columns

What exists:

- `RandomMatrix/Haar/` (18 declarations): `haarFrameLaw n k hkn` on the bundled type `Stiefel n k`,
  the pushforward of `orthogonalHaar n`; left invariance `haarFrameLaw_map_smul`; uniqueness
  `measure_eq_haarFrameLaw_of_invariant`; `gaussianMatrix_map_canonicalQRFrame`: the
  positive-diagonal QR factor of a tall Gaussian is Haar. Real, `Fin`-indexed. **No consumer uses
  the Haar law.**
- `gaussianRangeFrame A t G`: a measurable orthonormal basis of `range (A G)` with `min (rank A) t`
  columns; it removes the "supplied frame" hypotheses of R1, R2, R6; `hutchPlusPlusBasis`, the same
  for a fixed sketch.

Where an orthonormal random matrix is the natural statement:

- **R1-R6.** Each output depends on the test matrix only through `range Ω`, so each theorem holds
  verbatim for a Haar test matrix. The prototype states them for `HasLaw Ω gaussianMatrix` only.
  Consumers want a transfer lemma (a measurable function of `range Ω` has the same expectation under
  Gaussian and Haar), or the block-law and inverse-moment facts for both laws.
- **Random-start power and Lanczos (E6).** The Rayleigh quotient is scale-invariant and the source
  (Kuczyński-Woźniakowski) takes a start uniform on the sphere, the `k = 1` Haar frame. The
  prototype proves the Gaussian form; the sphere form is a missing corollary.
- **JL.** Dasgupta-Gupta Lemma 2.2 is about projecting onto a random subspace (the docstring of
  `jl_distributional` says so); the prototype proved the Gaussian form instead.
- **Trace estimation.** A probe uniform on the sphere of radius `√n` is isotropic, so E1 covers it;
  E2 and E3 do not (independent coordinates). E4 takes any orthonormal `Q(S)`.

A Haar sketch `S = √(n/k) Qᵀ`, `Q` an `n × k` Haar frame, would satisfy (none proved): exact
isotropy `E[SᵀS] = 1`; `specNorm S = √(n/k)` surely, which a Gaussian lacks; JL with the
Dasgupta-Gupta tail; a subspace embedding for a fixed `U` with Gaussian-type parameters, since
`Q = G (GᵀG)^{-1/2}` reduces the singular values of `QᵀU` to ratios of the Gaussian deviation
bounds.

## 8. Dependencies

Each number is the count of files in `Sketching/`, `LowRank/`, `Estimation/` whose source mentions
the name. `Krylov/` and `Solvers/` use nothing from `Probability/` or `RandomMatrix/`; the sparse
block uses only the Rademacher quadratic-form moments (CountSketch).

- **Laws.** `gaussianMatrix` 13 (Sketching 2, LowRank 7, Estimation 4); `rademacherVector` 11;
  `gaussianVector` 5; `rademacherMeasure` 3; `finiteSamplingLaw` 3; `gaussianRangeFrame` 3.
- **Coordinates of a standard vector.** `HasLaw.hasLaw_eval_gaussianReal` 3,
  `HasLaw.iIndepFun_eval_of_gaussianVector` 3, the Rademacher analogues 4 and 3; per law, 2 files
  each: moments of orders 1, 2, 4 with integrability; the sub-Gaussian MGF of a coordinate 1;
  `ae_forall_sq_eq_one_rademacherVector` 2.
- **Scalar tails.** Chi-square Chernoff `measureReal_le_sum_sq_le_gaussianVector`,
  `measureReal_sum_sq_le_one_sub_mul_le_gaussianVector` 1 (JL); Laurent-Massart for directionally
  sub-Gaussian vectors `measureReal_sq_norm_ge_add_two_sqrt_mul_add_le` 1 and
  `hasSubgaussianMGF_sum_mul_rademacher` 1 (SRHT).
- **Quadratic forms.** `hanson_wright_mgf` 1 (the Hutchinson tail, on which SLQ depends);
  `integral_quadForm_eq_trace` 3; `variance_quadForm` 2 and its two fourth-moment specialisations 1;
  `integral_quadForm_sq_rademacherVector_of_diag_zero` 1 (CountSketch).
- **Matrix concentration.** `matrix_chernoff_sampling_lower`, `matrix_chernoff_sampling_upper` 2
  each. For sampling without replacement, 1 file each:
  `measureReal_lambdaMax_ge_le_exp_mul_integral_traceExp` and its `lambdaMin` twin,
  `trace_cgf_subadditivity`, `chernoff_matrix_mgf_cgf_le`.
- **Gaussian rotation invariance.** `hasLaw_gaussianMatrix_mul_right` 1,
  `gaussianMatrix_map_mulVec_of_dotProduct_self_eq_one` 1, `hasLaw_gaussianMatrix_block_of_hasLaw`
  2, `gaussianMatrix_indepFun_block_of_hasLaw` 2,
  `measurePreserving_orthonormalBasis_repr_pi_gaussianReal` 1.
- **Gaussian extreme singular values.** `measure_sigmaMin_le_sqrt_sub_sqrt_sub_le_gaussianMatrix`,
  `measure_sqrt_add_sqrt_add_le_specNorm_le_gaussianMatrix` 1 (behind them Gordon, Sudakov-Fernique,
  Gaussian Lipschitz concentration through log-Sobolev).
- **Gaussian inverse moments.** `integrable_and_integral_frobSq_pinvR_gaussianMatrix` 2,
  `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le` 1 (behind them about 30 files of
  `InverseMoments/` and `Wishart/`); conditioning `integral_frobSq_mul_block_mul_pinvR_block`,
  `integral_frobSq_pinvL_block_mul_block_mul` 1; Chevet
  `integrable_and_integral_specNorm_mul_gaussianMatrix_mul_le` 1.
- **Gaussian, other.** Almost-sure rank `ae_rank_mul_gaussian_eq_min` 3,
  `gaussianMatrix_ae_isUnit_mul_transpose` 1; log-overlap moments
  `integrable_and_integral_log_sum_div_sq_pi_gaussianReal_le` 1 (random start).

Proved but outside the import closure of every consumer (47 of 170 leaf modules): 16 of the 33
matrix-concentration modules (every matrix Bernstein theorem, the Gaussian and Rademacher matrix
series), `McDiarmid`, `Concentration/Basic/Net`, `RandomMatrix/Haar`, `RandomMatrix/SubGaussian`,
`SmallBall`, the Gaussian AMM identity, and the Isserlis, Wick and Khintchine moment files.

## 9. Unproved and fragile material

- **`sorry`.** None in `Sketching/`, `Estimation/`, `Solvers/`, `Probability/`, `RandomMatrix/`.
  `LowRank/`: 2, deterministic, in `Cholesky/PartialCholesky.lean`
  (`partialCholeskyFactor_mul_transpose_eq_nystrom`, `partialCholeskyResidual_eq_sub_nystrom`).
  `Krylov/`: 25, deterministic (`CGRecurrence` 8, `LanczosRecurrence` 9, `Bidiagonalization` 3,
  `QRAlgorithm` 4, `PowerMethod` 1).
- **Files over 500 lines.** None in `Sketching/` (largest 444), `LowRank/`, `Estimation/`,
  `Solvers/`. In `Probability/` and `RandomMatrix/`, nine: `ChiSquare` 772, `SpectralSecondMoment`
  710, `GordonMinimax` 688, `Gordon` 668, `LogSobolevHerbst` 581, `OrnsteinUhlenbeckEntropy` 542,
  `CenteredSquare` 523, `EvenMoments` 517, `LogSobolevOneDim` 509. Also `Krylov/Spectral/Ritz` 747.
- **Docstrings admitting a gap from the source's constant:** the rows marked "proof's" in section 6,
  and `jl_lemma` (ordered pairs, a factor 2; the source's dimension is `4(ε²/2−ε³/3)⁻¹ log N`).
- **Statements weaker than their name.** The Gaussian embedding bounds an outer measure (the event
  is never shown measurable). Nyström is proved for the trace against `bestRankFrobSq F k` of a
  factor, not in nuclear norm. Hutch++ and XTrace have unbiasedness only. Atlas tags `(partial)`:
  `slq-error`, `rpcholesky`, `volume-sampling`, CountSketch under `sparse-ose`.
- **Unused.** The AMM theorem and all of `Properties/JL` have no caller;
  `Bands/Light/ZeroBlock.lean` is dead code (per `docs/SKETCH_INTERFACE.md`).

## 10. Recommendations for the design

**Interfaces.** Deterministic predicates over `𝕜`; probabilistic ones as tails `μ.real {…} ≤ δ`.

1. `IsSubspaceEmbedding S U ε`: the Loewner sandwich `(1 − ε) • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U)` and
   `(S * U)ᴴ * (S * U) ≤ (1 + ε) • (Uᴴ * U)` (§5.3's spectral equivalence), any `U`, any `Fintype`
   indices. API: `.mono`, invariance under `U ↦ U * C`, the norm form, the singular-value form, and
   for `HasOrthonormalCols U` the Gram form. Prove the Gaussian and Haar theorems first with
   separate lower and upper constants: the prototype's `3 * a ≤ ε` step and `ε ≤ 1` side conditions
   come from a symmetric `ε` forced too early.
2. `HasSubspaceEmbedding S U ε δ μ := μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U ε} ≤ δ` (§5.4's
   `HasOSE`): a fixed subspace. Leverage sampling proves it; sketch-and-solve consumes it.
3. `IsObliviousSubspaceEmbedding S d ε δ μ := ∀ U : Matrix m (Fin d) 𝕜, HasSubspaceEmbedding …` (no
   orthonormality needed, by basis invariance). Gaussian, Haar, SRHT, CountSketch, sparse.
4. `HasJLMoment S p ε δ μ`: for every unit `x`, `∫ |‖S ω x‖² − 1| ^ p ∂μ ≤ ε ^ p * δ`. It gives
   distributional JL (Markov), the JL lemma (union bound) and AMM (`p = 2`), replacing the three
   inline shapes; `HasJLTail S ε δ μ` is its consequence and the conclusion for Gaussian and Haar.
5. `HasGramTraceMoment S d q B μ`: for orthonormal `U` with `d` columns, `tr (G ^ (2 * q))` is
   integrable with integral at most `B`. One lemma turns it into 3 with `δ = B / ε ^ (2 * q)`.
   CountSketch is `q = 1`; the sparse laws are general `q`.
6. `IsIsotropic z μ`: `∫ z i * star (z j) ∂μ = if i = j then 1 else 0`, replacing the three isotropy
   bundles; variance and tail theorems add `iIndepFun` and a moment hypothesis.
7. For row sampling, a theorem rather than an interface: an average of `k` atoms `u_j u_jᴴ / p_j`
   with `‖u_j‖² ≤ L p_j`, drawn i.i.d. or as a uniform subset, satisfies 2 with
   `δ = 2 d exp(−ε² k / (3 L))`. Leverage sampling and both SRHTs become corollaries.
8. For range finding, keep the deterministic theorem (any `Ω`, any orthonormal `Q` containing
   `range (A * Ω)`) and state the probabilistic layer as a bound on
   `∫ ‖Σ₂ * (V₂ᴴ * Ω) * pinv (V₁ᴴ * Ω)‖²` with a named factor, for a test matrix that is Gaussian or
   has Haar orthonormal columns; other test matrices enter through 2 and 6 (HMT §11).

**Distributions.** Gaussian: 1-4, 8. Haar (`HasOrthonormalCols` surely, law invariant under unitary
multiplication; defined on matrices, with `HasLaw` for the QR or polar factor of a Gaussian, not on
a bundled `Stiefel` type): 3, 4, 6, 8, and the transfer lemma of section 7. Sub-Gaussian rows: 4,
and 3 through the existing singular-value bound. CountSketch: 5, hence 3. SRHT: 7, hence 3. Leverage
sampling: 7, hence 2. SparseStack, OSNAP: 5, scaffolded.

**Headline form.** Tail first, in the law's natural parameters, for `HasLaw X ν μ`: Gaussian
`2 exp(−t²/2)` at distortion `(√d + t)/√k`; sampling `2 d exp(−ε² k / (3 L))`; moment route
`B(d, q, m, s) / ε^{2q}`. The "`k ≥ …` suffices" corollary takes the size as a named definition
(`gaussianEmbeddingDim d ε δ`, `srhtRowBound n d δ`, `sparseEmbeddingSparsity`, …) whose docstring
records the source's value. An incomparable or improved bound is then a second tail theorem about
the same predicate; a named size changes without a rename.

**Do not port.** The `FiniteLaw` layer and `Frame`; the `MainConclusions` bundles; `_of_hasLaw` and
finite-index transport twins; the SRHT manuscript, capped-width and Walsh duplicates (one tail,
Walsh as an instance); real and complex twins; the Gaussian-only hypothesis bundles of `rsvd_main`
and `gn_main`; Kaczmarz as a development apart from sketch-and-project; the `Bands`, `FockModel` and
`IIDComparison` machinery until a consumer or a maintainer calls for it.