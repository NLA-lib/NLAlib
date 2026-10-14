# Probability round: final report

Date: 2026-10-14. Branch `scaffold`, local commits only, nothing pushed.

This is the report that `docs/PORT_PROBABILITY.md` §7 asks for: what the Probability and
RandomMatrix layers offer, what the orchestrator decided without the maintainer, and what is
open. The per-stage detail is in the design notes `docs/design/Probability-P0.md` to
`Probability-P7.md` (with P5a to P5d) and `docs/design/RandomMatrix-R1.md` to `RandomMatrix-R5.md`;
each ends with its review amendments (§8); P0 to P4 also have a stage report, and the later
stages record the proof round's changes in §8.

## 1. Summary

The round built the probabilistic foundation the sketching and low-rank layers will prove on: six
property interfaces, concentration stated once against them, and the standard laws (Gaussian
scalars, vectors and matrices, Rademacher, finite sampling, Haar frames, the uniform sphere) shown
to satisfy them. Every statement is proved; `NLAlibScaffold/` is empty. The work ran from commit
`b851677` (measurability moved to the Probability layer) through `0aa65e5` (wrap-up) to `c22904e`
(the last ports, §6.1), 65 commits on 2026-10-14, followed by the closing commit with this report.

- `NLAlib/Probability/` and `NLAlib/RandomMatrix/`: 61 files, 19,396 lines. With the 13 new
  `ForMathlib` files and `Matrix/Factorizations/PolarFrames.lean`, about 20,600 lines and about
  500 public declarations (27 definitions, structures or classes), plus about 410 private helpers.
  All modules are registered in `NLAlib.lean`; no `sorry` anywhere.
- Final stage check (`scripts/stage_check.sh`, after the closing changes): 218 proved modules (0 not yet), build with 0
  warnings, audit 5001 declarations with 0 violations, lint 0 errors in 3645 declarations (14
  linters), 41 bibliography keys with 0 problems. The lines are quoted in §7.
- Ledger: the completeness pass (`b5ce6e9`) leaves 0 of the prototype's 921 public
  `Probability/` and `RandomMatrix/` declarations unaccounted for. `docs/port/ledger.json` has
  938 entries tagged with a round stage: 245 with a target, 693 with a reason and no target. By
  stage (entries, with target): P0 13 (7), P1 41 (17), P2 59 (31), P3 114 (18), P4 43 (15),
  P5a 65 (29), P5b 6 (6), P5c 59 (10), P5d 49 (9), P6 55 (4), P7 15 (5), R1 68 (35), R2 34 (7),
  R3 41 (14), R4 257 (32; most of the Wishart and hard-edge cut is booked here), R5 19 (6). The
  completeness pass itself classified its 414 entries as 36 mapped, 15 in Mathlib, 69 reached by
  another route, 273 cut, 21 not ported; all but the two sub-Gaussian Johnson–Lindenstrauss
  entries were ported at the end of the round (§6.1).

| Stage | Headline results | Files |
|---|---|---|
| P0 | Product laws and their coordinates; Markov, power Markov, Chebyshev; moments from tails; isotropy and Hutchinson's mean `E x*Ax = tr A`; matrix integrals with trace, Loewner and positivity API | `Probability/{Law,Tail,Isotropic,MatrixIntegral}`, `Measurability/Matrix` |
| P1 | Sub-Gaussian API (proxy monotonicity, moments, maxima, weighted sums); sub-exponential interface, its tails and Bernstein's inequality for sums; centred square of a sub-Gaussian is sub-exponential `(32c², 4c)` | `SubGaussian/{Basic,Moments,Square}`, `SubExponential/{Basic,Tail}` |
| P2 | Standard Gaussian vector (an `IsGaussian` instance), Rademacher, finite sampling laws, with exact moments (`m₄ = 3`, `m₄ = 1`) and sub-Gaussian proxy 1 | `Distributions/{Gaussian,Rademacher,Sampling}` |
| P3 | Sub-Gaussian vectors over `𝕜`; norm tail (Hsu, Kakade and Zhang); χ² MGF, Laurent–Massart lower tail and the small ball `P(‖X‖² ≤ u) ≤ (e u / N)^{N/2}`; Hutchinson's variance over `𝕜` from moment parameters; Hanson–Wright with constant `1/196` | `SubGaussianVector/{Basic,Norm}`, `Distributions/ChiSquare`, `QuadraticForm/{Moments,HansonWright,HansonWright/*}` |
| P4 | Entropy, tensorization, Herbst's argument; Gross's log-Sobolev inequality on any Euclidean space; Gaussian concentration of Lipschitz functions with the sharp proxy `L²`; every log-Sobolev inequality extended to finite-energy `C¹` functions, with `g² log g²` integrable | `Entropy`, `EntropyTensorization`, `LogSobolev`, `Distributions/{GaussianLogSobolev,GaussianLogSobolevOneDim,GaussianConcentration}` |
| P5a | Matrix Laplace transform method, Lieb subadditivity, master bound; matrix Chernoff (tails, means, two-sided around `1`), Bernstein (Hermitian, rectangular, scalar corollary), sub-Gaussian matrix series; variance additivity `E (∑ Xₖ)² = ∑ E Xₖ²` for independent centred matrices | `MatrixConcentration/{Laplace,Subadditivity,MGFBound,Chernoff,ChernoffSum,Bernstein,Series,Variance}` |
| P5b | Generalised Laplace bound `P(t ≤ λ_max Y) ≤ E tr ψ(Y) / ψ(t)`; Chernoff and Bernstein in the intrinsic dimension, tails and means (mean constant 8) | `MatrixConcentration/IntrinsicDimension`, `Laplace` |
| P5c | `E Y² = ∑ Aᵢ²` for isotropic coefficients; noncommutative Khintchine `E tr Y^{2p} ≤ (2p-1)^p tr (∑ Aᵢ²)^p` for Gaussian and Rademacher series, from one law-free recursion | `MatrixConcentration/Khintchine` |
| P5d | Matrix conditional expectations; conditional Lieb (also for an `m`-measurable offset); Ville's inequality; trace supermartingale; matrix Freedman (Hermitian and rectangular) | `MatrixConditionalExpectation`, `MatrixConcentration/{ConditionalMGFBound,Freedman}`, two `ForMathlib` files |
| P6 | Stein's identity in covariance form (polynomial-growth class); Gaussian interpolation (Kahane); Sudakov–Fernique; Gordon's min-max inequality; `E ‖A X‖ ≤ ‖A‖_F` | `Distributions/{GaussianIntegrationByParts,GaussianComparison}`, additions to `Isotropic`, `ChiSquareMoments` |
| P7 | ψ₂ and ψ₁ (Orlicz) conditions imply the sub-Gaussian and sub-exponential interfaces; entropy of `exp (s g)` for bounded `g`; bounded differences and McDiarmid | `Orlicz`, `BoundedDifferences`, addition to `Entropy` |
| R1 | `gaussianMatrix m n`; rows, columns, flattening; two-sided orthogonal invariance; independence of orthogonal blocks; a.s. rank `rank (A G) = min (rank A) k`; Frobenius-Lipschitz concentration | `RandomMatrix/Gaussian/{Basic,Invariance,Rank,Concentration}` |
| R2 | `E ‖S X T‖_F² = ‖S‖_F² ‖T‖_F²` for isotropic entries, also with `S`, `T` random and independent; the random-start log-overlap `log (‖X‖² / (u ⬝ᵥ X)²)` of a Gaussian vector with a unit vector: tail, mean `≤ log (2N) + 2`, second moment | `RandomMatrix/Gaussian/Moments`, `Distributions/GaussianLogOverlap` |
| R3 | Chevet's inequality; `E ‖G‖ ≤ √N + √n` and `√N - √n ≤ E σ_min(G)`; Gaussian deviation tails and Loewner sandwich on `Gᴴ G`; the same for independent isotropic sub-Gaussian rows (constant 24) | `RandomMatrix/Gaussian/{SpectralNorm,ExtremeSingularValues}`, `RandomMatrix/SubGaussian/ExtremeSingularValues` |
| R4 | Real moments of χ²; `E (G Gᴴ)⁻¹ = (k - r - 1)⁻¹ • 1`, `E ‖G†‖_F² = r/(k - r - 1)`, Frobenius fourth moment, spectral moments `E ‖G†‖^q`; the range finder's block moments | `Distributions/ChiSquareMoments`, `RandomMatrix/Gaussian/{InverseMoments,InverseMoments/Spectral,BlockMoments}` |
| R5 | `haarFrame n k` (polar factor of a Gaussian); two-sided invariance; characterization by left invariance; QR law; Haar measure bridge; `E [Q B Qᴴ] = (tr B / n) • 1`; column law `uniformSphereVector`; Gaussian–Haar transfer of `rangeProjector (A Ω)` | `RandomMatrix/{UnitaryInvariance,Haar/{Basic,Uniqueness,Moments,Transfer}}`, `Matrix/Factorizations/PolarFrames` |

## 2. What a user gets

Conventions every statement follows (brief §2, D2 and D3): a random variable `X : Ω → E` with
Mathlib's `HasLaw X ν μ` (the measure form is `HasLaw.id`, no twins); i.i.d. as `HasLaw X
(Measure.pi fun _ => ν) μ`; tails in failure form `μ.real {ω | t ≤ f ω} ≤ …` with non-strict
events; every expectation upper bound beside an `integrable_…` companion; proxies in `ℝ≥0`.
Matrix expectations are Mathlib's `∫` and `μ[· | m]` under `open scoped Matrix.Norms.L2Operator`
(deviation 13); statements never mention the norm and carry `[DecidableEq]` on the column index.

### 2.1 Interfaces

| Interface | Field | How it is used |
|---|---|---|
| `HasSubgaussianMGF X c μ` (Mathlib) | `ℝ` | Instances: `hasSubgaussianMGF_of_hasLaw_gaussianReal`, `…_rademacherMeasure`, ψ₂ bridge, Lipschitz images of a Gaussian, bounded differences. API added: `mono`, `const_mul'`, `integral_eq_zero`, `integral_sq_le`, `integral_abs_rpow_le`, `measure_le_le`, `measure_abs_ge_le`, `sum_const_mul_of_iIndepFun`, maxima `measure_iSup_ge_le`, `integral_iSup_le`, `integral_iSup_abs_le` |
| `HasSubexponentialMGF X v b μ` | `ℝ` | MGF bound on the window `b * \|l\| < 1`; `b = 0` is the sub-Gaussian case (`hasSubexponentialMGF_zero_iff_hasSubgaussianMGF`). API: `congr`, `mono`, `neg`, `const_mul`, `add` (no independence), `add_of_indepFun`, `sum_of_iIndepFun`, tails `measure_ge_le`, `measure_abs_ge_le`, Bernstein `measure_sum_ge_le_of_iIndepFun`. Instances: centred squares, the off-diagonal chaos, ψ₁ bridge |
| `IsSubgaussianVector X c μ` | `𝕜` | every `re (u ⬝ᵥ X)` has proxy `c ‖u‖²`. Constructors `of_iIndepFun`, `mulVec`, Gaussian and Rademacher vectors (proxy 1), law transport `HasLaw.isSubgaussianVector_iff`; consumers: norm tails, Hanson–Wright, R3 rows |
| `IsIsotropic X μ` | `𝕜` | uncentred, entrywise `E X Xᴴ = 1`. Constructors `of_iIndepFun`, Gaussian, Rademacher, `√n` times a Haar column; `HasLaw.isIsotropic_iff`. Consumers: Hutchinson `integral_quadForm`, `integral_norm_mulVec_sq`, `integral_norm_mulVec_le`, R2, Khintchine's second moment, `IsIsotropic.integral_vecMulVec` |
| `HasMatrixMGFBound X g A s μ` | `𝕜` | a.s. Hermitian `X`, `∫ exp (θ • X) ≤ exp (g θ • A)` for `θ ∈ s`, with integrability. Constructors `hasMatrixMGFBound_of_posSemidef_of_le` (Chernoff), `hasMatrixMGFBound_of_integral_eq_zero_of_le` (Bernstein), `hasMatrixMGFBound_smul_of_hasSubgaussianMGF` (series). Master: `integral_re_trace_exp_sum_le`, `measure_eigenvalue_zero_sum_ge_le` |
| `HasCondMatrixMGFBound m hm X g A s μ` | `𝕜` | conditional form with `μ[· \| m]`, per `θ` almost surely, `m`-measurable bound `A`. Constructors `hasCondMatrixMGFBound_of_condExp_eq_zero_of_le` (conditional Bernstein), `hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF` (bridge from Mathlib). Consumer: `supermartingale_re_trace_exp`, Freedman |
| `HasLogSobolev ν c` | real `E` | on a law over a finite-dimensional real inner product space; `hasLogSobolev_stdGaussian`; `HasLogSobolev.hasSubgaussianMGF_sub_integral` (Herbst for Lipschitz `f`, proxy `c L²`) |
| `IsLeftUnitarilyInvariant ν`, `IsRightUnitarilyInvariant ν` | `𝕜` | classes on a measure on `Matrix n k 𝕜`; bridges `isLeftUnitarilyInvariant_iff` to `Matrix.unitaryGroup`; instances for `gaussianMatrix`, `haarFrame`; API `hasLaw_const_mul_of_isLeftUnitarilyInvariant`, `integral_eq_zero_of_isLeftUnitarilyInvariant`, `integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant` |

Laws, all real this round (D4): `gaussianVector n` (an `abbrev` for `Measure.pi`, with
`isGaussian_gaussianVector`), `rademacherMeasure`, `rademacherVector`, `samplingMeasure p`,
`gaussianMatrix m n` (an `abbrev`: rows are `gaussianVector n`, with explicit instances),
`haarFrame n k := (gaussianMatrix n k).map polarFactor` (a `def`; for `card n < card k` it has
orthonormal rows), `uniformSphereVector n` (the law of `g / ‖g‖`, a `def`). Random frames as
hypotheses are three Mathlib-form hypotheses (`Measurable Q`, `∀ᵐ ω, HasOrthonormalCols (Q ω)`,
`IndepFun Q Ψ μ`), bundled nowhere.

### 2.2 Main theorems by topic

**Tails and moments (P0).** `measureReal_ge_le_integral_div` (Markov),
`measureReal_abs_ge_le_integral_rpow_div`, `measureReal_ge_le_variance_div_sq` (Chebyshev),
`measureReal_abs_ge_le_add`, `integral_le_of_measureReal_ge_le`; `hasLaw_pi_pi_iff`,
`HasLaw.iIndepFun_entry`.

**Scalar concentration (P1, P7).** `HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun`
(Bernstein), `HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral`,
`HasSubgaussianMGF.integral_iSup_le` (maximal inequality); bounded-variable Bernstein
`measureReal_sum_ge_le_bernstein` (the `1 × 1` case of matrix Bernstein, stated in scalar terms);
`hasSubgaussianMGF_of_integral_exp_sq_div_le_two` and
`hasSubexponentialMGF_of_integral_exp_abs_div_le_two` (Orlicz bridges, with centred forms);
`hasSubgaussianMGF_sub_integral_of_abs_update_sub_le` (bounded differences, proxy `∑ cᵢ² / 4`),
`measureReal_sub_integral_ge_le_mcdiarmid`.

**Vectors and quadratic forms (P3, R2, R4).** `IsSubgaussianVector.measure_norm_sq_ge_le`,
`measureReal_abs_norm_sq_sub_integral_ge_le`; `measureReal_norm_sq_le_of_hasLaw_gaussianVector`
(Laurent–Massart); `measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector` (χ² small ball);
`integral_norm_sq_rpow_of_hasLaw_gaussianVector` (all real χ² moments);
`measureReal_log_norm_sq_div_sq_ge_le_of_hasLaw_gaussianVector`,
`integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector` and
`integral_log_norm_sq_div_sq_sq_le_of_hasLaw_gaussianVector` (random-start log-overlap with any
unit vector `u`: tail, mean, second moment);
`variance_quadForm_of_isHermitian` and its Gaussian and Rademacher corollaries (Hutchinson);
`measureReal_abs_quadForm_sub_integral_ge_le` and the one-sided forms (Hanson–Wright).

**Gaussian analysis (P4, P6).** `entropy_pi_le_sum`, `hasSubgaussianMGF_sub_integral_of_entropy_le`
(Herbst); `entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian` (Gross);
`HasLogSobolev.integrable_sq_mul_log_sq` and `HasLogSobolev.entropy_sq_le_of_integrable` (the
inequality for finite-energy `C¹` functions under any `HasLogSobolev` law);
`hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_stdGaussian` and the `gaussianVector`
form; `integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw` (Stein);
`integral_comp_le_integral_comp_of_hasGaussianLaw` (interpolation);
`integral_iSup_le_integral_iSup_of_hasGaussianLaw` (Sudakov–Fernique);
`integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw` (Gordon).

**Matrix concentration (P5a to P5d).** Variance additivity `integral_sum_sq_of_iIndepFun`,
`integral_sum_mul_sum_of_iIndepFun`, `integral_sum_sub_integral_sq_of_iIndepFun`
(`MatrixConcentration/Variance.lean`); Chernoff `measureReal_eigenvalue_zero_sum_ge_le_chernoff`,
`measureReal_eigenvalue_sum_le_le_chernoff`, the means, and `measureReal_specNorm_sum_sub_one_ge_le`
(`2 d e^{-ε²/(3L)}` when `∑ E Xₖ = 1`); the trace forms `…_of_integral_le` for a single matrix
(for sampling without replacement); Bernstein `measureReal_eigenvalue_zero_sum_ge_le_bernstein`,
`measureReal_specNorm_sum_ge_le_bernstein` (rectangular, by the dilation), means; series
`measureReal_specNorm_sum_smul_ge_le`; intrinsic forms `…_chernoff_intrinsicDim`,
`…_bernstein_intrinsicDim`; generalised Laplace
`measureReal_eigenvalue_zero_ge_le_integral_re_trace_cfc_div`; Khintchine
`integral_re_trace_sum_smul_pow_le_of_hasLaw_gaussianVector` and `…_rademacherVector`, the
law-free `integral_re_trace_pow_le_of_recursion`; conditional `Matrix.condExp_apply`,
`Matrix.ae_posSemidef_condExp`, `condExp_re_trace_exp_add_le` (conditional Lieb),
`MeasureTheory.Supermartingale.measure_exists_ge_le` (Ville),
`measureReal_exists_eigenvalue_zero_sum_ge_le_freedman` and the rectangular
`measureReal_exists_specNorm_sum_ge_le_freedman`.

**Gaussian matrices (R1 to R4).** `hasLaw_mul_mul_of_hasLaw_gaussianMatrix`,
`indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`, `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`,
`ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix`,
`hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianMatrix`;
`integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix` (and `…_of_indepFun`);
`integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix` (Chevet),
`integral_specNorm_le_of_hasLaw_gaussianMatrix`, `le_integral_singularValues_of_hasLaw_gaussianMatrix`,
`measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix`, the Gram forms
`measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix` and its upper twin;
`measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_isSubgaussianVector`
(sub-Gaussian rows); `integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix`,
`integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`, `integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`,
`integral_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix` (HMT's block step),
`integral_specNorm_mul_mul_pinv_le_of_hasLaw_gaussianMatrix` (HMT Theorem 10.6, two forms).

**Haar frames (R5).** `hasLaw_polarFactor_of_hasLaw_gaussianMatrix`,
`hasLaw_haarFrame_of_isLeftUnitarilyInvariant` (characterization),
`hasLaw_gramSchmidtQ_of_hasLaw_gaussianMatrix` (QR), `haarFrame_eq_map_haarMeasure`,
`uniformSphereVector_eq_map_toSphere`, `hasLaw_col_of_hasLaw_haarFrame`,
`integral_mul_mul_conjTranspose_of_hasLaw_haarFrame`, `integral_apply_sq_of_hasLaw_haarFrame`,
`isIsotropic_sqrt_mul_col_of_hasLaw_haarFrame`, `hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`
and `integral_comp_rangeProjector_mul_of_hasLaw_haarFrame` (transfer: a function of
`range (A Ω)` has the same law for Gaussian and Haar `Ω`), `ae_rank_mul_eq_min_of_hasLaw_haarFrame`.

General facts added to `ForMathlib`: resampling one coordinate of a product measure
(`MeasureTheory/Constructions/PiUpdate`), Lipschitz-preserving smooth approximation
(`Analysis/Calculus/BumpFunction/Convolution`), Jensen on a non-closed convex set
(`Analysis/Convex/Integral`), conditional Jensen for concave maps (`ConditionalExpectation/CondJensen`),
optional stopping for Ville (`Probability/Martingale/OptionalStopping`), the scoped `NormedSpace ℝ`
on matrices (`Analysis/CStarAlgebra/Matrix`), compactness of the unitary group
(`LinearAlgebra/UnitaryGroup`), Hessian lemmas, block sums, `|s log s| ≤ s² + 1` and `|G s log (G s)| ≤ |G log G| + G`, a square-root
lemma, the sine truncation `c sin (y / c)` (`Analysis/SpecialFunctions/Trigonometric/Sinc`).

## 3. Numerical constants

Rule (`CONTRIBUTING.md` §5.2, "Numerical bounds"): the source's small constant, when reached, is
written in the statement; any other is an `irreducible_def` with a one-sided comparison as its
only API.

Named constants:

| Constant | Value proved | API | Source or prototype |
|---|---|---|---|
| `hansonWrightConstant` | `1/196` | `hansonWrightConstant_pos`, `le_hansonWrightConstant : 1/196 ≤ …` | unspecified in Vershynin 2018 Theorem 6.2.1 and Rudelson–Vershynin 2013; prototype `1/(256 e²)` ≈ `1/1892`, about ten times smaller |
| `intrinsicBernsteinMeanConstant` | `8` | `_pos`, `_le : … ≤ 8` | unspecified in Tropp 2015 Theorem 7.3.1; prototype `20` |
| `subgaussianRowsConstant` | `24` | `_pos`, `_le : … ≤ 24` | unspecified in Vershynin 2018 Theorem 4.6.1 (`C K²`); prototype had two, `32 e K² √(log 9)` and `1024 e² K⁴`; the proof needs `16 √(log 9) ≈ 23.72`, a thin margin |
| `psiTwoSubgaussianConstant` | `1 + log 2` (≈ 1.69) | `_le : … ≤ 2` | unspecified in Vershynin 2018 Proposition 2.5.2 |
| `psiOneSubexponentialVarianceConstant` | `32/e²` (≈ 4.33) | `_le : … ≤ 5` | unspecified in Vershynin 2018 Proposition 2.7.1 |
| `psiOneSubexponentialScaleConstant` | `2` | `_le : … ≤ 2` | as above |

Constants written in statements, because the proof reaches the source's:
- Centred square of a sub-Gaussian: `(32 c², 4 c)` (Honorio and Jaakkola 2014; locator
  unchecked). The skeleton had two named constants; they were removed when the proof reached these.
- Hanson–Wright's ingredients: off-diagonal chaos `(18 c² ‖A‖_F², 12 c ‖A‖)`, whole form
  `(98 c² ‖A‖_F², 28 c ‖A‖)`, combined without independence by convexity (weights `4/7`, `3/7`).
- Matrix Chernoff, Bernstein, series and Freedman: Tropp's (Bernstein and Freedman
  `exp (-(t²/2) / (v + L t / 3))`), with the dimension factor `d`; Chernoff means `(e - 1)` and
  `(1 - e⁻¹)`; the intrinsic forms `2 intdim` (Chernoff) and `4 intdim` (Bernstein).
- Noncommutative Khintchine: `(2p - 1)^p` (Buchholz's `(2p - 1)!!` would be a dominated
  improvement of another shape).
- Gaussian Lipschitz concentration: proxy `L²`, sharp. Bounded differences: proxy `∑ cᵢ² / 4`,
  McDiarmid's `exp (-2 t² / ∑ cᵢ²)`, sharp.
- R4: `E ‖G†‖^q ≤ (e √((k + r - 1)/2) / (k - r))^q`, which improves the source's `e √k / (k - r)`
  (Halko, Martinsson and Tropp) whenever `r ≤ k + 1`; the source's form is kept as a corollary
  under a name that spells its right side. The constant `√((k + r - 1)/2)` has no source; it is
  what the probe proof reaches (it was the prototype's `_sharp` bound).
- R3: Gordon's `√N ± √n` exactly; the Gaussian tails have proxy 1.

## 4. Decisions taken by the orchestrator without the maintainer

The maintainer decided D1 to D10 (D4 revised, D10 amended to `L2Operator` from P0 §7 Q1) and
passed the P3 checkpoint. Everything below was decided by the orchestrator and recorded in the
note cited. **Costly** marks a decision whose reversal would touch many statements or the next
round. Three were of the brief's §2 kind (they fix an interface) and were decided without a stop,
against the approval rule: P5d Q1, P6 Q1 and R5 Q1. They are marked **§2 kind**.

Interfaces and carriers:
1. **§2 kind, costly but local to P5d.** P5d Q1: `HasCondMatrixMGFBound` is spelled with
   `μ[· | m]`, per `θ` almost surely, not with Mathlib's `condExpKernel` (deviation 17). Reason: no
   `[StandardBorelSpace Ω]` on every Freedman statement, and it is the form the proofs consume. Its
   only consumers are P5d's supermartingale and Freedman; the bridge from `HasCondSubgaussianMGF`
   is proved.
2. **§2 kind, costly.** R5 Q1: `IsLeftUnitarilyInvariant`, `IsRightUnitarilyInvariant` introduced
   now, as classes on a measure over `𝕜`, left and right separately (deviation 14). Reason: §5.4
   forbids the raw condition in statements; Mathlib's `SMulInvariantMeasure` needs a global
   `MulAction` on rectangular matrices. Every invariance theorem and the next round's
   oblivious-embedding proofs take it.
3. **§2 kind, low.** P6 Q1: a finite Gaussian family is `HasGaussianLaw (fun ω t => X t ω) μ`,
   not Mathlib's `IsGaussianProcess`. Reason: finite index sets only; composes with
   `HasGaussianLaw.map`. Six statements and their R3 call sites; the `IsGaussianProcess` bridge
   waits for a consumer.
4. P0 Q2: isotropy uncentred and entrywise, pseudo-covariance left out. Reason: Hutchinson needs
   `E X Xᴴ`, not the covariance, and holds for non-centred probes.
5. P0 Q3: matrix conditional expectations moved to P5 (their only consumer, Freedman).
6. P1 Q3: one sub-exponential parametrisation `(v, b)` with an open window. Known cost: the
   sub-gamma shape converts at a factor 2 (`(2v, 2b)`).
7. P4 Q1, Q2: `HasLogSobolev` is a predicate on laws with bounded `C¹` test functions (junk-free);
   Gross's theorem is stated separately in integrable form. Status records P4 as proceeding on
   these recommendations (Lipschitz as `LipschitzWith` on `EuclideanSpace`, constant `L²`), open
   to correction.
8. P5a Q1: `A` Hermitian is a field of `HasMatrixMGFBound`. Every constructor produces it.
9. P5d D1: square-integrable increments and Mathlib's `μ[X j ^ 2 | ℱ j]` replace the cut
   `HasLocalMatrixSecondMoment`. Lost: increments with finite but non-integrable conditional
   variance.
10. R5 §8.9: the column law is named, `uniformSphereVector n` on `n → ℝ` (deviation 16), rather
    than Mathlib's `Measure.toSphere` on a subtype.

Laws and fields:
11. **Costly for the next round only if reversed.** P2 Q1, R1, R5 Q5: real laws now; complex
    Gaussian vectors, matrices and Haar frames later as parallel definitions
    (`complexGaussianVector`, `complexHaarFrame`), so nothing is renamed. Interfaces are over `𝕜`.
12. P2 Q2, R1 Q1: `gaussianVector` and `gaussianMatrix` are `abbrev`s, so P0's product lemmas
    apply by unification; `rw` does not see through them (module docstrings say so).
    `haarFrame` and `uniformSphereVector` are `def`s with `HasLaw` bridges.
13. P3 Q1, R3 D3, P6 D6: norm tails, Hanson–Wright, the sub-Gaussian rows theorem, comparison and
    Gaussian matrix theorems are real. Reason: their proofs need a Gaussian of the same field, or
    the complex constant would be worse.
14. P3 Q2: Hutchinson's variance takes moment parameters `s`, `m₄`, not a law (covers complex
    Gaussian and Steinhaus probes too).
15. R1 §8.1: every typeclass fact about `gaussianMatrix` is an explicit instance (`Matrix` is a
    `def`, so `Measure.pi` instances are not found).
16. R5 Q3: `haarFrame` is defined on every shape; column theorems take `card k ≤ card n`.

Bounds, forms and scope:
17. **Costly for the next round.** R3 D2: one named constant in Vershynin 2018's shape
    `√N ± C c (√n + t)` outside `2 e^{-t²}`, not the prototype's two-constant shape. The next
    round's sub-Gaussian sample sizes will be written in it; another shape would coexist.
18. R3 D1: Loewner forms on `Xᴴ X` are the primary conclusions, lower and upper separately, as the
    next round's `IsSubspaceEmbedding` will take them.
19. P1 Q1: classical scalar Bernstein for bounded variables is the `1 × 1` matrix Bernstein,
    restated in scalar terms; the `eigenvalue _ 0` form is primary in P5a.
20. P1 Q2, P5a Q2: the Bernstein `min` exponent and the matrix variance statistic are written out,
    not definitions.
21. P5a §8.2, P5b D1: trace-level forms first, independent sums as corollaries (so sampling
    without replacement reuses the tails). P5a §8.1: `HasMatrixMGFBound.mono_bound` deleted as
    false.
22. P5b D3, D4: names `_intrinsicDim` (incomparable with the dimension form); Chernoff mean with
    free `θ`.
23. P5c D1, D4: one law-free Khintchine recursion; Stein's identity gets a polynomial-growth form
    (the bounded one is now its `k = 0` corollary), amending P6 D1.
24. P5c D5, P6 D2, P7 D3 to D5, R2 §0: not stated: spectral-norm Khintchine moments, Slepian,
    ψ₂ Hanson–Wright and ψ₁ Bernstein (each is a bridge plus an existing theorem), the Orlicz
    converses, McDiarmid's lower tail, R2's fourth moments and approximate matrix multiplication.
25. P6 D3, D4: comparison for centred families on two probability spaces.
26. P7 D1: bounded differences by the entropy method (no Borel hypothesis), not martingales.
27. P7 D2, §8.8: Orlicz conditions are raw constructor hypotheses, no Orlicz norm (an infimum
    would have a junk `0`); constant bodies through `Real.toNNReal`.
28. R3 D4, D5 and R4 Q1: Chevet first; dominated block and pseudoinverse bounds kept beside the
    better ones because LowRank cites them, neither named `_sharp`.
29. R5 Q2, Q4, Q7: the QR law through the characterization (no Haar uniqueness needed); Haar
    fourth moments deferred; transfer stated through `rangeProjector`.

Naming and contract rules added this round (`CONTRIBUTING.md`):
30. **Costly.** Tail-prefix rule (§4): `measure_` inside an interface's namespace, as Mathlib does for
    `μ.real` statements; `measureReal_` at root level. `IsSubgaussianVector.measureReal_norm_sq_ge_le`
    was renamed to `measure_norm_sq_ge_le`. A naming scheme; changing it would rename most tails.
31. `ℝ≥0` spelling (§5.1): `‖·‖₊`, never `⟨x, hx⟩` or `Real.toNNReal` in a statement.
32. Binder rule (§5.2): a bound variable that only meets `•` gets its type (`∀ θ : ℝ`); P5a's
    skeleton had elaborated `θ : ℕ`.

The other rules added this round are the maintainer's: `L2Operator` only for analysis on
matrices (§5.1, deviation 13), the numerical-bounds rules (§5.2, D5; P6 §8.1 applied the "no
bare `∃ C`" rule), and files of about 1000 lines (§7 below).

## 5. Mathlib deviations added this round

Entries in `docs/design/Mathlib-deviations.md`:

| Entry | Deviation | Status |
|---|---|---|
| 12 | Global `Matrix.instMeasurableSpace` (product σ-algebra), with a Borel instance | kept (maintainer, D8) |
| 13 | Matrix integrals and conditional expectations under `Matrix.Norms.L2Operator`, plus a scoped `NormedSpace ℝ` | decided (maintainer, D10 amended); bridges in `MatrixIntegral.lean` |
| 14 | `IsLeftUnitarilyInvariant`, `IsRightUnitarilyInvariant` classes in place of `SMulInvariantMeasure` | open (orchestrator); bridges `isLeftUnitarilyInvariant_iff`, `isRightUnitarilyInvariant_iff` proved |
| 15 | Haar measure as `haarFrame n k` on matrices, any shape | bridge `haarFrame_eq_map_haarMeasure` proved (needs the new `Matrix.compactSpace_unitaryGroup`) |
| 16 | `uniformSphereVector n` on `n → ℝ` in place of `Measure.toSphere` | bridge `uniformSphereVector_eq_map_toSphere` proved (`[Nonempty n]`) |
| 17 | `HasCondMatrixMGFBound` with `μ[· \| m]` in place of the `condExpKernel` form | bridge `hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF` proved (`[StandardBorelSpace Ω]` there only); orchestrator decision |

## 6. Open work

### 6.1 Not ported

The ledger completeness pass left 21 prototype declarations in five groups. All but the last were
ported at the end of the round (`c22904e`), under new names:

1. Random-start log-overlap (R2, 14 entries): `measureReal_log_norm_sq_div_sq_ge_le_of_hasLaw_gaussianVector`
   (tail), `integral_log_norm_sq_div_sq_le_of_hasLaw_gaussianVector` (mean `≤ log (2N) + 2`),
   `integral_log_norm_sq_div_sq_sq_le_of_hasLaw_gaussianVector` (second moment), with their
   `integrable_` companions, in `Distributions/GaussianLogOverlap.lean`. They hold for any unit
   vector `u`, not only a coordinate, and write the quantity out with no definition. They are the
   random-start step of the power and Lanczos methods [KuczynskiWozniakowski1992].
2. χ² small ball (P3): `measureReal_norm_sq_le_le_rpow_of_hasLaw_gaussianVector`,
   `P(‖X‖² ≤ u) ≤ (e u / N)^{N/2}` with `N = card n`, in `Distributions/ChiSquare.lean`.
3. Matrix variance (P5a, 2 entries): `integral_sum_sq_of_iIndepFun`,
   `integral_sum_mul_sum_of_iIndepFun`, `integral_sum_sub_integral_sq_of_iIndepFun`, in
   `MatrixConcentration/Variance.lean`, over `RCLike` with no Hermitian hypothesis.
4. Log-Sobolev extension (P4, 2 entries): `HasLogSobolev.integrable_sq_mul_log_sq` and
   `HasLogSobolev.entropy_sq_le_of_integrable`, in `LogSobolev.lean`, for every law with
   `HasLogSobolev`; the Gaussian integrability lemmas now follow from them.
5. Sub-Gaussian Johnson–Lindenstrauss (R3, 2 entries): not ported, for the next round.

Cut by design (D9 and the notes; ledgered): Wishart and the hard edge, the localized Freedman
interface, general-covariance Isserlis, Slepian, Ornstein–Uhlenbeck, the `_of_hasLaw` twins.

### 6.2 Unverified citation locators

- Honorio and Jaakkola 2014, the `(32 c², 4 c)` centred-square constants: locator unchecked
  (P1 §8; `SubGaussian/Square.lean`). The key is not in `docs/references.bib`.
- Tropp 2015, chapter 7 labels (Theorems 7.2.1, 7.3.1, Corollary 7.3.2, Proposition 7.4.1,
  Theorem 7.7.1): first taken from the prototype, then supplied by the review; not checked
  against the book (P5b §7, §8.3).
- Tropp 2015, the section of noncommutative Khintchine: unconfirmed; cited as chapter 4
  (P5c §8.3). Mackey et al. 2014 Theorem 7.1 is the review's locator.
- Tropp 2011, Theorem 1.2 (Freedman), Corollary 1.3 (rectangular), §2 (Lieb, supermartingale):
  first from memory, corrected by the review; bibliographic data added by the review (P5d §7,
  §8.5).
- Boucheron, Lugosi and Massart 2013, the entropy lemma cited as the proof of Theorem 6.2:
  unchecked (P7 §7).
- McDiarmid 1989: numbering unverified (the reviewer reads the inequality as Lemma (1.2)); both
  statements cite the paper without a label (P7 §8.4).
- `DavidsonSzarek2001`, `Gordon1985`, `Kahane1986`: entered without DOIs (P6 §8.4).
- `Gross1975` is not in the bibliography; docstrings cite Boucheron–Lugosi–Massart (P4 §9).

### 6.3 Next-round candidates

- Sub-Gaussian JL (§6.1, item 5) and the Haar JL in Dasgupta–Gupta form, with the Haar fourth
  moments it needs (R5 Q4) and concentration of `‖Qᴴ x‖²`.
- Complex Gaussian vectors and matrices and complex Haar frames, as parallel definitions; with
  them the complex χ², Hanson–Wright, rows theorem (constant depending on `finrank ℝ 𝕜`) and an
  `IsIsotropic` transport along the coercion from `ℝ` to `ℂ` (P2 §8.10).
- The sketching predicates (`IsSubspaceEmbedding` as the Loewner sandwich), range frames
  (`gaussianRangeFrame`), sampling without replacement on P5a's trace forms, the
  `IsGaussianProcess` bridge when a consumer holds one, and the joint law of
  `(rangeProjector (A X), Ψ)` for consumers that sketch twice (R5 §8.11).

### 6.4 Small items left from the wrap-up

- `Distributions/GaussianComparison.lean` is 1035 lines, over the soft limit.

`Matrix/Factorizations/PolarFrames.lean`, which holds the seven R5 Matrix-layer additions, is a
proved Matrix-layer file and stays separate by design; it is not merged into `Polar.lean` and
`Basic/OrthonormalBasis.lean` as R5 §8.12 had planned. The P5a row is now in the `status.md` table, and the final stage check is in
§7.

## 7. Process notes

- **File size.** The guideline was raised from 300 to 500 lines to about 1000 (maintainer,
  2026-10-14, `54a71e1`; Mathlib's 1500-line linter is the ceiling). The Entropy file (722 lines)
  had been split before the change; `InverseMoments.lean` was split at 1490 lines.
- **Skeleton rule.** A skeleton agent never adds a `sorry` to a proved file; new statements go in
  a new skeleton file, merged at wrap-up. It followed a P6/R3 skeleton agent adding three
  statements to proved files. Under it P5b to P7 used four temporary files (`LaplaceGeneral`,
  `RademacherSymmetry`, `GaussianIntegrationByPartsGrowth`, `EntropyExpBounded`), all merged in
  `0aa65e5`.
- **Delegation.** From midway the orchestrator delegated design-note drafts and skeletons to Opus
  agents, reviews to Fable, bookkeeping (ledger, registration, stage checks) to Sonnet. P5b, P5c,
  P5d and P7 were reviewed together by one Fable agent.
- **Incident.** A merge script wrote 36 MB into
  `NLAlib/Probability/Distributions/GaussianIntegrationByParts.lean`. The file was restored from
  git; nothing was lost.
- **False statements caught.** `HasMatrixMGFBound.mono_bound` (the exponential is not operator
  monotone) and Chevet's first comparison process (false for non-unit vectors) were found by
  review before proofs; the skeleton binder bug (`θ : ℕ`) by a proof agent.
- **Final check.** `scripts/stage_check.sh`, run after the closing changes (one public copy each of
  the sine-truncation and `x log x` lemmas, the Gaussian integrability lemmas derived from
  `HasLogSobolev`, the `KuczynskiWozniakowski1992` entry), printed:

  ```
  218 proved modules; 0 not yet
  build: Build completed successfully (3767 jobs).; warnings: 0
  audited 5001 declarations reachable through import NLAlib; 0 violations
  -- Found 0 errors in 3645 declarations (plus 1356 automatically generated ones) in NLAlib with 14 linters
  -- All linting checks passed!
  41 bibliography keys; 0 problems
  ```
