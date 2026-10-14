# Inventory of the prototype `Probability/` and `RandomMatrix/` layers

Sources: `~/Documents/prove2me/lean/NLAlib/{Probability,RandomMatrix}` (170 modules, 39 063
lines), `atlas/declarations.json` (921 declarations: 518 + 403; 855 theorems, 55 definitions,
11 instances and structures), greps of the pinned Mathlib (v4.33.1), and the proofs read. "n
statements" counts declarations whose signature mentions the notion. `P/` = `Probability/`,
`R/` = `RandomMatrix/`. Shapes: **T** tail, **M** moment generating function bound, **E≤**
expectation or moment bound, **E=** expectation identity, **L** law identity, **AS** almost
sure, **I** concludes a named predicate.

## 1. Map

| Subdirectory | n | Content |
|---|---|---|
| `P/ChiSquare` | 30 | χ² tails, Laplace transform, negative moments; χ² bound for `‖X‖²` |
| `P/Concentration/Basic` | 17 | named tails, variance statistics, net bound, tail to moment |
| `…/Entropy` | 11 | entropy tensorization, Herbst argument |
| `…/Martingales` | 38 | matrix Freedman, conditional Lieb, trace supermartingale |
| `…/Matrix` | 70 | Tropp 2015 ch. 3–7: Laplace, master, Chernoff, Bernstein, series |
| `…/QuadraticForms` | 92 | Hanson–Wright (about 60 proof leaves), Hutchinson moments |
| `…/Scalar` | 13 | McDiarmid, scalar Bernstein (ψ₁), Chernoff from a local CGF |
| `P/Gaussian/Basic` | 30 | `gaussianVector`, scalar moments, linear forms, covariance |
| `…/Calculus` | 48 | Stein identities, Ornstein–Uhlenbeck semigroup |
| `…/Comparison` | 7 | interpolation, Slepian, Sudakov–Fernique, Gordon minimax |
| `…/Concentration` | 32 | Gross log-Sobolev (1-D, n-D), Herbst, Lipschitz functions |
| `…/Moments` | 45 | Isserlis, noncommutative Khintchine, radial moments |
| `P/Rademacher` | 33 | `rademacherMeasure`, `rademacherVector`, moments, sign flips |
| `P/Sampling` | 5 | finite law from a probability vector |
| `P/SubGaussian` | 47 | tails, moments, maxima, `E e^{θX²}`, Orlicz bridge |
| `R/Gaussian/Basic` | 43 | `gaussianMatrix`, entries, rows, linear forms, concentration |
| `…/Invariance` | 15 | orthogonal invariance, blocks, laws of `Gᵀ`, `GU`, `Gx` |
| `…/InverseMoments` | 96 | inverse Wishart, pseudoinverse moments and tails, hard edge |
| `…/Moments` | 43 | `E‖SGT‖_F²`, fourth moment, AMM, conditioning, full rank |
| `…/Spectral` | 40 | Gordon, deviation, Chevet, small ball, rank of `AG` |
| `…/Wishart` | 144 | weak-derivative densities, soft minima of `tr (GGᵀ)^{-q}` |
| `R/Haar` | 18 | Haar on `O(n)`, law on Stiefel frames, Gaussian QR |
| `R/SubGaussian` | 4 | JL and singular values for independent isotropic rows |

Headline results (statement; hypotheses; shape):
- Sub-Gaussian, from `HasSubgaussianMGF X c μ` alone: `measureReal_lt_abs_le_of_hasSubgaussianMGF`
  `P(|X| > t) ≤ 2e^{-t²/(2c)}` (T); `integral_abs_rpow_le_of_hasSubgaussianMGF` (E≤);
  `integral_iSup_le_of_hasSubgaussianMGF` for a finite family without independence (E≤).
- `bernstein_sum_of_lintegral_exp_abs_le_two`: `P(|ΣXᵢ| ≥ t) ≤ 2exp(-min(t²/ΣKᵢ², t/B)/64)`;
  `iIndepFun`, mean 0, `∫⁻ e^{|Xᵢ|/Kᵢ} ≤ 2` (T). `mcdiarmid_upper_tail`: `exp(-2t²/Σcᵢ²)`;
  `iIndepFun`, coordinate oscillations `cᵢ` (T).
- `measureReal_le_sum_sq_le_gaussianVector` and six siblings: χ²_d tails, stated on the measure
  `gaussianVector (Fin d)` (T); `integral_rpow_inv_sum_sq_gaussianVector`:
  `E(χ²_d)^{-q} = Γ(d/2-q)/(2^qΓ(d/2))` (E=); `lintegral_exp_sq_norm_le_chi_square_mgf`:
  `E e^{θ‖X‖²} ≤ (1-2θ)^{-d/2}` if every `⟨X,u⟩` is sub-Gaussian with proxy `‖u‖²` (M).
- `hanson_wright_mgf`: `P(|XᵀAX - E XᵀAX| ≥ t) ≤ 2exp(-c·min(t²/(K⁴‖A‖_F²), t/(K²‖A‖)))`,
  `c = 1/(256e²)`; `iIndepFun`, coordinates with proxy `K²` (T). `integral_quadForm_eq_trace`,
  `variance_quadForm`: Hutchinson mean and variance (E=).
- `measureReal_ge_le_of_lipschitz_gaussianVector`: `γ(f ≥ Ef + Lt) ≤ e^{-t²/2}` (T);
  `hasSubgaussianMGF_of_logSobolev` under `HasEuclideanLogSobolev μ c` (I); `slepian_inequality`
  (T, in `ℝ≥0∞`), `sudakov_fernique_inequality`, `gordon_minimax_inequality` (E≤) for finite
  families with `HasGaussianLaw`; Isserlis and Stein identities (E=).
- Matrices (`Matrix (Fin d) (Fin d) ℂ`, `[NeZero d]`, `Fin N` families): Laplace tail (T), Lieb
  `integral_traceExp_add_le_traceExp_add_matrixLog` (M), master bounds via `cumulantSum` (T, E≤),
  `chernoff_matrix_mgf_cgf_le`, `bernstein_matrix_mgf_cgf_le`: `E e^{θX} ≼ exp(g(θ)·A)` (M).
- `measureReal_specNorm_sum_ge_le_bernsteinTail`: `P(‖ΣS_k‖ ≥ t) ≤ (m+n)e^{-(t²/2)/(v+Lt/3)}`,
  a Hermitian twin and expectation forms; `Measurable`, `iIndepFun`, mean 0, a.e. bound, the
  Hermitian case adds `MemLp 2` (T, E≤). Chernoff tails, `matrix_chernoff_sampling_lower`
  (`d·e^{-ε²N/(2L)}`), four intrinsic-dimension forms (T).
- `measureReal_specNorm_matrixSeries_ge_le`: `(m+n)e^{-t²/(2v)}`; `iIndepFun g`,
  `HasSubgaussianMGF (g k) 1` (T). `integral_re_trace_gaussianSeries_pow_le` and its Rademacher
  twin: `E tr Y^{2p} ≤ (2p-1)^p tr(ΣAᵢ²)^p` (E≤). `matrix_freedman`: `d·e^{-t²/(2(v+Lt/3))}`
  for increments centred given `ℱ j`, with `X_j ≤ L·1` (T).
- Gaussian matrices (on the measure `gaussianMatrix`, ℝ): `hasLaw_gaussianMatrix_orthogonal`,
  `hasLaw_gaussianMatrix_block`, `gaussianMatrix_indepFun_block` (L);
  `integral_frobSq_mul_gaussianMatrix_mul`: `E‖SGT‖_F² = ‖S‖_F²‖T‖_F²` (E=);
  `gordon_extreme_singular_values`: `√N - √n ≤ Eσ_min ≤ E‖G‖ ≤ √N + √n` (E≤);
  `one_sub_le_measure_sigmaMin_and_specNorm_gaussianMatrix` (T, success form); Chevet (E≤).
- `integral_inv_self_mul_transpose_gaussianMatrix`: `E(GGᵀ)⁻¹ = I/(k-r-1)`;
  `integrable_and_integral_frobSq_pinvR_gaussianMatrix`: `E‖G†‖_F² = r/(k-r-1)` (E=);
  `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le`: `E‖G†‖ ≤ e√k/(k-r)` (E≤);
  `gaussianMatrix_sigmaMin_transpose_sq_le_le` (T); `gaussianMatrix_ae_rank_eq` (AS);
  `gaussianMatrix_map_canonicalQRFrame`: the QR factor has the law `haarFrameLaw` (L).
- `measure_extreme_singular_failure_le_of_independent_isotropic_rows`: all singular values in
  `√N ± (32eK²√(log 9)√n + t)` outside probability `2e^{-t²/(1024e²K⁴)}`; independent rows,
  directional proxy `K²`, isotropy (T, in `ℝ≥0∞`).

## 2. How randomness is represented

| Object | Form in statements | Statements |
|---|---|---|
| Gaussian scalar | on the measure `gaussianReal 0 1` / `HasLaw g (gaussianReal 0 1) μ` | 26 / 19 |
| Gaussian vector | on `gaussianVector n` (`abbrev` of `Measure.pi`) / `HasLaw x …` | 34 / 5 |
| | raw `Measure.pi fun _ => gaussianReal 0 1` (all in `R/`) | 30 |
| | Mathlib `stdGaussian (EuclideanSpace ℝ (Fin n))` | 9 |
| | family `∀ k, HasLaw (g k) (gaussianReal 0 1) μ` + `iIndepFun g μ` | 6 |
| general Gaussian | `IsGaussian μ` / `HasGaussianLaw (fun ω t => X t ω) P` | 8 / 13 |
| Gaussian matrix | on `gaussianMatrix m n` / `HasLaw X (gaussianMatrix m n) μ` | 66 / 59 |
| Rademacher | on `rademacherMeasure`, `rademacherVector n` / `HasLaw` | 29 / 26 |
| sub-Gaussian | Mathlib `HasSubgaussianMGF X c μ` | 94 |
| Orlicz | `∫⁻ exp((X/K)²) ≤ 2`, `∫⁻ exp(|X|/K) ≤ 2` | 9 |
| independence | `iIndepFun` / `IndepFun` / `IdentDistrib` | 92 / 13 / 0 |
| conditioning | `μ[X j | ℱ j]` with `Filtration ℕ` | 11 |
| discrete | `finiteSamplingLaw p hp` / `PMF` | 3 / 5 |

Local definitions (statements using them, layer + outside): `gaussianMatrix` 183 + 47,
`gaussianVector` 65 + 18, `rademacherVector` 29 + 23, `rademacherMeasure` 28 + 5,
`finiteSamplingLaw` 3 + 8, `orthogonalHaar`, `haarFrameLaw` 7 + 0; predicates
`HasEuclideanLogSobolev` 12, `HasLocalMatrixSecondMoment` 11, `HasHansonWrightMGF` 3; named tails
(`gaussianSeriesTail` 6, `mcdiarmidTail` 3, `bernsteinTail` 2, Chernoff 1 + 1); statistics
(`cumulantSum` 5, `rectSecondMoment` 3, `hermitianSecondMoment` 3); proof vocabularies
(`randomVector` 11, `cutMatrix` 11, `linForm` 12, `ornsteinUhlenbeck` 13, `regularizedGram` 35).

Inconsistencies:
1. Five spellings of the standard Gaussian vector (table). Every Gaussian-matrix theorem is
   stated on the measure and again as an `_of_hasLaw` copy: 50 twins. Downstream takes the
   `HasLaw` form (29 `LowRank` theorems).
2. The sub-Gaussian proxy is written six ways: `c : ℝ≥0` (39), `1` (11), `⟨K ^ 2, _⟩` with real
   `K` (30), `‖toLp 2 u‖₊ ^ 2` (12), `(x ⬝ᵥ x).toNNReal` (2), plus a real slack `C₀ ≥ c` (17).
3. Sub-Gaussian vectors, four ways: `∀ u, HasSubgaussianMGF (X · ⬝ᵥ u) ‖u‖₊²` (`ChiSquare`),
   `∀ u, … ⟨K² * u ⬝ᵥ u, _⟩` (`SubGaussianJL`), `u ⬝ᵥ u = 1 → … ⟨K², _⟩` (`SubGaussianRows`),
   bilinear `∀ unit x y, … (y ⬝ᵥ A x) c` (`Basic/Net`).
4. Isotropy, three ways: mean 0, `E zᵢ² = 1` and independence (12 + 3 in `Estimation`);
   `∫ zᵢzⱼ = if i = j then 1 else 0` (3 + 4); `∫ (a ⬝ᵥ u)² = u ⬝ᵥ u` (3).
5. Tails: `μ.real {…} ≤ δ` 65, `μ {…} ≤ ENNReal.ofReal …` 15, `(μ {…}).toReal` 2, `1 - δ ≤
   μ.real {good}` 2; 73 non-strict events, 21 strict; thresholds `Ef + Lt` (Gaussian), `Ef + t`
   (log-Sobolev), relative `(1 ± ε)·mean` (Chernoff, χ²).
6. 37 `integrable_and_integral_…` conjunctions; the statistics silently use the junk value of
   a non-integrable Bochner integral.
7. Measurability: `Measurable` 53, `AEMeasurable` 32, `StronglyMeasurable` 6, none where the
   MGF gives it; entrywise `∀ i j, Measurable fun x => Q x i j` 3 + 15 downstream.
8. Matrix concentration is over ℂ, `Fin d`, `[NeZero d]` (50), `Fin N` families (43); Gaussian
   material over ℝ; nothing over `RCLike`. Norms appear as `x ⬝ᵥ x`, `∑ i, x i ^ 2`,
   `‖toLp 2 x‖`; Lipschitz conditions are written out (13), never `LipschitzWith`.

## 3. Parallel families

G Gaussian, R Rademacher, sG sub-Gaussian MGF, Bd bounded. ● a declaration with its own proof,
○ a declaration proved from another column's, blank: no declaration. Names and the property each
proof uses follow, by row.

| # | Result | G | R | sG | Bd | Other |
|---|---|---|---|---|---|---|
| 1 | scalar law: mean, `E x²`, `E x⁴`, `MemLp`, exponential moments | ● | ● | ● | | |
| 2 | product law ⟺ i.i.d. coordinates (vector, matrix) | ● | ● | | | |
| 3 | sub-Gaussian proxy of the law | ● | ● | | ● | ψ₂ ● |
| 4 | tail, absolute moments, maximum | | | ● | | |
| 5 | `Σ aᵢXᵢ`: proxy and moments (Khintchine) | | ○ | ● | | |
| 6 | `‖X‖²` upper tail | ● | | ● | | |
| 7 | `‖X‖²` lower tail, two-sided | ● | | ● | | |
| 8 | real and negative moments of `‖X‖²` | ● | | | | |
| 9 | quadratic form: mean, variance | ○ | ○ | | | isotropy ● |
| 10 | quadratic form: concentration | | | ● | ● | ψ₂ ○ |
| 11 | matrix series: MGF, `E λmax`, tail | ○ | ○ | ● | | |
| 12 | matrix series: trace moments | ● | ● | | | |
| 13 | function of the vector: concentration | ○ | | | ● | log-Sobolev ● |
| 14 | integration by parts, symmetry | ● | ● | | | |
| 15 | linear images, invariance | ● | | | | Haar ● |
| 16 | `E‖SXT‖_F²`, fourth moment | ● | | | | |
| 17 | extreme singular values, `‖X‖` | ● | | ● | | |
| 18 | `‖Xx‖²` for fixed `x` (JL) | | | ● | | |
| 19 | polynomial growth ⟹ integrable | ● | ● | | | |
| 20 | `σ_min` small ball, inverse moments | ● | | | | |

1. `integral_eq_zero_of_hasLaw_gaussianReal`, `integral_sq_eq_one_…`, `…pow_four_eq_three…`,
   `memLp_two_…`, `integrable_exp_mul_…` and the same for `rademacherMeasure`; sG bounds only
   (`integral_sq_le_…_of_le`). Consumers use centring, unit variance and `m₄`.
2. `hasLaw_gaussianVector_of_iIndepFun`, `HasLaw.iIndepFun_eval_of_gaussianVector`, Rademacher
   and matrix twins: each is Mathlib's `iIndepFun_iff_hasLaw_pi_pi`; nothing of the law is used.
3. `hasSubgaussianMGF_of_hasLaw_gaussianReal` (exact MGF), `…_rademacherMeasure`,
   `hasSubgaussianMGF_of_abs_le_of_integral_eq_zero` (Hoeffding's lemma), ψ₂: `…_le_two`.
4. `measureReal_lt_abs_le_of_hasSubgaussianMGF` and siblings: the MGF bound alone; the G, R,
   Bd cases are one composition with row 3 away and are not stated.
5. `hasSubgaussianMGF_finset_sum_mul_of_iIndepFun` (independence, MGF);
   `hasSubgaussianMGF_sum_mul_rademacher` restates it for `HasLaw ε (rademacherVector ι) μ`.
6. G: `measureReal_le_sum_sq_le_gaussianVector` and two siblings; sG:
   `measureReal_sq_norm_ge_le_chi_square_mgf` and two siblings. The sG proof uses only the MGF
   of every linear form (Gaussian linearization, Tonelli) and implies the G statements;
   `SRHTFlattening` applies it to Rademacher sums.
7. G: `measureReal_sum_sq_le_le_exp_mul_rpow` and three optimised forms (exact Laplace
   transform); sG: `measureReal_le_abs_sum_sq_sub_card_of_hasSubgaussianMGF` (two-sided, via
   row 10). The Gaussian-strength lower tail needs the Laplace transform, not an MGF bound.
8. `integral_rpow_inv_sum_sq_gaussianVector`, `integral_rpow_sum_sq_gaussianVector`: the density.
9. `integral_quadForm_eq_trace_of_second_moments` uses only `E zᵢzⱼ = δᵢⱼ`; `variance_quadForm`
   independence and `m₄` (G: `m₄ = 3`, R: `m₄ = 1`); `integral_quadForm_sq_rademacherVector`
   restates the R case on the measure.
10. `hanson_wright_mgf`: independent coordinates and their MGF bound (centred squares on the
    diagonal; decoupling by coordinate masks off it). Bd: `hasHansonWrightMGF_of_bounded`; ψ₂:
    `hanson_wright_of_lintegral_exp_sq_le_two`; G, R only downstream, through row 3.
11. `integral_matrixExp_smul_le_of_hasSubgaussianMGF`, `…hermitianSeries…`, `…matrixSeries…`, with
    12 per-law copies; uses the scalar MGF through `cfc` and independence.
12. `integral_re_trace_gaussianSeries_pow_le` (coordinate Stein identity),
    `integral_re_trace_rademacherSeries_pow_le` (sign flips preserve the law): both prove
    `E tr Y^{2p} ≤ (2p-1)E tr(VY^{2p-2})`, closed by the law-free
    `integral_re_trace_pow_le_of_polynomial_recursion`.
13. `measureReal_ge_le_of_lipschitz_gaussianVector`, `gaussian_concentration`,
    `hasSubgaussianMGF_of_logSobolev`, `hasSubgaussianMGF_of_independent_coordinate_oscillation`.
    The Gaussian proof is the log-Sobolev one with `c = 1`; shared conclusion: `f(X) - Ef(X)`
    has `HasSubgaussianMGF` (proxy `cL²`, resp. `Σcᵢ²/4`).
14. Seven Stein variants differing only in regularity class (`…_of_integrable`,
    `…_of_polynomial_growth`, …); R: `measurePreserving_update_neg_rademacherVector`.
15. `hasLaw_dotProduct_gaussianVector`, `gaussianMatrix_map_mulVec`, `hasLaw_gaussianMatrix_*`:
    all from Mathlib's `stdGaussian_map` (isometry invariance). Haar: `haarFrameLaw_map_smul`.
16. `integral_frobSq_mul_gaussianMatrix_mul` uses only `E G_ab G_cd = δ_ac δ_bd`; the fourth
    moment and AMM use independent entries with `m₄ = 3`.
17. G: `gordon_extreme_singular_values` (comparison) and `gaussian_concentration`; sG rows:
    `measure_extreme_singular_failure_le_of_independent_isotropic_rows` (net, row 7); bilinear
    marginals: `measureReal_lt_specNorm_le_of_hasSubgaussianMGF` (net, row 4, no independence).
18. `measure_lt_abs_mulVec_sq_sub_le_of_independent_isotropic_rows` (row 7). The Gaussian JL is
    `Sketching/Properties/JL/JL.lean`, from rows 6, 7, 15.
19. `integrable_gaussianVector_of_polynomial_growth`, `…_rademacherVector_…`: finite moments.
20. `measure_sigmaMin_le_le_gaussianMatrix`, `gaussianMatrix_sigmaMin_transpose_sq_le_le`:
    rotation invariance, independent rows, χ² law of a distance to a subspace.

Across dimensions: rectangular matrix results redo the dilation in four files; scalar Bernstein
(ψ₁, `1/64`) is not the `d = 1` case of matrix Bernstein; Mathlib's Hoeffding and Azuma are the
scalar cases of row 11 and of Freedman; the matrix Gaussian results go through `curry`.

## 4. Numerical bounds

**S** the cited source's constant; **P\*** explicit where the source leaves it unspecified;
**P** the proof's own.

| Result | Constants in the statement | Origin |
|---|---|---|
| sub-Gaussian tail; maximal inequality | `2e^{-t²/(2c)}`; `√(2c log N)`, `√(2c log 2N)` | S |
| sub-Gaussian moments, scalar Khintchine | `p(2c)^{p/2}Γ(p/2)` | P\* |
| `E e^{θX²}`, centred square, product | `e(1-θC₀e)⁻¹`, `2e(θC₀e)²`, `exp(e²C₀²θ²)` | P |
| Orlicz ψ₂, ψ₁ to MGF | proxy `9K²`; `exp(16K²t²)` on `|t| ≤ 1/(2K)` | P |
| scalar Bernstein; local CGF to tail | `1/64` ("conservative"); `1/(4C)` | P\*; P |
| McDiarmid | `exp(-2t²/Σcᵢ²)` | S |
| Hanson–Wright (MGF; ψ₂) | `1/(256e²)`; `1/(20736e²)` | P\* |
| net bound for `‖A‖` | `2(√(2 log 9·(m+n)c) + √c·t)`, `e^{-t²/2}` | P\* |
| χ² tails | Chernoff optimum, Laurent–Massart, `(eu/d)^{d/2}` | S |
| `E(χ²_d)^{-(d-1)/2}` | `< (3/d)^{(d-1)/2}` for `d ≥ 5` | S |
| matrix Bernstein, Freedman | `d·e^{-(t²/2)/(v+Lt/3)}`; `√(2v log d) + L log d/3` | S |
| matrix Chernoff; for sampling | `d(e^{-ε}/(1-ε)^{1-ε})^{μ/L}`; `d·e^{-ε²N/(2L)}`, `/(3L)` | S |
| intrinsic tails; expectation | `4·intdim`, `2·intdim`; `20(√(v log(1+r)) + L log(1+r))` | S; P\* |
| series; Khintchine | `d·e^{-t²/(2v)}`, `√(2v log d)`; `(2p-1)^p` | S |
| Gaussian Lipschitz; log-Sobolev | `e^{-t²/2}`; `2` | S |
| Gordon, deviation, Chevet | `√N ± √n`, `e^{-t²/2}`, `‖S‖‖T‖_F + ‖S‖_F‖T‖` | S |
| `σ_min` small ball (columns) | `n(e·n·s²/(N-n+1))^{(N-n+1)/2}` | P |
| `λmin(GGᵀ)` tail | `(t(k+r)/2)^{(k-r+1)/2}/Γ(k-r+2)` | S |
| `E‖G†‖` | `e√k/(k-r)`; sharp `e√((k+r-1)/2)/(k-r)` | S; P |
| `E‖(GGᵀ)⁻¹‖^p` | `(e²(k+r)/(2(k-r)²))^p`, `p ≤ 18`; sharp: `k+r-1`, real `p` | S; P |
| tails of `‖G†‖`, `‖G†‖_F²` | HMT A.3; `12rt/(k-r)`, `4t^{-(k-r)/2}` | S |
| sub-Gaussian rows, Gram, JL | `32eK²√(log 9)`, `1024e²K⁴`; `2·9ⁿ`; `256e²K⁴` | P\* |
| log overlap | `T + 2`, `T² + 4T + 8` with `T = log 2N` | S (manuscript) |

Several bounds for one quantity:
- `E‖G†‖`: `integrable_and_integral_specNorm_pinvR_gaussianMatrix_le` (HMT) and `…_le_sharp`:
  same hypotheses, the sharp one smaller for all admissible `(r, k)`; the old one is now proved
  from it and is the one `LowRank` cites. `E‖(GGᵀ)⁻¹‖^p`: integer `p ≤ 18`
  (`…specNorm_inv_self_mul_transpose_pow_gaussianMatrix_le`) against real `p ≤ (k-r)/2` with a
  smaller constant (`…rpow_specNorm_inv_gaussianMatrix_le_sharp`), plus endpoint and rooted
  forms. Both pairs are later improvements that subsume the original; suffix `_sharp`.
- `σ_min` small ball: `measure_sigmaMin_le_le_gaussianMatrix` (tall `N × n`, in `s`, needs
  `n s² ≤ N-n+1`) and `gaussianMatrix_sigmaMin_transpose_sq_le_le` (wide `r × k`, of `Gᵀ`, in
  `t = s²`): same exponent, different constants and proofs (column distances; hard-edge
  density), neither derived from the other, names in unrelated patterns.
- `‖X‖` upper tail: Gaussian `√N + √n + t`; sub-Gaussian rows `√N + 32eK²√(log 9)√n + t`;
  bilinear marginals `2√(2 log 9)√((m+n)c) + 2√c·t`. All three apply to a Gaussian matrix; the
  last two are incomparable (it depends on `N/n`).
- χ² lower tail: a parametrised Chernoff bound, its optimum
  (`measureReal_sum_sq_le_one_sub_mul_le_gaussianVector`) and two relaxations of it,
  `(eu/d)^{d/2}` (weaker by `e^{-u/2}`, the one `SmallBall` uses) and Laurent–Massart. Names
  transcribe the event (`…_le_one_sub_mul_le_…`), not the strength.
- Incomparable by hypothesis: Hanson–Wright `1/(256e²)` (MGF) and `1/(20736e²)` (ψ₂); matrix
  Chernoff `d·…` and intrinsic `2·intdim·…` (only for `ε ≥ L/μmax`), Bernstein and intrinsic
  Bernstein likewise, named by transcribing the right side (`_bernsteinTail`,
  `_intrinsicDimension_mul_exp`, then a further `_chernoff` to disambiguate).
- Parametrised and optimised pairs: maximal inequality, Chernoff expectation, Freedman
  (`measure_exists_matrix_crossing_le_of_condExp_sq`); four successive forms of `E e^{θX²}`.

Naming devices found: transcription of the statement, `_sharp` (6 names), `_of_<hypothesis>`,
five tail functions with piecewise degenerate cases (`bernsteinTail`, …). No named constant:
`1/(256e²)` is written out in five statements and re-derived as `1024e²` in a sixth.

## 5. Consumers

Downstream: `Sketching` 159 files, `LowRank` 41, `Estimation` 17, `Krylov` 36, `Solvers` 8. 33
use a declaration of the layer (Sk 13, LR 8, Est 12, none in `Krylov`, `Solvers`); 17 import it.

| Family | Downstream files | In `R/` |
|---|---|---|
| `gaussianMatrix`; `gaussianVector` | 13: Sk 2, LR 7, Est 4; 5: Est | yes |
| `rademacherVector`, `rademacherMeasure` | 13: Sk 5, Est 8 | |
| scalar-law lemmas (§3 rows 1–2) | 7: Est 4, Sk 3 | |
| Hutchinson mean and variance; Rademacher version | 3: Est; 1: `CountSketchMoments` | |
| `hanson_wright_mgf` | 1: `HutchinsonTail` | 2 (row 7) |
| χ² Gaussian tails; for sub-Gaussian vectors | 1: `JL`; 1: `SRHTFlattening` | `SmallBall` |
| χ² negative moments | 0 | 7 names |
| `matrix_chernoff_sampling_*` | 2: `LeverageSampling`, `UniformIidSampling` | |
| Laplace tails, `trace_cgf_subadditivity` | 2: `SamplingWithoutReplacement(Tails)` | |
| `finiteSamplingLaw`, `finiteSamplingPMF` | 4: Sk 3, LR 1 | |
| `hasSubgaussianMGF_sum_mul_rademacher` | 1: `SRHTFlattening` | |
| Gaussian comparison, Lipschitz concentration | 0 | `Gordon`, `Deviation` |
| block law, block independence | 2: LR | 5 files |
| `hasLaw_gaussianMatrix_mul_right`, deviation; law of `Gx` | 1: `GaussianEmbedding`; 1: `JL` | |
| `E‖G†‖_F²`; `E‖G†‖`; conditioning; Chevet | 2; 1; 1; 1: LR | |
| rank of `AG`, `gaussianRangeFrame` | 5: LR | |
| log overlap, basis coordinates | 1: `RandomStartPower` | |

The without-replacement files use the master ingredients, not a final theorem: the i.i.d.
theorems do not cover them; CGF-level statements do. Most discrete randomness downstream is
outside the layer's vocabulary: `PMF` in 16 files, `uniformOfFintype` 9, `Measure.pi` 9.

Used by no file outside its own subdirectory (headline results): matrix Bernstein, intrinsic
dimension, matrix series with its 12 per-law copies, noncommutative Khintchine, Freedman with
the 38 declarations under it, Chernoff expectations; McDiarmid, scalar Bernstein, ψ₂ and bounded
Hanson–Wright, sub-Gaussian maxima and moments, scalar Khintchine, the net bound, tail-to-moment
lemmas, general Isserlis; `R/Haar`, `R/SubGaussian`, AMM, the fourth-moment
sandwich, `E‖G†‖_F⁴`, both pseudoinverse tails, both small-ball bounds, the sharp moments; and
`R/Gaussian/Wishart` (144) with the hard-edge half of `InverseMoments` (44): about 190
declarations serve a `λmin` tail with no consumer, on which the moment bounds do not depend.

## 6. Mathlib overlap

- Sub-Gaussian (`Probability/Moments/SubGaussian.lean`): `HasSubgaussianMGF`, its `Kernel.` and
  conditional forms, `add_of_indepFun`, `sum_of_iIndepFun`, `const_mul`, `measure_ge_le`;
  Hoeffding `measure_sum_ge_le_of_iIndepFun`, Hoeffding's lemma
  `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, Azuma
  `measure_sum_ge_le_of_hasCondSubgaussianMGF`. `P/SubGaussian` extends it; 2 wrappers. Mathlib
  lacks `mono` in the proxy, the zero mean, moments, maxima.
- Chernoff (`Moments/Basic.lean`: `mgf`, `cgf`, `measure_ge_le_exp_mul_mgf`): used.
- Gaussian (`Distributions/Gaussian/`): `gaussianReal`, `mgf_gaussianReal` (no sub-Gaussian
  instance, no higher moments), `stdGaussian`, `stdGaussian_map`, `map_pi_eq_stdGaussian`,
  `multivariateGaussian`, `IsGaussian`, `HasGaussianLaw`, Fernique; wrapped by the prototype,
  which duplicates `HasGaussianLaw.indepFun_of_covariance_eq_zero` and `covarianceBilin`.
- Laws (`HasLaw.lean`): `iIndepFun.hasLaw_pi`, `iIndepFun_iff_hasLaw_pi_pi`, which 9 prototype
  lemmas restate; characteristic functions exist, unused directly.
- Martingales: `Supermartingale`, Doob's `maximal_ineq` for submartingales; the prototype adds
  Ville's bound. Conditional Jensen (`ConvexOn.map_condExp_le`) needs a closed set, which the
  positive definite cone is not; hence the prototype's `condExp_map_le_of_condExp_mem`.
- `gammaMeasure`, `betaMeasure` exist, unused. Absent: χ², Rademacher (only `bernoulliMeasure`),
  entropy and log-Sobolev (only KL divergence), McDiarmid, Bernstein, Hanson–Wright, Slepian,
  Stein, Isserlis: those families are independent of Mathlib.
- Haar (`haarMeasure`, `isHaarMeasure_eq_of_isProbabilityMeasure`): used. No `CompactSpace`
  instance for `Matrix.orthogonalGroup` and no `MeasurableSpace (Matrix …)` were found; the
  prototype proves the first, the new library has `Matrix.instMeasurableSpace`.

## 7. What this layer needs from the Matrix layer

Prototype → new library (each found by grep in `nlalib/NLAlib`):
- `exp_mul_lambdaMax_lambdaMin_le_traceExp_smul` →
  `Matrix.IsHermitian.exp_eigenvalue_zero_le_re_trace_exp`; `traceExp_le_traceExp` →
  `re_trace_exp_le_re_trace_exp_of_le`; `norm_matrixExp_sum_le_prod` → `specNorm_exp_sum_le_prod`;
  `traceExp_smul_le_mul_exp_mul_norm` → `…re_trace_exp_le_card_mul_exp`.
- `lieb_concavity`, `continuousOn_traceExp_add_matrixLog` → `concaveOn_re_trace_exp_add_cfc_log`,
  `continuousOn_re_trace_exp_add_cfc_log`; no proof here uses Golden–Thompson.
- `matrixExp_smul_le_one_add_smul_add_smul_sq_of_spectrum_le` →
  `exp_smul_le_one_add_smul_add_smul_sq`; `one_add_le_matrixExp_of_isHermitian` →
  `Matrix.IsHermitian.one_add_le_exp`; exp is PD, log monotone → `Matrix.IsHermitian.posDef_exp`,
  `Matrix.PosDef.cfc_log_le_cfc_log`.
- `lambdaMax`, `lambdaMin` (28 and 9 statements) → `eigenvalue A 0`, `…le_smul_one_iff`;
  `intrinsicDimension` and its trace bound → `intrinsicDimension`,
  `Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul`; `dilation_identities` →
  `eigenvalue_zero_dilation`, `specNorm_dilation`.
- Khintchine's trace inequalities (mixed powers, mean value, Young) →
  `re_trace_mul_pow_mul_pow_le`, `re_trace_sub_mul_pow_sub_pow_le`, `re_trace_mul_pow_le_add`.
- Nets → `exists_finite_isCover_sphere`, `specNorm_le_div_of_isCover_of_isCover`; Gram error →
  `specNorm_le_sqrt_mul_one_add_of_specNorm_sub_smul_one_le`; small `σ_min` →
  `exists_iInf_norm_mulVec_le_of_singularValues_le`; `abs_singularValues_sub_le_frobNorm`.
- `pinvR`, `frobSq_pinvR_eq_trace_inv` → `pinv`, `frobNorm_pinv_sq_eq_re_trace_inv`;
  `exists_unitary_completion` → `HasOrthonormalCols.exists_fromCols`; `polarFrame`,
  `qrNormalizedArray` → `polarFactor`, `gramSchmidtQ`; measurability → `Probability/Measurability`.

The audit's general and convenience gaps (§1A, §2) all have declarations now. Still absent, as
intended: `abs_re_trace_series_product_le`, `hasDerivAt_re_trace_mul_series_pow_update`
(Khintchine), `exp_sub_le_traceExp_compensated_of_crossing` (Freedman),
`hasDerivAt_matrix_trace_inv_pow` and two `_mul` forms (hard edge only),
`sum_offDiagonal_frame_contractions_eq` (`Sketching`).

Integration meets matrices, owned by no layer yet: integrals commute with entries, trace,
`reindex`, blocks, dilation (`integral_fromBlocks_diag`); integral and conditional expectation
of an a.s. PSD (PD) matrix are PSD (PD) and Loewner-monotone (`posDef_integral_of_ae_posDef`,
`ae_posSemidef_condExp_of_ae_posSemidef`); Jensen on a non-closed convex set
(`le_map_integral_of_integral_mem`); `E exp(s·A) = cfc (mgf s) A`
(`integrable_and_integral_matrixExp_smul_eq_cfc_mgf`), the bridge from scalar to matrix MGFs;
a nonzero polynomial in independent atomless coordinates is a.s. nonzero
(`ae_ne_zero_mvPolynomial`), the source of every "full rank a.s.".

## 8. Random matrices with orthonormal columns

Three disconnected pieces exist:
1. `R/Haar` over `Matrix/Subspaces/Stiefel.lean`: `Stiefel n k` (subtype, `Fin`, ℝ) with its
   `O(n)` action, `orthogonalHaar n`, `haarFrameLaw n k hkn` (image of the coordinate frame),
   left invariance `haarFrameLaw_map_smul`, uniqueness `measure_eq_haarFrameLaw_of_invariant`,
   and `gaussianMatrix_map_canonicalQRFrame`: the positive-diagonal QR factor of a Gaussian has
   that law (QR equivariance, rotation invariance, a.s. full rank, uniqueness). No consumer.
2. `gaussianRangeFrame A t`: the polar frame of `AG`, with a fallback off full rank; only a.s.
   orthonormality, reproduction of `AG` and measurability, no law; 3 `LowRank` files use it.
3. Downstream theorems take "a measurable frame-valued function of an independent sketch" as
   raw hypotheses (entrywise measurability, `∀ᵐ ω, HasOrthonormalCols …`: 13 and 19 `LowRank`
   statements; `Estimation/Trace/Unbiased` likewise).

Missing (none found by grep): moments (`E Qᵢⱼ² = 1/n`, `E QQᵀ = (k/n)·1`, `E QᵀAQ`, fourth
moments, of which the frame-contraction sum of `CountSketchExpectation` is the deterministic
half); invariance beyond the left action (right `O(k)`, signs, permutations, the law of a
column, of `Qᵀ`, of `Qx`); concentration (`‖Qᵀx‖²` near `k/n`, which `ChiSquare` cites as
Dasgupta–Gupta and does not state; Lipschitz functions on the sphere or `O(n)`); the polar
construction (the new `polarFactor_mul_left` gives its Haar law by the same uniqueness argument,
unstated), equality in law of the QR and polar factors, `G = QR` with `Q`, `R` independent; a
predicate "random frame with the invariant law" that downstream could take (the law lives on a
subtype, consumers hold `Matrix`-valued maps); the complex case.

## 9. Unproved and fragile material

- No `sorry` in the atlas for the layer (the prototype's 39 are elsewhere), none in the
  sources, no `axiom`. Over 500 lines: `ChiSquare/ChiSquare` 772, `SpectralSecondMoment` 710,
  `GordonMinimax` 688, `Spectral/Gordon` 668, `LogSobolevHerbst` 581, `OrnsteinUhlenbeckEntropy`
  542, `CenteredSquare` 523, `EvenMoments` 517, `LogSobolevOneDim` 509.
- Self-described provisional: `1/64` "conservative", Orlicz constants "deliberately
  unoptimized", ψ₂ Hanson–Wright "a conservative constant"; `FreedmanGlobal`,
  `TracePotentialProcess`, `ConditionalLieb` call themselves intermediates. Atlas `(partial)`:
  `matrix-freedman`, `mcdiarmid`, `isserlis`, `jl-subgaussian`, `random-start-power`.
- 98 docstrings in 34 files cite an unpublished project text as source ("operator
  re-derivation", "supplied audit", "local registry at `E:/…`"): `Martingales` 31,
  `InverseMoments` 22, `Haar` 16, `R/Gaussian/Moments` 15.
- Dead branch: the shifted hard-edge route ending in
  `integral_sigmaMin_transpose_sq_law_weak_nonneg_gaussianMatrix`; `LambdaMinTail` uses the
  `_unshifted_` one. Hanson–Wright is a port from HighDimProb with its own vocabulary.

## 10. Recommendations for the design

Interfaces:
1. **Law**: Mathlib's `HasLaw X ν μ` is the only distributional hypothesis; each theorem is
   stated once, for a random variable (`HasLaw.id` gives the measure form); no twins.
2. **Scalar MGF**: Mathlib's `HasSubgaussianMGF X c μ`, proxy always `c : ℝ≥0`, plus the missing
   API (`mono`, centring, moments, maxima); each law enters by one instance lemma.
3. **Local CGF bound** (new, e.g. `HasSubexponentialMGF X v b μ`: `cgf X μ l ≤ v l²/2` for
   `|l| < 1/b`, with integrability): the hypothesis of `measureReal_ge_le_exp_of_cgf_le`; scalar
   Bernstein, centred squares, ψ₁ and the Hanson–Wright certificate are instances.
4. **Sub-Gaussian vector** (new): every `⟨X, u⟩` has `HasSubgaussianMGF` with proxy `c‖u‖²`;
   replaces the four spellings; consumers: χ²-type tails, the net bound, JL, rows.
5. **Isotropy** (new): `∫ Xᵢ Xⱼ = δᵢⱼ` with square integrability, for vectors and for matrix
   entries; the fourth moment a separate parameter. Consumers: Hutchinson, `E‖SXT‖_F²`, AMM.
6. **Matrix CGF bound** (new): `∫ exp(θ•X) ≤ exp(g θ • A)` (Loewner), the conclusion of the
   Chernoff, Bernstein and sub-Gaussian-coefficient lemmas and the hypothesis of one master
   theorem; a conditional form for Freedman; sampling without replacement takes it directly.
7. **Concentration of a function**: conclude `HasSubgaussianMGF (f ∘ X - E f) σ²`; Gaussian
   Lipschitz, log-Sobolev (keep `HasEuclideanLogSobolev` as an interface) and bounded
   differences all produce it; tails then come from Mathlib's `measure_ge_le`.
8. **Invariance**: a law on matrices invariant under left (or right) unitary multiplication,
   bridged to Mathlib's `SMulInvariantMeasure`; Gaussian and frame laws are instances; the
   inverse-moment and block-independence proofs consume it.
9. **Random frame**: `X : Ω → Matrix n k 𝕜` with `∀ᵐ ω, HasOrthonormalCols (X ω)`; the
   invariant frame law as a measure on matrices characterised by item 8, with the QR and polar
   factors of a Gaussian as two constructions of it.
10. **Bounds behind names**: each family's constant or tail function is a definition
    (`hansonWrightConstant`, `bernsteinTail`), so an improvement changes one body; an
    incomparable bound is a second theorem named for its regime, never `_sharp`.

Stage order: P0 law vocabulary, matrix-valued integrals and conditional expectations (§7),
isotropy, tail-to-moment; P1 items 2–3, Bernstein, bounded variables, Orlicz; P2 Gaussian
(scalar, vector, matrix as one family), Rademacher, finite sampling; P3 item 4, squared norms,
quadratic forms, Hanson–Wright on `quadForm`; P4 entropy, Herbst, log-Sobolev, bounded
differences; P5 matrix concentration on item 6 (Laplace, Lieb, master, Chernoff, Bernstein,
series, intrinsic dimension, dilation once), Khintchine, Freedman last; P6 Stein (one
statement), Gaussian comparison. Then R1 Gaussian matrix law and invariance; R2 moments from
isotropy and Isserlis; R3 extreme singular values (Gordon with concentration; net with
Hanson–Wright); R4 inverse moments (Schur complements for exact moments, quadratic probes for
spectral ones); R5 frames (item 9: law, moments, both constructions); R6 a.s. rank, range frames.

Not to port:
- `R/Gaussian/Wishart` and the hard-edge half of `InverseMoments` (about 190 declarations)
  unless a consumer needs the `λmin` or `‖G†‖` tail; never the dead shifted branch.
- `_of_hasLaw` twins, `_pmf` copies, per-law corollaries (series, scalar lemma pairs), the
  `p ≤ 18` moment, the Hanson–Wright leaf vocabulary, `gaussianCovarianceMatrix`, `lambdaMax`.
- Until a consumer appears: the localized Freedman interface `HasLocalMatrixSecondMoment` (the
  square-integrable form first), nonnegative entropy tensorization, the log-Sobolev coverage
  extension, the general-covariance Isserlis machinery.
