# Downstream audit: dropped prototype Matrix declarations used by the upper layers

Scope: the 142 ledger-`null` prototype `Matrix/` declarations whose short name occurs outside
`Matrix/` in the prototype (`downstream_nulls.txt`). For each: atlas signature and docstring, the
use sites in `Probability`, `RandomMatrix`, `Sketching`, `LowRank`, `Krylov`, `Solvers`,
`Estimation`, `Polynomial`, and the new library under `NLAlib/`. Nothing was built or proved;
"lines away" is judged from statements. Old paths are relative to
`~/Documents/prove2me/lean/NLAlib/`, new paths to the repository root.

Counts: **gap 16** (9 names behind 6 general matrix facts, 7 proof-specific helpers),
**convenience gap 3**, **covered 104**, **coincidence 19**.

Thresholds used. *Covered*: a new declaration or vocabulary row gives the content, or it is a
derivation of at most about five lines from named lemmas (marked "short"). *Gap*: more than that.
Gaps are split into 1A, general matrix facts that would sit naturally in `NLAlib/Matrix`, and 1B,
helpers of one proof that the ledger deliberately moves to the consumer layer; 1B is listed so the
work is visible, not as a request to add it to Matrix.

Two findings beyond the classification: ten ledger notes are stale or wrong (section 5), and one
needed lemma exists in the new library but is `private` (section 3, last group).

## 1. Gaps

### 1A. General matrix facts missing from the new library

**A1. Trace-tail inequality for the Loewner order** (3 names)
  Old: `sq_max_re_trace_sub_spectralTraceTail_le_of_eigenvalues₀_le`,
    `sq_max_trace_sub_spectralTraceTail_le_mul_trace_sq` (its real twin),
    `rank_le_of_spectralTraceTail_eq_zero`.
  Statement: for positive semidefinite `R ≤ A`, with `τ = ∑ i ∈ Finset.Ico r (card n), eigenvalue
    A i`: `max (re R.trace - τ) 0 ^ 2 ≤ r * re (R * R).trace`. And: `A` positive semidefinite with
    `τ = 0` has `A.rank ≤ r`.
  Used by: 2 files (the real and complex RPCholesky proofs, one `𝕜` lemma serves both):
    `LowRank/Cholesky/RandomPivotedCholesky.lean:52,147`,
    `LowRank/Cholesky/ComplexRandomPivotedCholesky.lean:52,148`.
  Distance: about 20 lines from `eigenvalue_le_eigenvalue_of_le`,
    `Matrix.IsHermitian.re_trace_eq_sum_range_eigenvalue`,
    `re_trace_pow_eq_sum_range_eigenvalue_pow` and Cauchy–Schwarz; the rank statement about 8
    lines from `Matrix.IsHermitian.rank_eq_card_eigenvalue_ne_zero`.
  Suggested: `Matrix.PosSemidef.sq_max_re_trace_sub_sum_Ico_eigenvalue_le`,
    `Matrix.PosSemidef.rank_le_of_sum_Ico_eigenvalue_eq_zero` in
    `NLAlib/Matrix/Majorization/KyFan.lean` (341 lines, already owns eigenvalue partial sums). The
    definition `spectralTraceTail` and its `_nonneg`, `_le_trace` are covered (section 3).

**A2. Vershynin Lemma 5.36, scaled form** (2 names)
  Old: `specNorm_le_sqrt_mul_one_add_of_gram_error`,
    `sqrt_mul_one_sub_le_singularValues_last_of_gram_error`.
  Statement: if `specNorm (Aᴴ * A - N • 1) ≤ N * max α (α ^ 2)` with `0 ≤ N`, `0 ≤ α`, then
    `specNorm A ≤ √N * (1 + α)` and `√N * (1 - α) ≤ singularValues A k` for `k + 1 = card n`.
  Used by: 1 file: `RandomMatrix/SubGaussian/SubGaussianRows.lean:241,243`.
  Distance: about 10 lines each. The new library has the unscaled Loewner halves
    `one_sub_smul_one_le_conjTranspose_mul_self_of_specNorm_le`,
    `conjTranspose_mul_self_le_one_add_smul_one_of_specNorm_le` and the bridges
    `specNorm_sq_le_iff_conjTranspose_mul_self_le`, `le_sq_singularValues_last_of_smul_one_le`;
    the scaling by `N`, the step `max α (α ^ 2) ≤ 2 α + α ^ 2` and the square roots are not there.
    The ledger itself says "needed by the random-matrix layer".
  Suggested: `specNorm_le_sqrt_mul_one_add_of_specNorm_sub_smul_one_le`,
    `sqrt_mul_one_sub_le_singularValues_of_specNorm_sub_smul_one_le` in
    `NLAlib/Matrix/Spectral/SingularValueInequalities.lean` (346 lines).

**A3. Norm of the exponential of a sum of Hermitian matrices** (1 name)
  Old: `norm_matrixExp_sum_le_prod`.
  Statement: for Hermitian `A k`: `specNorm (exp (∑ k, A k)) ≤ ∏ k, specNorm (exp (A k))` (the
    prototype states the weaker bound with factors `1 + ‖exp (A k)‖`).
  Used by: 2 files, for integrability of the master bound under the one-sided hypothesis "`exp (θ
    • X k)` is integrable":
    `Probability/Concentration/Matrix/MasterSumExponentialIntegrable.lean:59`,
    `Probability/Concentration/Matrix/LiebRegularityShiftIntegrable.lean:54`.
  Distance: about 10 lines from `Matrix.IsHermitian.eigenvalue_exp`,
    `Matrix.PosSemidef.specNorm_eq_eigenvalue_zero`,
    `Matrix.IsHermitian.le_eigenvalue_zero_smul_one` and `Matrix.IsHermitian.le_smul_one_iff`,
    plus the empty index type. The ledger note is wrong here: `specNorm_exp_le` with the triangle
    inequality gives `∏ k, exp (specNorm (A k))`, which is not bounded by the prototype right-hand
    side when `A k` has a large negative eigenvalue, so it cannot replace the lemma in the
    integrability argument.
  Suggested: `Matrix.IsHermitian.specNorm_exp : specNorm (exp A) = Real.exp (eigenvalue A 0)`
    (nonempty index) and `specNorm_exp_sum_le_prod` in `NLAlib/Matrix/Functions/Exponential.lean`
    (316 lines).

**A4. Polynomial bound in a general polynomial weight** (1 name)
  Old: `quadForm_aeval_aeval_mulVec_le`.
  Statement: for Hermitian `A` with spectrum in `S`, `g ≥ 0` on `S` and `|p| ≤ c` on `S`: `re
    (quadForm (aeval A g) (aeval A p *ᵥ x)) ≤ c ^ 2 * re (quadForm (aeval A g) x)`.
  Used by: 2 files, as the shared step of CG (`g = X`) and MINRES (`g = X ^ 2`):
    `Krylov/Solvers/PolynomialMethods.lean:83`, `Krylov/Solvers/Minimizer.lean:235`.
  Distance: about 10 lines, the functional-calculus argument of the existing proof. The new
    library has `g = X` for positive semidefinite `A` (`re_quadForm_aeval_mulVec_le`) and `g = 1`
    (`Matrix.IsHermitian.specNorm_aeval_le`); `g = X ^ 2` alone is about 3 lines from the latter,
    since `aeval A p` commutes with `A`. Only the single statement with a general weight, which
    the prototype Krylov layer is organised around, is missing; it also covers indefinite `A`,
    which the `g = X` lemma excludes.
  Suggested: `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le` in
    `NLAlib/Matrix/Functions/Polynomial.lean` (258 lines), with the existing `g = X` lemma as its
    corollary.

**A5. A small least singular value puts a column near the span of the others** (1 name)
  Old: `exists_iInf_norm_mulVec_le_of_singularValues_last_le`.
  Statement: if `singularValues A k ≤ s` with `k + 1 = card n`, then for some column `j`, `⨅ x :
    {x // x j = 1}, ‖toLp 2 (A *ᵥ x)‖ ≤ √(card n) * s` (Rudelson–Vershynin, "invertibility via
    distance").
  Used by: 1 file: `RandomMatrix/Gaussian/Spectral/SmallBall.lean:307`.
  Distance: about 20 lines: a unit minimiser of `‖A x‖`, a coordinate of modulus at least `1 /
    √(card n)`, rescaling. The new library has no statement that the least singular value is
    attained on the unit sphere (only `exists_norm_eq_one_and_norm_mulVec_eq_specNorm` for the
    largest, and the infimum form `Matrix.IsHermitian.eigenvalue_last_eq_iInf`).
  Suggested: `exists_iInf_norm_mulVec_le_of_singularValues_le` in
    `NLAlib/Matrix/Spectral/SingularValueInequalities.lean`. The ledger defers it to RandomMatrix;
    the statement is deterministic, so either home works.

**A6. Tangent of the angle from a vector to a subspace, competitor bound** (1 name)
  Old: `vectorTangentToFrame_graph_col_le` (through
    `vectorTangentToFrame_le_of_orthogonal_competitor`, about 60 lines in the prototype).
  Statement: for a frame `Q`, a unit vector `u` and `w` with `star u ⬝ᵥ w = 0` and `u + w ∈
    LinearMap.range Q.mulVecLin`: `‖toLp 2 ((1 - Q * Qᴴ) *ᵥ u)‖ ≤ ‖toLp 2 w‖ * ‖toLp 2 (Qᴴ *ᵥ
    u)‖`. Corollary: if `range (U₁ + U₂ * F) ≤ range Q` with `U₁ᴴ * U₂ = 0`, column `i` of `U₁`
    has tangent at most `‖F e_i‖`.
  Used by: 1 file through Matrix, `LowRank/RangeFinding/SubspaceConvergence.lean:205`; the complex
    twin is re-proved upstairs in `LowRank/RangeFinding/ComplexSubspaceAngles.lean:27` (used at
    `:106` and in `ComplexSubspaceConvergence.lean`). One `𝕜` lemma replaces both.
  Distance: not derivable from `HasOrthonormalCols.tangentMatrix_add_mul`, which treats whole
    subspaces of equal dimension (the ledger says so). About 25 lines by Cauchy–Schwarz and
    Pythagoras (`norm_toLp_sq_eq_add_one_sub_rangeProjector`).
  Suggested: `HasOrthonormalCols.norm_toLp_one_sub_mul_mulVec_le_mul` and the column corollary in
    `NLAlib/Matrix/Subspaces/Tangent.lean` (323 lines).

### 1B. Proof-specific helpers (ledger: they move with the consumer)

Each is more than two lines from the new library, has one proof family as consumer, and was
dropped on purpose. They must be re-proved in the consumer layer.

- `abs_re_trace_series_product_le`: `|re tr (B * Y x ^ r * C * Y x ^ s)|` is at most a constant
  times `(1 + ‖x‖) ^ (r + s)` for `Y x = ∑ i, x i • A i`. About 25 lines (submultiplicativity and
  the triangle inequality). 2 files:
  `Probability/Gaussian/Moments/SeriesPolynomialMoments.lean:31,55`,
  `Probability/Concentration/Matrix/RademacherPolynomialMoments.lean:31`. Home: Probability, with
  the Khintchine proof.
- `hasDerivAt_re_trace_mul_series_pow_update`: coordinate derivative of `y ↦ re tr (B * Y (update
  x i y) ^ q)`, the noncommutative product rule. About 15 lines from
  `Matrix.hasDerivAt_pow_succ_apply` and `Matrix.hasDerivAt_trace`. 1 file:
  `Probability/Gaussian/Moments/SeriesPolynomialMoments.lean:102`. Home: Probability.
- `hasDerivAt_matrix_trace_inv_pow`: `(tr ((A t)⁻¹ ^ n))' = -n * tr ((A t)⁻¹ ^ (n + 1) * A')`.
  About 8 lines from `Matrix.hasDerivAt_trace_pow_succ` and `Matrix.hasDerivAt_inv_apply` (the
  ledger calls it one step). 1 file, three uses:
  `RandomMatrix/Gaussian/Wishart/SoftMin/InversePowerConcavity.lean:214,244,265`. If it is wanted
  in the library, `NLAlib/ForMathlib/Analysis/Calculus/Deriv/Matrix.lean` (188 lines) is the
  place.
- `hasDerivAt_matrix_trace_inv_pow_mul`, `hasDerivAt_matrix_trace_inv_pow_mul_const`: derivative
  of `tr ((A t)⁻¹ ^ (n + 1) * D t)` along a curve and along a line, with the sum over `range (n +
  1)` of mixed traces. About 30 lines; the second is the affine case of the first. 1 file:
  `InversePowerConcavity.lean:246,267`. Home: RandomMatrix (Wishart).
- `sum_offDiagonal_frame_contractions_eq`: for a real frame `U` with `d` columns, the two
  off-diagonal fourth-order contraction sums total `d ^ 2 + d - 2 * ∑ i, (∑ a, U i a ^ 2) ^ 2`. A
  file of its own in the prototype. 1 file: `Sketching/Sparse/CountSketchExpectation.lean:101`.
  Home: Sketching.
- `exp_sub_le_traceExp_compensated_of_crossing`: for Hermitian `Y`, `W`, `0 < θ`, `0 ≤ g`, `t ≤
  eigenvalue Y 0`, `specNorm W ≤ v`: `exp (θ * t - g * v) ≤ re tr (exp (θ • Y - g • W))`. About 10
  lines from `re_trace_exp_le_re_trace_exp_of_le`, `re_trace_exp_add_real_smul_one`,
  `Matrix.IsHermitian.exp_eigenvalue_zero_le_re_trace_exp`, `eigenvalue_real_smul`. 1 file:
  `Probability/Concentration/Martingales/FreedmanGlobal.lean:51`. Home: Probability (Freedman).

## 2. Convenience gaps

- `frobSq_eq_sum_sq`: over `ℝ`, `frobNorm A ^ 2 = ∑ i, ∑ j, A i j ^ 2`. 13 upper-layer files
  (Gaussian moment computations expand entrywise), e.g.
  `RandomMatrix/Gaussian/Moments/FourthMoment.lean`,
  `Probability/Concentration/QuadraticForms/Geometry.lean`. Today: `simp only [frobNorm_sq_eq_sum,
  Real.norm_eq_abs, sq_abs]`. Suggested: `frobNorm_sq_eq_sum_sq` in
  `NLAlib/Matrix/Norms/Frobenius.lean` (403 lines).
- `frobInner_eq_sum_mul`: over `ℝ`, `frobInner A B = ∑ i, ∑ j, A i j * B i j`. 9 files, e.g.
  `RandomMatrix/Gaussian/InverseMoments/GaussianWeakInequality.lean`,
  `Sketching/Sparse/CountSketchExpectation.lean`. Today: `simp only [frobInner_eq_sum,
  star_trivial, RCLike.re_to_real]`. Suggested: `frobInner_eq_sum_mul` in the same file. Caveat
  for both: `CONTRIBUTING.md` §5.1 discourages real twins that `simp` can produce; these are
  rewrite targets under integrals, where a named lemma is what gets used.
- `continuous_re_trace_series_product`: `x ↦ re tr (B * Y x ^ r * C * Y x ^ s)` is continuous. Two
  lines (`fun_prop` after exposing the real part of the trace as a continuous linear map). 5
  files, e.g. `Probability/Gaussian/Moments/SeriesKhintchine.lean`,
  `Probability/Concentration/Matrix/RademacherKhintchine.lean`. Suggested: keep the name, in the
  Probability file that owns the polynomial-series lemmas of 1B, not in Matrix.

## 3. Covered (104)

Format: old name → new spelling. "short" marks a derivation of three to five lines.

**Dropped definitions (vocabulary, `CONTRIBUTING.md` §5.3)**

- `frobSq` → `frobNorm A ^ 2`; `frobNorm_sq` → gone with it; `frobSq_nonneg` → `sq_nonneg`.
- `bestRankFrobSq` → `frobNorm (A - truncatedSVD A k) ^ 2`, the tail sum by
  `frobNorm_sub_truncatedSVD_sq`.
- `IsBestFrobRankApprox` → the hypothesis written out (rank bound and minimality) or `truncatedSVD
  (Qᴴ * A) k`; `isLeast_frobNorm_sub_of_rank_le`.
- `IsBestFrobRankApprox.frobSq_sub_eq_bestRankFrobSq` → minimality against
  `frobNorm_sub_truncatedSVD_le_of_rank_le`, then `frobNorm_sub_truncatedSVD_sq`.
- `lambdaMax` → `eigenvalue A 0`, with `Matrix.IsHermitian.le_smul_one_iff`;
  `lambdaMax_eq_eigenvalues₀_zero` → `Matrix.IsHermitian.eigenvalue_eq_eigenvalues₀`.
- `lambdaMin` → `eigenvalue A k` with `k + 1 = card n`, bounds in Loewner form by
  `Matrix.IsHermitian.smul_one_le_iff`; `eigenvalue_neg` turns it into a largest eigenvalue.
- `matrixExp` → `NormedSpace.exp A`; `matrixLog` → `cfc Real.log A`; `traceExp` → `RCLike.re
  (NormedSpace.exp A).trace`; `traceFunction` → `RCLike.re (cfc f A).trace`
  (`Matrix.IsHermitian.re_trace_cfc`).
- `traceEvenPower` → `RCLike.re (A ^ (2 * q)).trace`, convexity by `convexOn_re_trace_cfc`;
  `symmetricMatrices` → `{A | A.IsHermitian}`, as a subspace Mathlib's `selfAdjoint.submodule ℝ
  (Matrix n n ℝ)`.
- `projResidual` → `(1 - rangeProjector Y) * A`, for a frame
  `HasOrthonormalCols.rangeProjector_eq`; `residual_eq_one_sub_mul` →
  `one_sub_rangeProjector_mul`.
- `columnSpace` → `LinearMap.range A.mulVecLin`, projection by `toEuclideanLin_rangeProjector`.
- `pinvL`, `pinvR` → `pinv` with `pinv_eq_inv_mul_conjTranspose`, `pinv_eq_conjTranspose_mul_inv`;
  `pinvL_transpose` → `pinv_conjTranspose`.
- `rectDiag`, `rectDiag_apply`, `rectDiag_apply_ofReal`, `specNorm_rectDiag_le` → thin SVD with a
  square `Matrix.diagonal`; `specNorm_diagonal`, `specNorm_diagonal_le`.
- `IsSVD.truncatedMatrix`, `IsSVD.specNorm_sub_truncatedMatrix`,
  `IsSVD.frobSq_sub_truncatedMatrix`, `IsSVD.mul_conjTranspose_right` → `exists_isSVD_fromCols`
  (split SVD with the singular values of each block), `IsSVD.eq_add`, `IsSVD.fromCols_right`,
  `IsSVD.specNorm_eq`, `IsSVD.frobNorm_sq_eq`; or `specNorm_sub_truncatedSVD`,
  `frobNorm_sub_truncatedSVD_sq`. The partitioned SVD of the range-finder analysis
  (`LowRank/RangeFinding/SpectralRangeFinder.lean:302`) is rebuilt from these.
- `spectralTraceTail` → `∑ i ∈ Finset.Ico r (card n), eigenvalue A i`; `spectralTraceTail_nonneg`
  → `Matrix.PosSemidef.eigenvalue_nonneg`; `spectralTraceTail_le_trace` →
  `Matrix.IsHermitian.re_trace_eq_sum_range_eigenvalue` (short).
- `choleskyPivotProbability` → the ratio `re (A i i) / re A.trace` written out (the uniform
  fallback at trace zero is a LowRank-layer choice); `choleskyPivotProbability_nonneg` →
  `Matrix.PosSemidef.diag_nonneg`, `Matrix.PosSemidef.re_trace_nonneg`;
  `sum_choleskyPivotProbability` → `Finset.sum_div`, with
  `Matrix.PosSemidef.sum_smul_eliminationStep`.
- `subspaceTangent` → `specNorm (tangentMatrix U Y)`; `HasOrthonormalCols.tangentMatrix_add_mul`,
  `tangentMatrix_mul_right`, `HasOrthonormalCols.specNorm_tangentMatrix`.
- `vectorTangentToFrame` → the quotient of `‖(1 - Q * Qᴴ) *ᵥ u‖` and `‖Qᴴ *ᵥ u‖` written out (its
  bound is gap A6).
- `Stiefel`, `coordinateStiefel`, `qrColumnFamily` → by design (Matrix-Subspaces §7.5) the subtype
  and its group action are defined in the Haar layer; the Matrix ingredients exist:
  `isClosed_setOf_hasOrthonormalCols`, `isCompact_setOf_hasOrthonormalCols`,
  `conjTranspose_mul_self_eq_iff_exists_mul`, `selectionMatrix` with
  `hasOrthonormalCols_selectionMatrix`, `gramSchmidtQ_mul_left`, `measurable_gramSchmidtQ`.
- `givensQR` → `IsUpperHessenberg.exists_isQR` (the unitary factor is Hessenberg), which is what
  `Krylov/Spectral/QRAlgorithm.lean` needs from the routine.
- `eigenvectorProjector` → `cfc_eq_mul_diagonal_mul_conjTranspose` with any unitary
  diagonalisation.
- `dilationLinearMap`, `dilationLinearMap_apply` → three-line bundle of `dilation_add` and
  `dilation_smul_real` (also `dilation_sum`). Note: 3 files use it to move `∫` and `∑` through the
  dilation; every rectangular concentration bound will want that.
- `reTraceCLM` → `Complex.reCLM.comp (Matrix.traceLinearMap _ ℝ ℂ).toContinuousLinearMap`, one
  line, with the series lemmas of 1B.

**Ported or superseded since the ledger note was written (see section 5)**

- `det_gram_fromCols_eq_mul_frobSq_sub_projector`,
  `det_gram_fromCols_eq_mul_frobenius_norm_sq_sub_rangeProjector` →
  `re_det_conjTranspose_mul_self_fromCols` (`Factorizations/ColumnVolume.lean:122`).
- `eigenvalues₀_eq_of_charpoly_eq` → `Matrix.IsHermitian.eigenvalue_eq_of_charpoly_eq`
  (`Spectral/RankOneUpdate.lean:230`).
- `singularValues_gram_pow_mul` → `singularValues_pow_mul_conjTranspose_self_mul`;
  `rank_gram_pow_mul` → `rank_pow_mul_conjTranspose_self_mul` (`Functions/Polynomial.lean`).
- `measurable_polarFrame_entry` → `measurable_polarFactor`; `measurable_canonicalQRFrame` →
  `measurable_gramSchmidtQ` (`NLAlib/Probability/Measurability/Matrix.lean`).
- `specNorm_le_specNorm_map_ofReal` → `specNorm_complexify` (an equality, at `𝕜 = ℝ`).
- `specNorm_blockDiagonal_const_le` → Mathlib `Matrix.kronecker_one`, `specNorm_kronecker`,
  `specNorm_one_le`.

**One or two steps from new or Mathlib lemmas**

- `one_sub_two_mul_mul_specNorm_le_iSup` → `specNorm_le_div_of_isCover_of_isCover` (two nets).
- `Matrix.IsHermitian.eigenvalues₀_congr` → `eigenvalue A k` takes no proof argument; `rw`.
- `dilation_identities` → `isHermitian_dilation`, `dilation_mul_dilation`,
  `eigenvalue_zero_dilation`, `specNorm_dilation`.
- `mul_moorePenroseInverse_isHermitian`, `mul_moorePenroseInverse_isIdempotentElem`,
  `mul_pinvL_isHermitian` → `mul_pinv`, `isStarProjection_rangeProjector`;
  `moorePenroseInverse_mul_isHermitian`, `pinvR_mul_isHermitian` → `pinv_mul`.
- `dotProduct_moorePenroseInverse_mul_mulVec_le_dotProduct_self` → `pinv_mul`,
  `IsStarProjection.norm_toLp_mulVec_le`; `dotProduct_self_sub_moorePenroseInverse_mul_mulVec` →
  `pinv_mul`, `norm_toLp_sq_eq_add_one_sub_rangeProjector`.
- `specNorm_pinvR_sq` → `specNorm_pinv_sq`, `pinv_of_isUnit`; `specNorm_inv_self_mul_transpose_eq`
  → the same with `specNorm_pinv_of_injective` (short).
- `specNorm_gram_sub_one_eq_norm_singularValues_sq_sub_one` → the equality is not stated; its only
  use, "`specNorm (Aᴴ * A - 1) ≤ ε` iff all `σ_j ^ 2` lie in `[1 - ε, 1 + ε]`"
  (`Sketching/Properties/SubspaceEmbedding/SingularValueEmbedding.lean:24`), is the Loewner
  sandwich, assembled in about six lines from `Matrix.IsHermitian.specNorm_le_iff`,
  `le_sq_singularValues_last_of_smul_one_le`, `sq_singularValues_last_smul_one_le`,
  `specNorm_sq_le_iff_conjTranspose_mul_self_le`.
- `specNorm_diagonal_inv_le` → `specNorm_diagonal_le`;
  `aeval_gram_diagonal_mul_diagonal_inv_eq_one` → `aeval_diagonal`, `Matrix.diagonal_mul_diagonal`
  (short).
- `frobSq_sub_mul_le_of_isBestFrobRankApprox` → `frobNorm_sub_mul_sq`,
  `HasOrthonormalCols.rangeProjector_eq`, `HasOrthonormalCols.frobNorm_mul_left` (short).
- `eigenvalues_eq_dotProduct_mulVec` → Mathlib `Matrix.IsHermitian.eigenvalues_eq`,
  `re_quadForm_of_mulVec_eq_smul`; `eigenvectorBasis_dotProduct_aeval_mulVec` →
  `Matrix.IsHermitian.cfc_mulVec_of_mulVec_eq_smul`; `eval_interpolate_eigenvalues` →
  `Matrix.IsHermitian.exists_cfc_eq_aeval`, `Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq`.
- `posSemidef_cfc_of_nonneg_eigenvalues` → Mathlib `cfc_nonneg`,
  `Matrix.IsHermitian.spectrum_eq_image_eigenvalue`; `posSemidef_fromBlocks_diag` →
  `posSemidef_fromBlocks_iff_forall_norm_sq_le` at `B = 0` (the consumer wants
  `intrinsicDimension_fromBlocks_le`, which exists).
- `matrixExp_smul_sq_eq_cfc`, `smul_sq_eq_cfc` → `Matrix.IsHermitian.exp_eq_cfc`, Mathlib
  `cfc_comp'`, `cfc_const_mul`, `cfc_pow`; `traceExp_nonneg_of_isHermitian` →
  `Matrix.IsHermitian.posDef_exp`, `Matrix.PosSemidef.re_trace_nonneg`.
- `exists_unit_specNorm_mul_dotProduct_sq_le` →
  `Matrix.PosSemidef.exists_norm_eq_one_and_mulVec_eq_specNorm_smul` and the Cauchy–Schwarz
  inequality `Matrix.PosSemidef.norm_sq_star_dotProduct_mulVec_le` (short, 1 consumer).
- `quadForm_eq_sum` → the new `quadForm_eq_sum`; `quadForm_reindex` → `Equiv.sum_comp` twice
  (short); `quadForm_sq_eq_sum` → `quadForm_eq_sum`, `Finset.sum_mul_sum` (short).
- `frobInner_transpose` → `frobInner_conjTranspose`; `frobenius_norm_sq_eq_sum_norm_sq` →
  `frobNorm_eq_norm`, `frobNorm_sq_eq_sum`; `sum_diag_sq_le_frobNorm_sq` → `frobNorm_sq_eq_sum`,
  `Finset.single_le_sum` (short).
- `mulVec_dotProduct_mulVec_le_frobSq_mul` → `norm_toLp_mulVec_le_frobNorm_mul`;
  `mulVec_dotProduct_mulVec_eq_sum_sq` → Mathlib `EuclideanSpace.norm_sq_eq`.
- `dotProduct_self_nonneg`, `norm_toLp_eq_sqrt_dotProduct_self` →
  `EuclideanSpace.norm_toLp_sq_eq_dotProduct_self` (`ForMathlib/.../PiL2.lean`); 12 and 9 files
  use them, but only because the prototype spells `‖x‖ ^ 2` as `x ⬝ᵥ x` (§5.1).
- `norm_eq_sqrt_sum_sq` → Mathlib `EuclideanSpace.norm_eq`; `inner_eq_star_dotProduct_ofLp` →
  Mathlib `EuclideanSpace.inner_eq_star_dotProduct`; `inner_toEuclideanLin_eq_sum` → the same with
  `Matrix.toEuclideanLin_apply` (short); `mulVec_eq_sum_smul_col` → Mathlib
  `Matrix.mulVec_eq_sum`.
- `conjTranspose_mul_eq_zero_comm`, `gram_conjTranspose_mul_eq` → Mathlib
  `Matrix.conjTranspose_mul`, `Matrix.conjTranspose_eq_zero`.
- `posSemidef_inv_self_mul_transpose` → Mathlib `Matrix.PosSemidef.inv`,
  `Matrix.posSemidef_self_mul_conjTranspose`; `posSemidef_sum_sq_of_isHermitian` → Mathlib
  `Matrix.posSemidef_sum`, `Matrix.posSemidef_conjTranspose_mul_self`; `isHermitian_sum_smul_real`
  → Mathlib `isSelfAdjoint_sum`, `Matrix.IsHermitian.smul`.
- `singularValues_eq_zero_of_min_le` → `singularValues_of_card_rows_le`,
  `singularValues_of_card_cols_le`.
- `trace_conjStarAlgAut` → Mathlib `Unitary.conjStarAlgAut_apply`, `Matrix.trace_mul_cycle`;
  `trace_reindex` → `Equiv.sum_comp` (Mathlib has no lemma of that name).
- `matrixOf_curry_update_eq_add_single` → `ext`, `Function.update_apply`, `Matrix.single` (short);
  `sum_smul_sub_sum_smul_update_neg` → `Finset.sum_sub_distrib`, `Function.update_apply` (short).
  Neither has matrix content.

**Present but `private`**

- `trace_mul_diagonal_pow_mul_mul_diagonal_pow` (`tr (B * D ^ a * B * D ^ c)` as a weighted sum of
  `B i j ^ 2`) → `re_trace_mul_diagonal_mul_mul_diagonal`, private at
  `Functions/TracePowers.lean:156`, over `𝕜` and for any real diagonals. Used by
  `RandomMatrix/Gaussian/Wishart/SoftMin/InversePowerConcavity.lean:70`. Remove `private`, or
  re-derive in about five lines.

## 4. Coincidences (19)

The short name occurs upstairs, the declaration is not used. The parent structures `IsFullQR`,
`IsGradedColumnBasis`, `IsHessenbergForm`, `IsPivotedCholesky`, `IsLU`, `IsMoorePenroseInverse`,
`SymmetricGauge`, `UnitarilyInvariantNorm` do not occur at all in the upper layers (checked
case-insensitively; the one hit, `exists_isFullQR`, is in a docstring).

- `IsFullQR.eq`, `IsFullQR.mk`, `IsFullQR.orth`, `IsFullQR.upper`,
  `IsFullQR.conjTranspose_mul_eq`: the hits are fields of `IsQR` (mapped in the ledger), of the
  Krylov structure `IsGradedKrylovBasis`, `Prod.mk`, `NNReal.eq`, and prose.
- `IsGradedColumnBasis.mk`, `.nested`, `.orth`: same; `nested` is prose in
  `Sketching/Sparse/IIDComparison`.
- `IsHessenbergForm.eq`, `.mk`, `.orth`, `.isHermitian`: `isHermitian` is
  `Matrix.PosSemidef.isHermitian` and similar.
- `IsLU.submatrix` (hits are `Matrix.submatrix`), `IsMoorePenroseInverse.transpose` (hits are
  `Matrix.transpose`), `IsPivotedCholesky.mk`, `UnitarilyInvariantNorm.mk`, `SymmetricGauge.value`
  (prose).
- `IsSVD.apply`: no `h.apply` on an SVD upstairs; the 1387 hits are the tactic `apply`.
- `HasOrthonormalCols.orthonormal`: the three `.orthonormal` projections upstairs are
  `OrthonormalBasis.orthonormal`; the rest is prose. (It would be
  `hasOrthonormalCols_iff_orthonormal.mp` anyway.)

## 5. Ledger notes to correct

- Ported, ledger still `null`: `det_gram_fromCols_eq_mul_frobSq_sub_projector` and its complex
  twin (note says "no Gram determinant identity for an appended column in the new library"),
  `eigenvalues₀_eq_of_charpoly_eq` ("deferred"), `singularValues_gram_pow_mul`,
  `rank_gram_pow_mul` ("deferred"), `measurable_polarFrame_entry`, `measurable_canonicalQRFrame`
  ("deferred to M10"). New names in section 3.
- Covered by a later stage, note still says deferred: `specNorm_le_specNorm_map_ofReal`
  (`specNorm_complexify`), `specNorm_blockDiagonal_const_le` (`specNorm_kronecker`).
- Wrong substitute: `norm_matrixExp_sum_le_prod` (gap A3).
