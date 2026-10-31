# Discrete Stein equations

Design for the 2026-10-31 migration, base `d755c1adac581e9ea2b28df5f0f4890043aca5bd`.

## Objects and interfaces

No new definitions, predicates, or vocabulary rows. Use ordinary matrix powers, finite sums,
`Summable` and `tsum`, `Matrix.PosSemidef`, `Matrix.PosDef`, `MatrixOrder`, `specRadius`,
`specNorm`, and `frobNorm`. The forcing and solutions are arbitrary square matrices over
`RCLike`; positivity is separate. Empty finite index types are supported throughout.

## Signatures

The namespace is `NLAlib`, with variables
`{𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]`.

```lean
theorem sum_range_pow_mul_mul_conjTranspose_add (A Q : Matrix n n 𝕜) (M N : ℕ) :
    (∑ j ∈ Finset.range (M + N), A ^ j * Q * (Aᴴ) ^ j) =
      (∑ j ∈ Finset.range M, A ^ j * Q * (Aᴴ) ^ j) +
        A ^ M * (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) * (Aᴴ) ^ M
theorem sub_sum_range_pow_mul_mul_conjTranspose (A Q X : Matrix n n 𝕜)
    (hX : X - A * X * Aᴴ = Q) (N : ℕ) :
    X - (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) = A ^ N * X * (Aᴴ) ^ N
theorem sub_sum_range_add_mul_sum_range_mul_conjTranspose (A Q : Matrix n n 𝕜) (N : ℕ) :
    Q - (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) +
      A * (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ =
        A ^ N * Q * (Aᴴ) ^ N
theorem Matrix.PosSemidef.sum_range_pow_mul_mul_conjTranspose {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (A : Matrix n n 𝕜) (N : ℕ) :
    (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j).PosSemidef
theorem Matrix.PosSemidef.monotone_sum_range_pow_mul_mul_conjTranspose {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (A : Matrix n n 𝕜) :
    Monotone (fun N => ∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j)
theorem summable_pow_mul_mul_conjTranspose (A Q : Matrix n n 𝕜)
    (hA : specRadius A < 1) : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)
theorem sub_mul_mul_conjTranspose_tsum (A Q : Matrix n n 𝕜)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) -
      A * (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) * Aᴴ = Q
theorem eq_tsum_pow_mul_mul_conjTranspose (A Q X : Matrix n n 𝕜)
    (hA : specRadius A < 1) (hX : X - A * X * Aᴴ = Q) :
    X = ∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j
theorem Matrix.PosSemidef.tsum_pow_mul_mul_conjTranspose {Q : Matrix n n 𝕜}
    (hQ : Q.PosSemidef) (A : Matrix n n 𝕜)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j).PosSemidef
theorem Matrix.PosDef.tsum_pow_mul_mul_conjTranspose {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) (A : Matrix n n 𝕜)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j).PosDef
theorem existsUnique_sub_mul_mul_conjTranspose_eq (A Q : Matrix n n 𝕜)
    (hA : specRadius A < 1) : ∃! X : Matrix n n 𝕜, X - A * X * Aᴴ = Q
theorem SymmetricGauge.matrixNorm_tsum_pow_mul_mul_conjTranspose_le
    (Φ : SymmetricGauge) {A Q : Matrix n n 𝕜} {q : ℝ}
    (hA : specNorm A ≤ q) (hq : q < 1) :
    Φ.matrixNorm (∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) ≤ Φ.matrixNorm Q / (1 - q ^ 2)
theorem SymmetricGauge.matrixNorm_tsum_sub_sum_range_pow_mul_mul_conjTranspose_le
    (Φ : SymmetricGauge) {A Q : Matrix n n 𝕜} {q : ℝ}
    (hA : specNorm A ≤ q) (hq : q < 1) (N : ℕ) :
    Φ.matrixNorm ((∑' j : ℕ, A ^ j * Q * (Aᴴ) ^ j) -
      (∑ j ∈ Finset.range N, A ^ j * Q * (Aᴴ) ^ j)) ≤
        q ^ (2 * N) * Φ.matrixNorm Q / (1 - q ^ 2)
theorem specRadius_lt_one_iff_exists_posDef_sub_mul_mul_conjTranspose
    (A : Matrix n n 𝕜) :
    specRadius A < 1 ↔ ∃ X : Matrix n n 𝕜, X.PosDef ∧ (X - A * X * Aᴴ).PosDef
```

Result ids: `stein-equation` (convergence, equation, uniqueness),
`stein-series-truncation` (unitarily invariant norm bounds), and
`stein-stability-certificate` (stability equivalence). No Smith-algorithm claims or ids.

2026-10-31 review amendment: replace separate spectral and Frobenius estimates with arbitrary
`SymmetricGauge.matrixNorm` estimates. Their specializations follow from
`lpGauge_top_matrixNorm` and `lpGauge_two_matrixNorm`. Bound the full sum from its equation and
the gauge triangle/product inequalities, so no extra norm-continuity machinery is needed.
Include the explicit unique-existence endpoint.

2026-10-31 naming review amendment: the sum-equation theorem is named
`sub_mul_mul_conjTranspose_tsum`, matching the leading subtraction in its conclusion.
The proposed public exact-tail specialization is omitted: instantiate
`sub_sum_range_pow_mul_mul_conjTranspose` with the full series and
`sub_mul_mul_conjTranspose_tsum`. The unitarily invariant tail bound uses that direct
specialization. No compatibility alias is needed for these unpublished declarations.

## Reuse, material, and consumers

The source is the Stein partial-sum, Gramian, geometric-bound and real-certificate development
in `tchen-research/NLAlib` commit `77514ce42a0e437d837797a063ac161f41022730`, evaluated as mathematics and
proof material. Native sums replace its wrappers; `RCLike` replaces its real/complex twins.
The source's Frobenius scoped-topology proof is replaced by a unitarily invariant norm argument.
The source's Smith doubling algorithms are outside this matrix-analysis migration.

Mathlib and the whole current Matrix layer were searched by the migration explorer: no Stein
or discrete Lyapunov theory exists. Reuse `exists_forall_specNorm_pow_le_mul_pow`,
`tendsto_pow_zero_iff_specRadius_lt_one`, `specNorm_pow_le`,
`exists_mem_spectrum_norm_eq_specRadius`, the native complexification API,
`exists_vecMul_eq_smul_of_mem_spectrum`, quadratic-form API,
`Matrix.PosSemidef.of_hasSum`, and `SymmetricGauge` triangle and mixed product bounds. Native
finite-sum splitting, summable-series limits, and geometric-series identities are supporting
API, not duplicated public lemmas.

2026-10-31 citation review: the integration reviewer inspected Stephen Boyd's EE363 lecture 13,
<https://ee363.stanford.edu/archive/lectures/lq-lyap.pdf>, slides 13–21 through 13–23.
Slide 13–22 supports the real Stein series solution and uniqueness for symmetric forcing;
slides 13–21 through 13–23 support the real stability certificate. These are cited as
`Boyd2009`, with the extension to arbitrary forcing over `RCLike` stated explicitly.
The printed transpose orientation is obtained by applying the real
statement to the transpose of the present matrix. The sum-identity theorem further replaces
stability by summability. No printed source has been verified for the arbitrary
`SymmetricGauge` norm estimates, which retain the explicit “No printed source” statement.

All additions live in `NLAlib/Matrix/Spectral/SteinEquation.lean`, alongside the Sylvester
equation topic. Finite identities precede convergence, equation and positivity, norm bounds,
then the stability equivalence. No changes outside this file and this design note are planned.
Consumers are matrix-equation error analyses, control Gramians, and later Smith/low-rank
algorithms, which can rewrite with native sums and use the spectral-radius hypothesis for
existence without imposing norm contraction. No unresolved interface questions.
