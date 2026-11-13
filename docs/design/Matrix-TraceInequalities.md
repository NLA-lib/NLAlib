# Trace inequalities and the Loewner order

These six cards belong to the [matrix trace subsection](https://research.chen.pw/NLAlib/#matrix-trace)
of the [original atlas](https://github.com/tchen-research/NLAlib/tree/77514ce42a0e437d837797a063ac161f41022730).
The algebraic interfaces take arbitrary finite index types and use `[RCLike 𝕜]` wherever the
result works over both fields. The entrywise tail bound uses `Real.exp`. The two strip
inequalities have complex arguments even when the input matrices happen to be real.
The [library design](https://nla-lib.org/design/) places these results in the matrix layer.

The signatures use `open Matrix MeasureTheory Set`, `open scoped MatrixOrder ComplexOrder`,
and finite types `m n` with decidable equality where the native operations require it.
The vocabulary guide records the ordered products, strip weights and extended integral.

## Shared proof machinery

The scalar harmonic-measure step uses the following substitution directly in
the proof of the strip boundary integrals. It also gives the distribution of
the affine Cayley image of a uniformly distributed point on the unit circle.
The pin supplies the Jacobian substitution and the Cauchy density.

```lean
theorem Complex.circleAverage_eq_integral_cauchyPDFReal (a : ℝ) {b : ℝ≥0} (hb : 0 < b)
    (F : ℂ → ℝ) :
    Real.circleAverage (fun z => F ((a : ℂ) + ((b : ℝ) : ℂ) * Complex.I *
      ((1 + z) / (1 - z)))) 0 1 =
      ∫ w : ℝ, ProbabilityTheory.cauchyPDFReal a b w * F (w : ℂ)
```

For `A : Matrix n n ℂ` the single-factor power identities use Mathlib's
`cfc` and its positive real power. They supply the two list-product formulas
used by the finite-parameter interpolation estimate and the passage to
semidefinite matrices in the multivariate Araki–Lieb–Thirring theorem.
The nil and cons equations expose the product in either of those proofs.

```lean
theorem Matrix.PosDef.cfc_cpow_eq_exp_smul_log {A : Matrix n n ℂ}
    (hA : A.PosDef) (z : ℂ) :
    cfc (fun w : ℂ => w ^ z) A = NormedSpace.exp (z • cfc Real.log A)

theorem Matrix.PosSemidef.cfc_cpow_ofReal {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (r : ℝ) :
    cfc (fun w : ℂ => w ^ (r : ℂ)) A = A ^ r

theorem orderedMatrixCpow_eq_orderedMatrixExp_log
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosDef) (z : ℂ) :
    orderedMatrixCpow L z = orderedMatrixExp (L.map (cfc Real.log)) z

theorem orderedMatrixCpow_ofReal_eq_prod_rpow
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef) (r : ℝ) :
    orderedMatrixCpow L (r : ℂ) = (L.map (fun A => A ^ r)).prod
```

Both multivariate inequalities use `schattenNorm_rpow_abs_orderedMatrixExp_le_exp_integral`.
It gives the estimate at a finite strip parameter. Golden–Thompson takes that parameter to
zero, while Araki–Lieb–Thirring applies the estimate to logarithms of positive definite
approximations and then removes the regularization. Both proofs use `schattenNorm_rpow_abs`
to pass between a power of the modulus and a change of Schatten exponent. Their uniform
boundary estimates use `schattenNorm_le_card_rpow_mul_specNorm` to replace a matrix rank by
its column dimension, which remains fixed during regularization.

`NormedSpace.tendsto_pow_exp_of_tangent` supplies the power limit for both the classical
Lie product formula and the ordered-modulus limit. The former uses the differentiable-curve
corollary `HasDerivAt.tendsto_pow_inv_nat`. The latter first passes the tangent through the
modulus using `CFC.tendsto_smul_abs_sub_one_of_tendsto_smul_sub_one`.

## Schur products and the determinant root

**`schur-product-inequalities`.** The polynomial of degree one less than the dimension
certifies strict positivity of a real or complex PSD kernel with distinct rows. For real
matrices, each partial sum lies
below the full entrywise exponential in the Loewner order. The existing exponential-kernel
proof now uses the finite criterion. The proofs live with entrywise matrix functions.

```lean
theorem Matrix.PosSemidef.posDef_sum_inv_factorial_smul_map_pow_iff [Fintype n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    (∑ k ∈ Finset.range (Fintype.card n), (k.factorial : ℝ)⁻¹ • A.map fun t => t ^ k).PosDef ↔
      Function.Injective A.row

theorem Matrix.PosSemidef.sum_inv_factorial_smul_map_pow_le_map_exp [Finite n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) (N : ℕ) :
    (∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ • A.map fun t => t ^ k) ≤ A.map Real.exp
```

**`log-det-concavity`.** Equality in the determinant-root bound gives equality in the log-determinant
concavity bound after each positive definite matrix is scaled to determinant one. Strict
concavity forces those scaled matrices to agree. This gives an equality test for determinant
maximization. Setting both weights to one gives ordinary
Minkowski equality, and weights summing to one give equality in concavity of the determinant
root. Both use the following statement in `Inequalities/Minkowski`.

```lean
theorem Matrix.PosDef.re_det_smul_add_smul_rpow_eq_iff [Nonempty n] {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    RCLike.re (a • A + b • B).det ^ (Fintype.card n : ℝ)⁻¹ =
        a * RCLike.re A.det ^ (Fintype.card n : ℝ)⁻¹ +
        b * RCLike.re B.det ^ (Fintype.card n : ℝ)⁻¹ ↔
      ∃ c : ℝ, 0 < c ∧ A = c • B
```

## Block matrices and principal minors

**`psd-block-contraction`.** `Inequalities/Block` houses the sum and squared bilinear tests,
strict square-root contraction factorization and spectral-radius tests on positive definite
diagonal blocks. They use `quadForm`, `specNorm` and `specRadius`. The strict bilinear test
quantifies over nonzero vectors in each space. The factorization permits rectangular blocks.
Both formulations apply to Schur complement and preconditioning bounds.

```lean
theorem Matrix.PosDef.posDef_fromBlocks_iff_forall_norm_sq_lt
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.PosDef) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔ ∀ (x : m → 𝕜) (y : n → 𝕜), x ≠ 0 → y ≠ 0 →
      ‖star x ⬝ᵥ B *ᵥ y‖ ^ 2 < RCLike.re (quadForm A x) * RCLike.re (quadForm C y)

theorem Matrix.PosDef.posDef_fromBlocks_iff_exists_sqrt_mul_mul_sqrt
    {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜} (hA : A.PosDef) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔
      ∃ X : Matrix m n 𝕜, specNorm X < 1 ∧ B = CFC.sqrt A * X * CFC.sqrt C

theorem Matrix.PosDef.posDef_fromBlocks_iff_specRadius_lt_one [DecidableEq m]
    [DecidableEq n] {A : Matrix m m 𝕜} {B : Matrix m n 𝕜} {C : Matrix n n 𝕜}
    (hA : A.PosDef) (hC : C.PosDef) :
    (Matrix.fromBlocks A B Bᴴ C).PosDef ↔ specRadius (Bᴴ * A⁻¹ * B * C⁻¹) < 1
```

**`hadamard-fischer-inequalities`.** `Inequalities/Determinant` gives Hadamard equality for
PSD matrices, its column-norm form and Fischer equality for overlapping minors.
`Inequalities/PrincipalMinors` gives equality for deletion of a single index, the normalized
Szász chain across all positive orders and its consecutive equality case. The statements use
`principalMinor` and products over `Finset.powersetCard` directly. They apply to determinants
of Gram matrices and products of principal minors used for volume estimates.

```lean
theorem Matrix.PosSemidef.prod_re_principalMinor_rpow_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {d k l : ℕ} (hd : Fintype.card n = d + 1) (hkl : k ≤ l) (hl : l ≤ d) :
    (∏ s ∈ Finset.univ.powersetCard (l + 1), RCLike.re (principalMinor A s)) ^
        ((d.choose l : ℝ)⁻¹) ≤
      (∏ s ∈ Finset.univ.powersetCard (k + 1), RCLike.re (principalMinor A s)) ^
        ((d.choose k : ℝ)⁻¹)

theorem Matrix.PosDef.prod_re_principalMinor_rpow_eq_iff {A : Matrix n n 𝕜}
    (hA : A.PosDef) {d k : ℕ} (hd : Fintype.card n = d + 1) (hk : k < d) :
    (∏ s ∈ Finset.univ.powersetCard (k + 2), RCLike.re (principalMinor A s)) ^
        ((d.choose (k + 1) : ℝ)⁻¹) =
      (∏ s ∈ Finset.univ.powersetCard (k + 1), RCLike.re (principalMinor A s)) ^
        ((d.choose k : ℝ)⁻¹) ↔ A.IsDiag
```

## Ordered products

**`multivariate-araki-lieb-thirring`.** For $0<r<1$ the strip harmonic measure has density
$\sin(\pi r)/(2r(\cosh(\pi t)+\cos(\pi r)))$. The ordered powers are complex functional
calculus powers at $1+it$. Positive regularization and convergence of the logarithmic integral
extend the inequality to singular PSD inputs. In particular a zero norm contributes
$-\infty$ to the logarithm. The result lives in `Functions/PowerProducts`.

```lean
theorem log_schattenNorm_rpow_abs_prod_rpow_le_extendedLogIntegral
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ENNReal.log (ENNReal.ofReal (schattenNorm (ENNReal.ofReal p)
        ((CFC.abs (L.map (fun A => A ^ r)).prod) ^ (1 / r)))) ≤
      extendedLogIntegral (Real.stripHarmonicMeasure r)
        (fun t => schattenNorm (ENNReal.ofReal p) (orderedMatrixCpow L (1 + (t : ℂ) * I)))
```

**`multivariate-golden-thompson`.** As $r$ tends to zero the strip density becomes
$\pi/(2(\cosh(\pi t)+1))$. The boundary integrand is Lebesgue integrable. The
real logarithmic and exponentiated inequalities cover all finite dimensions and finite
Schatten exponents at least one. The ordered list retains the input order. The exponentiated
bound and the integrability theorem accompany the logarithmic form in
`Functions/MultivariateGoldenThompson`. Both multivariate results supply matrix-product
estimates for noncommuting PSD or Hermitian factors.

```lean
theorem log_schattenNorm_exp_sum_le_integral
    (H : List (Matrix n n ℂ)) (hH : ∀ A ∈ H, A.IsHermitian)
    {p : ℝ} (hp : 1 ≤ p) :
    Real.log (schattenNorm (ENNReal.ofReal p) (NormedSpace.exp H.sum)) ≤
      ∫ t : ℝ, Real.stripPoissonDensityZero t *
        Real.log (schattenNorm (ENNReal.ofReal p) (orderedMatrixExp H (1 + (t : ℂ) * I)))
```

## Dependencies and placement

* `ForMathlib/Analysis/Complex/Poisson` computes the strip densities and the associated
  probability measure. `ForMathlib/Analysis/Complex/Hadamard` gives the weighted boundary
  estimate for scalar holomorphic functions. Its scalar logarithmic submean inequality lives
  in `ForMathlib/Analysis/Complex/JensenFormula`. The disk-to-strip coordinates in the proof
  transport Mathlib's circle averages. Mathlib's three-lines supremum estimate lacks the
  boundary integrals required by the two cards.
* `Matrix/Norms/SchattenInterpolation` proves the strip estimate with the existing SVD,
  Schatten and spectral norms. `Matrix/Functions/AbsoluteValue` expresses the singular
  values of powers of the modulus. `Matrix/Perturbation/Continuity` gives continuity of the
  Schatten expression for finite positive exponents, including those below one.
* `Matrix/Functions/OrderedExponential` and `Matrix/Functions/ExponentialInterpolation`
  specialize the strip estimate to ordered exponentials. The former establishes the limiting
  power formula. `ForMathlib/Analysis/SpecialFunctions/Exponential` contains its Banach-algebra
  limit and `ForMathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs` handles
  the first-order limit for the modulus. The classical two-factor Lie product in
  `Matrix/Functions/GoldenThompson` uses the same power-limit argument.
* `ForMathlib/MeasureTheory/Integral/Log` integrates the positive and negative parts of
  Mathlib's extended logarithm and justifies passage through decreasing positive
  regularizations. The finite Schatten integrals and spectral bounds ensure finiteness of its
  positive part. A zero factor can give an infinite negative part.

The algebraic proofs draw on Horn and Johnson, *Matrix Analysis*, chapters 7.5–7.8.
The integral inequalities follow Theorem 3.2 and Corollary 3.3 of
[Sutter, Berta and Tomamichel](https://doi.org/10.1007/s00220-016-2778-5).
The source atlas supplied finite-dimensional proofs and the explicit zero conventions.
The implementation reuses native Schatten norms, CFC, Gram matrices, eigenvalues and matrix
order. The atlas's convenience bundles and duplicate real-only forms are recovered by
specializing the statements above.

## Boundary measures and the extended logarithm

Use the normalized probability `Real.stripHarmonicMeasure r` for each boundary
expectation. The two coefficients are the harmonic masses of the two lines.
The scalar and matrix inequalities have the same boundary expression.

```lean
(1 - r) * (∫ t, h₀ t ∂Real.stripHarmonicMeasure (1 - r)) +
  r * (∫ t, h₁ t ∂Real.stripHarmonicMeasure r)
```

`Real.integral_stripHarmonicMeasure` converts each expectation to its density
formula. The endpoint limit uses the existing limiting density. The Cayley
coordinates and the logarithm branch estimates serve a single proof. The
public Cayley transport identity and the two boundary inequalities supply
the reusable facts for Schatten interpolation.

The positive and negative Lebesgue parts give three interfaces.

```lean
(∀ᵐ x ∂μ, 0 < g x) → Integrable (fun x => Real.log (g x)) μ →
  extendedLogIntegral μ g = ((∫ x, Real.log (g x) ∂μ : ℝ) : EReal)
(g ≤ᵐ[μ] h) → extendedLogIntegral μ g ≤ extendedLogIntegral μ h
Measurable g → μ {x | g x ≤ 0} ≠ 0 → extendedLogIntegral μ g = ⊥
```

The first equality uses Mathlib's
`integral_eq_lintegral_pos_part_sub_lintegral_neg_part`. The last uses
`lintegral_eq_top_of_measure_eq_top_ne_zero` for the negative part.
The upper-deficit formula is exposed with an explicit right hand side.
For positive definite factors in positive dimension, the inverse-product
estimate bounds the logarithm below. In dimension zero every matrix has zero
Schatten norm. Mathlib defines the real logarithm of zero as zero, so the
integrand vanishes and the real inequality reads $0\le 1$. Both cases are
included in the finite form.

```lean
theorem schattenNorm_rpow_abs_prod_rpow_le_exp_integral_log
    {n : Type*} [Fintype n] [DecidableEq n]
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosDef) {p r : ℝ}
    (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    schattenNorm (ENNReal.ofReal p) ((CFC.abs (L.map (fun A => A ^ r)).prod) ^ (1 / r)) ≤
      Real.exp (∫ t, Real.log (schattenNorm (ENNReal.ofReal p)
        (orderedMatrixCpow L (1 + (t : ℂ) * Complex.I))) ∂Real.stripHarmonicMeasure r)
```

`integrable_log_schattenNorm_orderedMatrixCpow` gives the finite-integral
hypothesis for any finite boundary measure. Positive semidefinite inputs have
a continuous right-boundary product and its uniform operator-norm bound by the
product of the factor norms. These two facts are used in the regularization
proof for positive semidefinite factors. The list regularization and bounds
for the auxiliary displacement parameter stay private.
