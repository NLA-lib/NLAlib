# Ginibre perturbations: gap and eigenvector conditioning

This implements the dependency work authorized by
`nlalib-harness/reports/Spec-RandomMatrix-GinibreGapKappaV.md` (2026-11-16).
The final two event bounds remain the contract; intermediate polynomial bounds
do not replace them.

## Objects and interfaces

Use `complexGaussian`, `complexGaussianVector`, `complexGaussianMatrix`,
`HasLaw`, `Matrix.IsStarProjection`, `singularValues`, `IsEigenvalueListing`
and `pseudoConditionNumber` directly. No new definitions or hypothesis interfaces.
The field is complex because the small-ball exponent uses two real coordinates.
Index types remain arbitrary finite types.

## Shifted small balls

Add the following scalar result in `RandomMatrix/Gaussian/Complex.lean`:

```lean
theorem measureReal_norm_sub_le_le_of_hasLaw_complexGaussian
    {z : Ω → ℂ} (hz : HasLaw z complexGaussian μ) (a : ℂ)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ‖z ω - a‖ ≤ s} ≤ s ^ 2
```

Add a shifted projection result and a shifted least-singular-value result in
`RandomMatrix/Gaussian/Complex/LeastSingularValue.lean`:

```lean
theorem measureReal_norm_mulVec_add_le_le_of_hasLaw_complexGaussianVector
    {g : Ω → n → ℂ} (hg : HasLaw g (complexGaussianVector n) μ)
    {P : Matrix n n ℂ} (hP : IsStarProjection P) (hP₀ : P ≠ 0)
    (a : n → ℂ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ‖WithLp.toLp 2 (P *ᵥ (g ω + a))‖ ≤ s} ≤ s ^ 2

theorem measureReal_singularValues_add_le_le_of_hasLaw_complexGaussianMatrix
    {G : Ω → Matrix n n ℂ} (hG : HasLaw G (complexGaussianMatrix n n) μ)
    (A : Matrix n n ℂ) {k : ℕ} (hk : k + 1 = Fintype.card n)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (A + G ω) k ≤ x} ≤
      (Fintype.card n : ℝ) ^ 2 * x ^ 2
```

The existing unshifted results specialize the shifted results. The column-distance
argument is shared, rather than duplicated. Deterministic projection helpers stay
private because they are proof-local. The probe argument is also generalized over a deterministic shift, giving the
following stronger tail and its normalized corollary in the same file:

```lean
theorem measureReal_singularValues_add_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix
    {G : Ω → Matrix n n ℂ} (hG : HasLaw G (complexGaussianMatrix n n) μ)
    (M : Matrix n n ℂ) {k : ℕ} (hk : k + 1 = Fintype.card n)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (M + G ω) k ≤ x} ≤
      Real.exp 1 * (Fintype.card n : ℝ) * x ^ 2

theorem measureReal_singularValues_add_smul_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix
    {G : Ω → Matrix n n ℂ} (hG : HasLaw G (complexGaussianMatrix n n) μ)
    (M : Matrix n n ℂ) {k : ℕ} (hk : k + 1 = Fintype.card n)
    {γ x : ℝ} (hγ : 0 < γ) (hx : 0 ≤ x) :
    μ.real {ω | singularValues (M + (γ / √(Fintype.card n : ℝ)) • G ω) k ≤ x} ≤
      Real.exp 1 * (Fintype.card n : ℝ) ^ 2 * x ^ 2 / γ ^ 2
```

The unshifted probe tail also becomes a specialization, so there is one proof of
the Fubini/probe argument. Existing deterministic probe lemmas are reused unchanged.

## Consumers and normalization

R3 feeds pointwise pseudospectral area estimates (R5); the shifted projection
estimate also supports conditioning on columns for the second-smallest singular
value (R7′). A standard Gaussian bound `n² x²` becomes `n³ x² / γ²`
under the spec's `γ / √n` scaling. Obtaining the preferred R3 `n² x² / γ²`
requires improving the standard Gaussian coefficient to `n`, not only adding a shift.
The polynomial loss is acceptable for the final weaker gap/conditioning forms.
The probe extension reduces this to a constant factor `e` relative to the preferred R3.

## Sources and reuse

Read the supplied spec and the existing complex Gaussian, least singular value,
and pseudospectrum files. Search Mathlib's Gaussian distribution and Lebesgue
measure files and NLAlib before adding statements. No existing shifted complex
small-ball theorem was found. Use Mathlib's `prod_withDensity`,
`Complex.volume_preserving_equiv_real_prod`, `Complex.volume_closedBall`,
and the Gaussian density instead of proving Anderson's inequality.
Reuse NLAlib's unitary invariance and column-distance argument.

## Completing the two event bounds

`Complex/SimpleSpectrum.lean` applies the atomless polynomial-zero theorem to
`resultant(charpoly, derivative charpoly)`. The underlying polynomial theorem in
`Gaussian/Rank.lean` is generalized from real to `RCLike` coefficients; the complex
Gaussian singleton-null instance supplies atomlessness. A prescribed diagonal
matrix with distinct entries witnesses that the resultant is nonzero for every
mean and every nonzero perturbation scale.

`Matrix/Spectral/Diagonalizable.lean` rescales each eigenvector column to have
unit Euclidean norm. Its Frobenius norm squared is then the dimension, and the
inverse Frobenius norm squared is the sum of squared eigenvalue condition
numbers. This gives the diagonalizer-condition inequality R6 without selecting
random eigenvectors.

`Matrix/Perturbation/PseudospectralArea.lean` proves a one-sided local area bound
with factor four. The rescaled resolvent near a simple eigenvalue converges to
its rank-one spectral projector. Thus disks with radii equal to one half of
`ε` times the corresponding eigenvalue condition number lie in the
`ε`-pseudospectrum for small enough `ε`. They are eventually disjoint and inside
a deterministic spectral disk. Only this lower bound, not an area equality,
is needed.

`Complex/Shattering.lean` integrates these pseudospectral areas over a fixed
disk. Parameterized integration proves their measurability. Fubini, the shifted
least-singular-value bound and Fatou bound the expectation of the area liminf.
The failure to admit a diagonalizer of condition number at most `B`, on the norm
cutoff event, is contained almost surely in a superlevel set of that measurable
liminf. Markov therefore applies without any measurable eigenvector selection.
The resulting explicit conditioning tail has constants
`(C,a,b,c) = (128e,3,2,2)`.

For the gap bound, the rank-two projected Gaussian small ball has exponent four.
Conditioning on all other columns gives a rectangular least-singular-value tail;
deleting one fixed column and singular-value interlacing give
`P[σ_(n-2)(M+(γ/√n)G) ≤ x] ≤ n⁵(x/γ)⁴` with zero-based indices.
The deterministic two-eigenvalue bound lives in
`Matrix/Perturbation/EigenvalueClustering.lean`. The disk-net corollary in
`Matrix/QRIteration/SquareGrid.lean` gives a covering radius `r/2` and cardinality
at most `36(R/r)²`.

Choose `τ=r/γ`, `q=√(√τ)`, diagonalizer cutoff `B=1/q`, and Gaussian norm cutoff
`u=√(2 log(1/τ))`. Write `K=‖M‖/γ+log(1/τ)`; the spectral disk radius is at most
`3γK`. The conditioning failure is at most `128e n³√τ K²`, the norm failure is
`τ²`, and the net failure is at most `5184 n⁵τ K²`. These give the acceptable gap
constants `(C,a,b,c) = (10000e,5,1/2,2)`, with no additive error floor.
Both final existential statements retain the spec's laws, events, parameter
ranges and normalization. Index types are arbitrary finite types, including the
empty and singleton cases.

The [research note](research/GinibreSecondSingularValue.md) records the elementary
fourth-power argument and the constants used in the final implementation.

## Completion validation

The combined `Complex.Shattering` build passed on 2026-11-16 (3,629 jobs).
It checks both exact existential forms and the explicit constants above.
The generated library root imports all four new modules.
The full repository check is running, with log
`/tmp/ginibre-rmt-final-stage.log`. The first full run passed the build and
axiom audit, then found an unused probability-measure assumption on the private
Fatou/Markov helper. That assumption is removed; the complete check is rerunning.
