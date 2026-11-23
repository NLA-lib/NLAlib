# Pseudospectral shattering by Gaussian perturbations

A deterministic complex matrix $\mathbf{M}$ of order $n$ plus a normalized complex Gaussian
perturbation $\gamma n^{-1/2}\mathbf{G}$ has, with high probability, well-separated eigenvalues
and a well-conditioned eigenvector matrix ([BanksKulkarniMukherjeeSrivastava2021, Theorem 1.5],
[BanksGarzaVargasKulkarniSrivastava2020]). This note covers the first two results
of that topic, polynomial tails for the eigenvector condition number and for the eigenvalue gap,
and the dependencies they add to lower files. Later shattering results (the full shattering
statement with a grid, other perturbation laws) join the same home.

## 1. Objects and interfaces

No new definitions or hypothesis interfaces. The statements use `complexGaussian`,
`complexGaussianVector`, `complexGaussianMatrix`, `HasLaw`, `Matrix.IsStarProjection`,
`singularValues`, `IsEigenvalueListing` and `pseudoConditionNumber` directly, and the events are
the existing listing and diagonalizer events, so no random spectral statistic (a measurable
eigenvector selection, a random gap) is defined. The field is ℂ because the small-ball exponent
counts two real coordinates per entry. Index types are arbitrary finite types, including the
empty and singleton cases.

## 2. Statement shapes

The two headline tails, for $0 < 2\gamma \le \|\mathbf{M}\|_2$, in `NLAlib/RandomMatrix/Shattering/`:

```lean
theorem measureReal_not_exists_pseudoConditionNumber_le_le_log_sq_of_hasLaw_complexGaussianMatrix
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {γ t : ℝ} (hγ : 0 < γ) (hγM : 2 * γ ≤ specNorm M) (ht : 0 < t) (ht1 : t ≤ 1) :
    μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
      (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ t⁻¹} ≤
      (128 * Real.exp 1) * (Fintype.card n : ℝ) ^ 3 * t ^ 2 *
        (specNorm M / γ + Real.log t⁻¹) ^ 2

theorem measureReal_not_exists_isEigenvalueListing_le_le_log_sq_of_hasLaw_complexGaussianMatrix
    (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {γ t : ℝ} (hγ : 0 < γ) (hγM : 2 * γ ≤ specNorm M) (ht : 0 < t) (htγ : t ≤ γ) :
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
      (2048 * Real.exp 1) * (Fintype.card n : ℝ) ^ (11 / 3 : ℝ) * (t / γ) ^ (2 / 3 : ℝ) *
        (specNorm M / γ + Real.log (γ / t)) ^ 2
```

Each has an asymptotic corollary (`exists_forall_…`) with the constants $(C, a, b, c)$ existential
and $b > 0$. These are weaker than the printed tails ($n^3t^2/\gamma^2$ for the gap, a
$2(2\sqrt2 + \|\mathbf{M}\|_2/\gamma + \sqrt{4\log(1/t)/n})^2n^3t^2$ condition tail) by
polynomial and logarithmic factors; the eigensolvers that consume them need only some polynomial
tail.

Lower-file results, each general and stated for later use:

| Declaration | File | Statement |
|---|---|---|
| `measureReal_norm_sub_le_le_of_hasLaw_complexGaussian` | `RandomMatrix/Gaussian/Complex` | $\mathbb{P}[\lvert z - a\rvert \le s] \le s^2$ for every center $a$ |
| `measureReal_specNorm_add_smul_ge_mul_le_of_hasLaw_complexGaussianMatrix` | same | the norm cutoff $\mathbb{P}[3\gamma(\|\mathbf{M}\|_2/\gamma + \log(1/\tau)) \le \|\mathbf{M} + \gamma n^{-1/2}\mathbf{G}\|_2] \le \tau^2$ |
| `measureReal_norm_mulVec_add_le_le_of_hasLaw_complexGaussianVector` | `…/Complex/LeastSingularValue` | shifted projected small ball $s^2$ |
| `measureReal_norm_mulVec_add_le_le_pow_four_of_hasLaw_complexGaussianVector` | same | rank $\ge 2$ projection: $s^4$ |
| `measureReal_singularValues_add_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix` | same | shifted least singular value $e\,n x^2$ (the unshifted one is its specialization) |
| `measureReal_singularValues_add_smul_le_le_pow_four_of_hasLaw_complexGaussianMatrix` | same | second-smallest singular value $n^5(x/\gamma)^4$ |
| `ae_charpoly_separable_of_hasLaw_complexGaussianMatrix` | `…/Complex/SimpleSpectrum` | almost surely simple spectrum |
| `ae_eval_ne_zero_of_ne_zero` | `RandomMatrix/Gaussian/Rank` | generalized from ℝ to `RCLike` |
| `exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_sq_le` | `Matrix/Spectral/Diagonalizable` | unit-column diagonalizer, $\kappa_V^2 \le n\sum_i\kappa(\lambda_i)^2$ |
| `eventually_sum_mul_sq_le_measureReal_inter_ball_of_mul_eq_mul_diagonal`, `ofReal_sq_div_card_le_liminf_measure_inter_ball_of_not_exists` | `Matrix/Perturbation/PseudospectralArea` | local area lower bound of the $\varepsilon$-pseudospectrum near simple eigenvalues |
| `singularValues_le_mul_pseudoConditionNumber_of_mul_eq_mul_diagonal`, `exists_mem_singularValues_le_of_not_exists_isEigenvalueListing` | `Matrix/Perturbation/EigenvalueClustering` | two eigenvalues near $z$ force a small second singular value of $z\mathbf{I} - \mathbf{A}$ |
| `exists_finset_card_mul_sq_le_and_forall_norm_sub_le` | `Matrix/QRIteration/SquareGrid` | an $r/2$-net of a disk with $36(R/r)^2$ points |

## 3. Consumers

The two tails feed the diagonalization class of a Ginibre perturbation that the small-eigenvalue
solver of [BanksGarzaVargasSrivastava2025] consumes, through the stage's tail records
(`NLAlib/Eigensolvers/SmallEig/`). The shifted small balls and singular-value tails are general
smoothed-analysis facts.

## 4. Files and placement

* `NLAlib/RandomMatrix/Shattering/` is the home of the probabilistic shattering results, a
  subfolder of the RandomMatrix layer (no layer entry needed).
  * `ConditionTail.lean`: the area argument (Fubini, Fatou, Markov) and the condition tail.
  * `GapTail.lean`: the net argument and the gap tail; imports `ConditionTail`.
* Deterministic facts stay in Matrix, where their subject is: the local pseudospectral area
  inequality and the eigenvalue-cluster estimate beside `Matrix/Perturbation/Pseudospectrum.lean`;
  the diagonalizer rescaling in `Matrix/Spectral/Diagonalizable.lean`. A later deterministic
  shattering file (a shattered pseudospectrum bounds $\kappa_V$ and the gap) goes in
  `Matrix/Perturbation` beside them.
* Gaussian facts stay in their Gaussian files: small balls, norm tails, singular values,
  simple spectrum (`RandomMatrix/Gaussian/Complex*`).
* **Flagged:** the disk net `exists_finset_card_mul_sq_le_and_forall_norm_sub_le` is plane
  geometry, not QR iteration. It sits in `Matrix/QRIteration/SquareGrid.lean` because it is a
  corollary of the square grid's covering and cardinality bounds, which live there with
  `squareGrid` (the exceptional-shift grid). Its intended home, with the grid itself, is a
  plane-geometry file; moving `squareGrid` is a separate refactor.

## 5. Proofs

**Condition tail.** `Diagonalizable` rescales each eigenvector column to unit norm: then
$\|\mathbf{V}\|_F^2 = n$ and $\|\mathbf{V}^{-1}\|_F^2 = \sum_i\kappa(\lambda_i)^2$, the sum of
the squared eigenvalue condition numbers. `PseudospectralArea` shows that, near a simple
eigenvalue, the rescaled resolvent tends to the rank-one spectral projector, so for small
$\varepsilon$ the disks of radius $\varepsilon\kappa(\lambda_i)/2$ lie in the
$\varepsilon$-pseudospectrum, are disjoint and lie in a fixed disk: a one-sided area bound with
factor four (no area equality is needed). `ConditionTail` integrates the pseudospectral area over
the Gaussian law (parameterized integration gives measurability; Fubini and the shifted
least-singular-value tail bound its mean), applies Fatou to the liminf of the normalized areas,
and contains the diagonalizer failure event, on the norm cutoff, almost surely in a superlevel
set of that measurable liminf. Markov then applies, with no measurable eigenvector selection.
The norm cutoff at $u = \sqrt{2\log(1/t)}$ has radius at most $3\gamma K$,
$K = \|\mathbf{M}\|_2/\gamma + \log(1/t)$, and the constants are $(128e, 3, 2, 2)$.

**Second-smallest singular value** (no printed source; an elementary route, weaker than
Szarek's exact law or Śniady's coupling). Singular values are indexed in decreasing order.

1. *Rank-two small ball.* For a projector $P$ of rank at least two, orthonormal $u, v$ in its
   range give independent standard complex Gaussians $u^*\mathbf{g}$, $v^*\mathbf{g}$ (unitary
   invariance), so $\mathbb{P}[\|P(\mathbf{g} + a)\| \le s] \le s^4$ by two shifted disks.
2. *Rectangular least singular value.* For an $n \times (n-1)$ shifted Gaussian $\mathbf{Y}$, a
   unit $w$ with $\|\mathbf{Y}w\| \le x$ has a coordinate $|w_j| \ge (n-1)^{-1/2}$, so column $j$
   is within $\sqrt{n-1}\,x$ of the span of the others, whose complement has dimension at least
   two. Conditioning on the other columns and a union over $j$ give
   $\mathbb{P}[\sigma_{\min}(\mathbf{Y}) \le x] \le (n-1)^3x^4$. The union over fixed column
   indices avoids a measurable choice of $j$ or of a basis of the complement.
3. *Column deletion.* Deleting a fixed column does not increase the second-smallest singular
   value (`singularValues_submatrix_le`), so for the normalized perturbation
   $\mathbb{P}[\sigma_{n-1}(\mathbf{M} + \gamma n^{-1/2}\mathbf{G}) \le x] \le n^5(x/\gamma)^4$.

**Gap tail.** Put $\tau = t/\gamma$, $q = (n\tau)^{1/3}$ (when $n\tau \le 1$; otherwise the bound
exceeds $1$), condition cutoff $B = 1/q$, norm cutoff
radius $R = 3\gamma K$ with $K = \|\mathbf{M}\|_2/\gamma + \log(1/\tau)$, and a $t/2$-net of
$36(R/t)^2$ points of the disk of radius $R$. If two eigenvalues are within $t$, some net point
$y$ has both within $t$, and on the diagonalizer event `EigenvalueClustering` gives
$\sigma_{n-1}(y\mathbf{I} - \mathbf{X}) \le 2tB$. The three failure probabilities are at most
$128e\,n^3q^2K^2$ (condition at $q$), $\tau^2$ (norm) and
$36(R/t)^2n^5(2tB/\gamma)^4 = 576\,n^3q^2(R/\gamma)^2 \le 5184\,n^3q^2K^2$ (net, as $q^6 = n^2\tau^2$),
and sum to at most $2048e\,n^3q^2K^2 = 2048e\,n^{11/3}\tau^{2/3}K^2$: constants
$(2048e, 11/3, 2/3, 2)$, with no additive floor. The cutoff balances the net term against the
condition tail (the earlier $q = \tau^{1/4}$ gave $(10000e, 5, 1/2, 2)$). Orders
$0$ and $1$ have no pair of eigenvalues and are handled separately.

## 6. Shared machinery

* The unshifted small-ball, least-singular-value and probe tails are specializations of the
  shifted ones: one column-distance argument and one Fubini/probe argument.
* The norm cutoff at a logarithmic scale is one lemma
  (`measureReal_specNorm_add_smul_ge_mul_le_of_hasLaw_complexGaussianMatrix`) used by both tails.

## 7. Material

Mathlib: `prod_withDensity`, `Complex.volume_preserving_equiv_real_prod`,
`Complex.volume_closedBall` and the Gaussian density give the shifted disk bound directly
(Anderson's inequality is not needed); `lintegral_liminf_le` and `mul_meas_ge_le_lintegral₀`
give Fatou and Markov. Searched for a shifted complex Gaussian small ball: none. NLAlib: the
unitary invariance of `complexGaussianVector`, the column-distance argument of
`LeastSingularValue`, the probe lemmas, `squareGrid` and the polynomial-zero theorem of
`Gaussian/Rank` (applied to the resultant of the characteristic polynomial and its derivative,
nonzero at a diagonal matrix with distinct entries).

## 8. Open questions

* The preferred tails ($n^3t^2/\gamma^2$ for the gap) need the exact second-singular-value law
  or a sharper conditioning bound; recommend leaving them as stated targets until a consumer
  needs the exponents.
