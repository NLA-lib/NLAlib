# Design note: Probability stage P2, standard laws

Status: written 2026-10-14 by the orchestrator under `docs/PORT_PROBABILITY.md` (§2 decided). The
carrier and naming of the Gaussian law with complex analogues in view is the choice D4 leaves to
this note (§7 Q1); no question of the brief's §2 kind. Reviewed by a Fable agent on 2026-10-14;
the corrections are listed in §8 and the skeletons
(`NLAlib/Probability/Distributions/{Gaussian,Rademacher,Sampling}.lean`) carry them; where §3 and
a skeleton differ, the skeleton is the statement.

## 0. Scope and consumers

The laws the layers above sample from: the standard Gaussian scalar and vector, the Rademacher
scalar and vector, and the law of an index drawn from a finite probability vector. Each law is a
`Measure`, each is proved to satisfy the P0/P1 interfaces it has, with the exact moments the
consumers use; every statement takes a random variable with `HasLaw` (D2).

| Item | Consumers (prototype files) |
|---|---|
| `gaussianVector n`; its coordinates i.i.d. standard Gaussian | Estimation 5, LowRank and R1 (Gaussian matrices are built from it), P3, P4 |
| Gaussian: sub-Gaussian proxy, `m₂ = 1`, `m₄ = 3`, isotropy, law of `u ⬝ᵥ X`, bridge to Mathlib's `stdGaussian` | P3 (Hutchinson variance, χ², sub-Gaussian vector instance), JL (law of `Gx`), R1 (rotation invariance through `stdGaussian_map`) |
| `rademacherMeasure`, `rademacherVector n`; proxy `1`, `X² = 1` a.s., `m₄ = 1`, isotropy | Sketching 5, Estimation 8 (Hutchinson with Rademacher probes, SRHT signs, CountSketch signs) |
| `samplingMeasure p`: an index with `P(i) = p i` | Sketching 3, LowRank 1 (leverage-score and uniform row sampling) |

Not here: Gaussian matrices (R1), sub-Gaussian vectors and their instances (P3, which defines the
interface), Rademacher sign-flip symmetry (P5, with the Khintchine recursion that is its only
consumer), Gaussian integration by parts (P6), general Gaussian measures (`IsGaussian`,
`multivariateGaussian`: Mathlib's, used as they are when P4 or P6 needs them).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| standard Gaussian scalar | Mathlib's `gaussianReal 0 1`; general variance `gaussianReal 0 v`, `v : ℝ≥0` | — |
| standard Gaussian vector in `ℝⁿ` | `gaussianVector n := Measure.pi fun _ : n => gaussianReal 0 1`, an `abbrev` on `n → ℝ` | `gaussianVector_map_toLp : (gaussianVector n).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ n)` (from `map_pi_eq_stdGaussian`) |
| Rademacher scalar | `rademacherMeasure : Measure ℝ := bernoulliMeasure 1 (-1) (1 / 2)` | Mathlib's `bernoulliMeasure` |
| Rademacher vector | `rademacherVector n := Measure.pi fun _ : n => rademacherMeasure`, an `abbrev` | — |
| index with probabilities `p` | `samplingMeasure p := ∑ i, p i • dirac i` for `p : ι → ℝ≥0`, a probability measure when `∑ i, p i = 1` | Mathlib's `PMF.toMeasure` (`samplingMeasure_toNNReal_eq_toMeasure`); uniform: `samplingMeasure (fun _ => (card ι)⁻¹) = uniformOn Set.univ` |

`abbrev` for the two vector laws, so that P0's `HasLaw.eval`, `HasLaw.iIndepFun_eval` and
`hasLaw_pi_iff` apply to them with no unfolding: the vector laws are products, and that is the
only thing about them most proofs use. `samplingMeasure` takes the weights without a proof that
they sum to one (no proof term in a statement, `CONTRIBUTING.md` §5.2); the theorems carry
`hp : ∑ i, p i = 1` where they need it.

## 2. Interfaces

None new. The instances this stage proves, each once, as a lemma about a random variable with the
law:

| Law | `HasSubgaussianMGF` | `IsIsotropic` | other |
|---|---|---|---|
| `gaussianReal 0 v` | proxy `v` | — | mean `0`, `E X² = v`, `E X⁴ = 3 v²`, exact MGF (Mathlib) |
| `gaussianVector n` | coordinates, proxy `1` | yes | `u ⬝ᵥ X` has law `gaussianReal 0 ‖u‖²` |
| `rademacherMeasure` | proxy `1` | — | `X = ±1` a.s., mean `0`, `E X² = E X⁴ = 1`, MGF `cosh` |
| `rademacherVector n` | coordinates, proxy `1` | yes | coordinates squared are `1` a.s. |

## 3. Statement shapes

`namespace NLAlib`. Law-specific lemmas are named for the law in the hypothesis
(`hasSubgaussianMGF_of_hasLaw_gaussianReal`): they are the only form, not twins of a measure
form (D2), and a dot-notation name `HasLaw.hasSubgaussianMGF` would collide across laws.
Variables `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`, `{n : Type*} [Fintype n]`.

### 3.1 `Probability/Distributions/Gaussian.lean`

```lean
abbrev gaussianVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ : n => gaussianReal 0 1

theorem gaussianVector_map_toLp :
    (gaussianVector n).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ n)

theorem hasSubgaussianMGF_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ
theorem integral_sq_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ^ 2 ∂μ = v
theorem integral_pow_four_of_hasLaw_gaussianReal {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : ∫ ω, X ω ^ 4 ∂μ = 3 * v ^ 2

theorem isIsotropic_of_hasLaw_gaussianVector [DecidableEq n] {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) : IsIsotropic X μ
/-- A linear form of a standard Gaussian vector is a centred Gaussian with variance `‖u‖²`. -/
theorem hasLaw_dotProduct_of_hasLaw_gaussianVector {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) (u : n → ℝ) :
    HasLaw (fun ω => u ⬝ᵥ X ω) (gaussianReal 0 (‖WithLp.toLp 2 u‖₊ ^ 2)) μ
```

Mean zero and integrability are Mathlib's (`integral_id_gaussianReal`, `memLp_id_gaussianReal`)
through `HasLaw.integral_comp` and P0's `HasLaw.memLp_comp_iff`; the coordinates' laws and
independence are P0's `HasLaw.eval` and `HasLaw.iIndepFun_eval`; not restated. `E X⁴ = 3 v²` and
`E X² = v` are stated because consumers rewrite with them (Hutchinson's Gaussian variance).

### 3.2 `Probability/Distributions/Rademacher.lean`

```lean
noncomputable def rademacherMeasure : Measure ℝ := bernoulliMeasure 1 (-1) (1 / 2)
instance : IsProbabilityMeasure rademacherMeasure
abbrev rademacherVector (n : Type*) [Fintype n] : Measure (n → ℝ) :=
  Measure.pi fun _ : n => rademacherMeasure

theorem integrable_rademacherMeasure {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) :
    Integrable f rademacherMeasure
theorem integral_rademacherMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ∫ x, f x ∂rademacherMeasure = (2 : ℝ)⁻¹ • (f 1 + f (-1))

theorem ae_eq_one_or_neg_one_of_hasLaw_rademacher {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : ∀ᵐ ω ∂μ, X ω = 1 ∨ X ω = -1
theorem hasSubgaussianMGF_of_hasLaw_rademacher {X : Ω → ℝ}
    (hX : HasLaw X rademacherMeasure μ) : HasSubgaussianMGF X 1 μ
theorem mgf_of_hasLaw_rademacher {X : Ω → ℝ} (hX : HasLaw X rademacherMeasure μ) (t : ℝ) :
    mgf X μ t = Real.cosh t
theorem integral_of_hasLaw_rademacher {X : Ω → ℝ} (hX : HasLaw X rademacherMeasure μ) :
    ∫ ω, X ω ∂μ = 0
theorem integral_sq_of_hasLaw_rademacher {X : Ω → ℝ} (hX : HasLaw X rademacherMeasure μ) :
    ∫ ω, X ω ^ 2 ∂μ = 1
theorem integral_pow_four_of_hasLaw_rademacher {X : Ω → ℝ} (hX : HasLaw X rademacherMeasure μ) :
    ∫ ω, X ω ^ 4 ∂μ = 1

theorem isIsotropic_of_hasLaw_rademacherVector [DecidableEq n] {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : IsIsotropic X μ
theorem ae_sq_eq_one_of_hasLaw_rademacherVector {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : ∀ᵐ ω ∂μ, ∀ i, X ω i ^ 2 = 1
```

The name `rademacherMeasure` follows Mathlib's `bernoulliMeasure`, `gammaMeasure`,
`betaMeasure`. A complex (Steinhaus) analogue would be a separate law, not a rename (§7 Q1).

### 3.3 `Probability/Distributions/Sampling.lean`

For `{ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : ι → ℝ≥0)`:

```lean
/-- The law of a random index that equals `i` with probability `p i`. A probability measure
when `∑ i, p i = 1`; the definition takes any weights so that statements carry no proof term. -/
noncomputable def samplingMeasure (p : ι → ℝ≥0) : Measure ι := ∑ i, (p i : ℝ≥0∞) • dirac i

theorem isProbabilityMeasure_samplingMeasure (hp : ∑ i, p i = 1) :
    IsProbabilityMeasure (samplingMeasure p)
theorem samplingMeasure_real_singleton (i : ι) : (samplingMeasure p).real {i} = p i
theorem integrable_samplingMeasure {E : Type*} [NormedAddCommGroup E] (f : ι → E) :
    Integrable f (samplingMeasure p)
theorem integral_samplingMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → E) : ∫ i, f i ∂samplingMeasure p = ∑ i, (p i : ℝ) • f i
theorem measureReal_eq_of_hasLaw_samplingMeasure {X : Ω → ι} (hX : HasLaw X (samplingMeasure p) μ)
    (i : ι) : μ.real {ω | X ω = i} = p i
/-- The bridge to `PMF`. -/
theorem samplingMeasure_toNNReal_eq_toMeasure (q : PMF ι) :
    samplingMeasure (fun i => (q i).toNNReal) = q.toMeasure
theorem samplingMeasure_const_inv_card [Nonempty ι] :
    samplingMeasure (fun _ : ι => (Fintype.card ι : ℝ≥0)⁻¹) = uniformOn Set.univ
```

Importance-weighted estimators (`E [f X / p X]`) are the
next round's (sketching) and are one `integral_samplingMeasure` away.

## 4. Consumers of the headline statements

`gaussianVector`, `isIsotropic_of_hasLaw_gaussianVector`, `integral_pow_four_of_hasLaw_gaussianReal`:
P3's Hutchinson variance and χ²; `hasLaw_dotProduct_of_hasLaw_gaussianVector`: JL, P3's
sub-Gaussian-vector instance; `gaussianVector_map_toLp`: R1's rotation invariance. Rademacher:
P3 (Hutchinson with Rademacher probes, `m₄ = 1`), Sketching (SRHT and CountSketch signs).
`samplingMeasure`: Sketching's row sampling, P5's Chernoff for sampling.

## 5. Files

Independent of each other; each imports P0 and P1.

1. `NLAlib/Probability/Distributions/Gaussian.lean`: §3.1 (7 statements).
2. `NLAlib/Probability/Distributions/Rademacher.lean`: §3.2 (13 statements).
3. `NLAlib/Probability/Distributions/Sampling.lean`: §3.3 (8 statements).

## 6. Material

Read: the prototype's `Probability/Gaussian/Basic/{StandardGaussian,StandardVector}.lean`,
`Probability/Rademacher/{Core,RademacherSymmetry}.lean`, `Probability/Sampling/FiniteSampling.lean`.
Reused as proof material: the Gaussian fourth moment, the dot-product law, the Rademacher MGF
and integrals. Not reproduced: the measure-form lemmas and their `_of_hasLaw` twins (one form
here); `hasLaw_gaussianVector_of_iIndepFun`, `iIndepFun_eval_gaussianVector` and their Rademacher
twins (P0's `hasLaw_pi_iff`); `gaussianCovarianceMatrix` and the covariance representation of a
general Gaussian (Mathlib's `covarianceBilin`; no consumer); `integrable_*_of_polynomial_growth`
(Mathlib's `memLp` for every `p` covers the consumers); the Rademacher sign-flip lemmas (P5);
`finiteSamplingLaw p hp` with its proof argument (replaced by `samplingMeasure p`).

## 7. Open questions (orchestrator decisions, recorded for review)

**Q1. Real laws now, complex laws later as parallel definitions** (D4 leaves this to the note).
`gaussianVector n` is on `n → ℝ`; a complex standard Gaussian vector will be a separate
`complexGaussianVector n` (or a field-generic definition then, with `gaussianVector` kept as the
real case), proved to satisfy the same 𝕜-interfaces (isotropy over `ℂ`, unitary invariance), so no
statement of this round is renamed. Alternative: a field-generic `gaussianVector 𝕜 n` now,
defined through a uniform construction of the standard Gaussian on `𝕜` (no Mathlib object exists
for it; `gaussianReal` would be a bridge, not the definition). Rejected for now: every statement of
the round would carry `ℝ` explicitly and a bridge, to serve a law no consumer of this round
uses. The consumers of the Gaussian go through interfaces, so the complex law later adds
instances, not theorems.

**Q2. `abbrev` for the vector laws.** P0's product-law lemmas then apply by unification. Cost: a
`simp` lemma about `Measure.pi` fires on them; no such simp lemma is a problem today.

**Q3. Weights without a proof in `samplingMeasure`.** See §1.

## 8. Amendments from the review (2026-10-14)

1. `integral_rademacherMeasure` and `integral_samplingMeasure` take `[CompleteSpace E]` (the
   Bochner integral is `0` otherwise; Mathlib's `integral_bernoulliMeasure` has it).
2. `rademacherMeasure := (2⁻¹ : ℝ≥0∞) • (dirac 1 + dirac (-1))`: `bernoulliMeasure` takes
   `p : unitInterval`, which has no `1 / 2` literal, and the sum of Diracs is what `simp` wants.
3. New: `instance isGaussian_gaussianVector : IsGaussian (gaussianVector n)`, so Mathlib's
   `HasGaussianLaw` API (linear images, `map_eq_gaussianReal`, `memLp`, independence from
   covariance) applies to a standard Gaussian vector; it is the proof route for
   `hasLaw_dotProduct_of_hasLaw_gaussianVector` and what P4 and P6 consume.
4. `gaussianVector_map_toLp` dropped: it is Mathlib's `map_pi_eq_stdGaussian` through the
   `abbrev`.
5. `samplingMeasure_const_inv_card` without `[Nonempty ι]` (both sides are `0` for empty `ι`);
   new `instance isFiniteMeasure_samplingMeasure` (any weights) and
   `samplingMeasure_real_apply (s : Finset ι) : (samplingMeasure p).real s = ∑ i ∈ s, p i`.
6. Names: `_of_hasLaw_rademacherMeasure` and `_of_hasLaw_rademacherVector`, the full law name as
   Mathlib writes it. The conclusion-first `foo_of_hasLaw_law` form follows `CONTRIBUTING.md` §4
   and P0/P1; Mathlib's own `HasLaw` Gaussian lemmas in `Gaussian/Real.lean` are law-first
   (`gaussianReal_const_mul (hX : HasLaw X …)`), a different convention a reader will notice.
7. Mean zero is stated for both laws (`integral_of_hasLaw_gaussianReal`,
   `integral_of_hasLaw_rademacherMeasure`): consumers rewrite with it, and the route through P1's
   `HasSubgaussianMGF.integral_eq_zero` needs the probability instance found by hand.
8. `integrable_rademacherMeasure` and `integral_rademacherMeasure` are the one exception to "only
   the `HasLaw` form": they are the law's constructors, as `integral_bernoulliMeasure` is.
9. `abbrev` hazard (Q2): `simp`, `exact` and `apply` see through it, `rw` does not; a lemma stated
   for `gaussianVector n` does not rewrite a goal that prints `Measure.pi fun _ => gaussianReal 0 1`
   and conversely. The module docstrings say so.
10. Known cost of Q1, for the complex law to supply: `IsIsotropic X μ` for a real `X` is isotropy at
    `𝕜 = ℝ`, so a `𝕜`-generic consumer with `A : Matrix n n ℂ` cannot use a real Gaussian probe
    without an `IsIsotropic` transport along `(↑) : ℝ → ℂ` (absent; no consumer needs it now).
11. Importance-weighted estimators (next round): when `p i = 0`, `f i / p i = 0` in Lean, so the
    estimator is unbiased on the support; say so where it is stated.
