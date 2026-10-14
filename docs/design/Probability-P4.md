# Design note: Probability stage P4, Gaussian concentration of Lipschitz functions

Status: written 2026-10-14 by the orchestrator, after the maintainer's P3 checkpoint. The
hypothesis form for Lipschitz functions and the proof route (log-Sobolev and Herbst, constant
`L²`) are the orchestrator's recommendations given at the checkpoint, open to the maintainer's
correction. No question of the brief's §2 kind. Reviewed by a Fable agent on 2026-10-14; the
corrections are in §8 and in the skeletons (`NLAlib/Probability/{Entropy,LogSobolev}.lean`,
`NLAlib/Probability/Distributions/{GaussianLogSobolev,GaussianConcentration}.lean`), which are the
statements where they differ from §3.

## 0. Scope and consumers

A Lipschitz function of a standard Gaussian vector is sub-Gaussian about its mean with proxy
`L²` (Tsirelson, Ibragimov and Sudakov; the constant is sharp). The route is the one in
Boucheron–Lugosi–Massart, chapters 4 to 6: the entropy functional and its tensorization, the
Gaussian logarithmic Sobolev inequality (Gross), and Herbst's argument.

| Item | Consumers |
|---|---|
| Gaussian concentration of Lipschitz functions | R3 (`σ_max` and `σ_min` of a Gaussian matrix about their means, combined with Gordon's bounds in P6), Chevet |
| Herbst's argument from a log-Sobolev inequality | here; any later measure with a log-Sobolev inequality (strongly log-concave laws, products) |
| entropy tensorization | here (the `n`-dimensional Gross inequality); P7 (bounded differences, if it goes through entropy) |

Not here: bounded differences and McDiarmid (P7), the Poincaré inequality, Gaussian comparison
(P6), concentration on the sphere (R5).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| entropy of a nonnegative function | `entropy ν f := ∫ f * log f ∂ν - (∫ f ∂ν) * log (∫ f ∂ν)`, new | Mathlib has KL divergence of measures, not this functional; `entropy ν f = (∫ f) * klDiv (f • ν / ∫ f) ν` is not stated (no consumer) |
| log-Sobolev inequality with constant `c` | `HasLogSobolev ν c`, new (§2) | — |
| Lipschitz for the Euclidean norm, `f : (n → ℝ) → ℝ` | `LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x))`, with `lipschitzWith_ofLp_iff` to `∀ x y, |f x - f y| ≤ L * ‖WithLp.toLp 2 (x - y)‖` | Mathlib's `LipschitzWith`; `n → ℝ` itself carries the sup metric, hence `EuclideanSpace` |
| standard Gaussian on a Euclidean space | Mathlib's `stdGaussian E`; on `n → ℝ`, P2's `gaussianVector n` (`map_pi_eq_stdGaussian`) | — |

`LipschitzWith` is the notion the proof consumes: Mathlib's Rademacher theorem
(`LipschitzWith.ae_differentiableAt`) and `norm_fderiv_le_of_lipschitz` are stated with it, and
`L : ℝ≥0` lands directly in the `ℝ≥0` proxy `L ^ 2` (D2). The `fun x : EuclideanSpace ℝ n`
ascription is part of the statement (the exponent `2` is not inferable from `f ∘ WithLp.ofLp`);
the `iff` lemma is the form to discharge it by hand. R3 applies it to `g` of a matrix through the
flattening `m × n` and the bridge `frobNorm A = ‖toLp 2 (fun p => A p.1 p.2)‖` (R3's note).

## 2. Interfaces

**`HasLogSobolev ν c`** (new; a property of a law, not of a random variable, as a functional
inequality is). For a probability measure `ν` on a finite-dimensional real inner product space `E`
and `c : ℝ≥0`:

```lean
/-- `ν` satisfies a logarithmic Sobolev inequality with constant `c`: for every bounded `C¹`
function `g` with bounded derivative, `Ent_ν (g²) ≤ 2 c E_ν ‖∇g‖²`. -/
structure HasLogSobolev (ν : Measure E) (c : ℝ≥0) : Prop where
  entropy_sq_le : ∀ g : E → ℝ, ContDiff ℝ 1 g → (∃ M, ∀ x, |g x| ≤ M) →
    (∃ M, ∀ x, ‖fderiv ℝ g x‖ ≤ M) →
    entropy ν (fun x => g x ^ 2) ≤ 2 * c * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν
```

- Bounded `C¹` test functions with bounded derivative: every integral in the inequality is then
  finite, so the field has no junk values (D3); Herbst's argument needs only such test functions
  (it applies the inequality to `exp (s f / 2)` for bounded smooth Lipschitz `f`, then
  approximates). Gross's inequality is stated separately in its general integrable form (§3.3).
- The normalisation `2 c` makes the standard Gaussian `c = 1` and the conclusion of Herbst's
  argument the proxy `c L²`.
- Instance: `hasLogSobolev_stdGaussian : HasLogSobolev (stdGaussian E) 1`.

## 3. Statement shapes

`namespace NLAlib`. Variables `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`.

### 3.1 `Probability/Entropy.lean`

```lean
/-- The entropy of a nonnegative function: `Ent_ν f = E f log f - E f log E f`. -/
noncomputable def entropy (ν : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, f ω * Real.log (f ω) ∂ν - (∫ ω, f ω ∂ν) * Real.log (∫ ω, f ω ∂ν)

theorem entropy_nonneg [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[ν] f)
    (hf : Integrable f ν) (hflog : Integrable (fun ω => f ω * Real.log (f ω)) ν) :
    0 ≤ entropy ν f

/-- **Tensorization of entropy** (Boucheron–Lugosi–Massart, Theorem 4.10). -/
theorem entropy_pi_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] (ν : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (ν i)]
    {f : (∀ i, Ω i) → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f (Measure.pi ν))
    (hflog : Integrable (fun x => f x * Real.log (f x)) (Measure.pi ν)) :
    entropy (Measure.pi ν) f ≤
      ∑ i, ∫ x, entropy (ν i) (fun y => f (Function.update x i y)) ∂Measure.pi ν

/-- **Herbst's argument** (Boucheron–Lugosi–Massart, Proposition 6.1): an entropy bound for
`exp (s f)` gives a sub-Gaussian bound for `f - E f`. -/
theorem hasSubgaussianMGF_sub_integral_of_entropy_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    {c : ℝ≥0} (hint : ∀ s, Integrable (fun ω => rexp (s * f ω)) μ)
    (hent : ∀ s, 0 < s →
      entropy μ (fun ω => rexp (s * f ω)) ≤ c * s ^ 2 / 2 * ∫ ω, rexp (s * f ω) ∂μ) :
    HasSubgaussianMGF (fun ω => f ω - ∫ ω', f ω' ∂μ) c μ
```

Degenerate cases: `entropy` of a function whose `f log f` is not integrable is a junk value, so
every statement about it carries the integrability (the definition's docstring says so); in
Herbst's hypothesis the functions are `exp (s f)` with `hint`, and the `f log f` integrability
of `exp (s f)` follows from `hint` at `2 s` (stated as an internal lemma). `ι` empty: both sides
of the tensorization are `0`.

### 3.2 `Probability/LogSobolev.lean`

```lean
structure HasLogSobolev (ν : Measure E) (c : ℝ≥0) : Prop   -- §2
/-- **Concentration from a log-Sobolev inequality** (Herbst's argument with Lipschitz
approximation): a Lipschitz function of a law with a log-Sobolev inequality with constant `c` is
sub-Gaussian about its mean with proxy `c L²`. -/
theorem HasLogSobolev.hasSubgaussianMGF_sub_integral [IsProbabilityMeasure ν]
    (h : HasLogSobolev ν c) {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂ν) (c * L ^ 2) ν
theorem HasLogSobolev.integrable_of_lipschitzWith … : Integrable f ν
```

The integrability of a Lipschitz function is part of the conclusion's API (D3): the mean `∫ f` in
the statement is meaningful only because it holds, and a consumer needs it to rewrite.

### 3.3 `Probability/Distributions/GaussianLogSobolev.lean`

```lean
/-- **Gross's logarithmic Sobolev inequality** on `ℝ`. -/
theorem entropy_sq_le_two_mul_integral_deriv_sq_gaussianReal {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (gaussianReal 0 1))
    (hdg : Integrable (fun x => deriv g x ^ 2) (gaussianReal 0 1)) :
    entropy (gaussianReal 0 1) (fun x => g x ^ 2) ≤ 2 * ∫ x, deriv g x ^ 2 ∂gaussianReal 0 1
/-- **Gross's logarithmic Sobolev inequality** for the standard Gaussian on a Euclidean space. -/
theorem entropy_sq_le_two_mul_integral_norm_fderiv_sq_stdGaussian {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : Integrable (fun x => g x ^ 2) (stdGaussian E))
    (hdg : Integrable (fun x => ‖fderiv ℝ g x‖ ^ 2) (stdGaussian E)) :
    entropy (stdGaussian E) (fun x => g x ^ 2) ≤ 2 * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂stdGaussian E
theorem hasLogSobolev_stdGaussian … : HasLogSobolev (stdGaussian E) 1
```

The general (integrable) forms include the integrability of `g² log g²` as a conclusion of the
proof (the prototype's "coverage" argument by sine truncation), so a user meets no junk value.
If the coverage resists, the general forms go to `NLAlibScaffold` and the interface instance,
which needs only bounded test functions, stays proved.

### 3.4 `Probability/Distributions/GaussianConcentration.lean`

```lean
theorem lipschitzWith_ofLp_iff {n : Type*} [Fintype n] {f : (n → ℝ) → ℝ} {L : ℝ≥0} :
    LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x)) ↔
      ∀ x y, |f x - f y| ≤ L * ‖WithLp.toLp 2 (x - y)‖
/-- **Gaussian concentration of Lipschitz functions** (Tsirelson, Ibragimov and Sudakov;
Boucheron–Lugosi–Massart, Theorem 5.6). -/
theorem hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianVector {n : Type*} [Fintype n]
    {X : Ω → n → ℝ} (hX : HasLaw X (gaussianVector n) μ) {f : (n → ℝ) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x))) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) (L ^ 2) μ
theorem integrable_comp_of_hasLaw_gaussianVector … : Integrable (fun ω => f (X ω)) μ
/-- The upper tail: `P(E f(X) + t ≤ f(X)) ≤ exp (-t² / (2L²))`. -/
theorem measureReal_integral_add_le_of_hasLaw_gaussianVector … {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∫ ω', f (X ω') ∂μ + t ≤ f (X ω)} ≤ rexp (-t ^ 2 / (2 * L ^ 2))
```

`L = 0`: `f` constant, the tail's exponent is `-t²/0 = 0` in Lean, bound `1`, true. The lower and
two-sided tails follow from P1's `measure_le_le`, `measure_abs_ge_le`; not restated.

## 4. Consumers of the headline statements

`hasSubgaussianMGF_sub_integral_of_hasLaw_gaussianVector` and its tail: R3 (extreme singular
values of a Gaussian matrix about their means), Chevet. `HasLogSobolev`: later laws.
`entropy_pi_le_sum`: P7.

## 5. Files

1. `NLAlib/Probability/Entropy.lean`: §3.1 (4 statements).
2. `NLAlib/Probability/LogSobolev.lean`: §3.2 (3 statements); imports 1 and P1.
3. `NLAlib/Probability/Distributions/GaussianLogSobolev.lean`: §3.3 (3 statements); imports 1, 2,
   P2. The long file; may split the one-dimensional inequality off as
   `GaussianLogSobolevOneDim.lean`.
4. `NLAlib/Probability/Distributions/GaussianConcentration.lean`: §3.4 (4 statements).

## 6. Material

Read: the prototype's `Probability/Gaussian/Concentration/{LogSobolevOneDim,LogSobolev,
LogSobolevCoverage,LogSobolevHerbst,LipschitzConcentration}.lean` and
`Probability/Concentration/Entropy/{EntropyTensorization,EntropyTensorizationNonneg,Herbst}.lean`
(2,431 lines). Reused as proof material throughout. Not reproduced: `HasEuclideanLogSobolev` on
`ι → ℝ` with coordinate partial derivatives (replaced by `HasLogSobolev` on a Euclidean space with
`‖fderiv‖`, which is the gradient norm there); the explicit `√(∑ (x i - y i)²)` Lipschitz
hypotheses (replaced by `LipschitzWith` on `EuclideanSpace`); the measure-form statements on
`gaussianVector ι` (D2); the nonnegative-tensorization variant and `sineTruncation` as public
names (proof material).

## 7. Open questions (orchestrator decisions, recorded for review)

**Q1. `HasLogSobolev` as a predicate on laws.** It is the hypothesis of Herbst's argument, proved
once, with the Gaussian as its first instance (the maintainer's "no one-offs" input). It is a
property of a measure, like Mathlib's `IsGaussian`, not of a random variable; the random-variable
statement is the Gaussian corollary.

**Q2. Bounded test functions in the predicate**, general integrable ones in Gross's theorem:
junk-free interface, standard theorem.

## 8. Amendments from the review (2026-10-14)

1. Herbst's hypothesis is for every `s`, not `0 < s`: `HasSubgaussianMGF` bounds the MGF on all of
   `ℝ`, and the lower tail needs `s < 0` (at `s = 0` the hypothesis holds trivially). The
   log-Sobolev application supplies every `s`.
2. Proof route for `HasLogSobolev.hasSubgaussianMGF_sub_integral`: not Rademacher's theorem
   (Mathlib's is for Haar measures, and `stdGaussian` is not one), but approximation: mollify `f`
   (keeps the Lipschitz constant, gives `C^∞`, `|f * ρ_ε - f| ≤ L ε`; the Lipschitz bound of a
   convolution is not in Mathlib), clamp smoothly (`M tanh (· / M)`) for boundedness, apply Herbst,
   pass to the limit with Fatou. `HasLogSobolev.integrable_of_lipschitzWith` is a real theorem
   (for a general `ν` nothing gives `f ∈ L¹`): bound the centred truncations uniformly, for instance
   with P1's `HasSubgaussianMGF.integral_sq_le`. These are the hazards of §3.2.
3. General form first: `hasSubgaussianMGF_sub_integral_of_lipschitzWith_of_hasLaw_stdGaussian`
   for `X` with law `stdGaussian E` and `LipschitzWith L f` (no ascription); the `gaussianVector n`
   form is the corollary. Names carry `_of_lipschitzWith`.
4. For R3: the law bridge from a Gaussian matrix to `gaussianVector (m × n)` by flattening is R1's
   (P0's `measurePreserving_curry_pi` in `Law.lean`, private now, is the step; R1 makes it
   public), with the bridge `frobNorm A = ‖toLp 2 (fun p => A p.1 p.2)‖`.
5. D3 companions: `integrable_sq_mul_log_sq_gaussianReal` and `…_stdGaussian` are public beside
   Gross's inequalities; `integrable_comp_of_lipschitzWith_of_hasLaw_*` beside the concentration
   theorems.
6. Binders: the Euclidean-space statements carry `[FiniteDimensional ℝ E] [BorelSpace E]`; the
   tensorization's type family is `X : ι → Type*` (the section's `Ω` is not shadowed). The tail
   `measureReal_integral_add_le_of_lipschitzWith_of_hasLaw_gaussianVector` is kept because R3 wants
   the event in that shape (it is one rewrite of P1's `measure_ge_le`).

Amendment (2026-10-14, after `Entropy.lean` was proved at 722 lines): split into
`Probability/Entropy.lean` (definition, nonnegativity, Herbst), `Probability/EntropyTensorization.lean`
(`entropy_pi_le_sum`), and `ForMathlib/MeasureTheory/Constructions/PiUpdate.lean` (six public
lemmas on resampling one coordinate of a product of probability measures, for dependent families:
`MeasureTheory.measurePreserving_update_pi`, `integral_integral_update_pi`, …, general facts
for every conditioning-on-all-but-one argument).
