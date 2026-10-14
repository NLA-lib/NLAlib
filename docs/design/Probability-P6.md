# Design note: Probability stage P6, Gaussian integration by parts and comparison

Status: drafted 2026-10-14 for the orchestrator, under `docs/PORT_PROBABILITY.md` (§2 decided;
D9 keeps Gaussian comparison "behind R3"). Sized by R3's needs only (orchestrator's scope): one
Gaussian integration-by-parts identity, Sudakov–Fernique, Gordon's min-max inequality, and the
two expected-norm facts Gordon's matrix bounds use. No Ornstein–Uhlenbeck semigroup (no proof
here needs it; P4 avoided it too). Real throughout: these are statements about real-valued
Gaussian families (§7.2 D6). One question flagged for the maintainer (§7.1); not blocking.

## 0. Scope and consumers

| Item | Consumers |
|---|---|
| Gaussian integration by parts (Stein's identity, covariance form) | the interpolation inequality (here); later: Isserlis, Slepian, Gaussian Poincaré, if ported |
| Gaussian interpolation inequality (Kahane) | Sudakov–Fernique and Gordon (here); Slepian later on the same lemma |
| Sudakov–Fernique, `E max X ≤ E max Y` | R3: Chevet's inequality, hence `E ‖G‖ ≤ √m + √n` |
| Gordon's min-max inequality, `E min max X ≤ E min max Y` | R3: `√m - √n ≤ E σ_min(G)` |
| `E ‖A X‖ ≤ ‖A‖_F` for an isotropic vector | R3 (Chevet's comparison process; `E ‖g‖ ≤ √n`) |
| `√m - √n ≤ E ‖h_m‖ - E ‖g_n‖` for standard Gaussian vectors, `1 ≤ n ≤ m` | R3 (Gordon's lower bound) |

Not here: Slepian's tail comparison (needs equal variances; no consumer: R3 uses the expectation
forms, which need none), Sudakov's minoration, Dudley, Isserlis (P5c owns Gaussian moments), the
Ornstein–Uhlenbeck semigroup, the six further Stein variants of the prototype (§6).

## 1. Objects

No new definition. Used directly: Mathlib's `HasGaussianLaw X μ` (a random variable whose law is
`IsGaussian`), `covariance X Y μ`, `fderiv`, `iteratedFDeriv`, `ContDiff`; P0's `IsIsotropic`;
P2's `gaussianVector`; the Matrix layer's `frobNorm`.

Searched (Mathlib, `NLAlib/`): no Gaussian integration by parts, interpolation, Slepian,
Sudakov–Fernique or Gordon in Mathlib (`grep -rn "Stein\|Slepian\|Sudakov\|Gordon\|Kahane"`
under `Mathlib/Probability`: none); nothing on `E ‖X‖` for a Gaussian vector in `NLAlib/` beyond
R4's `integral_norm_sq_rpow_of_hasLaw_gaussianVector` (the `s = 1/2` case gives `E ‖X‖` as a
Gamma ratio, which §3.3 uses). Mathlib has no bridge `IsGaussianProcess X μ ↔
HasGaussianLaw (fun ω t => X t ω) μ` for finite `T` (§7.1).

## 2. Interfaces

None new. Two conventions, fixed here:
- **A function of a Gaussian vector** (Stein, interpolation): `X : Ω → ι → ℝ` with
  `HasGaussianLaw X μ`, the D2 random-vector form.
- **A finite Gaussian family** (Sudakov–Fernique, Gordon): `X : T → Ω → ℝ` with
  `HasGaussianLaw (fun ω t => X t ω) μ`, the process form of Mathlib's `IsGaussianProcess` and of
  P1's maxima (`HasSubgaussianMGF.measure_iSup_ge_le` takes `X : ι → Ω → ℝ`). Suprema read
  `⨆ t, X t ω`. Gordon's two-index family is `X : U → T → Ω → ℝ` with
  `HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ`.
- The two families of a comparison live on **different probability spaces** (`μ` on `Ω`, `ν` on
  `Ω'`): only the laws matter, and R3's comparison process (`⟨g, u⟩ + ⟨h, v⟩`) is not built on
  the space of `G`. The proofs realise both on `μ.prod ν`.
- Second moments are written as integrals (`∫ ω, (X s ω - X t ω) ^ 2 ∂μ`), the form R3 computes
  from isotropy; Stein uses Mathlib's `covariance` because it carries no centring hypothesis.

## 3. Statement shapes

`namespace NLAlib`; `{Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
{μ : Measure Ω} {ν : Measure Ω'}`; `{ι : Type*} [Fintype ι] [DecidableEq ι]`.

### 3.1 `Probability/Distributions/GaussianIntegrationByParts.lean`

```lean
/-- **Gaussian integration by parts** (Stein's identity, covariance form): for a Gaussian vector
`X` and `f` of class `C¹` with bounded derivative,
`E [(X i - E X i) f(X)] = ∑ j, Cov(X i, X j) E [∂_j f(X)]`.
[Vershynin2018, Lemma 7.2.5] (standard Gaussian, there `E [g f(g)] = E f'(g)`); here any mean and
covariance, possibly singular.
Result: gaussian-integration-by-parts -/
theorem integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw
    {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (hdf : ∃ C, ∀ x, ‖fderiv ℝ f x‖ ≤ C) (i : ι) :
    ∫ ω, (X ω i - ∫ ω', X ω' i ∂μ) * f (X ω) ∂μ =
      ∑ j, covariance (fun ω => X ω i) (fun ω => X ω j) μ *
        ∫ ω, fderiv ℝ f (X ω) (Pi.single j 1) ∂μ
```

- **The regularity class** is the one R3's proof needs: the interpolation (§3.2) applies the
  identity to `∂_i F` for a test function `F` of class `C²` with bounded Hessian (the soft-max
  and soft-min-max functions), so `C¹` with bounded derivative. A bounded derivative gives linear
  growth, so both integrands are integrable (`HasGaussianLaw.memLp_two`): the identity is never
  between junk values, and no integrability companion is stated (D3 asks for one beside upper
  bounds). The prototype's seven variants (integrable, polynomial growth, `HasDerivAt` along
  coordinates, `gaussianReal` with variance `v`, …) are not ported (§6).
- No centring hypothesis: the general mean costs nothing. A centred consumer rewrites with
  `hX0 i, sub_zero`.
- `ι` empty: no `i`, vacuous. A degenerate (singular) covariance is allowed; the proof does not
  use a density.
- Proof: Mathlib's `multivariateGaussian` and `IsGaussian.ext` write the law of `X` as the image
  of `gaussianVector ι` under `x ↦ m + √Σ x`; reduce to the standard case by the chain rule;
  the standard case is one-dimensional integration by parts against `gaussianPDFReal 0 1` in each
  coordinate, through P4's `ForMathlib/MeasureTheory/Constructions/PiUpdate.lean` (resampling one
  coordinate of a product measure).

### 3.2 `Probability/Distributions/GaussianComparison.lean`

```lean
/-- **Gaussian interpolation** (Kahane): for centred Gaussian vectors `X`, `Y` and `F` of class
`C²` with bounded Hessian, if `∑ i j (E Yᵢ Yⱼ - E Xᵢ Xⱼ) ∂ᵢⱼF(x) ≥ 0` for every `x`, then
`E F(X) ≤ E F(Y)`. [Vershynin2018, Lemma 7.2.7 and the proof of Theorem 7.2.1]; there as an
identity for the interpolating path, here the inequality it gives. -/
theorem integral_comp_le_integral_comp_of_hasGaussianLaw {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X μ) (hY : HasGaussianLaw Y ν)
    (hX0 : ∀ i, ∫ ω, X ω i ∂μ = 0) (hY0 : ∀ i, ∫ ω, Y ω i ∂ν = 0)
    {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) (hF2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C)
    (hcov : ∀ x, 0 ≤ ∑ i, ∑ j, (∫ ω, Y ω i * Y ω j ∂ν - ∫ ω, X ω i * X ω j ∂μ) *
      iteratedFDeriv ℝ 2 F x ![Pi.single i 1, Pi.single j 1]) :
    ∫ ω, F (X ω) ∂μ ≤ ∫ ω, F (Y ω) ∂ν
/-- A `C²` function with bounded Hessian of a Gaussian vector is integrable. -/
theorem integrable_comp_of_hasGaussianLaw_of_contDiff_two {X : Ω → ι → ℝ}
    (hX : HasGaussianLaw X μ) {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (hF2 : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) : Integrable (fun ω => F (X ω)) μ

variable {T U : Type*} [Fintype T] [Fintype U]

/-- The maximum of a finite Gaussian family is integrable. -/
theorem integrable_iSup_of_hasGaussianLaw {X : T → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω t => X t ω) μ) : Integrable (fun ω => ⨆ t, X t ω) μ
/-- The min-max of a finite Gaussian family is integrable. -/
theorem integrable_iInf_iSup_of_hasGaussianLaw {X : U → T → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ) :
    Integrable (fun ω => ⨅ u, ⨆ t, X u t ω) μ
/-- **The Sudakov–Fernique inequality**: for centred finite Gaussian families with
`E (X s - X t)² ≤ E (Y s - Y t)²`, `E max X ≤ E max Y`.
[Vershynin2018, Theorem 7.2.11]; no equal-variance hypothesis (unlike Slepian).
Result: sudakov-fernique -/
theorem integral_iSup_le_integral_iSup_of_hasGaussianLaw {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω t => X t ω) μ) (hY : HasGaussianLaw (fun ω t => Y t ω) ν)
    (hX0 : ∀ t, ∫ ω, X t ω ∂μ = 0) (hY0 : ∀ t, ∫ ω, Y t ω ∂ν = 0)
    (hinc : ∀ s t, ∫ ω, (X s ω - X t ω) ^ 2 ∂μ ≤ ∫ ω, (Y s ω - Y t ω) ^ 2 ∂ν) :
    ∫ ω, ⨆ t, X t ω ∂μ ≤ ∫ ω, ⨆ t, Y t ω ∂ν
/-- **Gordon's min-max inequality**: for centred Gaussian families on `U × T` whose increments
compare one way within a block (`u` fixed) and the other way across blocks,
`E min_u max_t X ≤ E min_u max_t Y`. [Vershynin2018, Exercise 7.2.14]; Gordon 1985.
Result: gordon-minimax -/
theorem integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw
    {X : U → T → Ω → ℝ} {Y : U → T → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω (p : U × T) => X p.1 p.2 ω) μ)
    (hY : HasGaussianLaw (fun ω (p : U × T) => Y p.1 p.2 ω) ν)
    (hX0 : ∀ u t, ∫ ω, X u t ω ∂μ = 0) (hY0 : ∀ u t, ∫ ω, Y u t ω ∂ν = 0)
    (hsame : ∀ u t s, ∫ ω, (X u t ω - X u s ω) ^ 2 ∂μ ≤ ∫ ω, (Y u t ω - Y u s ω) ^ 2 ∂ν)
    (hdiff : ∀ u u' t s, u ≠ u' →
      ∫ ω, (Y u t ω - Y u' s ω) ^ 2 ∂ν ≤ ∫ ω, (X u t ω - X u' s ω) ^ 2 ∂μ) :
    ∫ ω, ⨅ u, ⨆ t, X u t ω ∂μ ≤ ∫ ω, ⨅ u, ⨆ t, Y u t ω ∂ν
```

Degenerate cases.
- `T` empty: `⨆ t, X t ω = 0` (`Real.iSup_of_isEmpty`), both sides `0`. `U` empty, or `T` empty
  with `U` nonempty: `⨅ u, ⨆ t, … = 0`, both sides `0`. The proofs split these off before the
  soft-max functions (which need `Nonempty`).
- No probability hypothesis: `HasGaussianLaw` implies it (`HasGaussianLaw.isProbabilityMeasure`).
- Integrability (D3): both sides of each comparison are integrable by the companions, so neither
  inequality is between junk values. The companions follow from `|⨆ t, x t| ≤ ∑ t, |x t|` and
  `HasGaussianLaw.memLp`.
- The interpolation's `ι` empty: `F` is evaluated at the unique point, both sides `F 0`.
- The `C²`/bounded-Hessian class makes `F (X)` of quadratic growth, hence integrable; the
  companion is stated because the conclusion is an upper bound by an integral.

Proof routes. Interpolation: on `μ.prod ν`, `Z θ = cos θ • X + sin θ • Y` for `θ ∈ [0, π/2]`
(no singularity at the ends, unlike `√t X + √(1-t) Y`); differentiate under the integral
(Hessian bounded, linear growth of `∇F`); `Z θ` and `Z' θ` are jointly Gaussian
(`IndepFun.hasGaussianLaw` and `HasGaussianLaw.map`); §3.1 on `∂_i F` turns the derivative into
`sin θ cos θ ∑ (E YᵢYⱼ - E XᵢXⱼ) E ∂ᵢⱼF(Z θ) ≥ 0`. Sudakov–Fernique: soft-max
`F_β x = β⁻¹ log ∑ t, exp (β x t)`, whose Hessian `β (diag p - p pᵀ)` has zero row sums and
non-positive off-diagonal entries, so `hcov` reduces to `hinc`; `β → ∞` with
`max x ≤ F_β x ≤ max x + log |T| / β`. Gordon: `F_β x = -β⁻¹ log ∑ u, (∑ t, exp (β x (u, t)))⁻¹`
(prototype `gmmF`), Hessian signs within and across blocks give `hcov` from `hsame` and `hdiff`.

### 3.3 Additions to existing files (expected norms)

`Probability/Isotropic.lean` (P0), over `𝕜`:

```lean
/-- `E ‖A X‖ ≤ ‖A‖_F` for an isotropic vector, by Jensen and `integral_norm_mulVec_sq`. -/
theorem IsIsotropic.integral_norm_mulVec_le [IsProbabilityMeasure μ] (hX : IsIsotropic X μ)
    {m : Type*} [Fintype m] (A : Matrix m n 𝕜) :
    ∫ ω, ‖WithLp.toLp 2 (A *ᵥ X ω)‖ ∂μ ≤ frobNorm A
theorem IsIsotropic.integrable_norm_mulVec [IsProbabilityMeasure μ] (hX : IsIsotropic X μ)
    {m : Type*} [Fintype m] (A : Matrix m n 𝕜) :
    Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ X ω)‖) μ
```

`E ‖g‖ ≤ √n` is the case `A = 1` with `frobNorm_one_sq`; no separate statement. The probability
hypothesis is needed: isotropy does not imply it (`n` empty; or mass `≠ 1` with a rescaled
vector), and Jensen's step `E ‖Y‖ ≤ (E ‖Y‖²)^{1/2}` fails on a measure of mass `> 1`.

`Probability/Distributions/ChiSquareMoments.lean` (R4's file):

```lean
/-- **Growth of `E ‖g_d‖`**: for standard Gaussian vectors of dimensions `1 ≤ n ≤ m`,
`√m - √n ≤ E ‖h‖ - E ‖g‖`. [DavidsonSzarek2001, proof of Theorem II.13]; the step of Gordon's
lower bound for `σ_min`. -/
theorem le_integral_norm_sub_integral_norm_of_hasLaw_gaussianVector {n m : Type*} [Fintype n]
    [Fintype m] {X : Ω → n → ℝ} {Y : Ω' → m → ℝ} (hX : HasLaw X (gaussianVector n) μ)
    (hY : HasLaw Y (gaussianVector m) ν) (hn : 0 < Fintype.card n)
    (hnm : Fintype.card n ≤ Fintype.card m) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) ≤
      ∫ ω, ‖WithLp.toLp 2 (Y ω)‖ ∂ν - ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ∂μ
```

Both hypotheses are needed: `n = 0` would claim `√m ≤ E ‖h_m‖`, false for `m ≥ 1`
(`E ‖h_m‖ < √m`), and for `n > m` the inequality reverses. Integrability of both norms is
§3.3's isotropic companion (with P2's `isIsotropic_of_hasLaw_gaussianVector`). Proof: R4's
`integral_norm_sq_rpow_of_hasLaw_gaussianVector` at `s = 1/2` gives
`a_d = √2 Γ((d+1)/2) / Γ(d/2)`; then `a_d a_{d+1} = d`, `a_d ≤ √d`, and the sequence argument of
the prototype (`ExpectationNormDiff`: comparison function `d - 1/2 + 3/(20 d)`) give
`a_{d+1} - a_d ≥ √(d+1) - √d`; telescope.

## 4. Consumers of the headline statements

R3 only (§0): Sudakov–Fernique behind Chevet and `E ‖G‖ ≤ √m + √n`; Gordon behind
`√m - √n ≤ E σ_min`; §3.3 in both. Stein and the interpolation inequality are the tools; a later
Slepian, Isserlis or Poincaré inequality would take them.

## 5. Files

1. `Probability/Distributions/GaussianIntegrationByParts.lean`: §3.1 (1 statement); imports P2's
   `Gaussian.lean`, P4's `PiUpdate`. About 300 lines expected (one-dimensional integration by
   parts, the reduction to the standard vector).
2. `Probability/Distributions/GaussianComparison.lean`: §3.2 (6 statements); imports 1. The soft
   max and soft min-max with their derivative bounds are private (about 700 lines in the
   prototype for the two; may split as `GaussianInterpolation.lean` + `GaussianComparison.lean`
   if it passes 1000 lines, recorded as an amendment).
3. `Probability/Isotropic.lean`: + 2 (§3.3).
4. `Probability/Distributions/ChiSquareMoments.lean`: + 1 (§3.3).

3 and 4 are independent of 1 and 2 and of each other.

Bibliography keys to add before citing: `DavidsonSzarek2001` (Handbook of the Geometry of Banach
Spaces, vol. 1, "Local operator theory, random matrices and Banach spaces"), `Gordon1985`
(Israel J. Math. 50), `Kahane1986` (Israel J. Math. 55, "Une inégalité du type de Slepian et
Gordon"). Labels in `Vershynin2018` are to be checked against the book by the proof agent.

## 6. Material

Read: the prototype's `Probability/Gaussian/Comparison/{Interpolation,Slepian,SlepianTails,
SudakovFernique,GordonMinimax}.lean` (1,831 lines), `Probability/Gaussian/Calculus/{Stein,
IntegrationByParts,ProductIntegrationByParts,PolynomialGrowthIntegrationByParts}.lean` and the
names of `OrnsteinUhlenbeck*.lean`, `Probability/Gaussian/Moments/ExpectationNormDiff.lean`.

Reused as proof material: the soft max and soft min-max with their Hessian sign lemmas
(`sfF`, `sfH`, `gmmF`, `gmmH`, `gmm_hess_nonneg`), the rotation interpolation
(`covariance_rotation_eq`), the one-dimensional integration by parts
(`integral_mul_eq_integral_deriv_gaussianReal_of_integrable`), the sequence argument of
`ExpectationNormDiff`.

Not reproduced: the seven Stein variants differing only in regularity class (inventory §3 row
14; one statement in the class R3 needs); the polynomial-growth integrability lemmas
(`HasGaussianLaw.memLp` and a growth bound do it); `indepFun_of_hasGaussianLaw_of_covariance_eq_zero`
(Mathlib's `HasGaussianLaw.indepFun_of_covariance_eq_zero`); `integral_mul_eq_sum_covariance_mul_integral`
(the bounded-`G` covariance identity, subsumed by §3.1); the interpolation lemma's one-space form
with explicit gradient and Hessian functions (`hF : HasFDerivAt F (∑ i, g i x • proj i) x`,
replaced by `ContDiff ℝ 2` and `iteratedFDeriv`); `integral_sub_sq_eq` (proof-local);
Slepian and its tail form (no consumer; they can join this file on the interpolation lemma);
the Ornstein–Uhlenbeck semigroup and its entropy files (about 1,360 lines; no proof here or in
P4 uses them).

## 7. Open questions

### 7.1 Of the brief's §2 kind (for the maintainer)

**Q1. The carrier of a finite Gaussian family.** The comparison theorems take
`HasGaussianLaw (fun ω t => X t ω) μ` (the orchestrator's scope). Mathlib's notion of a Gaussian
family is `IsGaussianProcess X μ` (every finite restriction is Gaussian), which for finite `T` is
equivalent but not syntactically the same, and which later theorems over infinite index sets
(Dudley, Sudakov minoration, a sphere-indexed Gordon) would take. Every comparison theorem
takes this hypothesis, so it is an interface. *Recommendation:* keep `HasGaussianLaw` (finite
index sets are all this round has, and it composes with `HasGaussianLaw.map` and the product
constructions the proofs use), and add the `ForMathlib` bridge
`ProbabilityTheory.isGaussianProcess_iff_hasGaussianLaw [Finite T]` when the first consumer
holding an `IsGaussianProcess` appears. *Rework if changed:* the six statements of §3.2 and
their R3 call sites; low. Not blocking.
*Decided (orchestrator, 2026-10-14):* `HasGaussianLaw` of the finite family, as recommended
(§8.2).

### 7.2 Decisions taken (recorded for review)

**D1. One Stein statement in covariance form**, `C¹` with bounded derivative, no centring
hypothesis; the standard-vector form is its corollary in one line and is not stated.

**D2. Expectation forms only.** Sudakov–Fernique and Gordon in expectation form (what R3 uses;
no equal-variance hypothesis); Slepian not ported (no consumer).

**D3. Centred families**, as the sources state them. Equal means would also do (the increments
carry the mean differences equally on both sides) but no consumer has uncentred families.

**D4. Two probability spaces** in every comparison (§2): the comparison process need not live on
the space of the process it bounds.

**D5. The interpolation inequality is public** (Kahane's inequality, the tool from which every
Gaussian comparison is proved); its hypothesis is the Hessian pairing, its regularity class
`C²` with bounded Hessian, the same class through which §3.1 is applied.

**D6. Real only.** The processes are real-valued by nature; a complex Gaussian vector enters as a
real Gaussian vector in `2n` coordinates. The §3.3 isotropic additions are over `𝕜` (D4 of the
brief).

**D7. Expected-norm facts live with their objects**: `E ‖A X‖ ≤ ‖A‖_F` in `Isotropic.lean` (it
uses only isotropy), the dimension growth of `E ‖g_d‖` beside R4's χ² moments.

## 8. Amendments from the review (2026-10-14)

The skeletons (`Probability/Distributions/{GaussianIntegrationByParts,GaussianComparison}.lean`,
the additions to `Probability/Isotropic.lean` and `Probability/Distributions/ChiSquareMoments.lean`)
are the statements where they differ from §3. Findings that concern R3's use of these statements
are in `docs/design/RandomMatrix-R3.md` §8.

1. **No bare `∃ C` in a statement** (CONTRIBUTING §5.2, "Numerical bounds" rule 3). The
   derivative bounds are an implicit constant and a universally quantified bound:
   `{C : ℝ} (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C)` in §3.1, and
   `{C : ℝ} (hF2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ C)` in the interpolation inequality and its
   integrability companion (§3.2). Same meaning; a consumer passes its bound directly instead of
   packing an existential.
2. **§7.1 Q1 decided by the orchestrator** (2026-10-14): the comparison theorems take Mathlib's
   `HasGaussianLaw` of the finite family, `HasGaussianLaw (fun ω t => X t ω) μ` (two-index:
   `fun ω (p : U × T) => X p.1 p.2 ω`), as recommended. The `IsGaussianProcess` bridge waits for
   a consumer holding one.
3. **How R3 applies §3.2** (recorded here so the statements are read with their consumers).
   Sudakov–Fernique, for Chevet's inequality: `X_{uv} = ⟨u, S G T v⟩` against
   `Y_{uv} = ‖Sᴴu‖ ⟨g, T v⟩ + ‖T v‖ ⟨h, Sᴴu⟩` over finite symmetric nets (R3 §8.1). Gordon, for
   `√N - √n ≤ E σ_min`: the `X` side of
   `integral_iInf_iSup_le_integral_iInf_iSup_of_hasGaussianLaw` is `⟨g, u⟩ + ⟨h, v⟩`, the `Y`
   side is `⟨v, G u⟩` (`u` outer, ranging over a net of the unit sphere of `ℝⁿ`; `v` inner, over a
   net of the sphere of `ℝᴺ`); `hsame` holds with equality (`‖(v - v') uᵀ‖_F = ‖v - v'‖`),
   `hdiff` is `‖v uᵀ - v' u'ᵀ‖_F² ≤ ‖u - u'‖² + ‖v - v'‖²`. No statement of §3.2 changes; the
   increment-only form (no equal variances) is what both applications need, and the soft min-max
   Hessian has the required signs (non-positive off-diagonal within a block, non-negative across
   blocks, zero row sums).
4. **Bibliography.** `DavidsonSzarek2001` (incollection, Handbook of the Geometry of Banach
   Spaces vol. 1, pp. 317–366), `Gordon1985` (Israel J. Math. 50(4), 265–289) and `Kahane1986`
   (Israel J. Math. 55(1), 109–110) are in `docs/references.bib`, without DOIs (not certain of
   them). The skeletons cite `[Kahane1986]` (interpolation), `[Gordon1985]` (min-max) and
   `[DavidsonSzarek2001, proof of Theorem II.13]` (growth of `E ‖g_d‖`).
5. **Result ids**: `gaussian-integration-by-parts`, `gaussian-interpolation`, `sudakov-fernique`,
   and `gordon-inequality` for the min-max inequality (§3.2 had `gordon-minimax`). The
   expectation-norm facts of §3.3 carry none.
6. **Skeleton notes.** Gordon's docstring records that [Vershynin2018, Exercise 7.2.14] assumes
   equal variances and compares tails; this statement is the expectation form from increments
   alone. The unused-instance warnings of the skeleton (`[Fintype T]`, `[Fintype U]` where
   `[Finite _]` suffices in a type; `[DecidableEq ι]` in
   `integrable_comp_of_hasGaussianLaw_of_contDiff_two`) are left to the proof agent (proof-agent
   brief, "Rules").
