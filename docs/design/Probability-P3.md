# Design note: Probability stage P3, random vectors and quadratic forms

Status: written 2026-10-14 by the orchestrator under `docs/PORT_PROBABILITY.md` (§2 decided).
Introduces the sub-Gaussian-vector interface D6 fixed. The maintainer's design checkpoint (D1)
follows this stage. No new question of the brief's §2 kind. Reviewed by a Fable agent on
2026-10-14; corrections in §8. The skeletons
(`NLAlib/Probability/{SubGaussianVector/{Basic,Norm},Distributions/ChiSquare,QuadraticForm/{Moments,HansonWright}}.lean`)
carry them; where §3 and a skeleton differ, the skeleton is the statement.

## 0. Scope and consumers

Random vectors whose linear forms are sub-Gaussian, the tails of their squared norm, the
moments of a quadratic form `Xᴴ A X` (Hutchinson's variance), and the Hanson–Wright inequality.

| Item | Consumers (prototype files) |
|---|---|
| `IsSubgaussianVector` and its instances | χ² tails here, R3 (the net argument for a matrix with sub-Gaussian rows), Sketching (JL for sub-Gaussian sketches, `SRHTFlattening`) |
| `‖X‖²` upper tail for a sub-Gaussian vector | JL, `SRHTFlattening` |
| `‖X‖²` two-sided tail, independent sub-Gaussian coordinates | JL for sub-Gaussian sketches, R3 |
| exact Gaussian χ²: Laplace transform, lower tail | JL (Gaussian), R4 (small ball) |
| second moment of `quadForm A X` | Estimation (Hutchinson's variance with Gaussian, Rademacher and complex probes), CountSketch moments |
| Hanson–Wright | `HutchinsonTail`, R3 |

Not here: negative moments of χ² (R4, their only consumer, through inverse Wishart moments);
the sub-Gaussian-vector instance for an orthonormal frame's rescaled columns (R5); matrix
quadratic forms (P5).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| sub-Gaussian random vector, proxy `c : ℝ≥0` | `IsSubgaussianVector X c μ` for `X : Ω → n → 𝕜`, new (§2) | for `n` a singleton and `𝕜 = ℝ`, `HasSubgaussianMGF` of the coordinate (`isSubgaussianVector_unique_iff`) |
| squared Euclidean norm | `‖WithLp.toLp 2 (X ω)‖ ^ 2` (Matrix layer convention) | `EuclideanSpace.norm_eq` |
| quadratic form | the Matrix layer's `quadForm A x = star x ⬝ᵥ A *ᵥ x` | — |
| Hanson–Wright constant | `hansonWrightConstant : ℝ`, `irreducible_def` (D5 rule 2) | — |

## 2. Interfaces

**`IsSubgaussianVector X c μ`** (D6, with D4's `𝕜`). For `X : Ω → n → 𝕜`:

```lean
/-- `X` is a sub-Gaussian random vector with proxy `c`: every real linear functional of `X`,
`re (u ⬝ᵥ X)`, is sub-Gaussian with proxy `c ‖u‖²`. -/
structure IsSubgaussianVector (X : Ω → n → 𝕜) (c : ℝ≥0) (μ : Measure Ω) : Prop where
  hasSubgaussianMGF : ∀ u : n → 𝕜,
    HasSubgaussianMGF (fun ω => RCLike.re (u ⬝ᵥ X ω)) (c * ‖WithLp.toLp 2 u‖₊ ^ 2) μ
```

- Every real-linear functional of `𝕜ⁿ` is `x ↦ re (u ⬝ᵥ x)` for some `u`, so over `ℂ` this
  constrains the real and imaginary parts alike; over `ℝ`, `re` is the identity
  (`RCLike.re_to_real`, a `simp` lemma).
- The unstarred pairing `u ⬝ᵥ X`, as in `IsIsotropic.integral_norm_dotProduct_sq` (P0 review).
- It replaces the prototype's four spellings (inventory §2 item 3); the bilinear form of the net
  argument is this predicate applied to the vectorised matrix (R3 decides).
- Mean zero is implied (`IsSubgaussianVector.integral_eq_zero` under a probability measure).
- Raw-condition constructors: independent real coordinates with a common proxy
  (`IsSubgaussianVector.of_iIndepFun`), the Gaussian and Rademacher vectors (proxy `1`), and
  linear images (`mulVec`, proxy `c ‖A‖²`).

## 3. Statement shapes

`namespace NLAlib`; variables `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`,
`{n : Type*} [Fintype n]`, `{𝕜 : Type*} [RCLike 𝕜]`.

### 3.1 `Probability/SubGaussianVector/Basic.lean`

```lean
structure IsSubgaussianVector (X : Ω → n → 𝕜) (c : ℝ≥0) (μ : Measure Ω) : Prop   -- §2
namespace IsSubgaussianVector
theorem mono (h : IsSubgaussianVector X c μ) {d : ℝ≥0} (hcd : c ≤ d) : IsSubgaussianVector X d μ
theorem hasSubgaussianMGF_apply [DecidableEq n] (h : IsSubgaussianVector X c μ) (i : n) :
    HasSubgaussianMGF (fun ω => RCLike.re (X ω i)) c μ
theorem integral_eq_zero [IsProbabilityMeasure μ] (h : IsSubgaussianVector X c μ) (i : n) :
    ∫ ω, X ω i ∂μ = 0
/-- A linear image of a sub-Gaussian vector, with proxy `c ‖A‖²`. -/
theorem mulVec {m : Type*} [Fintype m] (h : IsSubgaussianVector X c μ) (A : Matrix m n 𝕜) :
    IsSubgaussianVector (fun ω => A *ᵥ X ω) (c * ‖specNorm A‖₊ ^ 2) μ
/-- Independent real coordinates with a common proxy. -/
theorem of_iIndepFun {X : Ω → n → ℝ} (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) : IsSubgaussianVector X c μ
end IsSubgaussianVector
theorem isSubgaussianVector_of_hasLaw_gaussianVector {X : Ω → n → ℝ}
    (hX : HasLaw X (gaussianVector n) μ) : IsSubgaussianVector X 1 μ
theorem isSubgaussianVector_of_hasLaw_rademacherVector {X : Ω → n → ℝ}
    (hX : HasLaw X (rademacherVector n) μ) : IsSubgaussianVector X 1 μ
```

`specNorm A` is real; `‖specNorm A‖₊` is its `ℝ≥0` value (or `⟨specNorm A, specNorm_nonneg A⟩`
via a Matrix-layer `specNNNorm` if one exists; the skeleton uses what the Matrix layer has).
`of_iIndepFun` is real: over `ℂ` a scalar `HasSubgaussianMGF` hypothesis on a coordinate says
nothing about its imaginary part; a complex constructor waits for a complex consumer.

### 3.2 `Probability/SubGaussianVector/Norm.lean`

Real vectors (`X : Ω → n → ℝ`). The proofs linearise with a standard Gaussian vector of the same
dimension (`gaussianVector n`, P2), which exists only over `ℝ` in this round; over `ℂ` the same
statements hold with `2 · card n` real coordinates and follow once the complex Gaussian law
exists.

```lean
/-- `E exp (θ ‖X‖²) ≤ (1 - 2θc)^{-n/2}` (Hsu, Kakade and Zhang 2012, the χ²_n Laplace transform
as an upper bound). -/
theorem IsSubgaussianVector.integral_exp_mul_norm_sq_le (h : IsSubgaussianVector X c μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ * c < 1) :
    ∫ ω, rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2) ∂μ ≤ (1 - 2 * θ * c) ^ (-(Fintype.card n / 2 : ℝ))
theorem IsSubgaussianVector.integrable_exp_mul_norm_sq … (hθ : 2 * θ * c < 1) :
    Integrable (fun ω => rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2)) μ
/-- The upper tail of `‖X‖²` (Hsu, Kakade and Zhang 2012, Theorem 2.1 for `A = 1`; for the
Gaussian it is Laurent and Massart's bound). -/
theorem IsSubgaussianVector.measure_norm_sq_ge_le (h : IsSubgaussianVector X c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | c * (Fintype.card n + 2 * √(Fintype.card n * t) + 2 * t) ≤
      ‖WithLp.toLp 2 (X ω)‖ ^ 2} ≤ rexp (-t)
/-- Two-sided tail of `‖X‖²` for independent sub-Gaussian coordinates: Bernstein's inequality
for the centred squares (P1). -/
theorem measureReal_abs_norm_sq_sub_integral_ge_le [IsProbabilityMeasure μ]
    (hind : iIndepFun (fun i ω => X ω i) μ) (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |‖WithLp.toLp 2 (X ω)‖ ^ 2 - ∫ ω', ‖WithLp.toLp 2 (X ω')‖ ^ 2 ∂μ|} ≤
      2 * rexp (-min (t ^ 2 / (2 * (Fintype.card n * (32 * c ^ 2)))) (t / (2 * (4 * c))))
```

The two-sided form carries P1's constants `32` and `4` (the centred square's variance proxy and
scale) unsimplified, so the statement is visibly Bernstein's inequality applied to them. The `t = 0` and
`c = 0` cases are the junk cases of P1 (bound `≥ 1` or `2`).

### 3.3 `Probability/Distributions/ChiSquare.lean`

The exact Gaussian case, for `X` with `HasLaw X (gaussianVector n) μ`:

```lean
theorem integral_exp_mul_norm_sq_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {θ : ℝ} (hθ : 2 * θ < 1) :
    ∫ ω, rexp (θ * ‖WithLp.toLp 2 (X ω)‖ ^ 2) ∂μ = (1 - 2 * θ) ^ (-(Fintype.card n / 2 : ℝ))
/-- The lower tail of χ²_n (Laurent and Massart 2000, Lemma 1). -/
theorem measureReal_norm_sq_le_of_hasLaw_gaussianVector (hX : HasLaw X (gaussianVector n) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ‖WithLp.toLp 2 (X ω)‖ ^ 2 ≤ Fintype.card n - 2 * √(Fintype.card n * t)} ≤ rexp (-t)
```

The Gaussian upper tail is `IsSubgaussianVector.measure_norm_sq_ge_le` at `c = 1` through
`isSubgaussianVector_of_hasLaw_gaussianVector`, and is Laurent and Massart's exactly, so it is not
restated. The lower tail needs the exact Laplace transform at negative `θ` (a sub-Gaussian
vector has no lower tail in general). The prototype's `(e u / d)^{d/2}` small-ball form goes to
R4 if its consumer there needs it.

### 3.4 `Probability/QuadraticForm/Moments.lean`

Over `𝕜` (D4). For `X : Ω → n → 𝕜` with independent coordinates, mean zero, `E |X i|² = 1`,
pseudo-variance `E X i² = s` and `E |X i|⁴ = m₄` (all coordinates alike):

```lean
theorem integrable_norm_quadForm_sq (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ) (A : Matrix n n 𝕜) :
    Integrable (fun ω => ‖quadForm A (X ω)‖ ^ 2) μ
/-- The second moment of a quadratic form about its mean `tr A`: Hutchinson's variance. -/
theorem integral_norm_quadForm_sub_trace_sq [IsProbabilityMeasure μ]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hL4 : ∀ i, MemLp (fun ω => X ω i) 4 μ)
    (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0) (hvar : ∀ i, ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1)
    {s : 𝕜} (hs : ∀ i, ∫ ω, X ω i ^ 2 ∂μ = s) {m₄ : ℝ} (hm₄ : ∀ i, ∫ ω, ‖X ω i‖ ^ 4 ∂μ = m₄)
    (A : Matrix n n 𝕜) :
    ∫ ω, ‖quadForm A (X ω) - A.trace‖ ^ 2 ∂μ =
      ∑ i, ∑ j, (if i = j then 0 else ‖A i j‖ ^ 2) +
        ‖s‖ ^ 2 * RCLike.re (∑ i, ∑ j, if i = j then 0 else A i j * star (A j i)) +
        (m₄ - 1) * ∑ i, ‖A i i‖ ^ 2
/-- The real symmetric case: `Var (Xᵀ A X) = 2 ‖A‖_F² + (m₄ - 3) ∑ A i i²`. -/
theorem variance_quadForm_of_isHermitian {X : Ω → n → ℝ} … (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (X ω)) μ = 2 * frobNorm A ^ 2 + (m₄ - 3) * ∑ i, A i i ^ 2
```

The general formula is the one the complex probes need (Gaussian over `ℂ`: `s = 0`, `m₄ = 2`;
Steinhaus: `s = 0`, `m₄ = 1`); the real case `s = 1` is the corollary consumers cite (Gaussian
`m₄ = 3`: `2 ‖A‖_F²`; Rademacher `m₄ = 1`: `2 ‖A‖_F² - 2 ∑ A i i²`). `DecidableEq n` for the
`if`. The hypotheses are per coordinate and equal across coordinates; a version with
coordinate-dependent moments is the same proof and is not stated (no consumer).

### 3.5 `Probability/QuadraticForm/HansonWright.lean`

Real, for `X : Ω → n → ℝ` with independent coordinates, each `HasSubgaussianMGF … c`, and any
`A : Matrix n n ℝ`:

```lean
/-- The Hanson–Wright constant. The sources (Rudelson and Vershynin 2013, Theorem 1.1;
Vershynin 2018, Theorem 6.2.1) leave it unspecified; the value here is what the proof reaches. -/
noncomputable irreducible_def hansonWrightConstant : ℝ := 1 / (256 * rexp 2)
theorem hansonWrightConstant_pos : 0 < hansonWrightConstant
theorem le_hansonWrightConstant : 1 / (256 * rexp 2) ≤ hansonWrightConstant
/-- **The Hanson–Wright inequality.** -/
theorem measureReal_abs_quadForm_sub_integral_ge_le [IsProbabilityMeasure μ]
    (hind : iIndepFun (fun i ω => X ω i) μ) (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ)
    (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ|} ≤
      2 * rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A))))
theorem measureReal_quadForm_sub_integral_ge_le … :   -- the upper tail, constant 1 in front
    μ.real {ω | t ≤ quadForm A (X ω) - ∫ ω', quadForm A (X ω') ∂μ} ≤
      rexp (-(hansonWrightConstant * min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A))))
```

Constant (D5): a lower bound is the API (a larger constant is a better bound), so the comparison
lemma is `le_hansonWrightConstant`. Degenerate cases: `A = 0` or `c = 0` make the exponent `0`
(bound `2`, true). `[IsProbabilityMeasure μ]` stays: `iIndepFun` implies it, but the statement
reads better with it and it costs nothing (`CONTRIBUTING.md` §5.2 says drop implied hypotheses:
the proof agent drops it if the linter flags it). Proof (prototype, about 90 declarations):
the diagonal is P1's Bernstein for `∑ A i i (X i² - E X i²)` (`sum_const_mul_of_iIndepFun` with
`hasSubexponentialMGF_sq_sub_integral`); the off-diagonal part by decoupling and Gaussian
comparison. The file is split by the proof agent as it needs (`HansonWright/Decoupling.lean`
etc.), and only the statements above are public unless a second file uses a helper.

## 4. Consumers of the headline statements

`IsSubgaussianVector` and `measure_norm_sq_ge_le`: Sketching's JL and `SRHTFlattening`, R3.
`measureReal_abs_norm_sq_sub_integral_ge_le`: JL for sub-Gaussian sketches. The Gaussian χ²
statements: Gaussian JL, R4. `integral_norm_quadForm_sub_trace_sq` and its real corollary:
Estimation's Hutchinson error. Hanson–Wright: `HutchinsonTail`, R3.

## 5. Files

1. `NLAlib/Probability/SubGaussianVector/Basic.lean`: §3.1 (8 statements).
2. `NLAlib/Probability/SubGaussianVector/Norm.lean`: §3.2 (4 statements); imports 1 and P2.
3. `NLAlib/Probability/Distributions/ChiSquare.lean`: §3.3 (2 statements); imports P2.
4. `NLAlib/Probability/QuadraticForm/Moments.lean`: §3.4 (3 statements); independent.
5. `NLAlib/Probability/QuadraticForm/HansonWright.lean` (and its proof files): §3.5
   (5 statements); imports P1.

1 to 4 are short; 5 is the stage's long proof and may go to `NLAlibScaffold` under the budget
rule if decoupling resists, with the rest of the stage unaffected.

## 6. Material

Read: the prototype's `Probability/ChiSquare/{ChiSquare,DirectionalSquaredNorm}.lean`,
`Probability/Concentration/QuadraticForms/` (Hanson–Wright in 12 files, Hutchinson's moments in
`QuadraticMoments.lean` and `RademacherQuadraticMoments.lean`). Not reproduced: the `_pmf` copies
of the directional χ² statements (a `PMF` is a measure through `toMeasure`); the measure-form
Gaussian χ² family on `gaussianVector (Fin d)` and its optimised and relaxed variants
(`measureReal_le_sum_sq_le_gaussianVector`, `…exp_mul_rpow`; the Laurent–Massart forms are the
ones consumers cite); `hasHansonWrightMGF_*` and the leaf vocabulary (`cutMatrix`, masks,
`linForm`); `hanson_wright_of_lintegral_exp_sq_le_two` (ψ₂ form; P7 with the Orlicz bridges);
`integral_quadForm_sq_rademacherVector` (an instance of §3.4).

## 7. Open questions (orchestrator decisions, recorded for review)

**Q1. Real χ² and Hanson–Wright, `𝕜` interface and moments.** The interface and the quadratic
moments are over `𝕜` as D4 asks; the norm tails and Hanson–Wright are over `ℝ` because their
proofs need a Gaussian of the same field (linearisation, decoupling) and the complex Gaussian is
not in this round (P2 Q1). Their complex versions are additive later.

**Q2. Hutchinson's variance with explicit moment parameters** `s` and `m₄` rather than a law:
one statement covers Gaussian, Rademacher, complex Gaussian and Steinhaus probes (brief D6:
fixed moments are parameters).

## 8. Amendments from the review (2026-10-14)

1. `IsSubgaussianVector.measure_norm_sq_ge_le` takes `hc : c ≠ 0`: with `c = 0` the vector
   is `0` a.s., the non-strict event is everything, and `exp (-t) < 1`.
2. `measureReal_norm_sq_le_of_hasLaw_gaussianVector` takes `hn : 0 < Fintype.card n`: for
   `n = 0` the event `{0 ≤ 0}` is everything.
3. The second moment of the quadratic form in the vocabulary of §5.3, with no `if` and no
   `DecidableEq`: `frobNorm A ^ 2 + ‖s‖ ^ 2 * frobInner A Aᵀ + (m₄ - 2 - ‖s‖ ^ 2) * ∑ ‖A i i‖ ^ 2`
   (the review derived it independently). The real corollary drops `hs` (forced to `1`).
4. New corollaries `variance_quadForm_of_hasLaw_gaussianVector` (`= 2 ‖A‖_F²`) and
   `…_rademacherVector` (`= 2 (‖A‖_F² - ∑ A i i²)`), so a consumer with a law does not assemble six
   hypotheses; they replace the prototype's `integral_quadForm_sq_rademacherVector`.
5. `memLp_quadForm : MemLp (quadForm A X) 2 μ` in place of the integrability of `‖·‖²` (what
   Chebyshev and `variance` take).
6. `[IsProbabilityMeasure μ]` dropped wherever `iIndepFun` is a hypothesis (Mathlib's
   `iIndepFun.isProbabilityMeasure`); kept in `IsSubgaussianVector.integral_apply_eq_zero` and
   `integral_norm_sq_le`.
7. Hanson–Wright: the constant's body is what the proof reaches (the skeleton has the
   prototype's `1/(256 e²)` as a placeholder; the diagonal now goes through P1's sharper `32`,
   `4`); `le_hansonWrightConstant` states the number the docstring promises. New lower tail
   `measureReal_quadForm_sub_integral_le_le`.
8. `IsSubgaussianVector` API: `congr`, `memLp_apply` (coordinates over `𝕜`), the real part of a
   coordinate (`hasSubgaussianMGF_re_apply`, no `DecidableEq`), law transport
   `HasLaw.isSubgaussianVector_iff`; `integral_norm_sq_le : E ‖X‖² ≤ c n` (real, in `Norm.lean`).
   `isSubgaussianVector_unique_iff` (§1) is not stated: no consumer.
9. The general-`A` form of Hsu–Kakade–Zhang (`‖A X‖²` with `tr Σ`, `‖Σ‖_F`, `‖Σ‖`) is the same
   linearisation and what a reader of the citation expects; no consumer needs it now, so it is
   not stated.
10. Noted inconsistencies, not changed: P1's scalar `E exp (θX²) ≤ 1 / √(1 - 2θc)` against the
    rpow form here (a bridge for `n` a singleton is one `rw`); tail names use `measureReal_` here
    and in P0 but Mathlib's `measure_` (for `μ.real` statements) in P1's dot-notation lemmas.

## 9. Stage report (2026-10-14)

All files proved, nothing in `NLAlibScaffold`. Changes from the design and §8:
- **Hanson–Wright reached `hansonWrightConstant = 1/196`** (the prototype had `1/(256 e²)`, about
  ten times smaller), in 884 lines against the prototype's 3,400. The diagonal goes through P1's
  centred square (`32 c²`, `4 c`) and Bernstein; the off-diagonal part is decoupled by random cuts
  and compared with a Gaussian chaos. The two parts are added without independence by convexity
  of `exp` (weights `4/7`, `3/7`), giving variance proxy `98 c² ‖A‖_F²` and scale `28 c ‖A‖`.
  Amendment to §5: two proof files, `QuadraticForm/HansonWright/LinearImage.lean` (public
  `lintegral_exp_mul_dotProduct_le`, `lintegral_exp_mul_norm_mulVec_sq_le`) and
  `QuadraticForm/HansonWright/OffDiagonal.lean` (public `hasSubexponentialMGF_quadForm_sub_diagonal`:
  the off-diagonal chaos is sub-exponential with `(18 c² ‖A‖_F², 12 c ‖A‖)`).
- `IsSubgaussianVector.aemeasurable` is public over `𝕜` (Basic).
- Hutchinson's variance is proved over `𝕜` through the complex fourth mixed moment
  `E[conj X i · X j · X k · conj X l]` (private); the uncentred `E |Xᴴ A X|²` is a private lemma a
  consumer could ask for.
- The Laurent–Massart lower tail is proved without the prototype's "`χ² > 0` a.s." argument (two
  choices of the Chernoff parameter).

Follow-ups for the wrap-up: the non-independent sum of two sub-exponential variables (private in
`OffDiagonal.lean`) belongs in `SubExponential/Basic.lean` as a public lemma;
`lintegral_exp_mul_dotProduct_le` overlaps `IsSubgaussianVector.of_iIndepFun` and could be derived
from it; `lintegral_exp_mul_dotProduct_gaussianVector` is duplicated privately in `Norm.lean` and
`LinearImage.lean` and should be public once, in `Distributions/Gaussian.lean`.
- Renamed after the stage review: `IsSubgaussianVector.measureReal_norm_sq_ge_le` →
  `IsSubgaussianVector.measure_norm_sq_ge_le` (the tail-prefix rule now in `CONTRIBUTING.md` §4).
  Not changed: P1's scalar `E exp (θX²) ≤ 1 / √(1 - 2θc)` keeps its square-root form (the
  readable scalar statement; the vector form's `card n = 1` case is one `rw`).
