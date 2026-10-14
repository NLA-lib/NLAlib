# Design note: Probability stage P5a, matrix concentration by the Laplace transform

Status: written 2026-10-14 by the orchestrator. P5 is split: **P5a** (this note: the matrix
moment generating function interface, the master bound through Lieb's theorem, and the Chernoff,
Bernstein and series inequalities with their rectangular forms), **P5b** (intrinsic-dimension
forms), **P5c** (trace moments and noncommutative Khintchine), **P5d** (Freedman, with the
conditional form of the interface and matrix conditional expectations). Introduces
`HasMatrixMGFBound`, fixed by D6. No question of the brief's §2 kind.

## 0. Scope and consumers

The Laplace transform method for sums of independent random Hermitian matrices over `𝕜`
(Tropp 2015, chapters 3 to 6). Consumers (inventory §5): Sketching's leverage-score and uniform
row sampling (`matrix_chernoff_sampling_*`, the Chernoff lower and upper tails in the simplified
form), sampling without replacement (the CGF-level statements: the trace exponential of a sum
bounded through the sum of matrix CGFs), and the round's own R3 and P1 (the scalar Bernstein
corollary, P1 §7 Q1).

| Item | Consumers |
|---|---|
| Laplace transform bounds (tail and mean of `λ_max` from `E tr exp (θ Y)`) | the master bounds here; P5b; P5d |
| subadditivity of matrix CGFs (Lieb) | the master bounds; sampling without replacement |
| `HasMatrixMGFBound` and the master tail and mean | every inequality here and in P5b |
| Chernoff (bounded PSD summands) | Sketching (leverage-score and uniform sampling), R-stages |
| Bernstein (bounded centred summands), Hermitian and rectangular | Sketching (AMM by sampling), the scalar Bernstein corollary |
| series with sub-Gaussian coefficients, Hermitian and rectangular | Gaussian and Rademacher series (R2, Sketching) |

## 1. Objects

| Concept | Spelling | Mathlib or Matrix-layer bridge |
|---|---|---|
| a finite family of random matrices | `X : ι → Ω → Matrix n n 𝕜`, `[Fintype ι]`, `iIndepFun X μ` | Mathlib's `iIndepFun` with the global matrix σ-algebra (D8) |
| largest and smallest eigenvalue | `eigenvalue A 0` and `eigenvalue A (Fintype.card n - 1)` (brief §3.1) | Matrix layer |
| matrix exponential, trace exponential | Mathlib's `NormedSpace.exp`, written `exp`; `RCLike.re (exp A).trace` | Matrix layer `Functions/Exponential.lean` |
| matrix logarithm | `cfc Real.log A` (deviation entry 6) | Matrix layer |
| expectation of a random matrix | `∫ ω, X ω ∂μ` under `open scoped Matrix.Norms.L2Operator` (D10) | P0 `MatrixIntegral.lean` |
| the variance statistic | `v := specNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ)`; rectangular: `max` of the two `specNorm`s | no definition: written out, as Tropp writes it |
| dilation | the Matrix layer's `dilation A` | `eigenvalue_zero_dilation`, `specNorm_dilation` |

No named tail functions: every tail here is the source's and short (D5 rule 2). The Chernoff
tail `(e^δ / (1 + δ)^{1+δ})^{μ/L}` is written out.

## 2. Interfaces

**`HasMatrixMGFBound X g A s μ`** (D6). For `X : Ω → Matrix n n 𝕜`, `g : ℝ → ℝ`,
`A : Matrix n n 𝕜`, `s : Set ℝ`:

```lean
/-- `X` is almost surely Hermitian and its matrix moment generating function is bounded by
`exp (g θ • A)` in the Loewner order for every `θ ∈ s`. -/
structure HasMatrixMGFBound (X : Ω → Matrix n n 𝕜) (g : ℝ → ℝ) (A : Matrix n n 𝕜) (s : Set ℝ)
    (μ : Measure Ω) : Prop where
  ae_isHermitian : ∀ᵐ ω ∂μ, (X ω).IsHermitian
  isHermitian_bound : A.IsHermitian
  integrable_exp : ∀ θ ∈ s, Integrable (fun ω => exp (θ • X ω)) μ
  integral_exp_le : ∀ θ ∈ s, ∫ ω, exp (θ • X ω) ∂μ ≤ exp (g θ • A)
```

- `A` Hermitian is part of the interface, since `exp (g θ • A)` is compared with a positive
  definite matrix and the master bound takes `cfc Real.log` of it (operator monotonicity of the
  logarithm, `Matrix.PosDef.cfc_log_le_cfc_log`).
- Integrability is a field (D3): `∫ exp (θ X)` is a junk `0` otherwise, and `0 ≤ exp (gθ A)` holds
  trivially.
- Constructors (§3.3 to §3.5): bounded positive semidefinite summands (Chernoff), bounded centred
  summands (Bernstein), a sub-Gaussian scalar times a fixed Hermitian matrix (series).
- The conditional form for martingales is P5d's.

## 3. Statement shapes

`namespace NLAlib`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`. Variables
`{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]` (the Laplace
method uses it; implied when `iIndepFun` is a hypothesis, and then dropped), `{𝕜 : Type*}
[RCLike 𝕜]`, `{n : Type*} [Fintype n] [DecidableEq n]`, `{ι : Type*} [Fintype ι]`.

Degenerate cases, common to every tail: for empty `n`, `eigenvalue _ 0 = 0` and the event
`{t ≤ 0}` is everything for `t ≤ 0` while the bound has a factor `card n = 0`; so the tails take
`[Nonempty n]` (the Matrix layer's convention for `exp_eigenvalue_zero_le_re_trace_exp`). `ι`
empty: the sum is `0`, and the bounds read `card n * exp (-θ t)`, true for `t ≥ 0` (all tails
take `0 ≤ t` or are stated so that `t < 0` is harmless).

### 3.1 `Probability/MatrixConcentration/Laplace.lean`

For one random Hermitian matrix `Y : Ω → Matrix n n 𝕜` (Tropp, Proposition 3.2.1):

```lean
theorem measureReal_eigenvalue_zero_ge_le [Nonempty n] (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian)
    {θ : ℝ} (hθ : 0 < θ) (hint : Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ) (t : ℝ) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤ rexp (-θ * t) * ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ
theorem measureReal_eigenvalue_last_le_le [Nonempty n] (hY …) {θ : ℝ} (hθ : θ < 0) (hint …) (t) :
    μ.real {ω | eigenvalue (Y ω) (Fintype.card n - 1) ≤ t} ≤
      rexp (-θ * t) * ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ
theorem integral_eigenvalue_zero_le [Nonempty n] (hY …) (hYi : Integrable Y μ) {θ} (hθ : 0 < θ)
    (hint …) : ∫ ω, eigenvalue (Y ω) 0 ∂μ ≤ θ⁻¹ * Real.log (∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ)
theorem integrable_eigenvalue_zero (hYi : Integrable Y μ) : Integrable (fun ω => eigenvalue (Y ω) 0) μ
```

`integrable_eigenvalue_zero` is the D3 companion (`|λ_max| ≤ ‖Y‖`, needs `Measurable` of
`eigenvalue` from `Probability/Measurability/Matrix.lean` composed with an a.e.-measurable `Y`).

### 3.2 `Probability/MatrixConcentration/Subadditivity.lean`

```lean
/-- Lieb's theorem in expectation (Tropp, Corollary 3.4.2). -/
theorem integral_re_trace_exp_add_le {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hint : Integrable (fun ω => exp (X ω)) μ) :
    ∫ ω, RCLike.re (exp (H + X ω)).trace ∂μ ≤
      RCLike.re (exp (H + cfc Real.log (∫ ω, exp (X ω) ∂μ))).trace
/-- **Subadditivity of matrix cumulant generating functions** (Tropp, Lemma 3.5.1). -/
theorem integral_re_trace_exp_sum_le (hind : iIndepFun X μ)
    (hX : ∀ k, ∀ᵐ ω ∂μ, (X k ω).IsHermitian) (hint : ∀ k, Integrable (fun ω => exp (X k ω)) μ) :
    ∫ ω, RCLike.re (exp (∑ k, X k ω)).trace ∂μ ≤
      RCLike.re (exp (∑ k, cfc Real.log (∫ ω, exp (X k ω) ∂μ))).trace
theorem integrable_re_trace_exp_sum … : Integrable (fun ω => RCLike.re (exp (∑ k, X k ω)).trace) μ
```

The first needs Jensen for the concave trace function on the positive definite cone, which is not
closed (P0 §0: the non-closed Jensen lives here); the proof route is the prototype's
`ConcaveOn.le_map_integral_of_integral_mem` (Jensen for a continuous concave function on a convex
set containing the mean). Independence enters through the product structure: condition on all
but one summand (Fubini on `Measure.pi`, or P0's `HasLaw` decomposition), apply the first
inequality, induct.

### 3.3 `Probability/MatrixConcentration/MGFBound.lean`

```lean
structure HasMatrixMGFBound … : Prop   -- §2
/-- **The master tail bound**: for independent summands with matrix MGF bounds,
`P(t ≤ λ_max (∑ X k)) ≤ e^{-θt} tr exp (g θ ∑ A k)` for every `θ ∈ s`, `θ > 0`. -/
theorem HasMatrixMGFBound.measureReal_eigenvalue_zero_sum_ge_le [Nonempty n]
    (hind : iIndepFun X μ) (h : ∀ k, HasMatrixMGFBound (X k) g (A k) s μ) {θ : ℝ} (hθs : θ ∈ s)
    (hθ : 0 < θ) (t : ℝ) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      rexp (-θ * t) * RCLike.re (exp (g θ • ∑ k, A k)).trace
/-- The master tail in the dimension form: `≤ d e^{-θt + g θ λ_max (∑ A k)}`. -/
theorem HasMatrixMGFBound.measureReal_eigenvalue_zero_sum_ge_le_card [Nonempty n] … (hg : 0 ≤ g θ) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * rexp (-θ * t + g θ * eigenvalue (∑ k, A k) 0)
/-- The master bound for the mean. -/
theorem HasMatrixMGFBound.integral_eigenvalue_zero_sum_le [Nonempty n] (hind …) (h …)
    (hX : ∀ k, Integrable (X k) μ) {θ} (hθs : θ ∈ s) (hθ : 0 < θ) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      θ⁻¹ * Real.log (RCLike.re (exp (g θ • ∑ k, A k)).trace)
theorem HasMatrixMGFBound.mono_bound (h : HasMatrixMGFBound X g A s μ) {A'} (hA' : A'.IsHermitian)
    (hAA' : A ≤ A') (hg : ∀ θ ∈ s, 0 ≤ g θ) : HasMatrixMGFBound X g A' s μ
theorem HasMatrixMGFBound.neg (h : HasMatrixMGFBound X g A s μ) :
    HasMatrixMGFBound (fun ω => -X ω) (fun θ => g (-θ)) A (-s) μ
```

`neg` gives the lower tails (`λ_min (∑ X) = -λ_max (∑ -X)`). Lower-tail forms are stated in the
Chernoff file, where they have their own shape.

### 3.4 `Probability/MatrixConcentration/Chernoff.lean`

Summands `0 ≤ X k ≤ L` almost surely (`(X k ω).PosSemidef`, `eigenvalue (X k ω) 0 ≤ L`), means
`μmax := eigenvalue (∑ k, ∫ X k) 0`, `μmin := eigenvalue (∑ k, ∫ X k) (card n - 1)`:

```lean
/-- The Chernoff MGF bound: `E exp (θ X) ≤ exp ((e^{θL} - 1)/L • E X)` (Tropp, Lemma 5.4.1). -/
theorem hasMatrixMGFBound_of_posSemidef_of_le {L : ℝ} (hL : 0 < L)
    (hpsd : ∀ᵐ ω ∂μ, (X ω).PosSemidef) (hle : ∀ᵐ ω ∂μ, eigenvalue (X ω) 0 ≤ L) :
    HasMatrixMGFBound X (fun θ => (rexp (θ * L) - 1) / L) (∫ ω, X ω ∂μ) Set.univ μ
/-- **Matrix Chernoff, upper tail** (Tropp, Theorem 5.1.1). -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff [Nonempty n] (hind …) (hpsd …) (hle …)
    (hL : 0 < L) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ.real {ω | (1 + δ) * μmax ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * (rexp δ / (1 + δ) ^ (1 + δ)) ^ (μmax / L)
/-- **Matrix Chernoff, lower tail** (Tropp, Theorem 5.1.1). -/
theorem measureReal_eigenvalue_last_sum_le_le_chernoff … {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (∑ k, X k ω) (Fintype.card n - 1) ≤ (1 - δ) * μmin} ≤
      Fintype.card n * (rexp (-δ) / (1 - δ) ^ (1 - δ)) ^ (μmin / L)
/-- The lower tail in the form the sampling arguments use: `≤ d e^{-δ² μmin / (2L)}`. -/
theorem measureReal_eigenvalue_last_sum_le_le_exp … (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | eigenvalue (∑ k, X k ω) (Fintype.card n - 1) ≤ (1 - δ) * μmin} ≤
      Fintype.card n * rexp (-δ ^ 2 * μmin / (2 * L))
/-- The upper tail in the form the sampling arguments use: `≤ d e^{-δ² μmax / (3L)}`. -/
theorem measureReal_eigenvalue_zero_sum_ge_le_exp … (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | (1 + δ) * μmax ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * rexp (-δ ^ 2 * μmax / (3 * L))
```

The simplified forms are dominated by the source forms in every regime and are proved from them
(D5 rule 5: kept because consumers cite them). The event at `δ = 1` in the lower tail is
`λ_min ≤ 0`, which the source form excludes (`(1 - δ)^{1-δ}` at `δ = 1` is `0^0 = 1` in Lean, so
the source form is actually fine at `δ = 1` too; the proof agent decides whether `hδ1 : δ ≤ 1`
works there). `L = 0` is excluded (`0 < L`): with `L = 0` the summands vanish.

### 3.5 `Probability/MatrixConcentration/Bernstein.lean`

Summands centred, `E X k = 0`, with `eigenvalue (X k ω) 0 ≤ L` a.s. (one-sided, Tropp 6.1.1), and
`v := specNorm (∑ k, ∫ ω, X k ω ^ 2 ∂μ)`:

```lean
/-- The Bernstein MGF bound (Tropp, Lemma 6.6.2): for `0 < θ < 3/L`,
`E exp (θ X) ≤ exp (θ²/2 / (1 - Lθ/3) • E X²)`. -/
theorem hasMatrixMGFBound_of_integral_eq_zero_of_le {L : ℝ} (hL : 0 < L)
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hX2 : MemLp X 2 μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (hle : ∀ᵐ ω ∂μ, eigenvalue (X ω) 0 ≤ L) :
    HasMatrixMGFBound X (fun θ => θ ^ 2 / 2 / (1 - L * θ / 3)) (∫ ω, X ω ^ 2 ∂μ)
      (Set.Ioo 0 (3 / L)) μ
/-- **Matrix Bernstein**, Hermitian summands (Tropp, Theorem 6.1.1). -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein [Nonempty n] (hind …) (hX …) (hX2 …)
    (hmean …) (hL : 0 < L) (hle …) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      Fintype.card n * rexp (-(t ^ 2 / 2) / (v + L * t / 3))
/-- **Matrix Bernstein**, rectangular summands (Tropp, Theorem 6.1.1, through the dilation), with
`v := max (specNorm (∑ k, ∫ S k * (S k)ᴴ)) (specNorm (∑ k, ∫ (S k)ᴴ * S k))`. -/
theorem measureReal_specNorm_sum_ge_le_bernstein {m : Type*} [Fintype m] [DecidableEq m]
    [Nonempty m] [Nonempty n] {S : ι → Ω → Matrix m n 𝕜} (hind : iIndepFun S μ)
    (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) (hL : 0 < L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, S k ω)} ≤
      (Fintype.card m + Fintype.card n) * rexp (-(t ^ 2 / 2) / (v + L * t / 3))
/-- Matrix Bernstein for the mean (Tropp, Theorem 6.1.1). -/
theorem integral_specNorm_sum_le_bernstein … :
    ∫ ω, specNorm (∑ k, S k ω) ∂μ ≤
      √(2 * v * Real.log (Fintype.card m + Fintype.card n)) +
        L * Real.log (Fintype.card m + Fintype.card n) / 3
/-- **Bernstein's inequality** for bounded centred real variables, the `1 × 1` case
(P1 §7 Q1): `P(t ≤ ∑ X k) ≤ exp (-(t²/2) / (σ² + L t / 3))`. -/
theorem measureReal_sum_ge_le_bernstein {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0) (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L) (hL : 0 < L)
    (hX2 : ∀ k, MemLp (X k) 2 μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ k, X k ω} ≤
      rexp (-(t ^ 2 / 2) / (∑ k, ∫ ω, X k ω ^ 2 ∂μ + L * t / 3))
```

`v` is written out in each statement (no definition), as Tropp does. `L = 0` excluded. The
`v = 0` case (summands a.s. zero): the bound is `d exp (-3t/(2L))`, true.

### 3.6 `Probability/MatrixConcentration/Series.lean`

`X k = γ k • B k` with `γ` independent, `HasSubgaussianMGF (γ k) c μ`, `B k` Hermitian (Tropp,
chapter 4), `v := specNorm (∑ k, B k ^ 2)`:

```lean
theorem hasMatrixMGFBound_smul_of_hasSubgaussianMGF {γ : Ω → ℝ} {c : ℝ≥0}
    (hγ : HasSubgaussianMGF γ c μ) {B : Matrix n n 𝕜} (hB : B.IsHermitian) :
    HasMatrixMGFBound (fun ω => γ ω • B) (fun θ => c * θ ^ 2 / 2) (B ^ 2) Set.univ μ
/-- **The matrix series tail** (Tropp, Theorem 4.1.1). -/
theorem measureReal_eigenvalue_zero_sum_smul_ge_le [Nonempty n] (hind : iIndepFun γ μ)
    (hγ : ∀ k, HasSubgaussianMGF (γ k) c μ) (hB : ∀ k, (B k).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, γ k ω • B k) 0} ≤
      Fintype.card n * rexp (-t ^ 2 / (2 * c * v))
/-- Rectangular coefficients, through the dilation. -/
theorem measureReal_specNorm_sum_smul_ge_le {m} … {B : ι → Matrix m n 𝕜} … :
    μ.real {ω | t ≤ specNorm (∑ k, γ k ω • B k)} ≤
      (Fintype.card m + Fintype.card n) * rexp (-t ^ 2 / (2 * c * v))   -- v the rectangular max
theorem integral_specNorm_sum_smul_le … :
    ∫ ω, specNorm (∑ k, γ k ω • B k) ∂μ ≤ √(2 * c * v * Real.log (Fintype.card m + Fintype.card n))
```

Gaussian and Rademacher series are the instances `c = 1` (P2's
`hasSubgaussianMGF_of_hasLaw_gaussianReal`, `hasSubgaussianMGF_of_hasLaw_rademacherMeasure`); no
per-law copies (the prototype had 12).

## 4. Consumers of the headline statements

Chernoff simplified tails: Sketching's row sampling. Bernstein rectangular and mean: AMM by
sampling, R-stages. Series: R2, Sketching. Subadditivity: sampling without replacement. The
scalar Bernstein: P1's consumers.

## 5. Files

1. `Probability/MatrixConcentration/Laplace.lean`: §3.1 (4).
2. `Probability/MatrixConcentration/Subadditivity.lean`: §3.2 (3); the Jensen step may go to
   `NLAlib/ForMathlib/Analysis/Convex/Integral.lean` if it is a general fact.
3. `Probability/MatrixConcentration/MGFBound.lean`: §3.3 (6); imports 1 and 2.
4. `Probability/MatrixConcentration/Chernoff.lean`: §3.4 (5).
5. `Probability/MatrixConcentration/Bernstein.lean`: §3.5 (5); the scalar corollary may move to
   `Probability/SubExponential/` or a `Bernstein` file of its own.
6. `Probability/MatrixConcentration/Series.lean`: §3.6 (4).
4 to 6 are independent of each other.

## 6. Material

Read: the prototype's `Probability/Concentration/Matrix/` (70 declarations over `ℂ` and
`Fin d`), `Concentration/Basic/{MatrixStatistics,ChernoffFunctions,MatrixCalculus}.lean`,
`ForMathlib/MeasureTheory/Integral.lean` (`ConcaveOn.le_map_integral_of_integral_mem`). Reused as
proof material: the Laplace bounds, probabilistic Lieb and subadditivity, the Chernoff and
Bernstein MGF bounds, the dilation step. Not reproduced: `cumulantSum`, `hermitianSecondMoment`,
`rectSecondMoment` (the statements write `∑ k, ∫ X k ^ 2` and its `specNorm` directly);
`bernsteinTail`, `chernoffUpperTail`, `chernoffLowerTail`, `chernoffCgfCoefficient`,
`gaussianSeriesTail` (tails written out, D5 rule 2); `lambdaMax`, `lambdaMin`, `matrixExp`,
`traceExp`, `matrixLog` (Matrix-layer spellings); the 12 per-law series copies;
`[NeZero d]` and `Fin d`, `Fin N` (generic index types).

## 7. Open questions (orchestrator decisions, recorded for review)

**Q1. `A` Hermitian as a field of the interface**, not a hypothesis of each theorem: every
constructor produces a Hermitian `A` and every consumer needs it.

**Q2. The variance statistic written out**, not a definition: it is a one-term expression in
the Matrix layer's vocabulary, the same in every statement, and a definition would hide the
`∫ X ^ 2` a consumer must compute.

**Q3. Non-strict events and `[Nonempty n]`** throughout (D3; brief §3.1 permits a hypothesis on
the cardinal; `[Nonempty n]` is the Matrix layer's form of it).
