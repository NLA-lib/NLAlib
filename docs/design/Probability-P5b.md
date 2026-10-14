# Design note: Probability stage P5b, matrix concentration in the intrinsic dimension

Status: drafted 2026-10-14 by an Opus agent from the orchestrator's brief; not yet reviewed.
Second part of P5 (P5a §0): the generalised Laplace transform bound and the intrinsic-dimension
forms of matrix Chernoff and Bernstein (Tropp 2015, chapter 7), on top of P5a's
`HasMatrixMGFBound` and trace-level master bound. No new interface. No question of the brief's §2
kind (§7).

## 0. Scope and consumers

No consumer in either survey (inventory §5). Kept under D9 because a user expects it: the
dimension factor `d` of P5a becomes `intdim V ≤ rank V`, which makes the bounds usable for
kernel, covariance and sampling matrices with fast spectral decay.

| Item | Consumers |
|---|---|
| generalised Laplace bound `P(t ≤ λ_max Y) ≤ E tr ψ(Y) / ψ(t)` | the intrinsic tails here; any later trace-function tail |
| intrinsic Chernoff (trace form, sums, mean) | none in the surveys; sampling arguments of the next round may cite it |
| intrinsic Bernstein (trace form, Hermitian, rectangular, means) | none in the surveys; AMM-by-sampling variants |

## 1. Objects

| Concept | Spelling | Bridge |
|---|---|---|
| intrinsic dimension | the Matrix layer's `intrinsicDimension A = re (tr A) / specNorm A` (junk `0` at `A = 0`) | `Matrix.PosSemidef.one_le_intrinsicDimension`, `.intrinsicDimension_le_rank`, `intrinsicDimension_fromBlocks_le` (`Matrix/Functions/TraceFunctions.lean`) |
| intrinsic dimension lemma | `Matrix.PosSemidef.re_trace_cfc_le_intrinsicDimension_mul`: `tr φ(A) ≤ intdim A · φ(‖A‖)`, `φ` convex on `[0,∞)`, `φ 0 = 0` | Matrix layer, proved |
| trace function | `RCLike.re (cfc ψ A).trace` (no `traceFunction`, Matrix layer §5.3) | `Matrix.IsHermitian.re_trace_cfc` |
| variance proxy | a deterministic `V` with `∑ k, ∫ X k ^ 2 ≤ V` (Bernstein), `M` with `∑ k, ∫ X k ≤ M` (Chernoff); rectangular `V₁`, `V₂` and `intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂)` | P5a's variance statistic, bounded above in Loewner order |
| mean constant | `irreducible_def intrinsicBernsteinMeanConstant : ℝ := 20` | §3.3 |

`V ≥ ∑ E X²` is a hypothesis, not the definition of `V`: P5a's review (§8.1) showed the MGF bound
is not monotone in `A`, so the larger matrix enters after the trace,
`tr exp (g θ • ∑ A k) ≤ tr exp (g θ • V)` (`re_trace_exp_le_re_trace_exp_of_le`, `g θ ≥ 0`). A
user chooses `V` to trade `‖V‖` against `intdim V`; `V = ∑ E X²` is allowed.

## 2. Interfaces

None new. The sum forms go through P5a's constructors and
`HasMatrixMGFBound.integral_re_trace_exp_sum_le`; the trace forms take P5a's `htr` shape
(`Chernoff.lean`), so a non-independent `Y` gets the intrinsic tails from its trace bound alone.

## 3. Statement shapes

Conventions of P5a §3: `namespace NLAlib`, `open scoped Matrix.Norms.L2Operator MatrixOrder
ComplexOrder`, `rexp := Real.exp`, `{𝕜} [RCLike 𝕜] {n} [Fintype n] [DecidableEq n] {ι}
[Fintype ι]`, `[IsProbabilityMeasure μ]` unless noted (implied by `iIndepFun` in the sum forms).

Degenerate cases. *Empty `n`:* the Bernstein threshold forces `t ≥ L/3 > 0`, so the event is
empty: no `[Nonempty n]`; in the Chernoff tail `M ≠ 0` forces `n` nonempty. *`V = 0`
(Bernstein):* the summands are a.s. `0`, the event empty, the bound `0`: true, no `V ≠ 0` (the
prototype had one). *`M = 0` (Chernoff tail):* the event `{0 ≤ λ_max 0}` is everything and the
bound `2 · intdim 0 = 0`: false, so `M ≠ 0`. *`M = 0` (Chernoff mean):* both sides `0`
(`Real.log 0 = 0`), no hypothesis. *`L`:* `0 < L` as in P5a. *Non-integrable trace function:*
`hint` (the right side would be a junk `0`).

### 3.1 `Probability/MatrixConcentration/Laplace.lean` (P5a's file; dated amendment to P5a §5)

```lean
/-- **The generalised matrix Laplace transform bound**: for `ψ ≥ 0` nondecreasing on `[0, ∞)`,
`t ≥ 0` and `ψ t > 0`, `P(t ≤ λ_max Y) ≤ E tr ψ(Y) / ψ(t)`.
[Tropp2015, Proposition 7.4.1]; any measure (Markov's inequality), any `RCLike` field.
Result: generalized-matrix-laplace -/
theorem measureReal_eigenvalue_zero_ge_le_integral_re_trace_cfc_div [Nonempty n]
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {ψ : ℝ → ℝ} (hψ0 : ∀ x, 0 ≤ ψ x)
    (hψ : MonotoneOn ψ (Set.Ici 0))
    (hint : Integrable (fun ω => RCLike.re (cfc ψ (Y ω)).trace) μ) {t : ℝ} (ht : 0 ≤ t)
    (hψt : 0 < ψ t) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤ (∫ ω, RCLike.re (cfc ψ (Y ω)).trace ∂μ) / ψ t
```

`[Nonempty n]`: for empty `n` and `t = 0` the event is `Ω`, the right side `0`. No probability
hypothesis. Proof: `ψ t ≤ ψ (λ_max) ≤ tr ψ(Y)` pointwise (`hψ0`), then Markov.

### 3.2 `Probability/MatrixConcentration/IntrinsicDimension.lean`: Chernoff

```lean
/-- **Intrinsic-dimension matrix Chernoff, trace form**: for a.s. PSD `Y` with
`E tr exp (θ Y) ≤ tr exp ((e^{θL} - 1)/L • V)` for `θ > 0` and `δ ≥ L / λ_max V`,
`P((1 + δ) λ_max V ≤ λ_max Y) ≤ 2 intdim V (e^δ / (1 + δ)^{1+δ})^{λ_max V / L}`.
[Tropp2015, Theorem 7.2.1, (7.2.2)], there for independent sums. -/
theorem measureReal_eigenvalue_zero_ge_le_chernoff_intrinsicDim_of_integral_le
    (hY : ∀ᵐ ω ∂μ, (Y ω).PosSemidef) (hV : V.PosSemidef) (hV0 : V ≠ 0) (hL : 0 < L)
    (hint : ∀ θ : ℝ, 0 < θ → Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ : ℝ, 0 < θ → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp (((rexp (θ * L) - 1) / L) • V)).trace)
    {δ : ℝ} (hδ : L / eigenvalue V 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue V 0 ≤ eigenvalue (Y ω) 0} ≤
      2 * intrinsicDimension V * (rexp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue V 0 / L)
```

Proof (Tropp §7.6): §3.1 with `ψ a = max (e^{θa} - 1) 0`, the trace bound minus `card n`, the
intrinsic dimension lemma for `φ a = e^{g a} - 1`, and `e^a / (e^a - 1) ≤ 2` at `a = θ t ≥ 1`,
which `δ ≥ L / λ_max V` gives for `θ = log (1 + δ) / L`. `Y` PSD is needed for
`tr ψ(Y) = tr exp (θ Y) - d`.

Sum forms (hypotheses of `ChernoffSum.lean`, `M` in place of `∑ E X k`):

```lean
/-- **Intrinsic-dimension matrix Chernoff** (Tropp, Theorem 7.2.1). Better than
`measureReal_eigenvalue_zero_sum_ge_le_chernoff` when `2 intdim M < card n`; needs
`δ ≥ L / λ_max M`. -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff_intrinsicDim (hind : iIndepFun X μ)
    (hXm : ∀ k, AEMeasurable (X k) μ) (hL : 0 < L) (hpsd : ∀ k, ∀ᵐ ω ∂μ, (X k ω).PosSemidef)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {M : Matrix n n 𝕜}
    (hM : ∑ k, ∫ ω, X k ω ∂μ ≤ M) (hM0 : M ≠ 0) {δ : ℝ} (hδ : L / eigenvalue M 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue M 0 ≤ eigenvalue (∑ k, X k ω) 0} ≤
      2 * intrinsicDimension M * (rexp δ / (1 + δ) ^ (1 + δ)) ^ (eigenvalue M 0 / L)
/-- The mean (Tropp, Theorem 7.2.1): for every `θ > 0`,
`E λ_max (∑ X k) ≤ (e^θ - 1)/θ · λ_max M + L/θ · log (2 intdim M)`. -/
theorem integral_eigenvalue_zero_sum_le_chernoff_intrinsicDim (hind : iIndepFun X μ)
    (hXm …) (hL : 0 < L) (hpsd …) (hle …) {M : Matrix n n 𝕜} (hM : ∑ k, ∫ ω, X k ω ∂μ ≤ M)
    {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤
      (rexp θ - 1) / θ * eigenvalue M 0 + L / θ * Real.log (2 * intrinsicDimension M)
```

`M` PSD follows from `hM`; the mean's integrability is P5a's (`integrable_eigenvalue`).

### 3.3 `IntrinsicDimension.lean`: Bernstein

```lean
/-- **Intrinsic-dimension matrix Bernstein, trace form**: for centred `Y` with
`E tr exp (θ Y) ≤ tr exp (g θ • V)` on `(0, 3/L)` and `t ≥ √‖V‖ + L/3`,
`P(t ≤ λ_max Y) ≤ 4 intdim V exp (-(t²/2) / (‖V‖ + L t / 3))`. [Tropp2015, Theorem 7.7.1]. -/
theorem measureReal_eigenvalue_zero_ge_le_bernstein_intrinsicDim_of_integral_le
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) (hYi : Integrable Y μ) (hmean : ∫ ω, Y ω ∂μ = 0)
    (hV : V.PosSemidef) (hL : 0 < L)
    (hint : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) →
      Integrable (fun ω => RCLike.re (exp (θ • Y ω)).trace) μ)
    (htr : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (3 / L) → ∫ ω, RCLike.re (exp (θ • Y ω)).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • V)).trace)
    {t : ℝ} (ht : √(specNorm V) + L / 3 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (Y ω) 0} ≤
      4 * intrinsicDimension V * rexp (-(t ^ 2 / 2) / (specNorm V + L * t / 3))
/-- **Intrinsic-dimension matrix Bernstein**, Hermitian summands. Better than
`measureReal_eigenvalue_zero_sum_ge_le_bernstein` when `4 intdim V < card n`, and only for `t`
above the threshold. -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein_intrinsicDim (hind : iIndepFun X μ)
    (hL : 0 < L) (hX2 : ∀ k, MemLp (X k) 2 μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, X k ω ≤ L • (1 : Matrix n n 𝕜)) {V : Matrix n n 𝕜}
    (hV : ∑ k, ∫ ω, X k ω ^ 2 ∂μ ≤ V) {t : ℝ} (ht : √(specNorm V) + L / 3 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ k, X k ω) 0} ≤
      4 * intrinsicDimension V * rexp (-(t ^ 2 / 2) / (specNorm V + L * t / 3))
/-- Rectangular summands, through the dilation ([Tropp2015, Theorem 7.3.1]). -/
theorem measureReal_specNorm_sum_ge_le_bernstein_intrinsicDim {m : Type*} [Fintype m]
    [DecidableEq m] {S : ι → Ω → Matrix m n 𝕜} (hind : iIndepFun S μ) (hL : 0 < L)
    (hS2 : ∀ k, MemLp (S k) 2 μ) (hmean : ∀ k, ∫ ω, S k ω ∂μ = 0)
    (hle : ∀ k, ∀ᵐ ω ∂μ, specNorm (S k ω) ≤ L) {V₁ : Matrix m m 𝕜} {V₂ : Matrix n n 𝕜}
    (hV₁ : ∑ k, ∫ ω, S k ω * (S k ω)ᴴ ∂μ ≤ V₁) (hV₂ : ∑ k, ∫ ω, (S k ω)ᴴ * S k ω ∂μ ≤ V₂)
    {t : ℝ} (ht : √(max (specNorm V₁) (specNorm V₂)) + L / 3 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ k, S k ω)} ≤
      4 * intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂) *
        rexp (-(t ^ 2 / 2) / (max (specNorm V₁) (specNorm V₂) + L * t / 3))
/-- The absolute constant of the intrinsic Bernstein means. [Tropp2015, Corollary 7.3.2, (7.3.3)]
leaves it unspecified; the prototype proved `20`. Use only the two lemmas below. -/
noncomputable irreducible_def intrinsicBernsteinMeanConstant : ℝ := 20
theorem intrinsicBernsteinMeanConstant_pos : 0 < intrinsicBernsteinMeanConstant
theorem intrinsicBernsteinMeanConstant_le : intrinsicBernsteinMeanConstant ≤ 20
theorem integral_eigenvalue_zero_sum_le_bernstein_intrinsicDim (hind …) (hL …) (hX2 …)
    (hmean …) (hle …) (hV : ∑ k, ∫ ω, X k ω ^ 2 ∂μ ≤ V) :
    ∫ ω, eigenvalue (∑ k, X k ω) 0 ∂μ ≤ intrinsicBernsteinMeanConstant *
      (√(specNorm V * Real.log (1 + intrinsicDimension V)) +
        L * Real.log (1 + intrinsicDimension V))
theorem integral_specNorm_sum_le_bernstein_intrinsicDim … (hV₁ …) (hV₂ …) :
    ∫ ω, specNorm (∑ k, S k ω) ∂μ ≤ intrinsicBernsteinMeanConstant *
      (√(max (specNorm V₁) (specNorm V₂) *
          Real.log (1 + intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂))) +
        L * Real.log (1 + intrinsicDimension (Matrix.fromBlocks V₁ 0 0 V₂)))
```

Proof (Tropp §7.7): §3.1 with `ψ a = e^{θa} - θa - 1 ≥ 0` (no PSD hypothesis;
`E tr ψ(Y) = E tr e^{θY} - d` by `hmean`), the intrinsic dimension lemma, and
`e^a / (e^a - a - 1) ≤ 1 + 3/a² ≤ 4` at `a = θ t ≥ 1` for `θ = t / (v + L t / 3)` (the threshold
gives `θ t ≥ 1`). At `V = 0` that `θ` is `3/L`, outside the window, but then any `θ` in the window
gives `E tr ψ(Y) ≤ 0`. Sum forms: P5a's constructor and `integral_re_trace_exp_sum_le`, then
monotonicity after the trace; rectangular through P5a's dilation step. Means: integrate the tail
above the threshold (P0's `integral_le_of_measureReal_ge_le`).

## 4. Consumers of the headline statements

None in the surveys (§0).

## 5. Files

1. `Probability/MatrixConcentration/Laplace.lean`: §3.1 (+1), amendment to P5a §5.
2. `Probability/MatrixConcentration/IntrinsicDimension.lean`: §3.2 (3), §3.3 (8, with the
   constant and its two lemmas); imports `ChernoffSum.lean`, `Bernstein.lean`. About 600 lines
   expected; if over budget, Bernstein splits to `IntrinsicDimensionBernstein.lean`.
3. `Bernstein.lean` (P5a): `exists_bernstein_exponent`, `integral_dilation_sq` made public.

## 6. Material

Read: the prototype's `Concentration/Matrix/{GeneralizedLaplace,IntrinsicChernoff,
IntrinsicHermitianBernstein,IntrinsicBernstein,IntrinsicBernsteinExpectation}.lean` (7
declarations over `ℂ`, `Fin d`, `[NeZero d]`) and the Matrix layer's `TraceFunctions.lean`.
Reused: the choices of `ψ` and `θ`, the dilation block. Not reproduced: `traceFunction`,
`lambdaMax`; the hypotheses `E (∑ X)² ≤ V`, `E Z Zᴴ ≤ V₁` (replaced by sums of second moments,
P5a's statistic, equal under independence and centring); `V ≠ 0` in the Bernstein forms; the
unused `Measurable Y`; `0 ≤ L`. Atlas id: `intrinsic-dimension`.

## 7. Open questions

**Of the brief's §2 kind:** none.

**Decisions taken (recorded for review):**

- **D1. Trace forms first** (P5a §8.2's pattern); the independent sums are corollaries.
- **D2. Constants** (D5 rule 2): Tropp's `2 intdim`, `4 intdim` written; the means' unspecified
  constant behind `intrinsicBernsteinMeanConstant` (P\* value `20`) with `_pos` and `_le`.
- **D3. Names** `…_chernoff_intrinsicDim`, `…_bernstein_intrinsicDim` (D5 rule 3); docstrings
  name the dimension form and the regime. No minimum of the two (D5 rule 4).
- **D4. Chernoff mean with free `θ > 0`**, as Tropp states it; P5a fixed `θ = 1` for the
  dimension form. `θ = 1` is a one-line instance and is not stated.
- **D5. Hypotheses only where a degenerate case fails** (§3): `M ≠ 0` in the Chernoff tail; no
  `V ≠ 0`, no `[Nonempty n]` in the Bernstein forms.
- **D6.** The generalised Laplace bound goes in P5a's `Laplace.lean` (it owns the subject).

Unchecked: the theorem labels of Tropp 2015 chapter 7 (taken from the prototype's docstrings; the
Hermitian intrinsic Bernstein is cited there as 7.7.1 and the rectangular as 7.3.1).
