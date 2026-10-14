# Design note: Probability stage P5c, trace moments and noncommutative Khintchine

Status: drafted 2026-10-14 by an Opus agent from the orchestrator's brief; not yet reviewed.
Third part of P5 (P5a §0): the second moment of a matrix series with isotropic coefficients and
the even trace moments `E tr Y^{2p} ≤ (2p-1)^p tr (∑ A i²)^p` of Gaussian and Rademacher series,
from one law-free recursion. Needs one statement in P2's file (the Rademacher sign flip) and one in
P6's file (Stein's identity for derivatives of polynomial growth). No new interface. No question
of the brief's §2 kind (§7).

## 0. Scope and consumers

No consumer in either survey (inventory §5). Kept under D9 because a user expects it: the
moment form behind P5a's series tail, giving every moment of `‖Y‖`.

| Item | Consumers |
|---|---|
| `E Y² = ∑ A i²` for isotropic real coefficients | the `p = 1` case; variance of a series (R-stages, Sketching, if they need it) |
| law-free recursion `E tr Y^{2q+2} ≤ (2q+1) E tr (V Y^{2q})` ⟹ `≤ (2q+1)^{q+1} tr V^{q+1}` | the two laws here; any later law with the recursion (exchangeable pairs) |
| Gaussian and Rademacher noncommutative Khintchine, with integrability | none in the surveys |

## 1. Objects

No new definition. The series is written out, `∑ i, g ω i • A i` with real coefficients
`g : Ω → ι → ℝ` and `A : ι → Matrix n n 𝕜`; its variance is written out, `∑ i, A i ^ 2` (P5a §7
Q2: no named variance statistic). Laws by P2: `HasLaw g (gaussianVector ι) μ`,
`HasLaw ε (rademacherVector ι) μ` (D2). Trace moments are `RCLike.re ((…) ^ r).trace`. Matrix layer
used directly: `re_trace_mul_pow_mul_pow_le` (`tr (C Hˡ C Hᵏ) ≤ tr (C² Hˡ⁺ᵏ)` for even `l + k`),
`re_trace_sub_mul_pow_sub_pow_le` (the mean value trace inequality), `re_trace_mul_pow_le_add`
(trace Young with the exact absorption constant), `Matrix.IsHermitian.re_trace_pow_nonneg`
(`Matrix/Functions/TracePowers.lean`); P0's `IsIsotropic`.

## 2. Interfaces

None new. The second moment takes P0's `IsIsotropic` (over `ℝ`), the moments the two laws. No
"symmetric coefficient" interface: the two recursions use different properties (Stein, sign
flips), and the shared step is the law-free lemma, which takes the recursion as hypothesis.

## 3. Statement shapes

`namespace NLAlib`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`;
`{𝕜} [RCLike 𝕜] {n} [Fintype n] [DecidableEq n] {ι} [Fintype ι] [DecidableEq ι]`,
`{A : ι → Matrix n n 𝕜}`. The probability measure is implied by `HasLaw` with a probability law
(D2); the law-free lemma takes `[IsProbabilityMeasure μ]`.

Degenerate cases: *`p = 0`:* both sides are `card n` (`tr 1`, and `(2·0 - 1 : ℝ)^0 = 1`), true,
so `p` is any natural number. *`ι` empty or `A = 0`:* `Y = 0`, the left side is `0` for `p ≥ 1`
and the right side `(2p-1)^p tr 0 = 0`. *Empty `n`:* both traces `0`. *Non-Hermitian `A i`:*
excluded (`re tr Y^{2p}` is not the Schatten moment and the inequality can fail). *Integrability:*
a companion for each law (D3); the law-free lemma needs none (if either trace moment is not
integrable, `hrec` forces the left side to be `0`, and the conclusion holds since its right side
is nonnegative). Exponents in the recursions are `2 * q + 2` and `2 * q` (no truncated
subtraction, `CONTRIBUTING.md` §5.3); the headline uses `2 * p` with the real constant
`(2 * p - 1 : ℝ) ^ p`.

### 3.1 `Probability/MatrixConcentration/Khintchine.lean`

```lean
/-- A matrix series with isotropic real coefficients has `E [Y²] = ∑ A i²`. No Hermitian
hypothesis. [Tropp2015, §4.6] (Gaussian and Rademacher coefficients). -/
theorem IsIsotropic.integral_sum_smul_sq {ε : Ω → ι → ℝ} (hε : IsIsotropic ε μ)
    (A : ι → Matrix n n 𝕜) : ∫ ω, (∑ i, ε ω i • A i) ^ 2 ∂μ = ∑ i, A i ^ 2
theorem IsIsotropic.integrable_sum_smul_sq {ε : Ω → ι → ℝ} (hε : IsIsotropic ε μ)
    (A : ι → Matrix n n 𝕜) : Integrable (fun ω => (∑ i, ε ω i • A i) ^ 2) μ

/-- **The moment recursion closes.** If `E tr Y^{2q+2} ≤ (2q+1) E tr (V Y^{2q})` for a PSD `V`,
then `E tr Y^{2q+2} ≤ (2q+1)^{q+1} tr V^{q+1}`. Law-free; the Gaussian and Rademacher series
satisfy the recursion with `V = ∑ A i²`. [MackeyEtAl2014, §7] (the absorption step). -/
theorem integral_re_trace_pow_le_of_recursion [IsProbabilityMeasure μ] {Y : Ω → Matrix n n 𝕜}
    (hY : ∀ᵐ ω ∂μ, (Y ω).IsHermitian) {V : Matrix n n 𝕜} (hV : V.PosSemidef) (q : ℕ)
    (hrec : ∫ ω, RCLike.re (Y ω ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) * ∫ ω, RCLike.re (V * Y ω ^ (2 * q)).trace ∂μ) :
    ∫ ω, RCLike.re (Y ω ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) ^ (q + 1) * RCLike.re (V ^ (q + 1)).trace

/-- Polynomial trace moments of a Gaussian series are integrable. -/
theorem integrable_re_trace_sum_smul_pow_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (A : ι → Matrix n n 𝕜) (r : ℕ) :
    Integrable (fun ω => RCLike.re ((∑ i, g ω i • A i) ^ r).trace) μ
/-- The Gaussian moment recursion, by Stein's identity in each coordinate. -/
theorem integral_re_trace_sum_smul_pow_le_mul_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (q : ℕ) :
    ∫ ω, RCLike.re ((∑ i, g ω i • A i) ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) * ∫ ω, RCLike.re ((∑ i, A i ^ 2) * (∑ i, g ω i • A i) ^ (2 * q)).trace ∂μ
/-- **Noncommutative Khintchine inequality**, Gaussian series:
`E tr (∑ g i A i)^{2p} ≤ (2p - 1)^p tr (∑ A i²)^p`.
[Tropp2015, §4.7]; [MackeyEtAl2014, §7]; over any `RCLike` field, any finite index types.
Result: noncommutative-khintchine -/
theorem integral_re_trace_sum_smul_pow_le_of_hasLaw_gaussianVector {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    ∫ ω, RCLike.re ((∑ i, g ω i • A i) ^ (2 * p)).trace ∂μ ≤
      (2 * p - 1 : ℝ) ^ p * RCLike.re ((∑ i, A i ^ 2) ^ p).trace

theorem integrable_re_trace_sum_smul_pow_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (A : ι → Matrix n n 𝕜) (r : ℕ) :
    Integrable (fun ω => RCLike.re ((∑ i, ε ω i • A i) ^ r).trace) μ
/-- The Rademacher moment recursion, by flipping one sign at a time. -/
theorem integral_re_trace_sum_smul_pow_le_mul_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (q : ℕ) :
    ∫ ω, RCLike.re ((∑ i, ε ω i • A i) ^ (2 * q + 2)).trace ∂μ ≤
      (2 * q + 1 : ℝ) * ∫ ω, RCLike.re ((∑ i, A i ^ 2) * (∑ i, ε ω i • A i) ^ (2 * q)).trace ∂μ
/-- **Noncommutative Khintchine inequality**, Rademacher series. [Tropp2015, §4.7];
[MackeyEtAl2014, §7]. Result: noncommutative-khintchine -/
theorem integral_re_trace_sum_smul_pow_le_of_hasLaw_rademacherVector {ε : Ω → ι → ℝ}
    (hε : HasLaw ε (rademacherVector ι) μ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    ∫ ω, RCLike.re ((∑ i, ε ω i • A i) ^ (2 * p)).trace ∂μ ≤
      (2 * p - 1 : ℝ) ^ p * RCLike.re ((∑ i, A i ^ 2) ^ p).trace
```

Proofs. *Law-free:* trace Young pointwise,
`(q+1)(2q+1) tr (V Y^{2q}) ≤ (2q+1)^{q+1} tr V^{q+1} + q tr Y^{2q+2}`, integrated and combined
with `hrec`: `(q+1) M ≤ (2q+1)^{q+1} tr V^{q+1} + q M`. *Gaussian:*
`tr Y^{2q+2} = ∑ i, g i tr (A i Y^{2q+1})`; Stein's identity (§3.2) turns `E [g i F(g)]` into
`E [∂_i F(g)] = ∑_{l ≤ 2q} E tr (A i Y^l A i Y^{2q-l})`, each term at most `E tr (A i² Y^{2q})`
(`re_trace_mul_pow_mul_pow_le`, `l + (2q - l)` even). *Rademacher:* with `Y⁽ⁱ⁾` the series with
the `i`-th sign flipped, the law is unchanged (§3.3), so
`E [ε i tr (A i Y^{2q+1})] = ¼ E tr ((Y - Y⁽ⁱ⁾)(Y^{2q+1} - Y⁽ⁱ⁾^{2q+1}))`, and the mean value trace
inequality with `Y - Y⁽ⁱ⁾ = 2 ε i A i`, `ε i² = 1`, gives `(2q+1) E tr (A i² Y^{2q})` after a
second flip. *Headline:* `p = 0` directly, `p = q + 1` from the recursion and the law-free lemma.
*Integrability:* Gaussian polynomial moments (`HasGaussianLaw.memLp`, P6 §6); Rademacher
coordinates are a.s. bounded.

### 3.2 Addition to `Probability/Distributions/GaussianIntegrationByParts.lean` (P6's file)

P6's Stein identity takes `f` of class `C¹` with **bounded** derivative (P6 D1, chosen for R3).
`x ↦ re tr (B (∑ x j • A j)^q)` has a derivative of polynomial growth, so P6's statement does not
apply. One sibling, of which P6's is the case `k = 0`:

```lean
/-- **Gaussian integration by parts** for `f` of class `C¹` whose derivative grows at most
polynomially. [Vershynin2018, Lemma 7.2.5] (standard Gaussian); any mean and covariance. -/
theorem integral_sub_integral_mul_eq_sum_covariance_mul_integral_fderiv_of_hasGaussianLaw_of_le_pow
    {X : Ω → ι → ℝ} (hX : HasGaussianLaw X μ) {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} {k : ℕ} (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ k) (i : ι) :
    ∫ ω, (X ω i - ∫ ω', X ω' i ∂μ) * f (X ω) ∂μ =
      ∑ j, covariance (fun ω => X ω i) (fun ω => X ω j) μ *
        ∫ ω, fderiv ℝ f (X ω) (Pi.single j 1) ∂μ
```

`‖x‖` is the sup norm of `ι → ℝ`; any norm gives the same class, `C` absorbs the change. Proof:
P6's route (reduction to the standard vector, one-dimensional integration by parts in each
coordinate) with Gaussian moments of every order in place of linear growth. P6's theorem is then
reproved from it at `k = 0` and keeps its name (D5 rule 5).

### 3.3 Addition to `Probability/Distributions/Rademacher.lean` (P2's file)

P2 deferred the sign-flip symmetry to here (P2 §0).

```lean
/-- The Rademacher law is symmetric. -/
theorem measurePreserving_neg_rademacherMeasure :
    MeasurePreserving (fun x : ℝ => -x) rademacherMeasure rademacherMeasure
/-- Flipping one coordinate of a Rademacher vector preserves its law. -/
theorem measurePreserving_update_neg_rademacherVector [DecidableEq n] (i : n) :
    MeasurePreserving (fun x : n → ℝ => Function.update x i (-x i))
      (rademacherVector n) (rademacherVector n)
```

The second is Mathlib's `measurePreserving_pi` (`-·` in coordinate `i`, `id` elsewhere). Proofs
with `HasLaw ε (rademacherVector n) μ` transport through `integral_map`; no twin is stated.

## 4. Consumers of the headline statements

None in the surveys (§0).

## 5. Files

1. `Probability/Distributions/Rademacher.lean`: §3.3 (+2). Independent of 2.
2. `Probability/Distributions/GaussianIntegrationByParts.lean`: §3.2 (+1, and P6's theorem
   reproved).
3. `Probability/MatrixConcentration/Khintchine.lean`: §3.1 (9); imports 1, 2, P0's
   `Isotropic.lean`, P2's laws. The derivative of `x ↦ re tr (B Y(x)^q)` is a private helper here
   unless `ForMathlib/Analysis/Calculus/Deriv/Matrix.lean` already has the product rule it needs.
   If over budget: `Khintchine.lean` (law-free lemma, second moment, Rademacher) and
   `KhintchineGaussian.lean`.

## 6. Material

Read: the prototype's `Concentration/Matrix/{PolynomialMoment,RademacherKhintchine,
RademacherPolynomialMoments}.lean`, `Gaussian/Moments/{Khintchine,SeriesKhintchine,
SeriesPolynomialMoments,SeriesSecondMoment}.lean`, `Rademacher/RademacherSymmetry.lean` (over `ℂ`,
on the measures `gaussianVector (Fin n)` and `rademacherVector κ`, with `_of_hasLaw` twins).
Reused: the absorption argument, the coordinate Stein step and the sign-flip step. Not
reproduced: the measure-form statements and their four `_of_hasLaw` twins (D2: one random-variable
form); the rooted forms `(E tr Y^{2p})^{1/2p} ≤ √(2p-1) …` (one `rpow` step from the headline);
the separate integrability lemmas for products `tr (B Y^r C Y^s)` and coordinate products (proof
helpers, private); `integral_re_trace_independent_series_sq` (replaced by the isotropic form,
which needs no independence); `integral_coordinate_mul_coordinate_rademacherVector` and
`integral_update_neg_rademacherVector` (proof leaves). The prototype's
`Gaussian/Moments/{Isserlis,WickPairings,PolynomialLinearMoments,PositiveMoments}.lean` (P6 §0
assigned Gaussian moments to this stage): not ported, no consumer; general-covariance Isserlis is
cut by D9 and the standard case has no user (R2 §0 does not port the fourth moments). Atlas id:
`noncommutative-khintchine`.

## 7. Open questions

**Of the brief's §2 kind:** none.

**Decisions taken (recorded for review):**

- **D1. One law-free lemma**, the laws entering by their recursions (brief); the recursions are
  public, the step another law (exchangeable pairs) would prove.
- **D2. Constant `(2p - 1)^p` written** (D5 rule 2: the source's small constant). Buchholz's
  `(2p - 1)!!` would be a dominated improvement of another shape (D5 rule 5).
- **D3. Over `𝕜` with real coefficients**; standard laws only. Correlated Gaussian coefficients
  are a linear change of the `A i`.
- **D4. Stein's identity gets a polynomial-growth sibling in P6's file** (§3.2), amending P6 D1
  (an orchestrator decision, not a maintainer one): the bounded class cannot reach trace
  polynomials. Alternative: an expansion into monomials with the one-dimensional Gaussian moment
  recursion, rejected as longer and private to this file.
- **D5. Not stated:** the spectral-norm moments `E ‖Y‖^{2p} ≤ (2p-1)^p d ‖∑ A i²‖^p` (two
  Matrix-layer lemmas, `specNorm_pow_le_re_trace_pow` and
  `re_trace_pow_le_card_mul_specNorm_pow`, compose with the headline), the rooted and Schatten
  forms, scalar Khintchine (P1's sub-Gaussian moments cover scalar series).

Unchecked: the printed label of the `(2p-1)^p` bound (Tropp 2015 discusses noncommutative
Khintchine in the notes to chapter 4; Mackey et al. 2014 prove the trace form by exchangeable
pairs). The docstring agent fixes the labels.

## 8. Amendments from the review (2026-10-14)

Review: Fable, of P5b, P5c, P5d and P7 together; the orchestrator accepted every finding. The
skeletons are written under the rule that no `sorry` enters a proved file: new statements go in
new files, merged at wrap-up.

1. **Polynomial-growth Stein confirmed needed and cheap** (D4 stands). P6's one-dimensional step
   `integral_mul_eq_integral_deriv_gaussianReal_one` (private) takes only integrability; the bound
   on the derivative is used only for the growth and `L²` estimates
   (`memLp_two_comp_of_norm_fderiv_le`), which polynomial growth replaces through
   `memLp_id_gaussianReal` and `HasGaussianLaw.memLp`. Recorded in the docstring. The statement
   of §3.2 is unchanged. P6's bounded theorem stays as it is until wrap-up, where it either
   becomes the `k = 0` corollary (D5 rule 6, keeping its name) or stays as proved.
2. **Law-free lemma, integrability** (in the docstring): no integrability hypothesis is needed,
   by a case split. If `tr (V Y^{2q})` is not integrable its integral is `0`, and `hrec` makes the
   left side at most `0`; if `tr Y^{2q+2}` is not integrable the left side is `0`; either way the
   right side is nonnegative (`Matrix.PosSemidef.re_trace_pow_nonneg`). If both are integrable,
   trace Young is integrated (and `|tr (V Y^{2q})| ≤ ‖V‖ (d + tr Y^{2q+2})` on a probability
   measure shows the second integrability follows from the first). This replaces §3's sentence
   "if either trace moment is not integrable, `hrec` forces the left side to be `0`".
3. **Citations.** The trace bound is [MackeyEtAl2014, Theorem 7.1], not "§7". Tropp 2015's
   section numbers for noncommutative Khintchine are unconfirmed: cite [Tropp2015, chapter 4].
   The review asked for the key `MackeyJordanChenFarrellTropp2014`; the same paper is already in
   `docs/references.bib` as `MackeyEtAl2014` (cited by `TracePowers.lean`), so no second key was
   added and the skeletons cite `MackeyEtAl2014`.
4. **Files** (amends §5). §3.3 is in a new skeleton file
   `Probability/Distributions/RademacherSymmetry.lean` (2 statements), to be merged into
   `Rademacher.lean`; §3.2 in a new skeleton file
   `Probability/Distributions/GaussianIntegrationByPartsGrowth.lean` (1 statement), to be merged
   into `GaussianIntegrationByParts.lean`, where P6's theorem is then reproved from it or kept.
   `Probability/MatrixConcentration/Khintchine.lean` (9 statements, §3.1 unchanged) imports both
   new files, `TracePowers.lean`, `Gaussian.lean` and `MatrixIntegral.lean`. The proved files get
   no `sorry`; nothing is registered in `NLAlib.lean` yet.
5. **Instances.** `[DecidableEq ι]` is taken only by the two isotropic second-moment lemmas
   (`IsIsotropic` needs it); the law statements do not use it.
6. **Wrap-up** (resolves items 1 and 4). `RademacherSymmetry.lean` is merged into
   `Rademacher.lean` and `GaussianIntegrationByPartsGrowth.lean` into
   `GaussianIntegrationByParts.lean`, where P6's bounded theorem is now the `k = 0` corollary of
   the polynomial-growth one, keeping its name; P6's bounded-derivative helpers are deleted.
