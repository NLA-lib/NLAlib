# Design note: Probability stage P7, remaining concentration

Status: drafted 2026-10-14 by an Opus agent from the orchestrator's brief; not yet reviewed.
The end of the Probability layer (brief §4 P7, D9): the Orlicz bridges (`ψ₂` to sub-Gaussian,
`ψ₁` to sub-exponential) and the bounded differences inequality (McDiarmid), proved by the
entropy method on P4's tensorization. No new interface. No question of the brief's §2 kind (§7).
D9 allows this stage to be scaffolded; §5 marks what may be.

## 0. Scope and consumers

No consumer in either survey (inventory §5). Kept because a user expects them: the Orlicz
conditions are how much of the literature (Vershynin's book) states sub-Gaussian and
sub-exponential hypotheses, and bounded differences is the standard inequality for functions of
independent non-Gaussian variables.

| Item | Consumers |
|---|---|
| `ψ₂` bridge: `E exp (X²/K) ≤ 2`, centred ⟹ `HasSubgaussianMGF X (C K)` | every theorem taking `HasSubgaussianMGF` (P1, P3's Hanson–Wright, P5a's series) |
| `ψ₁` bridge: `E exp (|X|/K) ≤ 2`, centred ⟹ `HasSubexponentialMGF X (C₁ K²) (C₂ K)` | P1's Bernstein for sums, P3 |
| entropy of `exp (s g)` for a bounded `g` | McDiarmid; later entropy-method results |
| bounded differences ⟹ `HasSubgaussianMGF` of the centred function; McDiarmid's tail | none in the surveys |

What D9 and brief §4 also list, and where it is: *entropy and its tensorization in general* is P4
(`entropy_pi_le_sum` for nonnegative functions on any finite product, Herbst's argument as
`hasSubgaussianMGF_sub_integral_of_entropy_le`); the prototype's remaining entropy declarations
were proof leaves (ledgered by P4). *Scalar Bernstein in `ψ₁` form* is the `ψ₁` bridge followed
by P1's `HasSubexponentialMGF.measure_sum_ge_le_of_iIndepFun` (§7 D4). *`ψ₂` Hanson–Wright* is
the `ψ₂` bridge followed by P3's `measureReal_quadForm_sub_integral_ge_le` (§7 D3).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| `ψ₂` condition with squared scale `K` | `Integrable (fun ω => rexp (X ω ^ 2 / K)) μ` and `∫ ω, rexp (X ω ^ 2 / K) ∂μ ≤ 2`, `K : ℝ≥0`, `0 < K` | Mathlib's condition (iv) in the docstring of `Probability/Moments/SubGaussian.lean` (`𝔼[exp(X^2 / K₄)] ≤ 2`, the Orlicz norm left as a TODO); Vershynin's `‖X‖_ψ₂ ≤ K'` is `K = K' ^ 2` |
| `ψ₁` condition with scale `K` | `Integrable (fun ω => rexp (|X ω| / K)) μ` and `∫ ω, rexp (|X ω| / K) ∂μ ≤ 2` | Vershynin's `‖X‖_ψ₁ ≤ K` |
| bounded differences | `∀ i x y, |f (Function.update x i y) - f x| ≤ c i`, `c : ι → ℝ≥0`, on `∀ i, S i` | P4's `PiUpdate.lean` vocabulary |
| constants | `psiTwoSubgaussianConstant`, `psiOneSubexponentialVarianceConstant`, `psiOneSubexponentialScaleConstant : ℝ≥0`, each an `irreducible_def` (D5 rule 2) | §3.1 |

Each scale is the one in which the condition is linear (`X² / K`, `|X| / K`); proxies `C K`,
`C₁ K²`, `C₂ K`, in `ℝ≥0` (D2). No Orlicz norm is defined: as an infimum it is a junk `0` for a
variable with no finite norm, and every consumer passes through the bridges.

## 2. Interfaces

None new. The Orlicz conditions are constructor hypotheses of the existing interfaces (D6 lists
`ψ₂` and `ψ₁` as instances of the sub-Gaussian and sub-exponential interfaces), never hypotheses
of a concentration theorem. Bounded differences concludes Mathlib's `HasSubgaussianMGF` of the
centred function (D6, "concentration of a function").

## 3. Statement shapes

`namespace NLAlib`; `{Ω} {mΩ} {μ : Measure Ω}`; `rexp := Real.exp`; `open scoped NNReal`.

Degenerate cases. *`K = 0`:* `X²/0 = 0` in Lean, so the `ψ` condition holds for every `X` and the
bridge would give proxy `0`: false, hence `0 < K`. *Measure:* `μ = 2 • δ₀`, `X = 0` satisfies
the `ψ₂` condition and is centred but `mgf X μ 0 = 2 > 1`: `[IsProbabilityMeasure μ]`.
*Measurability:* integrability of `exp (X² / K)` does not give `AEMeasurable X` (the sign is
lost), so it is a hypothesis. *Bounded differences, `ι` empty:* `f` is constant, proxy `0`, true.
*`∑ c i ^ 2 = 0`:* the tail's exponent is `-2t²/0 = 0`, bound `1`, true; no special case (the
prototype's piecewise `mcdiarmidTail` is not needed). *`t < 0`:* the tail fails (the event can
have probability `1`), so `0 ≤ t`. *Integrability of `f (X)`:* bounded differences on a finite
product make `f` bounded, so none is assumed.

### 3.1 `Probability/Orlicz.lean`

```lean
/-- The proxy constant of the `ψ₂` bridge. [Vershynin2018, Proposition 2.5.2] leaves it
unspecified; the proof (`e^y ≤ y + e^{y²}`, then Jensen for `λ² K ≤ 1` and
`λX ≤ λ²K/2 + X²/(2K)` otherwise) reaches `1 + log 2`. Use only `_le`. -/
noncomputable irreducible_def psiTwoSubgaussianConstant : ℝ≥0 := 2
theorem psiTwoSubgaussianConstant_le : psiTwoSubgaussianConstant ≤ 2
/-- **A centred variable with a `ψ₂` bound is sub-Gaussian**: `E exp (X²/K) ≤ 2` and `E X = 0`
give `HasSubgaussianMGF X (C K)`. [Vershynin2018, Proposition 2.5.2]; the proxy constant is
`psiTwoSubgaussianConstant`. -/
theorem hasSubgaussianMGF_of_integral_exp_sq_div_le_two [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (hmean : ∫ ω, X ω ∂μ = 0) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (X ω ^ 2 / K)) μ)
    (hψ : ∫ ω, rexp (X ω ^ 2 / K) ∂μ ≤ 2) :
    HasSubgaussianMGF X (psiTwoSubgaussianConstant * K) μ

/-- The variance-proxy and scale constants of the `ψ₁` bridge. [Vershynin2018, Proposition 2.7.1]
leaves them unspecified; the proof (`e^y ≤ 1 + y + y² e^{|y|}/2` on `|λ| < 1/(2K)` and
`u² ≤ 4 e^{u-2}`) reaches `32 / e²` and `2`. Use only the `_le` lemmas. -/
noncomputable irreducible_def psiOneSubexponentialVarianceConstant : ℝ≥0 := 5
noncomputable irreducible_def psiOneSubexponentialScaleConstant : ℝ≥0 := 2
theorem psiOneSubexponentialVarianceConstant_le : psiOneSubexponentialVarianceConstant ≤ 5
theorem psiOneSubexponentialScaleConstant_le : psiOneSubexponentialScaleConstant ≤ 2
/-- **A centred variable with a `ψ₁` bound is sub-exponential.** [Vershynin2018,
Proposition 2.7.1]. -/
theorem hasSubexponentialMGF_of_integral_exp_abs_div_le_two [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (hmean : ∫ ω, X ω ∂μ = 0) {K : ℝ≥0} (hK : 0 < K)
    (hint : Integrable (fun ω => rexp (|X ω| / K)) μ)
    (hψ : ∫ ω, rexp (|X ω| / K) ∂μ ≤ 2) :
    HasSubexponentialMGF X (psiOneSubexponentialVarianceConstant * K ^ 2)
      (psiOneSubexponentialScaleConstant * K) μ
```

The comparison lemmas are upper bounds: a smaller proxy is the better bound, so an improvement
lowers the body and keeps `_le` true (D5 rule 2; the Hanson–Wright constant has a lower bound
because there a larger value is better). The bodies are literals in `ℝ≥0` above the values the
sketched proofs reach; the proof agent sets each body to the value it proves if that is cleaner
(`1 + Real.log 2` needs a `Real.toNNReal` in the body, which is allowed there and nowhere else).
No positivity lemma: no consumer divides by these constants.

### 3.2 Addition to `Probability/Entropy.lean` (P4's file)

```lean
/-- **The entropy of an exponential of a bounded function**: if the oscillation of `g` is at most
`c`, then `Ent(e^{s g}) ≤ s² c² / 8 · E e^{s g}`. The entropy form of Hoeffding's lemma.
[BoucheronLugosiMassart2013, proof of Theorem 6.2]. -/
theorem entropy_exp_mul_le_of_abs_sub_le [IsProbabilityMeasure ν] {g : Ω → ℝ}
    (hg : AEMeasurable g ν) {c : ℝ≥0} (hc : ∀ x y, |g x - g y| ≤ c) (s : ℝ) :
    entropy ν (fun ω => rexp (s * g ω)) ≤ s ^ 2 * c ^ 2 / 8 * ∫ ω, rexp (s * g ω) ∂ν
```

Proof: with `Λ = log E e^{sg}`, `Ent(e^{sg}) / E e^{sg} = s Λ'(s) - Λ(s) = ∫₀ˢ θ Λ''(θ) dθ`, and
`Λ''` is the variance of `g` under the tilted law, at most `c²/4` (the step of Mathlib's proof of
Hoeffding's lemma, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`). `c = 0`: `g` constant,
entropy `0`.

### 3.3 `Probability/BoundedDifferences.lean`

`{ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]`,
`{X : Ω → ∀ i, S i}`, `{f : (∀ i, S i) → ℝ}`, `{c : ι → ℝ≥0}`.

```lean
/-- **Bounded differences**: a function of independent coordinates whose change in each
coordinate is at most `c i` is sub-Gaussian about its mean with proxy `∑ c i² / 4`.
[BoucheronLugosiMassart2013, Theorem 6.2]; [McDiarmid1989, Lemma 3.3]. Coordinates in arbitrary
measurable spaces; no integrability hypothesis (`f` is bounded). -/
theorem hasSubgaussianMGF_sub_integral_of_abs_update_sub_le
    (hX : ∀ i, AEMeasurable (fun ω => X ω i) μ) (hind : iIndepFun (fun i ω => X ω i) μ)
    (hf : Measurable f) (hc : ∀ i x y, |f (Function.update x i y) - f x| ≤ c i) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) ((∑ i, c i ^ 2) / 4) μ
/-- **McDiarmid's inequality**: `P(t ≤ f(X) - E f(X)) ≤ exp (-2t² / ∑ c i²)`.
[McDiarmid1989, Theorem 3.1]; [BoucheronLugosiMassart2013, Theorem 6.2].
Result: mcdiarmid -/
theorem measureReal_sub_integral_ge_le_mcdiarmid (hX …) (hind …) (hf …) (hc …) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ f (X ω) - ∫ ω', f (X ω') ∂μ} ≤ rexp (-2 * t ^ 2 / ∑ i, (c i : ℝ) ^ 2)
```

No probability hypothesis: `iIndepFun` gives it (P0 §9), and the zero measure makes both
statements trivial. Proof of the first: on the product `Measure.pi ν` (the law of `X`, from
`iIndepFun` and `hX`), P4's `entropy_pi_le_sum` for `e^{sf}`, §3.2 in each coordinate on the
fibre `y ↦ f (update x i y)` (oscillation `≤ c i`), P4's `integral_integral_update_pi` to
reassemble `E e^{sf}`, then Herbst (`hasSubgaussianMGF_sub_integral_of_entropy_le`) with
`c s² / 2 = s² ∑ c i² / 8`; transport to `X` by the law. The tail is Mathlib's
`HasSubgaussianMGF.measure_ge_le` rewritten (`t² / (2 · ∑ c²/4) = 2t² / ∑ c²`). Lower and
two-sided tails: the same lemma applied to `-f` and P0's `measureReal_abs_ge_le_add`; not
restated.

## 4. Consumers of the headline statements

None in the surveys (§0). The bridges feed every `HasSubgaussianMGF` and `HasSubexponentialMGF`
consumer of P1, P3 and P5a.

## 5. Files

1. `Probability/Orlicz.lean`: §3.1 (8, of which 3 constants and 3 comparison lemmas). Imports
   P1's `SubGaussian/Basic.lean`, `SubExponential/Basic.lean`. Prove; easy to medium.
2. `Probability/Entropy.lean` (P4): §3.2 (+1). Medium (the tilted variance and the integral in
   `θ`). **May be scaffolded.**
3. `Probability/BoundedDifferences.lean`: §3.3 (2); imports 2, P4's `EntropyTensorization.lean`,
   `LogSobolev.lean`. Medium given 2 (the fibre measurability and the product law are the work).
   **May be scaffolded.**
1 is independent of 2 and 3.

## 6. Material

Read: the prototype's `SubGaussian/OrliczMGF.lean` (4 declarations, `∫⁻` conditions, proxy
`9K²` in Vershynin's scale), `Concentration/Scalar/{McDiarmid,ScalarBernstein}.lean` (13),
`Concentration/Entropy/` (ledgered by P4). Reused: McDiarmid's statement shape (heterogeneous
coordinate spaces, no integrability). Not reproduced: the `∫⁻ … ENNReal.ofReal` conditions
(Bochner with integrability, D3); `mcdiarmidTail` and its zero branch (the Lean value of
`x / 0` makes the closed form true at `∑ c² = 0`); `mcdiarmid_lower_tail`; the McDiarmid MGF lemma
with a bound `M` on `|f|` (not needed); the canonical-space twin
`hasSubgaussianMGF_pi_of_coordinate_oscillation` (D2; `X = id` with `iIndepFun` of the
coordinates under `Measure.pi` is the measure form); `bernstein_sum_of_lintegral_exp_abs_le_two`
and its uniform-scale twin (`1/64`, superseded by P1's sub-exponential Bernstein and the `ψ₁`
bridge, P1 §6); `measureReal_ge_le_exp_of_cgf_le` (P1). The martingale proof of McDiarmid is not
used (§7 D1). Atlas ids: `mcdiarmid`, `subgaussian-def`, `bernstein-scalar`. Bibliography: add
`McDiarmid1989` (Surveys in Combinatorics 1989, LMS Lecture Note Ser. 141, 148–188).

## 7. Open questions

**Of the brief's §2 kind:** none.

**Decisions taken (recorded for review):**

- **D1. Bounded differences by the entropy method**, not by martingales. P4 built tensorization
  and Herbst for this (P4 §0 names P7), and they give the sharp proxy `∑ c i² / 4` with no
  Borel hypothesis. The martingale route needs Mathlib's Azuma
  (`measure_sum_ge_le_of_hasCondSubgaussianMGF`), hence `HasCondSubgaussianMGF` and
  `[StandardBorelSpace Ω]`, a conditional Hoeffding lemma, and the conditional range argument on
  the product (the Doob increment lies in an `ℱ i`-measurable interval of length `c i`), which
  is the same product-fibre work as here plus the kernel.
- **D2. Orlicz conditions as two raw constructor hypotheses** (integrability and the integral
  bound), not a new interface and not an Orlicz norm (§1): D6 makes `ψ₂`, `ψ₁` instances of the
  existing interfaces, and only the two bridges take them.
- **D3. `ψ₂` Hanson–Wright not stated** (the brief's "if cheap from P3"): it is cheap, but it
  would be a concentration theorem taking a raw `ψ₂` hypothesis, against D6 and
  `CONTRIBUTING.md` §5.4. A user composes
  `measureReal_quadForm_sub_integral_ge_le hind (fun i => hasSubgaussianMGF_of_… (hψ i))`, whose
  exponent is Vershynin's with `c = psiTwoSubgaussianConstant * K`; the bridge's docstring shows
  this line. The orchestrator may override if the read-back form is wanted.
- **D4. Scalar Bernstein in `ψ₁` form not stated**, for the same reason (bridge + P1).
- **D5. Not stated:** the converses (`HasSubgaussianMGF X c` gives `E exp (3X² / (8c)) ≤ 2`, one
  line from P1's `integral_exp_mul_sq_le` at `θ = 3 / (8c)`); McDiarmid's lower tail.
- **D6. Named constants** with upper-bound API (§3.1); McDiarmid's `2t² / ∑ c²` is the source's
  constant and is written (D5 rule 2).

Unchecked: the label of the entropy lemma in Boucheron–Lugosi–Massart (cited as the proof of
Theorem 6.2). Checked: `iIndepFun_iff_map_fun_eq_pi_map` takes `AEMeasurable` coordinates and
`[IsProbabilityMeasure μ]`, which the proof derives from `iIndepFun`.

## 8. Amendments from the review (2026-10-14)

Review: Fable, of P5b, P5c, P5d and P7 together; the orchestrator accepted every finding. The
skeletons are written under the rule that no `sorry` enters a proved file: new statements go in
new files, merged at wrap-up. None is registered in `NLAlib.lean`.

1. **§3.2 restated as Mathlib's Hoeffding** (amends §3.2 and §5 item 2). The primary statement is
   `entropy_exp_mul_le_of_mem_Icc [IsProbabilityMeasure ν] (hg : AEMeasurable g ν)
   (hab : ∀ᵐ ω ∂ν, g ω ∈ Set.Icc a b) (s : ℝ) : entropy ν (fun ω => rexp (s * g ω)) ≤
   s ^ 2 * (b - a) ^ 2 / 8 * ∫ ω, rexp (s * g ω) ∂ν`, whose docstring gives the proof through
   the steps of Mathlib's `mgf_le_of_mem_Icc_of_integral_eq_zero`
   (`exists_cgf_eq_iteratedDeriv_two_cgf_mul`, `variance_tilted_mul`,
   `variance_le_sq_of_bounded`). The pointwise-oscillation form
   `entropy_exp_mul_le_of_abs_sub_le` (the §3.2 statement, unchanged) is its corollary with
   `a = sInf (Set.range g)`, `b = a + c`. Both are in a new skeleton file
   `Probability/EntropyExpBounded.lean` (2), to be merged into the proved `Entropy.lean` at
   wrap-up.
2. **§3.3**: the sentence "the zero measure makes both statements trivial" is deleted:
   `iIndepFun` gives a probability measure (`ProbabilityTheory.iIndepFun.isProbabilityMeasure`),
   which the module docstring of `BoundedDifferences.lean` says.
3. **Centring** (amends §3.1). The bridges need `E X = 0`; two corollaries are added for a
   variable that is not centred, citing the centring lemma [Vershynin2018, Lemma 2.6.8]:
   `hasSubgaussianMGF_sub_integral_of_integral_exp_sq_div_le_two` (proxy
   `psiTwoSubgaussianConstant * (4 * K)`: `X - E X` has the `ψ₂` condition at `4K`, since
   `(EX)² ≤ K log 2` and `E exp (X² / (2K)) ≤ √2`) and
   `hasSubexponentialMGF_sub_integral_of_integral_exp_abs_div_le_two` (proxies
   `psiOneSubexponentialVarianceConstant * (2 * K) ^ 2`, `psiOneSubexponentialScaleConstant *
   (2 * K)`: the `ψ₁` condition at `2K`). The bridges' docstrings point to them.
   `Orlicz.lean` has 10 declarations, not 8.
4. **Constants and labels.** The docstrings record what the proofs reach: `1 + log 2` for
   `psiTwoSubgaussianConstant` (body `2`), `32 / e²` and `2` for the `ψ₁` constants (bodies `5`
   and `2`). Labels kept: [BoucheronLugosiMassart2013, Theorem 6.2], [Vershynin2018,
   Proposition 2.5.2], [Vershynin2018, Proposition 2.7.1]. McDiarmid 1989's numbering is
   unverified (the reviewer reads the inequality as Lemma (1.2) there), so both bounded
   differences statements cite `[McDiarmid1989]` without a label (the §3.3 "Lemma 3.3" and
   "Theorem 3.1" are withdrawn). `McDiarmid1989` is added to `docs/references.bib`.
5. **Entropy method** for McDiarmid confirmed (§7 D1 stands).
6. **Files** (amends §5). Skeletons written, each compiling with only `sorry` warnings:
   `Probability/Orlicz.lean` (10: 3 constants, 3 comparison lemmas, 2 bridges, 2 centred forms),
   `Probability/EntropyExpBounded.lean` (2), `Probability/BoundedDifferences.lean` (2; imports
   `EntropyExpBounded.lean` and `EntropyTensorization.lean`; `LogSobolev.lean` is not needed,
   Herbst's argument being in `Entropy.lean`). No statement needed an elaboration fix.
7. **Result ids**: `subgaussian-def` (the `ψ₂` bridge), `subexponential-def` (new, the `ψ₁`
   bridge), `bounded-differences` (new) and `mcdiarmid`.
