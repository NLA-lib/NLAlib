# Design note: Probability stage P1, scalar MGF bounds

Status: written 2026-10-14 by the orchestrator under `docs/PORT_PROBABILITY.md` (§2 decided). It
introduces the sub-exponential interface D6 fixed; no new question of the brief's §2 kind.
Reviewed by a Fable agent on 2026-10-14; its corrections are folded in (weighted sub-exponential
sums, the structure's basic API, `⨆` and two-sided union bounds, names, file order, proof
hazards in §3.3, requirements on P5 in §7).

## 0. Scope and consumers

Real random variables with a bound on their moment generating function: Mathlib's
`HasSubgaussianMGF` with the API Mathlib lacks, the new `HasSubexponentialMGF` with Bernstein's
inequality for sums, and the one instance of the second that the round needs beyond sub-Gaussian
variables, the centred square of a sub-Gaussian variable.

| Item | Consumers |
|---|---|
| `HasSubgaussianMGF.mono`, `.integral_eq_zero`, `.integral_sq_le` | every instance proof in P2 (Gaussian, Rademacher), P3 (vectors), P4 (concentration of functions concludes a proxy that is then compared) |
| two-sided and lower tails | P3, R3, Sketching (all two-sided statements) |
| weighted sums `∑ a i * X i` | P3 (linear forms of a vector with independent coordinates), P5 (matrix series coefficients), Sketching (`SRHTFlattening`: Rademacher sums) |
| maxima: tail by the union bound, mean | R3 (the net argument for sub-Gaussian rows), Chevet |
| absolute moments | P3 (`m₄` of a sub-Gaussian coordinate), Khintchine |
| `E exp (θ X²)` | P3 (`χ²`-type tails of a sub-Gaussian vector), this stage's centred square |
| `HasSubexponentialMGF`, Bernstein for sums | P3 (Hanson–Wright's diagonal part, the two-sided `‖X‖²` tail) |
| centred square of a sub-Gaussian variable | P3 (the same) |

Not here, by decision (§7): the classical Bernstein inequality for bounded variables,
`exp (-t ^ 2 / (2 * (σ² + L t / 3)))`, which is the `1 × 1` case of matrix Bernstein (P5) and is
stated there as its scalar corollary rather than proved twice; Orlicz-norm bridges (`ψ₂`, `ψ₁`),
which no survey consumer uses, go to P7 with McDiarmid; Hoeffding's lemma and inequality are
Mathlib's (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`,
`HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| sub-Gaussian MGF, proxy `c : ℝ≥0` | Mathlib's `HasSubgaussianMGF X c μ` | — |
| sub-exponential MGF, `v b : ℝ≥0` | `HasSubexponentialMGF X v b μ`, new (§2) | `hasSubexponentialMGF_zero_iff_hasSubgaussianMGF`: `b = 0` is `HasSubgaussianMGF X v μ` |
| scale of a coefficient | `‖a‖₊ ^ 2 * c` for the proxy of `a * X` (no `⟨a ^ 2, _⟩`, D2) | Mathlib's `const_mul` uses `⟨r ^ 2, sq_nonneg r⟩ * c`; `HasSubgaussianMGF.const_mul'` restates it in this form |
| constants of the centred square | `centeredSqVarianceConstant`, `centeredSqScaleConstant : ℝ≥0`, `irreducible_def` (D5 rule 2) | — |

## 2. Interfaces

**`HasSubexponentialMGF X v b μ`** (D6). For `X : Ω → ℝ`, `v b : ℝ≥0`:

```lean
/-- `X` has a sub-exponential moment generating function with variance proxy `v` and scale `b`:
for every `l` with `b * |l| < 1`, `exp (l * X)` is integrable and `mgf X μ l ≤ exp (v * l ^ 2 / 2)`.
With `b = 0` the window is all of `ℝ` and this is `HasSubgaussianMGF X v μ`. -/
structure HasSubexponentialMGF (X : Ω → ℝ) (v b : ℝ≥0) (μ : Measure Ω) : Prop where
  integrable_exp_mul : ∀ l : ℝ, b * |l| < 1 → Integrable (fun ω => rexp (l * X ω)) μ
  mgf_le : ∀ l : ℝ, b * |l| < 1 → mgf X μ l ≤ rexp (v * l ^ 2 / 2)
```

- Fields mirror Mathlib's `HasSubgaussianMGF` (integrability, then the MGF bound), restricted to
  the open window `b * |l| < 1`. The open window is the one in the literature (Wainwright 2019,
  Definition 2.7: `|λ| < 1 / α`), and with it the sub-Gaussian case is exactly `b = 0`.
- Like `HasSubgaussianMGF`, it implies mean zero under a probability measure
  (`HasSubexponentialMGF.integral_eq_zero`) and `μ univ ≤ 1`.
- Raw-condition constructors: from `HasSubgaussianMGF` (`b = 0`), and the centred square of a
  sub-Gaussian variable (§3.4). A bounded centred variable is sub-Gaussian by Hoeffding's lemma.
- No kernel or conditional form: the conditional consumer (Freedman) is matrix-valued and has its
  own interface in P5.

No other interface is introduced. Concentration of a function concludes `HasSubgaussianMGF`
of the centred function (D6); nothing here changes that.

## 3. Statement shapes

`namespace NLAlib`; lemmas about `HasSubgaussianMGF` are `_root_.ProbabilityTheory.HasSubgaussianMGF.foo`.
Variables `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}`. Exponents
are written as Mathlib writes them (`-t ^ 2 / (2 * c)`).

### 3.1 `Probability/SubGaussian/Basic.lean`

```lean
theorem HasSubgaussianMGF.mono (h : HasSubgaussianMGF X c μ) {d : ℝ≥0} (hcd : c ≤ d) :
    HasSubgaussianMGF X d μ
/-- `const_mul` with the proxy `‖r‖₊ ^ 2 * c`. -/
theorem HasSubgaussianMGF.const_mul' (h : HasSubgaussianMGF X c μ) (r : ℝ) :
    HasSubgaussianMGF (fun ω => r * X ω) (‖r‖₊ ^ 2 * c) μ
theorem HasSubgaussianMGF.integral_eq_zero [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ∂μ = 0
/-- The second moment is at most the proxy. -/
theorem HasSubgaussianMGF.integral_sq_le [IsProbabilityMeasure μ] (h : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ^ 2 ∂μ ≤ c
theorem HasSubgaussianMGF.measure_le_le (h : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | X ω ≤ -t} ≤ rexp (-t ^ 2 / (2 * c))
theorem HasSubgaussianMGF.measure_abs_ge_le (h : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * rexp (-t ^ 2 / (2 * c))
/-- Independent sub-Gaussian variables with coefficients. -/
theorem HasSubgaussianMGF.sum_const_mul_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0} {s : Finset ι} (h : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) (a : ι → ℝ) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ s, a i * X i ω) (∑ i ∈ s, ‖a i‖₊ ^ 2 * c i) μ
/-- The union bound for the maximum of sub-Gaussian variables; no independence. -/
theorem HasSubgaussianMGF.measure_exists_ge_le {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    (h : ∀ i, HasSubgaussianMGF (X i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, t ≤ X i ω} ≤ Fintype.card ι * rexp (-t ^ 2 / (2 * c))
theorem HasSubgaussianMGF.measure_iSup_ge_le [Fintype ι] [Nonempty ι] … :
    μ.real {ω | t ≤ ⨆ i, X i ω} ≤ Fintype.card ι * rexp (-t ^ 2 / (2 * c))
theorem HasSubgaussianMGF.measure_exists_abs_ge_le [Fintype ι] … :
    μ.real {ω | ∃ i, t ≤ |X i ω|} ≤ 2 * Fintype.card ι * rexp (-t ^ 2 / (2 * c))
```

The `∃` form is primary (true for empty `ι`); the `⨆` form is the event R3's net argument
produces and needs `Nonempty ι` for the finite supremum to be attained.

`measure_exists_ge_le` takes one proxy for all `i` (the consumers' case); a family of proxies
would put `∑ i, exp (…)` on the right, which the union bound gives directly. Degenerate cases:
`c = 0` gives `-t ^ 2 / 0 = 0` in Lean, so the tails read `≤ 1` and `≤ 2`, true and weak; the
variable is `0` a.e. then (Mathlib's `ae_eq_zero_of_hasSubgaussianMGF_zero`). `ι` empty: both
sides `0`. Mean and second moment need a probability measure: with `μ univ < 1` the MGF bound
does not force the mean to vanish.

### 3.2 `Probability/SubGaussian/Moments.lean`

```lean
/-- Absolute moments: `E |X| ^ p ≤ p (2c)^{p/2} Γ(p/2)`, the integral of the two-sided tail. -/
theorem HasSubgaussianMGF.integral_abs_rpow_le (h : HasSubgaussianMGF X c μ) {p : ℝ} (hp : 0 < p) :
    ∫ ω, |X ω| ^ p ∂μ ≤ p * (2 * c) ^ (p / 2) * Real.Gamma (p / 2)
theorem HasSubgaussianMGF.integrable_iSup {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}
    (h : ∀ i, HasSubgaussianMGF (X i) c μ) : Integrable (fun ω => ⨆ i, X i ω) μ
/-- **Maximal inequality**: `E max_i X_i ≤ √(2 c log N)`; no independence. -/
theorem HasSubgaussianMGF.integral_iSup_le [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, X i ω ∂μ ≤ √(2 * c * Real.log (Fintype.card ι))
theorem HasSubgaussianMGF.integrable_iSup_abs …  : Integrable (fun ω => ⨆ i, |X i ω|) μ
theorem HasSubgaussianMGF.integral_iSup_abs_le [IsProbabilityMeasure μ] … :
    ∫ ω, ⨆ i, |X i ω| ∂μ ≤ √(2 * c * Real.log (2 * Fintype.card ι))
```

Integrability of `|X| ^ p` is Mathlib's `HasSubgaussianMGF.memLp` (every finite `p`), so the
moment bound has its companion already (D3). The moment formula is an exact integral of the tail
bound, not a lossy constant, so it is written out (D5 rule 2 is about constants a better proof
would change; this one changes only with the tail). Maxima: the source's constants
(Boucheron–Lugosi–Massart 2013, Theorem 2.5). No `Nonempty ι`: over an empty type `⨆` is `0`
and so are `log 0` and `√0`, so both bounds hold there as written.

### 3.3 `Probability/SubExponential/{Basic,Tail}.lean`

```lean
structure HasSubexponentialMGF (X : Ω → ℝ) (v b : ℝ≥0) (μ : Measure Ω) : Prop  -- §2
namespace HasSubexponentialMGF
theorem aemeasurable (h : HasSubexponentialMGF X v b μ) : AEMeasurable X μ
theorem measure_univ_le_one (h) : μ Set.univ ≤ 1
theorem isFiniteMeasure (h) : IsFiniteMeasure μ
theorem memLp (h) (p : ℝ≥0) : MemLp X p μ      -- `0` is interior to `integrableExpSet`
theorem integrable (h) : Integrable X μ
theorem cgf_le (h) {l : ℝ} (hl : b * |l| < 1) : cgf X μ l ≤ v * l ^ 2 / 2
theorem congr {Y : Ω → ℝ} (h) (hXY : X =ᵐ[μ] Y) : HasSubexponentialMGF Y v b μ
theorem mono (h : HasSubexponentialMGF X v b μ) {v' b' : ℝ≥0} (hv : v ≤ v') (hb : b ≤ b') :
    HasSubexponentialMGF X v' b' μ
theorem neg (h : HasSubexponentialMGF X v b μ) : HasSubexponentialMGF (fun ω => -X ω) v b μ
theorem const_mul (h : HasSubexponentialMGF X v b μ) (r : ℝ) :
    HasSubexponentialMGF (fun ω => r * X ω) (‖r‖₊ ^ 2 * v) (‖r‖₊ * b) μ
theorem add_of_indepFun {Y : Ω → ℝ} {v' b' : ℝ≥0} (hX : HasSubexponentialMGF X v b μ)
    (hY : HasSubexponentialMGF Y v' b' μ) (hXY : IndepFun X Y μ) :
    HasSubexponentialMGF (fun ω => X ω + Y ω) (v + v') (max b b') μ
theorem sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {v b : ι → ℝ≥0} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ) :
    HasSubexponentialMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) (s.sup b) μ
/-- Weighted sums: Hanson–Wright's diagonal `∑ A i i (X i² - E X i²)` is one. -/
theorem sum_const_mul_of_iIndepFun … (a : ι → ℝ) :
    HasSubexponentialMGF (fun ω => ∑ i ∈ s, a i * X i ω) (∑ i ∈ s, ‖a i‖₊ ^ 2 * v i)
      (s.sup fun i => ‖a i‖₊ * b i) μ
theorem integral_eq_zero [IsProbabilityMeasure μ] (h : HasSubexponentialMGF X v b μ) :
    ∫ ω, X ω ∂μ = 0
/-- **Sub-exponential tail** (Wainwright 2019, Proposition 2.9):
`P(t ≤ X) ≤ exp (-min (t²/(2v)) (t/(2b)))`. With `b = 0` or `v = 0` Lean's division by zero makes
the bound `1`; the regime forms below are the usable statements then. -/
theorem measure_ge_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b)))
/-- The sub-Gaussian regime `b t ≤ v`. -/
theorem measure_ge_le_of_mul_le (h : HasSubexponentialMGF X v b μ) {t : ℝ} (ht : 0 ≤ t)
    (hbt : b * t ≤ v) : μ.real {ω | t ≤ X ω} ≤ rexp (-t ^ 2 / (2 * v))
/-- The exponential regime `v ≤ b t`. -/
theorem measure_ge_le_of_le_mul (h : HasSubexponentialMGF X v b μ) {t : ℝ}
    (hbt : v ≤ b * t) : μ.real {ω | t ≤ X ω} ≤ rexp (-t / (2 * b))
theorem measure_le_le … : μ.real {ω | X ω ≤ -t} ≤ rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b)))
theorem measure_abs_ge_le … : μ.real {ω | t ≤ |X ω|} ≤ 2 * rexp (-min (t ^ 2 / (2 * v)) (t / (2 * b)))
/-- **Bernstein's inequality** for independent sub-exponential variables. -/
theorem measure_sum_ge_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {v b : ι → ℝ≥0} {s : Finset ι} (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (v i) (b i) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
      rexp (-min (t ^ 2 / (2 * ∑ i ∈ s, v i)) (t / (2 * s.sup b)))
end HasSubexponentialMGF
theorem _root_.ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF
    (h : HasSubgaussianMGF X c μ) : HasSubexponentialMGF X c 0 μ
theorem hasSubexponentialMGF_zero_iff_hasSubgaussianMGF {v : ℝ≥0} :
    HasSubexponentialMGF X v 0 μ ↔ HasSubgaussianMGF X v μ
```

Bound forms (D5): the `min` form is the source's and dominates the combined form
`exp (-t ^ 2 / (2 * (v + b * t)))` in every regime (`min (t²/2v) (t/2b) ≥ t²/(2(v + bt))`), so the
combined form is not stated; the two regime forms are corollaries a consumer can use without the
`min`, and they are the ones that survive `b = 0` and `v = 0`. Names follow Mathlib's
(`measure_ge_le`, `measure_sum_ge_le_of_iIndepFun`), with "Bernstein" in the docstring. The
combined form is the only one junk-free at both `b = 0` and `v = 0` and is the classical
Bernstein shape; it is added as a corollary only if a consumer asks (D5 rule 6).

Proof hazards (the statements are true as written): in `measure_ge_le` and its regime forms the
optimising `l` is `1 / b` at the boundary, outside the open window, so the proof takes the
infimum over `l < 1 / b` by continuity, not one evaluation; in `add_of_indepFun`, integrability of
the product must come from `IndepFun.integrable_exp_mul_add`, not from `memLp_exp_mul _ 2`
(which needs `2 l` in the window).

### 3.4 `Probability/SubGaussian/Square.lean`

```lean
theorem HasSubgaussianMGF.integrable_exp_mul_sq (h : HasSubgaussianMGF X c μ) {θ : ℝ}
    (hθ : 2 * θ * c < 1) : Integrable (fun ω => rexp (θ * X ω ^ 2)) μ
/-- `E exp (θ X²) ≤ (1 - 2θc)^{-1/2}` for `0 ≤ θ < 1 / (2c)`, by Gaussian linearisation: the
value for a centred Gaussian of variance `c`. -/
theorem HasSubgaussianMGF.integral_exp_mul_sq_le (h : HasSubgaussianMGF X c μ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : 2 * θ * c < 1) : ∫ ω, rexp (θ * X ω ^ 2) ∂μ ≤ 1 / √(1 - 2 * θ * c)

irreducible_def centeredSqVarianceConstant : ℝ≥0 := …   -- the value the proof reaches
irreducible_def centeredSqScaleConstant : ℝ≥0 := …
theorem centeredSqVarianceConstant_pos : 0 < centeredSqVarianceConstant
theorem centeredSqScaleConstant_pos : 0 < centeredSqScaleConstant
theorem centeredSqVarianceConstant_le : centeredSqVarianceConstant ≤ …  -- the proved value
theorem centeredSqScaleConstant_le : centeredSqScaleConstant ≤ …
/-- The centred square of a sub-Gaussian variable is sub-exponential. -/
theorem HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) :
    HasSubexponentialMGF (fun ω => X ω ^ 2 - ∫ ω', X ω' ^ 2 ∂μ)
      (centeredSqVarianceConstant * c ^ 2) (centeredSqScaleConstant * c) μ
```

The `θ < 0` side of `integrable_exp_mul_sq` needs no hypothesis but is covered by `hθ` as
written (`2 θ c < 1` holds for `θ ≤ 0`). Constants (D5 rule 2): the literature has
`(v, b) = (32 c², 4 c)` (Honorio–Jaakkola 2014, from memory, locator to be checked) and the
prototype reached `(4 e³ c², 2 e c)`; the proof agent aims for the source's and records what it
reaches in the docstring and the `_le` lemma. Consumers use only `_pos`, `_le` and `mono`.

## 4. Consumers of the headline statements

`sum_const_mul_of_iIndepFun`: P3's sub-Gaussian vector with independent coordinates, P5's series,
Sketching's Rademacher sums. `measure_exists_ge_le`, `integral_iSup_le`: R3. `integral_abs_rpow_le`:
P3, Khintchine (P5). `integral_exp_mul_sq_le`: P3 (`χ²`-type tails for sub-Gaussian vectors use the
vector form, proved there by the same linearisation). `measure_sum_ge_le_of_iIndepFun` and
`hasSubexponentialMGF_sq_sub_integral`: P3 (Hanson–Wright's diagonal, `‖X‖²` two-sided tails).

## 5. Files

In build order; 1 and 3 are independent, 2 imports 1, 4 imports 1 and 3.

1. `NLAlib/Probability/SubGaussian/Basic.lean`: §3.1 (10 statements).
2. `NLAlib/Probability/SubGaussian/Moments.lean`: §3.2 (5 statements). `integral_abs_rpow_le`
   needs no probability measure, so its proof uses Mathlib's layer cake
   (`Integrable.integral_eq_integral_meas_le`), not P0's `integral_le_of_measureReal_ge_le`, which
   assumes one.
3. `NLAlib/Probability/SubExponential/Basic.lean` (the structure, its API, sums and the
   sub-Gaussian case; 16 statements) and `NLAlib/Probability/SubExponential/Tail.lean` (the tails
   and Bernstein; 6 statements), split at the skeleton because §3.3 is over the file budget.
4. `NLAlib/Probability/SubGaussian/Square.lean`: §3.4 (9 statements); imports 1 and 3.

## 6. Material

Read: the prototype's `Probability/SubGaussian/{EvenMoments,Moments,CenteredSquare,ExpSquare,
OrliczMGF}.lean` and `Probability/Concentration/Scalar/ScalarBernstein.lean`. Reused as proof
material: the mean-zero and second-moment arguments (`EvenMoments`), the layer-cake moment and the
maximal inequality (`Moments`), the centred-square CGF bound (`CenteredSquare`), the `exp (θX²)`
series (`ExpSquare`; replaced by Gaussian linearisation if shorter), the local-CGF tail
(`ScalarBernstein.measureReal_ge_le_exp_of_cgf_le`, which becomes `HasSubexponentialMGF.measure_ge_le`).

Not reproduced: the `_of_le` variants with a real slack `C₀ ≥ c` (17 statements; `mono` replaces
them); the four successive forms of `E exp (θX²)` (one sharp statement); the per-law corollaries
(`hasSubgaussianMGF_sum_mul_rademacher` and its moments: a Rademacher vector is an instance in
P2); the even-Taylor-term lemmas and `integral_cosh_mul_le` (proof leaves); the ψ₁ Bernstein with
constant `1/64` (superseded by the sub-exponential form; the ψ₁ bridge goes to P7);
`bernsteinTail`, `chernoffUpperTail`, `gaussianSeriesTail` (P5 defines its tails).

## 7. Open questions (orchestrator decisions, recorded for review)

**Q1. Classical scalar Bernstein in P5.** For bounded centred variables with variance `σ²`, the
tail `exp (-t² / (2 (σ² + L t / 3)))` is matrix Bernstein for `1 × 1` Hermitian matrices, and P5
proves matrix Bernstein for every dimension from the Matrix layer's
`exp_smul_le_one_add_smul_add_smul_sq`. Stating the scalar form as that corollary proves it once
(the survey found the prototype's scalar Bernstein unrelated to its matrix one). Cost: a scalar
user waits for P5. Alternative: a scalar proof here and the matrix proof separately.
Requirement on P5 (from the review): the one-sided tail with constant `1` is the `d = 1` case of
the `eigenvalue _ 0` (largest eigenvalue) form, so P5 states that form as primary (the `specNorm`
form carries a `2`), and the scalar corollary is restated in scalar terms, with no
`Matrix Unit Unit ℝ` in its statement; the bridge `eigenvalue (of fun _ _ => x) 0 = x` lives in
P5.

**Q2. The `min` form with the regime corollaries** (§3.3), not a tail function behind a
definition: the exponent is the source's and two lines long; D5 rule 2's definitions are for
constants and tails that a better proof would change, and this one is optimal for the interface.

**Q3. One sub-exponential parametrisation `(v, b)` with an open window**, not Vershynin's
`‖X‖_ψ₁` nor the Bernstein moment condition: those are constructors (P7), and every proof
consumes the MGF. Known cost, not a defect: the sub-gamma shape `cgf ≤ v l² / (2 (1 - b l))`,
which bounded variables and the Bernstein moment condition produce natively and which P5's
`HasMatrixMGFBound` carries, converts to `(v, b)` at the price of a constant (`(2v, 2b)`), so a
`1 × 1` bridge from P5 to this interface and the P7 constructors do not reach the source's
constants.
