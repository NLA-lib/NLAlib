# Design note: Probability stage P5d, matrix conditional expectations and matrix Freedman

Status: drafted 2026-10-14 by an Opus agent from the orchestrator's brief; not yet reviewed.
Last part of P5: matrix conditional expectations (deferred by P0 §7 Q3), the conditional form
of P5a's interface (`HasCondMatrixMGFBound`, D6), conditional Lieb, the trace supermartingale and
Freedman's inequality (Tropp 2011). One question touches D6 (§7 Q1); the rest is decided.

## 0. Scope and consumers

No consumer in either survey (inventory §5). Kept under D9 as the martingale matrix Bernstein a
user expects (adaptive sampling, streaming). D9 cut `HasLocalMatrixSecondMoment`; the
square-integrable form replaces it (§7 D1).

| Item | Consumers |
|---|---|
| matrix conditional expectations | Freedman; R2/R4 if they condition through `condExp` (P0 §7 Q3) |
| `HasCondMatrixMGFBound`, supermartingale, Freedman | none in the surveys; later martingale tails |

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| conditional expectation of a random matrix | Mathlib's `μ[X | m]` under `open scoped Matrix.Norms.L2Operator` (D10 as amended) | Mathlib's `condExp`; entrywise by §3.1 |
| filtration, increments | `ℱ : Filtration ℕ mΩ`, `X : ℕ → Ω → Matrix n n 𝕜` with `X j` `ℱ (j + 1)`-measurable; partial sums `∑ j ∈ Finset.range k, X j ω` (so `Y 0 = 0`) | Mathlib's `Filtration`, `Supermartingale` |
| predictable quadratic variation | `∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω`, written out | Mathlib's `condExp` |
| Loewner monotonicity of `condExp` | Mathlib's `condExp_mono` (instances as for `integral_mono_ae`, P0) | no NLAlib statement |

Index convention: Mathlib's Azuma conditions `Y (i + 1)` on `ℱ i` and treats `Y 0` apart; here
`X j = Y (j + 1)`, `Y 0 = 0` (Tropp's), so there is no special first term.

## 2. Interfaces

```lean
/-- `X` is a.s. Hermitian and, conditionally on `m`, its matrix moment generating function is
bounded by `exp (g θ • A)` for every `θ ∈ s`, with `A` an `m`-measurable, a.s. Hermitian random
matrix. The conditional form of `HasMatrixMGFBound`. -/
structure HasCondMatrixMGFBound (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (X : Ω → Matrix n n 𝕜)
    (g : ℝ → ℝ) (A : Ω → Matrix n n 𝕜) (s : Set ℝ) (μ : Measure Ω) : Prop where
  ae_isHermitian : ∀ᵐ ω ∂μ, (X ω).IsHermitian
  stronglyMeasurable_bound : StronglyMeasurable[m] A
  ae_isHermitian_bound : ∀ᵐ ω ∂μ, (A ω).IsHermitian
  integrable_exp : ∀ θ ∈ s, Integrable (fun ω => exp (θ • X ω)) μ
  condExp_exp_le : ∀ θ ∈ s, μ[fun ω => exp (θ • X ω) | m] ≤ᵐ[μ] fun ω => exp (g θ • A ω)
```

- Spelled with `μ[· | m]`, not `condExpKernel` as Mathlib's `HasCondSubgaussianMGF` (§7 Q1);
  `∀ θ` outside the `ᵐ` (the supermartingale uses one `θ`). `hm` explicit, as Mathlib's: without
  it `μ[· | m] = 0` and the bound would be vacuous.
- Constructors (§3.3): conditional Bernstein (the Freedman input) and the bridge from Mathlib's
  `HasCondSubgaussianMGF` (CONTRIBUTING §1.3). API: `congr`, `mono_set`. Deviation entry in
  `Mathlib-deviations.md` with the structure.

## 3. Statement shapes

`namespace NLAlib`, `open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder`;
`{Ω} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}`, `{𝕜} [RCLike 𝕜] {n} [Fintype n]
[DecidableEq n]`; `[IsProbabilityMeasure μ]` in §3.3–§3.4.

Degenerate cases: *empty `n`:* at `k = 0` the Freedman event is `{t ≤ 0 ∧ 0 ≤ v}`, everything for
`t = 0 ≤ v`, while `card n · … = 0`: `[Nonempty n]`. *`t`:* `0 ≤ t` (at `t = 0` the bound is
`card n ≥ 1`). *`v`:* no hypothesis: `v < 0` makes the event empty; `v = 0` is handled by
`θ = 3/(2L)` (P5a's `exists_bernstein_exponent`, made public). *`L`:* `0 < L` (P5a; centred and
`≤ 0` forces `X j = 0`). *`m` not a sub-σ-algebra:* excluded by `hm` / `ℱ.le j`.
*Integrability:* `MemLp (X j) 2 μ` (§7 D1); the potential's integrability is derived in Freedman.

### 3.1 `Probability/MatrixConditionalExpectation.lean` (the sibling of P0's `MatrixIntegral.lean`)

```lean
theorem _root_.Matrix.condExp_apply {X : Ω → Matrix l n 𝕜} (hX : Integrable X μ) (i : l) (j : n) :
    (fun ω => μ[X | m] ω i j) =ᵐ[μ] μ[fun ω => X ω i j | m]
theorem _root_.Matrix.condExp_conjTranspose (X : Ω → Matrix l n 𝕜) :
    μ[fun ω => (X ω)ᴴ | m] =ᵐ[μ] fun ω => (μ[X | m] ω)ᴴ
theorem _root_.Matrix.condExp_trace {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ) :
    (fun ω => (μ[X | m] ω).trace) =ᵐ[μ] μ[fun ω => (X ω).trace | m]
theorem _root_.Matrix.ae_isHermitian_condExp (h : ∀ᵐ ω ∂μ, (X ω).IsHermitian) :
    ∀ᵐ ω ∂μ, (μ[X | m] ω).IsHermitian
theorem _root_.Matrix.ae_posSemidef_condExp (h : ∀ᵐ ω ∂μ, (X ω).PosSemidef) :
    ∀ᵐ ω ∂μ, (μ[X | m] ω).PosSemidef
/-- Proof: `μ[X | m] ≥ μ[f | m] • 1` for `f = min (λ_min X) 1 > 0`, and `μ[f | m] > 0` a.s. -/
theorem _root_.Matrix.ae_posDef_condExp (hm : m ≤ mΩ) [IsFiniteMeasure μ] (hX : Integrable X μ)
    (h : ∀ᵐ ω ∂μ, (X ω).PosDef) : ∀ᵐ ω ∂μ, (μ[X | m] ω).PosDef
```

Plus `condExp_dilation` and `condExp_dilation_sq` (the conditional forms of P5a's
`integral_dilation`, `integral_dilation_sq`) for the rectangular Freedman. The first three are
`ContinuousLinearMap.comp_condExp_comm`; conjugate transpose, Hermitian and PSD need no
integrability (as P0's integral versions); PSD is Mathlib's `condExp_nonneg`. PD removes the
prototype's hypothesis `(μ[exp X | m] ω).PosDef` from conditional Lieb.

### 3.2 `ForMathlib` (upstream candidates, no NLAlib vocabulary)

```lean
/-- Conditional Jensen on a convex set that need not be closed (Mathlib's needs it closed). -/
theorem ConcaveOn.condExp_map_le_of_condExp_mem (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set E} {φ : E → ℝ} {f : Ω → E} (hφ : ConcaveOn ℝ s φ) (hφc : ContinuousOn φ s)
    (hfs : ∀ᵐ ω ∂μ, f ω ∈ s) (hf : Integrable f μ) (hφf : Integrable (fun ω => φ (f ω)) μ)
    (hmean : ∀ᵐ ω ∂μ, μ[f | m] ω ∈ s) :
    μ[fun ω => φ (f ω) | m] ≤ᵐ[μ] fun ω => φ (μ[f | m] ω)
/-- **Ville's maximal inequality** for a nonnegative supermartingale. -/
theorem MeasureTheory.Supermartingale.measure_exists_ge_le [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hf : Supermartingale f ℱ μ)
    (hf0 : ∀ k, 0 ≤ᵐ[μ] f k) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | ∃ k, c ≤ f k ω} ≤ (∫ ω, f 0 ω ∂μ) / c
```

Searched: Mathlib has the closed conditional Jensen and Doob's finite-horizon `maximal_ineq` for
submartingales, no Ville. Ville: optional stopping at the first crossing, then `k → ∞`.

### 3.3 `Probability/MatrixConcentration/ConditionalMGFBound.lean`

```lean
structure HasCondMatrixMGFBound …       -- §2, with `congr` and `mono_set` as P5a's
/-- **Conditional Lieb inequality**: for `H` `m`-measurable,
`E[tr exp (H + X) | m] ≤ tr exp (H + log E[exp X | m])` a.s. [Tropp2011, proof of
Theorem 1.1]; Lieb's concavity theorem with conditional Jensen. -/
theorem condExp_re_trace_exp_add_le (hm : m ≤ mΩ) {H X : Ω → Matrix n n 𝕜}
    (hHm : StronglyMeasurable[m] H) (hH : ∀ᵐ ω ∂μ, (H ω).IsHermitian)
    (hX : ∀ᵐ ω ∂μ, (X ω).IsHermitian) (hint : Integrable (fun ω => exp (X ω)) μ) :
    μ[fun ω => RCLike.re (exp (H ω + X ω)).trace | m] ≤ᵐ[μ]
      fun ω => RCLike.re (exp (H ω + cfc Real.log (μ[fun ω => exp (X ω) | m] ω))).trace
/-- The conditional Bernstein bound, the input of Freedman's inequality. -/
theorem hasCondMatrixMGFBound_of_condExp_eq_zero_of_le (hm : m ≤ mΩ) {X : Ω → Matrix n n 𝕜}
    {L : ℝ} (hL : 0 < L) (hX2 : MemLp X 2 μ) (hmean : μ[X | m] =ᵐ[μ] 0)
    (hle : ∀ᵐ ω ∂μ, X ω ≤ L • (1 : Matrix n n 𝕜)) :
    HasCondMatrixMGFBound m hm X (fun θ => θ ^ 2 / 2 / (1 - L * θ / 3))
      (μ[fun ω => X ω ^ 2 | m]) (Set.Ioo 0 (3 / L)) μ
/-- The bridge from Mathlib's conditionally sub-Gaussian scalars. -/
theorem hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF [StandardBorelSpace Ω]
    {γ : Ω → ℝ} {c : ℝ≥0} (hγ : HasCondSubgaussianMGF m hm γ c μ) {B : Matrix n n 𝕜}
    (hB : B.IsHermitian) :
    HasCondMatrixMGFBound m hm (fun ω => γ ω • B) (fun θ => θ ^ 2 / 2)
      (fun _ => (c : ℝ) • B ^ 2) Set.univ μ
```

Conditional Lieb needs no integrability of `tr exp (H + X)` (else the left side is `0`). Proof:
for constant `H`, §3.2 with Lieb's concave map on the PD cone (`concaveOn_re_trace_exp_add_cfc_log`)
and §3.1's PD statement; for `m`-measurable `H`, countably-valued `m`-measurable `Hₖ → H`
uniformly, localisation on the pieces, and the domination `re_trace_exp_le_exp_specNorm_sub_mul`.
Difficulty high. Conditional Bernstein: P5a's pointwise `exp (θX) ≤ 1 + θX + g θ X²`,
`condExp_mono`, centring, `1 + A ≤ exp A`.

### 3.4 `Probability/MatrixConcentration/Freedman.lean`

```lean
/-- The trace potential `tr exp (θ Yₖ - g θ Wₖ)`, `Wₖ = ∑_{j<k} A j`, is a supermartingale. -/
theorem HasCondMatrixMGFBound.supermartingale_re_trace_exp {ℱ : Filtration ℕ mΩ}
    {X A : ℕ → Ω → Matrix n n 𝕜} (hX : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j))
    (h : ∀ j, HasCondMatrixMGFBound (ℱ j) (ℱ.le j) (X j) g (A j) s μ) {θ : ℝ} (hθ : θ ∈ s)
    (hint : ∀ k, Integrable (fun ω => RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω -
      g θ • ∑ j ∈ Finset.range k, A j ω)).trace) μ) :
    Supermartingale (fun k ω => RCLike.re (exp (θ • ∑ j ∈ Finset.range k, X j ω -
      g θ • ∑ j ∈ Finset.range k, A j ω)).trace) ℱ μ
/-- **The martingale master tail.** -/
theorem HasCondMatrixMGFBound.measure_exists_eigenvalue_zero_sum_ge_le [Nonempty n] (hX …)
    (h …) {θ : ℝ} (hθs : θ ∈ s) (hθ : 0 < θ) (hg : 0 ≤ g θ) (hint …) (t w : ℝ) :
    μ.real {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
        ∑ j ∈ Finset.range k, A j ω ≤ w • (1 : Matrix n n 𝕜)} ≤
      Fintype.card n * rexp (-θ * t + g θ * w)
/-- **Freedman's inequality for matrix martingales.** [Tropp2011, Theorem 1.1]; over `𝕜`, any
finite index type, square-integrable increments.
Result: matrix-freedman -/
theorem measureReal_exists_eigenvalue_zero_sum_ge_le_freedman [Nonempty n]
    {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → Matrix n n 𝕜}
    (hX : ∀ j, StronglyMeasurable[ℱ (j + 1)] (X j)) (hX2 : ∀ j, MemLp (X j) 2 μ)
    (hmean : ∀ j, μ[X j | ℱ j] =ᵐ[μ] 0) {L : ℝ} (hL : 0 < L)
    (hle : ∀ j, ∀ᵐ ω ∂μ, X j ω ≤ L • (1 : Matrix n n 𝕜)) {t v : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0 ∧
        specNorm (∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω) ≤ v} ≤
      Fintype.card n * rexp (-(t ^ 2 / 2) / (v + L * t / 3))
/-- With an a.s. bound on the predictable quadratic variation: the martingale matrix Bernstein. -/
theorem measureReal_exists_eigenvalue_zero_sum_ge_le_freedman_of_ae_le [Nonempty n] (hX …)
    (hX2 …) (hmean …) (hL : 0 < L) (hle …) {t v : ℝ}
    (hv : ∀ k, ∀ᵐ ω ∂μ, specNorm (∑ j ∈ Finset.range k, μ[fun ω' => X j ω' ^ 2 | ℱ j] ω) ≤ v)
    (ht : 0 ≤ t) :
    μ.real {ω | ∃ k, t ≤ eigenvalue (∑ j ∈ Finset.range k, X j ω) 0} ≤
      Fintype.card n * rexp (-(t ^ 2 / 2) / (v + L * t / 3))
```

Rectangular (Tropp 2011, Corollary 1.3; may be scaffolded): `S : ℕ → Ω → Matrix r n 𝕜`,
`specNorm (S j ω) ≤ L`, the event `t ≤ specNorm (∑ S j)` with `max` of the two predictable
variances `≤ v`, bound `(card r + card n) · rexp (…)`, name
`measureReal_exists_specNorm_sum_ge_le_freedman`, through the dilation. Master tail: on the event
the potential is at least `e^{θt - gθ w}`; Ville with `f 0 = tr 1 = card n`. Freedman: conditional
Bernstein, `θ = t / (v + L t / 3)`, `specNorm W ≤ v ⟹ W ≤ v • 1`; `hint` from `W ≥ 0` and
`Yₖ ≤ k L • 1`. A finite horizon `N` is `X j = 0` for `j ≥ N`.

## 4. Consumers of the headline statements

None in the surveys (§0).

## 5. Files

1. `Probability/MatrixConditionalExpectation.lean`: §3.1 (8).
2. `ForMathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean`,
   `ForMathlib/Probability/Martingale/OptionalStopping.lean`: §3.2 (1 each). Independent of 1.
3. `Probability/MatrixConcentration/ConditionalMGFBound.lean`: §3.3 (6); imports 1, 2, P5a's
   `MGFBound.lean`, `Bernstein.lean` (`exp_mul_le_bernstein`, `exists_bernstein_exponent` public).
4. `Probability/MatrixConcentration/Freedman.lean`: §3.4 (5); imports 3.

## 6. Material

Read: the prototype's `ForMathlib/MeasureTheory/{MatrixConditionalExpectation,ConditionalJensen}.lean`
and `Concentration/Martingales/` (38 declarations over `ℂ`, none ledgered). Reused: non-closed
conditional Jensen, conditional Lieb, the conditional CGF and supermartingale steps, Ville. Not
reproduced: `HasLocalMatrixSecondMoment` and its 15 declarations (D9); `matrixIncrementSum`,
`conditionalMatrixSecondMoment`, `matrixCompensatedTracePotential` (written out);
`matrixVectorSqNorm`, `matrixQuadraticFormReal`; the convexity and closedness of the PSD cone
(Mathlib's `condExp_nonneg` replaces them); `algebraMap ℝ _ L` bounds (`L • 1`). Docstrings
citing unpublished "operator rederivations" (inventory §9) are rewritten against Tropp 2011.
Atlas id: `matrix-freedman`. Bibliography: add `Tropp2011` (Electron. Commun. Probab. 16).

## 7. Open questions

**Of the brief's §2 kind:**

**Q1. The conditional interface spelled with `μ[· | m]`, not `condExpKernel`.** D6 asks for the
form "as in Mathlib's `HasCondSubgaussianMGF`", which is
`Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm)` and needs `[StandardBorelSpace Ω]`.
(a) `condExp` form (§2): no Borel hypothesis, `∀ θ` outside the a.e., the form Mathlib's own API
exposes (`HasCondSubgaussianMGF.ae_condExp_le`). (b) Kernel form: every statement carries
`[StandardBorelSpace Ω]`. *Recommendation (a)*, with the bridge (§3.3) and a deviation entry.
*Rework:* low (one consumer), but it fixes the round's only conditional interface.

**Decisions taken (recorded for review):**

- **D1. Square-integrable form** in place of `HasLocalMatrixSecondMoment` (D9): increments take
  `MemLp (X j) 2 μ` and the predictable variance is Mathlib's `μ[X j ^ 2 | ℱ j]` itself (no `V`
  parameter, no local moment identity). Lost: increments whose conditional variance is finite but
  not integrable; such a user stops the martingale when the variance budget is exceeded.
- **D2. One master from the conditional interface**; Freedman is its Bernstein instance; the
  sub-Gaussian bridge gives matrix Azuma-type tails with no further theorem.
- **D3. Events:** `Wₖ ≤ w • 1` in the master, `specNorm Wₖ ≤ v` in Freedman (Tropp's; equal since
  `Wₖ ≥ 0`). **D4.** The potential's integrability is a hypothesis of the generic
  supermartingale and derived in Freedman.
- **D5.** Index convention of §1, noted in the module docstring; not a deviation (no Mathlib
  notion is replaced). **D6.** The rectangular form may be scaffolded.

Unchecked: Tropp 2011's labels (the prototype cites Theorem 1.2 for the global form; Theorem 1.1
and Corollary 1.3 here are from memory) and the bibliographic data of `Tropp2011`.

## 8. Amendments from the review (2026-10-14)

Review: Fable, of P5b, P5c, P5d and P7 together; the orchestrator accepted every finding and
decided Q1. The skeletons are written under the rule that no `sorry` enters a proved file: new
statements go in new files, merged or registered at wrap-up. None is registered in `NLAlib.lean`.

0. **Q1 decided (a)**: the conditional interface is spelled with `μ[· | m]`, per `θ` almost
   surely (§2), not with `condExpKernel`. `docs/design/Mathlib-deviations.md` entry 17 records
   it (status open until the bridge is proved); the bridge
   `hasCondMatrixMGFBound_smul_of_hasCondSubgaussianMGF` is a skeleton statement in
   `ConditionalMGFBound.lean`, the only one there with `[StandardBorelSpace Ω]` (it also needs
   `[IsFiniteMeasure μ]`, as Mathlib's `HasCondSubgaussianMGF` does).
1. **Conditional Lieb** is split in two statements so that the random-`H` step can be
   scaffolded alone: `condExp_re_trace_exp_const_add_le` (fixed Hermitian `H`: conditional
   Jensen on Lieb's concave map) and `condExp_re_trace_exp_add_le` (`m`-measurable `H`, the §3.3
   statement, marked "may be scaffolded"). Its docstring says why the kernel would not help
   (`condExpKernel_ae_eq_condExp` is per measurable set, so an `m`-measurable `H` is constant
   under `κ ω'` only through approximation anyway) and gives the approximants: entrywise
   rounding of `H` to a `1/k` grid (`m`-measurable, countable range), simpler than
   `StronglyMeasurable.approx`. `ConditionalMGFBound.lean` has 7 declarations, not 6.
2. **Ville** (docstring of `MeasureTheory.Supermartingale.measure_exists_ge_le`): Mathlib has
   `Submartingale.maximal_ineq` and `Submartingale.expected_stoppedValue_mono`; the finite
   horizon comes from `expected_stoppedValue_mono` on `hf.neg` with `σ = 0` and
   `τ = hittingBtwn f (Set.Ici c) 0 n ⊓ n`, then `n → ∞` by continuity from below. The §3.2
   remark "optional stopping at the first crossing" is this.
3. **`Matrix.condExp_conjTranspose`** without integrability: the docstring prescribes the case
   split (`condExp_of_not_integrable` on both sides; the conjugate transpose preserves
   integrability both ways).
4. **Freedman's proof**: `exists_bernstein_exponent` needs `0 ≤ v`; the docstring of
   `measureReal_exists_eigenvalue_zero_sum_ge_le_freedman` puts the case split `v < 0` (event
   empty) first. `exists_bernstein_exponent` and `exp_mul_le_bernstein` are still `private` in
   the proved `Bernstein.lean`; making them public is left to the proof round.
5. **Labels**: [Tropp2011, Theorem 1.2] for matrix Freedman (Theorem 1.1 is the scalar one;
   the §3.4 citation "Theorem 1.1" is corrected), [Tropp2011, Corollary 1.3] for the
   rectangular form, [Tropp2011, §2] for conditional Lieb, the supermartingale and the master
   tail. `Tropp2011` is added to `docs/references.bib`
   (Electron. Commun. Probab. 16 (2011) 262–270, doi 10.1214/ECP.v16-1624).
6. **Files** (amends §5). Skeletons written, each compiling with only `sorry` warnings:
   `Probability/MatrixConditionalExpectation.lean` (8),
   `ForMathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean` (1),
   `ForMathlib/Probability/Martingale/OptionalStopping.lean` (1),
   `Probability/MatrixConcentration/ConditionalMGFBound.lean` (7: the structure, `congr`,
   `mono_set`, two conditional Lieb statements, conditional Bernstein, the bridge),
   `Probability/MatrixConcentration/Freedman.lean` (5, the rectangular form included, marked
   "may be scaffolded").
7. **Elaboration fixes** (same meaning). The structure binds `μ : @Measure Ω mΩ`: with the
   explicit `m : MeasurableSpace Ω` parameter, `Measure Ω` picks up `m` as the instance and the
   fields would be stated on `m`. `MatrixConditionalExpectation.lean` takes `[DecidableEq]` on
   both index types (the L2 operator norm on `Matrix l n 𝕜` needs `DecidableEq n`).
   `Matrix.ae_posDef_condExp` and the bridge take `[IsFiniteMeasure μ]`; the Lieb, Bernstein,
   supermartingale and Freedman statements `[IsProbabilityMeasure μ]` (as §3 says).
8. **Result ids**: `matrix-freedman` (the Hermitian Freedman inequality), `ville-inequality`
   (new, for Ville's inequality).
