# Design note: Probability stage P0, vocabulary

Status: written 2026-10-14 by the orchestrator, under `docs/PORT_PROBABILITY.md` (§2 decided by
the maintainer the same day). Reviewed by a Fable agent on 2026-10-14; its corrections are folded in (identDistrib is Mathlib's;
names of the Chebyshev and two-sided tails; the unstarred pairing; `IsIsotropic.mulVec`; power
Markov; Q1 re-diagnosed). One question
of the brief's §2 kind came up while checking D10 against Mathlib (§7, Q1); the file that
depends on it (`MatrixIntegral.lean`) waits for the maintainer, and the rest of the stage does not
depend on it.

## 0. Scope and consumers

P0 is the vocabulary every later stage states things in: how a random vector with a product law
is taken apart into independent coordinates, the tail and moment conversions every tail theorem
ends with, isotropy, and integrals of matrix-valued functions.

Consumers (from `docs/port/inventory-probability.md` §2, §5, §7, §10 and
`docs/port/inventory-sketching.md` §2, §3):

| Item | Consumers |
|---|---|
| product laws and their coordinates | P2 (Gaussian and Rademacher vectors as `Measure.pi`), R1 (a Gaussian matrix has i.i.d. entries), Sketching (Rademacher and sparse sign matrices); the prototype restated `iIndepFun_iff_hasLaw_pi_pi` 9 times |
| law transport of integrability and `MemLp` | every moment of a law stated for a random variable (D2): P2's moments, P3's `m₄`, R2 |
| Markov and Chebyshev in `μ.real` | Hutchinson's tail (P3), sample averages, every "expectation bound implies tail" step in Sketching |
| moments from tails | P1 (absolute moments of a sub-Gaussian), P3 (negative moments of `χ²`), R4 (`E ‖pinv G‖` from its tail); the prototype had five `TailIntegral` lemmas and four `ExponentialTailMoments` ones |
| two-sided tail from one-sided tails | P1, P3, P5 (every two-sided statement) |
| isotropy | P3 (Hutchinson's mean `E quadForm A X = trace A`), R2 (`E ‖S X T‖_F²`), Sketching (JL second moment, AMM), R5 (rescaled Haar columns) |
| matrix-valued integrals | P5 (master bound, Lieb step, dilation), R2, R5 (`E [Q Qᴴ] = (k / n) • 1`), Sketching (`E [Sᴴ S] = 1`) |

Not here: `HasSubexponentialMGF` and the sub-Gaussian API (P1), conditional expectations of
matrices (P5, with Freedman, their only consumer; amendment to the brief's §3.1, which listed
them under P0), Jensen on a convex set that is not closed (P5, with the Lieb step that needs it),
`E exp (s • A) = cfc (mgf s) A` (P5).

## 1. Objects

| Concept | Spelling | Mathlib bridge |
|---|---|---|
| law of a random variable | Mathlib's `HasLaw X ν μ` | — |
| i.i.d. coordinates with laws `ν i` | `HasLaw X (Measure.pi ν) μ` | `iIndepFun_iff_hasLaw_pi_pi` |
| independent entries of a random matrix | `HasLaw X (Measure.pi fun i => Measure.pi fun j => ν i j) μ` for `X : Ω → Matrix m n α`; the matrix σ-algebra is `MeasurableSpace.pi` (`Matrix.instMeasurableSpace`, D8), and the statement elaborates without an ascription (checked); `HasLaw.isProbabilityMeasure` does not find the `Measure.pi` probability instance at type `Measure (Matrix m n α)`, a note for R1 | `Measure.infinitePi_map_curry` |
| failure probability | `μ.real {ω | t ≤ f ω}` (D3) | Mathlib's `measureReal_*` API |
| variance | Mathlib's `variance X μ` | — |
| isotropic random vector | `IsIsotropic X μ` for `X : Ω → n → 𝕜`, new (§2) | Mathlib's `covarianceBilin` is the centred form on a real inner product space; isotropy here is uncentred and over `𝕜` |
| integral of a matrix-valued function | `∫ ω, X ω ∂μ` under one scope (D10; §7 Q1) | Mathlib's Bochner integral |

## 2. Interfaces

**`IsIsotropic X μ`** (new; `CONTRIBUTING.md` §5.4). For `X : Ω → n → 𝕜`:

```lean
/-- A random vector `X` in `𝕜ⁿ` is isotropic for `μ` when its coordinates are square integrable
and its second-moment matrix `E [X Xᴴ]` is the identity. No mean is assumed. -/
structure IsIsotropic [DecidableEq n] (X : Ω → n → 𝕜) (μ : Measure Ω) : Prop where
  memLp : ∀ i, MemLp (fun ω => X ω i) 2 μ
  integral_mul_star : ∀ i j, ∫ ω, X ω i * star (X ω j) ∂μ = if i = j then 1 else 0
```

- Entrywise, so it does not depend on the matrix-integral scope (§7 Q1), and the matrix form
  `∫ vecMulVec (X ω) (star (X ω)) = 1` becomes a lemma in `MatrixIntegral.lean` once that file
  exists.
- Uncentred and not normalised by a measure assumption: a Rademacher or Gaussian vector is
  isotropic, so is `√n` times a uniform point of the sphere, and so is a non-centred vector with
  `E [X Xᴴ] = 1`. Over `ℂ` it says nothing about `E [X Xᵀ]` (the pseudo-covariance), which the
  complex Hutchinson variance needs; P3 adds that as a parameter, not here.
- The fourth moment is not part of it (brief D6: fixed moments are parameters).
- Raw-condition constructor: `IsIsotropic.of_iIndepFun` (independent coordinates, mean zero,
  `E |X i|² = 1`). Law transport: `HasLaw.isIsotropic_iff`, so a law is proved isotropic once,
  as `IsIsotropic id ν`, and every random variable with that law inherits it.

No other interface is introduced here.

## 3. Statement shapes

All in `namespace NLAlib`; lemmas about a Mathlib structure hypothesis are
`_root_.ProbabilityTheory.HasLaw.foo` so that `hX.foo` works (`CONTRIBUTING.md` §3).

Common variables: `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}`; `{ι : Type*} [Fintype ι]`;
`{𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ν : Measure 𝓧}`.

### 3.1 `Probability/Law.lean`

Product laws, for `{E : ι → Type*} [∀ i, MeasurableSpace (E i)] {ν : ∀ i, Measure (E i)}
{X : Ω → ∀ i, E i}`:

```lean
/-- A random vector has the product law `Measure.pi ν` exactly when its coordinates are
independent and the `i`-th has law `ν i`. -/
theorem hasLaw_pi_iff [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw X (Measure.pi ν) μ ↔
      iIndepFun (fun i ω => X ω i) μ ∧ ∀ i, HasLaw (fun ω => X ω i) (ν i) μ

theorem _root_.ProbabilityTheory.HasLaw.eval [∀ i, IsProbabilityMeasure (ν i)]
    (hX : HasLaw X (Measure.pi ν) μ) (i : ι) : HasLaw (fun ω => X ω i) (ν i) μ

theorem _root_.ProbabilityTheory.HasLaw.iIndepFun_eval [∀ i, IsProbabilityMeasure (ν i)]
    (hX : HasLaw X (Measure.pi ν) μ) : iIndepFun (fun i ω => X ω i) μ
```

`HasLaw.eval` and `.iIndepFun_eval` need no `[IsProbabilityMeasure μ]`: it follows from `hX`
(`HasLaw.isProbabilityMeasure`, which needs `Measure.pi ν` to be a probability measure, hence the
instance on the factors). `hasLaw_pi_iff` keeps it because the right-hand side does not imply it
when `ι` is empty.

Random matrices with independent entries, for `{m n α : Type*} [Fintype m] [Fintype n]
[MeasurableSpace α] {ν : m → n → Measure α} [∀ i j, IsProbabilityMeasure (ν i j)]
{X : Ω → Matrix m n α}`:

```lean
/-- A random matrix has the law `Measure.pi fun i => Measure.pi fun j => ν i j` exactly when its
entries, indexed by `m × n`, are independent and the `(i, j)` entry has law `ν i j`. -/
theorem hasLaw_pi_pi_iff [IsProbabilityMeasure μ] :
    HasLaw X (Measure.pi fun i => Measure.pi fun j => ν i j) μ ↔
      iIndepFun (fun p : m × n => fun ω => X ω p.1 p.2) μ ∧
        ∀ i j, HasLaw (fun ω => X ω i j) (ν i j) μ

theorem _root_.ProbabilityTheory.HasLaw.entry
    (hX : HasLaw X (Measure.pi fun i => Measure.pi fun j => ν i j) μ) (i : m) (j : n) :
    HasLaw (fun ω => X ω i j) (ν i j) μ

theorem _root_.ProbabilityTheory.HasLaw.iIndepFun_entry
    (hX : HasLaw X (Measure.pi fun i => Measure.pi fun j => ν i j) μ) :
    iIndepFun (fun p : m × n => fun ω => X ω p.1 p.2) μ
```

Law transport (Mathlib has `HasLaw.integral_comp` and `HasLaw.lintegral_comp`, not these):

```lean
theorem _root_.ProbabilityTheory.HasLaw.integrable_comp_iff {E : Type*} [NormedAddCommGroup E]
    {X : Ω → 𝓧} (hX : HasLaw X ν μ) {f : 𝓧 → E} (hf : AEStronglyMeasurable f ν) :
    Integrable (fun ω => f (X ω)) μ ↔ Integrable f ν

theorem _root_.ProbabilityTheory.HasLaw.memLp_comp_iff {E : Type*} [NormedAddCommGroup E]
    {X : Ω → 𝓧} (hX : HasLaw X ν μ) {f : 𝓧 → E} (hf : AEStronglyMeasurable f ν) {p : ℝ≥0∞} :
    MemLp (fun ω => f (X ω)) p μ ↔ MemLp f p ν
```

Searched: `HasLaw.lean`, `IdentDistrib.lean`, `Independence/`; Mathlib has
`iIndepFun_iff_hasLaw_pi_pi` (per-coordinate laws as a hypothesis), `iIndepFun.hasLaw_pi`,
`measurePreserving_eval`, `integrable_map_measure`, `memLp_map_measure_iff`, and
`HasLaw.identDistrib` (so it is not restated); `hasLaw_pi_iff` is the
form without the per-coordinate hypothesis, and the rest are one-line wrappers that consumers
otherwise rewrite by hand (the prototype has 9 such restatements).

### 3.2 `Probability/Tail.lean`

Mathlib's Chernoff bound `measure_ge_le_exp_mul_mgf` is already in `μ.real` (the brief's D3
said `ℝ≥0∞`; corrected there), and Markov's `mul_meas_ge_le_integral_of_nonneg` is too. Chebyshev
(`meas_ge_le_variance_div_sq`) is in `ℝ≥0∞`. The union bound, complement and monotonicity are
Mathlib's (`measureReal_union_le`, `measureReal_biUnion_finset_le`, `probReal_compl_eq_one_sub`,
`measureReal_mono`).

```lean
/-- **Markov's inequality** as a failure probability. -/
theorem measureReal_ge_le_integral_div {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hf : Integrable f μ)
    {t : ℝ} (ht : 0 < t) : μ.real {ω | t ≤ f ω} ≤ (∫ ω, f ω ∂μ) / t

/-- **Markov's inequality for a moment**, the step every moment-method tail ends with. -/
theorem measureReal_abs_ge_le_integral_rpow_div {X : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hX : Integrable (fun ω => |X ω| ^ p) μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ (∫ ω, |X ω| ^ p ∂μ) / t ^ p

/-- **Chebyshev's inequality** as a failure probability. -/
theorem measureReal_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω - ∫ ω', X ω' ∂μ|} ≤ variance X μ / t ^ 2

/-- A two-sided tail is at most the sum of the two one-sided tails. -/
theorem measureReal_abs_ge_le_add (X : Ω → ℝ) (t : ℝ) :
    μ.real {ω | t ≤ |X ω|} ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | X ω ≤ -t}
```

Moments from tails, with the integrability companion (D3). The hypothesis is the non-strict tail
that every tail theorem of the round produces; it bounds the strict tail as well.

```lean
/-- A nonnegative random variable whose tail beyond `a` is bounded by an integrable function is
integrable. -/
theorem integrable_of_measureReal_ge_le [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEMeasurable f μ)
    (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} {F : ℝ → ℝ} (hF : IntegrableOn F (Set.Ioi a))
    (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) : Integrable f μ

/-- The layer-cake bound: the mean of a nonnegative random variable is at most `a` plus the
integral of a bound on its tail beyond `a`. -/
theorem integral_le_of_measureReal_ge_le [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a : ℝ} {F : ℝ → ℝ}
    (hF : IntegrableOn F (Set.Ioi a)) (htail : ∀ t, a < t → μ.real {ω | t ≤ f ω} ≤ F t) :
    ∫ ω, f ω ∂μ ≤ a + ∫ t in Set.Ioi a, F t
```

Degenerate cases: `hF` makes `F ≥ 0` a.e. on `Ioi a` automatic (`F t` bounds a probability);
`a` may be negative (then `F ≥ 1` on `(a, 0]` and the bound still holds), so no `0 ≤ a`; moments `E f ^ p` are the same lemma applied to `f ^ p`, whose tail is
`μ.real {t ^ (1 / p) ≤ f}`, so no `rpow` variant is stated (the prototype's
`integral_le_of_tail_le_rpow` is a corollary a consumer instantiates; P1 states the sub-Gaussian
moment it needs).

Searched: `Layercake.lean` (`Integrable.integral_eq_integral_meas_le`, which assumes
integrability), `Variance.lean`, `Bochner/Basic.lean`, `Measure/Real.lean`.

### 3.3 `Probability/Isotropic.lean`

Variables `{n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜] {X : Ω → n → 𝕜}`.

```lean
structure IsIsotropic (X : Ω → n → 𝕜) (μ : Measure Ω) : Prop   -- §2

namespace IsIsotropic

theorem integrable_mul_star (hX : IsIsotropic X μ) (i j : n) :
    Integrable (fun ω => X ω i * star (X ω j)) μ

theorem integrable_quadForm (hX : IsIsotropic X μ) (A : Matrix n n 𝕜) :
    Integrable (fun ω => quadForm A (X ω)) μ

/-- **Hutchinson's identity**: for an isotropic probe the quadratic form is an unbiased estimator
of the trace. -/
theorem integral_quadForm (hX : IsIsotropic X μ) (A : Matrix n n 𝕜) :
    ∫ ω, quadForm A (X ω) ∂μ = A.trace

theorem integrable_norm_mulVec_sq (hX : IsIsotropic X μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ X ω)‖ ^ 2) μ

/-- `E ‖A X‖² = ‖A‖_F²` for an isotropic `X`. -/
theorem integral_norm_mulVec_sq (hX : IsIsotropic X μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : ∫ ω, ‖WithLp.toLp 2 (A *ᵥ X ω)‖ ^ 2 ∂μ = frobNorm A ^ 2

/-- `E |⟨u, X⟩|² = ‖u‖²` for an isotropic `X`: the second moment behind the JL lemma. -/
theorem integral_norm_dotProduct_sq (hX : IsIsotropic X μ) (u : n → 𝕜) :
    ∫ ω, ‖u ⬝ᵥ X ω‖ ^ 2 ∂μ = ‖WithLp.toLp 2 u‖ ^ 2

/-- A map with orthonormal rows preserves isotropy. -/
theorem mulVec (hX : IsIsotropic X μ) {m : Type*} [Fintype m] [DecidableEq m]
    {U : Matrix m n 𝕜} (hU : HasOrthonormalCols Uᴴ) : IsIsotropic (fun ω => U *ᵥ X ω) μ

theorem integral_norm_sq (hX : IsIsotropic X μ) :
    ∫ ω, ‖WithLp.toLp 2 (X ω)‖ ^ 2 ∂μ = Fintype.card n

/-- Independent coordinates with mean zero and unit second moment form an isotropic vector. -/
theorem of_iIndepFun (hind : iIndepFun (fun i ω => X ω i) μ)
    (hL2 : ∀ i, MemLp (fun ω => X ω i) 2 μ) (hmean : ∀ i, ∫ ω, X ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, ‖X ω i‖ ^ 2 ∂μ = 1) : IsIsotropic X μ

end IsIsotropic

/-- Isotropy depends only on the law. -/
theorem _root_.ProbabilityTheory.HasLaw.isIsotropic_iff {ν : Measure (n → 𝕜)} (hX : HasLaw X ν μ) :
    IsIsotropic X μ ↔ IsIsotropic id ν
```

`integral_norm_dotProduct_sq` is `integral_norm_mulVec_sq` for the one-row matrix
`Matrix.replicateRow (Fin 1) u`, stated with the unstarred pairing `u ⬝ᵥ X ω` that the
sub-Gaussian-vector interface (D6) and a sketch row applied to a vector use; it is stated because the JL and sketching consumers hold
a vector, not a matrix. Over `ℝ`, `‖r‖ ^ 2` is `r ^ 2` by `Real.norm_eq_abs, sq_abs`; no real twin.
Degenerate cases: `n` empty (`card n = 0`, everything zero); `A = 0`; `μ` not a probability
measure is allowed everywhere (`iIndepFun` in `of_iIndepFun` already implies one).

Searched: `CovarianceBilin.lean` (centred, real inner product spaces, a law not a random
variable), `Independence/Integration.lean` (`IndepFun.integral_fun_mul_eq_mul_integral` over
`𝕜`), the Matrix layer's `quadForm` and `frobNorm` API.

### 3.4 `Probability/MatrixIntegral.lean` (waits on §7 Q1)

Under the scope chosen in Q1 (written here for `Matrix.Norms.L2Operator`, the recommendation),
with `[DecidableEq m] [DecidableEq n]` where the instance needs them:

```lean
theorem Matrix.integrable_iff {X : Ω → Matrix m n 𝕜} :
    Integrable X μ ↔ ∀ i j, Integrable (fun ω => X ω i j) μ
theorem Matrix.memLp_iff {X : Ω → Matrix m n 𝕜} {p : ℝ≥0∞} :
    MemLp X p μ ↔ ∀ i j, MemLp (fun ω => X ω i j) p μ
theorem Matrix.integral_apply {X : Ω → Matrix m n 𝕜} (hX : ∀ i j, Integrable (fun ω => X ω i j) μ)
    (i : m) (j : n) : (∫ ω, X ω ∂μ) i j = ∫ ω, X ω i j ∂μ
-- no integrability needed: an injective linear map with a continuous inverse
theorem Matrix.integral_conjTranspose (X : Ω → Matrix m n 𝕜) : ∫ ω, (X ω)ᴴ ∂μ = (∫ ω, X ω ∂μ)ᴴ
theorem Matrix.integral_reindex (e : m ≃ m') (f : n ≃ n') (X : Ω → Matrix m n 𝕜) :
    ∫ ω, Matrix.reindex e f (X ω) ∂μ = Matrix.reindex e f (∫ ω, X ω ∂μ)
theorem Matrix.integral_submatrix (hX : Integrable X μ) (r : l → m) (c : k → n) :
    ∫ ω, (X ω).submatrix r c ∂μ = (∫ ω, X ω ∂μ).submatrix r c
theorem Matrix.integral_trace (hX : Integrable X μ) : ∫ ω, (X ω).trace ∂μ = (∫ ω, X ω ∂μ).trace
theorem Matrix.integral_const_mul (A : Matrix l m 𝕜) (hX : Integrable X μ) :
    ∫ ω, A * X ω ∂μ = A * ∫ ω, X ω ∂μ
theorem Matrix.integral_mul_const (hX : Integrable X μ) (B : Matrix n k 𝕜) :
    ∫ ω, X ω * B ∂μ = (∫ ω, X ω ∂μ) * B
theorem Matrix.integral_quadForm (hX : Integrable X μ) (z : n → 𝕜) :
    ∫ ω, quadForm (X ω) z ∂μ = quadForm (∫ ω, X ω ∂μ) z
-- order: no integrability needed (a non-integrable function integrates to `0`)
theorem Matrix.isHermitian_integral (h : ∀ᵐ ω ∂μ, (X ω).IsHermitian) : (∫ ω, X ω ∂μ).IsHermitian
theorem Matrix.posSemidef_integral (h : ∀ᵐ ω ∂μ, (X ω).PosSemidef) : (∫ ω, X ω ∂μ).PosSemidef
theorem Matrix.posDef_integral [NeZero μ] (hX : Integrable X μ) (h : ∀ᵐ ω ∂μ, (X ω).PosDef) :
    (∫ ω, X ω ∂μ).PosDef
theorem IsIsotropic.integral_vecMulVec (hX : IsIsotropic X μ) :
    ∫ ω, vecMulVec (X ω) (star (X ω)) ∂μ = 1
```

Loewner monotonicity is Mathlib's `integral_mono_ae` once the Loewner order has
`ClosedIciTopology` over `𝕜` (`ForMathlib/Analysis/Matrix/Order.lean`, new; `IsOrderedModule ℝ`
is Mathlib's, and `OrderClosedTopology` exists only for `ℂ`, through `CStarAlgebra`). Scalar times matrix is Mathlib's `integral_smul_const`.

## 4. Consumers of the headline statements

`hasLaw_pi_iff`, `hasLaw_pi_pi_iff`: P2 and R1 build the Gaussian and Rademacher vectors and
matrices from scalar laws and take them apart. `integral_le_of_measureReal_ge_le`: P1's absolute
moments, P3's negative `χ²` moments, R4. `measureReal_abs_sub_integral_ge_le`: P3's Hutchinson
tail. `IsIsotropic.integral_quadForm`: P3 (Hutchinson), Sketching (trace estimation).
`integral_norm_mulVec_sq`: R2, Sketching (AMM). `HasLaw.isIsotropic_iff`: every law in P2, R5.

## 5. Files

In build order; the first three are independent of each other.

1. `NLAlib/Probability/Law.lean`: §3.1 (8 statements).
2. `NLAlib/Probability/Tail.lean`: §3.2 (6 statements).
3. `NLAlib/Probability/Isotropic.lean`: §3.3 (11 statements); imports `Law.lean`.
4. After Q1: `NLAlib/ForMathlib/Analysis/Matrix/Order.lean` (`ClosedIciTopology` for the
   Loewner order over `𝕜`), the scope's missing instance (Q1), and
   `NLAlib/Probability/MatrixIntegral.lean`: §3.4 (15 statements).

Existing: `NLAlib/Probability/Measurability/Matrix.lean`, `NLAlib/ForMathlib/MeasureTheory/Matrix.lean`.

## 6. Material

Read: the prototype's `ForMathlib/Probability/HasLaw.lean` (`hasLaw_iff_map_eq`, not reproduced:
it is `HasLaw`'s constructor), `ForMathlib/MeasureTheory/{Integral,TailComparison,MomentInterpolation,
ExponentialTailMoments}.lean`, `Probability/Concentration/Basic/TailIntegral.lean` (the five
tail-integration lemmas become two; the `rpow` and `exp (-t / 2)` special cases are not
reproduced), `Probability/Concentration/Basic/MatrixCalculus.lean` and
`Concentration/Matrix/LiebIntegralPosDef.lean` (matrix integrals over `Matrix (Fin d) (Fin d) ℂ`
under `Matrix.Norms.L2Operator`; generalised to `𝕜` and any index types),
`ForMathlib/MeasureTheory/MatrixConditionalExpectation.lean` (P5). The three prototype spellings of
isotropy (inventory §2 item 4) are replaced by `IsIsotropic`.

Not reproduced: `hasLaw_iff_map_eq`; `integrable_comp_of_abs_le_sum_abs`; the `update_pi` family
(proof material for bounded differences, P7); `integral_le_sqrt_integral_sq` (Mathlib's
`integral_mul_le_Lp_mul_Lq` family gives it; a consumer that wants it asks P1).

## 7. Open questions

**Q1 (§2 kind; for the maintainer). The scope for matrix integrals (amends D10).** D10 chose one
library-wide scope, `Matrix.Norms.Frobenius`. Checked against the pinned Mathlib, it does not
work, and neither does `Matrix.Norms.Elementwise`: under either, `Integrable X μ` for
`X : Ω → Matrix m n 𝕜` fails with

```
error: failed to synthesize instance of type class
  ContinuousENorm (Matrix m n ℝ)
```

(fresh file, `Matrix m n ℝ`, only `Mathlib.Analysis.Matrix.Normed` and the Bochner integral
imported). The cause is Mathlib's global topology on matrices,
`instance : TopologicalSpace (Matrix m n R) := inferInstanceAs (TopologicalSpace (m → n → R))`
(`Mathlib/Topology/Instances/Matrix.lean`), which is not reducibly `Pi.topologicalSpace`
(`with_reducible_and_instances rfl` fails). `Integrable` takes that topology and then looks for
`ContinuousENorm` at it; the Frobenius and elementwise normed groups carry the product topology,
so the search fails. `∫` alone elaborates (it takes only the normed group), which is why the
draft and its review missed it. Only `Matrix.Norms.L2Operator` works: Mathlib builds that
instance with `replaceTopology` to the global topology. Under it `Integrable`, `∫`, `μ[X|m]`
and `integral_mono_ae` elaborate (checked), but Mathlib gives it a `NormedSpace 𝕜` and no
`NormedSpace ℝ`, which the Bochner integral needs; over `ℂ` that comes from
`NormedSpace.complexToReal`, over a general `𝕜` from nothing.
- (a′) **`Matrix.Norms.L2Operator`, library-wide**, plus one scoped instance in `ForMathlib`,
  `NormedSpace ℝ (Matrix m n 𝕜)` on the existing `Module ℝ` (no new data; the proof is
  `‖r • A‖ = ‖(r : 𝕜) • A‖`). Checked: integrals and conditional expectations elaborate over
  `𝕜`, and at `𝕜 = ℂ` the new instance and `NormedSpace.complexToReal` agree by
  `with_reducible_and_instances rfl`, so there is no diamond. The operator norm is the C*-norm,
  which the Matrix layer already opens for its functional-calculus files, so a P5 file that needs
  the isometric functional calculus and integrals opens one scope. Costs: `[DecidableEq n]` on
  every matrix-expectation statement (the instance needs it; a permanent but small tax), and a
  `ClosedIciTopology` instance for the Loewner order over `𝕜` (Mathlib has `IsOrderedModule ℝ`
  and, for `ℂ` only, `OrderClosedTopology` through `CStarAlgebra`). *Recommended.*
- (a″) `Matrix.Norms.Frobenius` (or `Elementwise`), with an NLAlib replacement of Mathlib's
  instance whose topology is replaced by the global one, as Mathlib does for `L2Operator`: no
  `DecidableEq` tax, but a library-owned normed structure under Mathlib's scope name that shadows
  Mathlib's. The proper fix is upstream (make the global topology reducibly `Pi`, or replace the
  topology in the Frobenius and elementwise instances), after which (a″) could become the choice.
- (b) Entrywise (`Matrix.of fun i j => ∫ ω, X ω i j ∂μ`, or a named `matrixIntegral`), D10's
  alternative, with conditional expectation and Jensen rebuilt.
In every case statements never mention the norm, and `Mathlib-deviations.md` entry 13 is
rewritten. *Rework if changed later:* every matrix expectation statement (P5, R2, R5, Sketching),
mostly the instance arguments, since the integral's value is the same. Nothing before P5 depends
on it except §3.4, so the stage proceeds without it.

**Q2 (orchestrator, decided).** Isotropy is uncentred and entrywise, with the pseudo-covariance
left to P3. Alternative: Mathlib's `covarianceBilin` of the law equal to the inner product; it is
centred, real and on a law, so it fits none of the consumers (Hutchinson needs `E [X Xᴴ]`, not
the covariance, and holds for non-centred probes).

**Q3 (orchestrator, decided).** Conditional expectations of matrices move to P5. Their only
consumer is Freedman, last in P5; stating them now would fix a shape before its consumer exists.
Caveat from the review: R2's conditioning on a block and R4's `E ‖Σ₂ Ω₂ Ω₁⁺‖²` condition on an
independent block; R2's note says whether they go through `condExp` or through independence and
Fubini, and if the former, the matrix `condExp` API moves before R2.
