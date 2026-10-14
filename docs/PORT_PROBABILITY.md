# Port brief: the Probability round (Probability and RandomMatrix)

For the orchestrating agent building `NLAlib/Probability/` and `NLAlib/RandomMatrix/`. Read
`CONTRIBUTING.md` in full first, then `docs/design/Matrix-REPORT.md` (what the Matrix layer
exports and what it learned), `docs/design/Mathlib-deviations.md`, and the two surveys of the
prototype this brief is built on: `docs/port/inventory-probability.md` (the prototype's
`Probability/` and `RandomMatrix/`) and `docs/port/inventory-sketching.md` (`Sketching/` and the
layers that consume randomness). Status: **draft, 2026-10-14; §2 awaits the maintainer.**

## 0. What this is and is not

- **The goal** is the probabilistic foundation that the layers above (sketching, randomized
  low-rank approximation, trace estimation, randomized solvers) will prove their theorems on: a
  small set of distributional interfaces, concentration inequalities stated once against them,
  and the standard distributions shown to satisfy them. Each result is proved once, from the
  property its proof uses, and each distribution enters by showing it has the property.
- **The prototype** (`~/Documents/prove2me/lean/NLAlib/{Probability,RandomMatrix}`, 170 modules,
  39k lines, 921 declarations, no `sorry`) is material, not a template. The surveys found its
  faults: five spellings of a Gaussian vector, six of a sub-Gaussian proxy, four of a
  sub-Gaussian vector, three of isotropy; 50 `_of_hasLaw` twins; per-distribution copies of
  results whose proofs use one property; constants written out in statements (`1/(256e²)` five
  times) and improvements named `_sharp`; matrix concentration over `ℂ` on `Fin d` only.
- **Scope of the round** (decision D1): the Probability layer and the RandomMatrix layer,
  designed together because the distributions (Gaussian vectors and matrices, Rademacher,
  orthonormal frames) and the properties they satisfy are one design, and built in sequence.
  Sketching is the next round, but its property predicates constrain this one (§5).
- **Not in scope:** sketch distributions and their embedding theorems (next round), the sparse
  embedding machinery, randomized algorithms, finite precision.

## 1. Process

As in the Matrix layer (`docs/PORT_MATRIX.md` §1, §2, "Models and delegation"), with the
amendments the Matrix report proposed, applied here from the start:

- **Consumers first.** Each stage's design note opens with the list of what the layers above use
  from it (the surveys give it; `scripts/downstream_nulls.py` and greps refresh it), and is sized
  by that list, not by the prototype's file list. Material with no consumer is ported only when it
  is part of a standard treatment a user would expect, and the note says which.
- **Degenerate-case checklist** for every statement: empty index type, zero matrix or vector,
  constants that may be zero, indices past the size, rank deficiency, a probability measure that
  is not assumed, non-integrable functions (§3.2).
- **File budget.** A skeleton file has at most about fifteen statements, or the note names its
  split in advance.
- **Duplicate search** against the library, not only Mathlib, before a statement enters a
  skeleton; a helper a second file could want is public from the start.
- **Checks on the proved part** with `scripts/stage_check.sh`; a wrap-up agent with a fixed list
  and a read-only ledger pass close each stage; ledger notes never say "deferred".
- **Approval** (maintainer, 2026-10-14): the maintainer decides the serious design questions,
  those that would need substantial rework to change once the round is finished. They are §2.
  The orchestrator does not write skeletons that depend on an open §2 question. Every other
  decision proceeds without a stop and is recorded in the stage's design note. A new question of
  the §2 kind that arises later is added to §2 and the work that depends on it waits.
- **Deviations from Mathlib** get an entry in `docs/design/Mathlib-deviations.md` in the commit
  that introduces them (`CONTRIBUTING.md` §8).
- The ledger accounts for the 921 public declarations of the prototype's `Probability/` and
  `RandomMatrix/` (and for `Sketching/` declarations this round ports, if any).

## 2. Decisions for the maintainer

Each with the alternatives and a recommendation. "Rework" says what changing it later would cost.

**D1. Scope.** (a) Probability and RandomMatrix in one round, as above; (b) Probability alone,
RandomMatrix designed later. *Recommendation (a):* the Gaussian and Haar laws, their invariance
and their moments are the same objects at vector and matrix level, and the user's main
requirement (one interface per property, all distributions as instances) is a cross-layer
design. *Rework:* low for the choice itself; high if (b) leads to interfaces RandomMatrix cannot
use.

**D2. How randomness appears in statements.** (a) Random variables only: a theorem takes
`X : Ω → E` with Mathlib's `HasLaw X ν μ` (or a property such as `HasSubgaussianMGF`), never the
canonical space `E` with the measure `ν`; the measure form is `HasLaw.id`, never a twin. Discrete
laws are measures (`PMF.toMeasure`), `PMF` appears only as a constructor. (b) State on the
canonical measure, with `_of_hasLaw` corollaries (the prototype; 50 twins). *Recommendation (a).*
*Rework:* every statement.

**D3. Tails and expectations.**
- Tails in failure form, real-valued, with non-strict events:
  `μ.real {ω | t ≤ f ω} ≤ bound`, `μ.real {ω | f ω ≤ t}`, `μ.real {ω | t ≤ |f ω - m|}`. Never the
  success form `1 - δ ≤ …`, never `ENNReal.ofReal` or `.toReal` on the right. A non-strict event is
  the stronger statement. `μ.real` of a non-measurable set is its outer measure, so a tail bound
  never needs a measurability hypothesis on the event.
- Expectations are Bochner integrals `∫ ω, f ω ∂μ`. **Every bound of the form `∫ f ≤ B` comes with
  an integrability theorem, as a separate statement** (`integrable_…`, then `integral_…_le`).
  Reason: the Bochner integral of a non-integrable function is `0`, a junk value, so for
  nonnegative `f` the bound alone is true whenever `B ≥ 0` and says nothing; this is the same
  hazard as the out-of-range eigenvalue (`Mathlib-deviations.md` §1). Alternative: lower
  Lebesgue integrals `∫⁻` (no junk value, but values in `ℝ≥0∞` and no subtraction or variance).
  *Recommendation:* the Bochner form with the integrability companion; `∫⁻` only where finiteness
  is itself the question. *Rework:* every expectation statement.

**D4. Fields.** Random scalars and random vectors are real (`Ω → ℝ`, `Ω → n → ℝ`). Matrix
concentration is over `𝕜`: sums of random Hermitian matrices over `𝕜`, real random coefficients
times deterministic matrices over `𝕜`. Random-matrix laws (Gaussian matrices, Haar frames) are
defined over `ℝ` in this round, and the interfaces they satisfy (invariance, frames) are stated
over `𝕜`, so complex Gaussian and complex Haar laws are later instances, not redesigns.
Alternative: everything over `ℝ`, or Gaussian laws over `𝕜` now. *Recommendation:* as stated.
*Rework:* high for the interfaces, low for the laws.

**D5. Numerical bounds and naming.** Bounds begin in this round, and later improvements and
incomparable new proofs must fit without renaming. Proposed rules (to enter `CONTRIBUTING.md`
§4 and §5.2 when approved):
1. **A name says what the statement is, never how good it is.** No `_sharp`, `_improved`,
   `_tight`, `_v2`, `_new`. Classical names are kept where the subject uses them (`bernstein`,
   `hoeffding`, `mcdiarmid`, `hansonWright`, `freedman`, `gordon`).
2. **Constants and tail functions are definitions**, introduced with `irreducible_def`:
   `hansonWrightConstant : ℝ`, `matrixBernsteinTail d v L t : ℝ`. The docstring records the
   source's value, the value proved, and the gap. Consumers use only API lemmas that remain true
   when the bound improves: positivity, and a one-sided explicit comparison
   (`1 / (256 * exp 2) ≤ hansonWrightConstant` for a constant in an exponent,
   `matrixBernsteinTail d v L t ≤ 2 * d * exp (…)` for a tail). An improvement of the same shape
   changes a definition's body and one comparison lemma; no statement, no name.
3. **Incomparable bounds coexist**, each named by what distinguishes it: its hypothesis
   (`_of_bounded`, `_of_variance_le`) or the parameter its bound is in (`_intrinsicDim` against
   the dimension form). Each docstring says in which regime it is the better bound and names the
   other.
4. **One canonical statement per result** for consumers who want the best available bound: an
   unqualified theorem whose bound is a named function defined as the minimum of the available
   bounds (for tails), or as the minimum of the sufficient sizes (for sample sizes: `k ≥ min k₁ k₂`
   suffices because each `kᵢ` does). A new incomparable bound adds a term to the minimum; the
   canonical statement gets stronger and keeps its name.
5. **A dominated result** (the new bound is at least as good in every regime) is reproved from the
   new one and keeps its name if consumers cite its simpler form; otherwise it is deprecated with
   `@[deprecated]` and removed after a release.
6. **Tail before sample size** (`CONTRIBUTING.md` §5.2, unchanged): the sample size is a named
   definition with comparison lemmas.
Alternative: rules 1–3 and 5 without rule 4 (no canonical minimum; consumers choose a bound).
*Recommendation:* all six. *Rework:* every quantitative statement in this round and the next.

**D6. The property interfaces** (CONTRIBUTING §5.4). Every theorem of the round takes one of these
or a Mathlib notion, never a raw bundle. Names are proposals.

| Interface | Form | Instances | Consumers |
|---|---|---|---|
| sub-Gaussian scalar | Mathlib's `HasSubgaussianMGF X c μ`, `c : ℝ≥0` always | Gaussian, Rademacher, bounded centred, Lipschitz images of Gaussian | tails, maxima, Hoeffding, series |
| sub-exponential scalar | `HasSubexponentialMGF X v b μ`: `cgf X μ l ≤ v * l ^ 2 / 2` for `|l| < 1 / b`, with integrability | Bernstein condition, centred squares, ψ₁ | Bernstein, Hanson–Wright |
| sub-Gaussian vector | `IsSubgaussianVector X c μ`: every `⟨u, X⟩` has `HasSubgaussianMGF` with proxy `c * ‖u‖ ^ 2` | Gaussian, Rademacher, independent sub-Gaussian coordinates | χ²-type tails, nets, JL, rows |
| isotropy | `IsIsotropic X μ`: `MemLp 2` coordinates and `∫ X i * X j = if i = j then 1 else 0` | Gaussian, Rademacher, uniform on the sphere of radius `√n`, Haar columns rescaled | Hutchinson, `E ‖S X T‖_F²`, AMM |
| matrix MGF bound | `HasMatrixMGFBound X g A s μ`: `∫ exp (θ • X ω) ≤ exp (g θ • A)` in the Loewner order for `θ ∈ s` | bounded (Chernoff, Bernstein), sub-Gaussian coefficients (series) | one master tail; sampling without replacement |
| unitary invariance | `IsLeftUnitarilyInvariant ν` (and right): `ν.map (U * ·) = ν` for unitary `U` | Gaussian matrices, Haar frames | block laws, inverse moments, transfer |
| random frame | `X : Ω → Matrix n k 𝕜` with `∀ᵐ ω, HasOrthonormalCols (X ω)` | Haar frames, range frames | low-rank layer |

Concentration of functions concludes Mathlib's `HasSubgaussianMGF (fun ω => f (X ω) - ∫ f ∘ X)`
(Gaussian Lipschitz, log-Sobolev, bounded differences), so it needs no interface of its own.
Fixed moments enter as parameters (`∫ X i ^ 4 = m₄`), not as interfaces. *Rework:* the
interfaces are what every later layer takes; this is the most expensive decision of the round.

**D7. Matrices with orthonormal columns (Haar).** (a) A measure `haarFrame n k` on
`Matrix n k ℝ`, defined as the law of `polarFactor G` for a standard Gaussian `G`, with the
theorems that it is the unique left-invariant probability measure on matrices with orthonormal
columns and that the QR factor `gramSchmidtQ G` has the same law. (b) The same with the QR factor
as the definition. (c) Mathlib's Haar measure on the orthogonal group pushed to its first `k`
columns, on a bundled Stiefel type (the prototype). *Recommendation (a):* matrix-valued as
consumers hold them, rectangular from the start, and it is literally the normalized Gaussian; (c)
puts the law on a subtype no consumer uses. *Rework:* moderate; every frame theorem cites it.

**D8. Measurable space on matrices.** Keep the global instance `Matrix.instMeasurableSpace`
(product σ-algebra) in `ForMathlib`, with its Borel instance. It mirrors Mathlib's own global
`TopologicalSpace (Matrix m n R)` instance (`Mathlib/Topology/Instances/Matrix.lean`), so the
Borel structure agrees with the topology Mathlib already uses. Alternative: no instance,
transport to `m → n → α` at each use. *Recommendation:* keep. *Rework:* every measurability
statement.

**D9. Cuts.** Not ported unless a consumer appears (§6): the Wishart and hard-edge material
(about 190 declarations serving a `λ_min` tail nothing uses), the localized Freedman interface,
the general-covariance Isserlis machinery, the sparse embedding machinery (next round). Material
with no consumer kept because a user expects it: matrix Bernstein and the intrinsic-dimension
forms, McDiarmid, log-Sobolev and Gaussian Lipschitz concentration, Gaussian comparison
(Slepian, Gordon) behind the extreme singular values. *Rework:* low (cuts can be undone);
listed for the maintainer's information rather than as a hard decision.

## 3. Conventions the stages follow

Subject to §2; repeated here as the working rules.

### 3.1 Statements

- Index types `[Fintype ι]`, generic; no `Fin` versions, no `[NeZero d]` (the degenerate case is
  proved or excluded by a hypothesis on the cardinal).
- Independence by Mathlib's `iIndepFun`, `IndepFun`; identically distributed by `HasLaw` with a
  common law, not `IdentDistrib`, unless the proof needs the latter.
- The Euclidean norm of a vector is `‖WithLp.toLp 2 x‖` (Matrix layer, §5.1); matrix norms are the
  Matrix layer's named functions; eigenvalue extremes are `eigenvalue A 0` and the last index.
- Measurability hypotheses: `Measurable` when the theorem needs it, never both `Measurable` and
  `AEMeasurable`; nothing that `HasLaw` or `HasSubgaussianMGF` already implies.
- Matrix-valued integrals and conditional expectations (entrywise; trace, blocks and the Loewner
  order commute with them; a.s. positive semidefinite integrands have positive semidefinite
  integrals) are a stage of their own (P0): the prototype re-proved them per file.

### 3.2 The junk-value checklist for this round

Before a statement enters a skeleton: does it hold vacuously when the integrand is not
integrable (D3)? when the measure is not a probability measure? when an index is out of range
(`NLAlib/Matrix/Spectral/Eigenvalues.lean`, module docstring)? when a proxy or variance is `0`?
when `t ≤ 0` in a tail? Each answer is either a hypothesis or a sentence in the docstring.

## 4. Stages

Order is a dependency order; each stage gets a design note `docs/design/Probability-<Stage>.md`
or `RandomMatrix-<Stage>.md`. Consumers are from the surveys (counts are prototype files).

- **P0 Vocabulary.** `HasLaw` conventions; matrix-valued integrals and conditional expectations
  (§3.1); tail and moment conversions; isotropy; the measurability file already in
  `Probability/Measurability/Matrix.lean`. Consumers: every later stage.
- **P1 Scalar MGF.** `HasSubgaussianMGF` API Mathlib lacks (monotonicity in the proxy, centring,
  absolute moments, maxima of finite families), `HasSubexponentialMGF` and Bernstein's
  inequality, bounded variables (Mathlib's Hoeffding), Orlicz bridges. Material:
  `P/SubGaussian`, `P/Concentration/Scalar`, `P/Concentration/Basic`.
- **P2 Standard laws.** Gaussian scalars and vectors (Mathlib's `gaussianReal`, `stdGaussian`,
  `Measure.pi`), Rademacher, finite sampling laws; each proved to satisfy the §2 D6 interfaces it
  has, with its exact moments (`m₄ = 3`, `m₄ = 1`). Consumers: 13 files (Rademacher), 5
  (Gaussian vector), 4 (finite sampling). Material: `P/Gaussian/Basic`, `P/Rademacher`,
  `P/Sampling`.
- **P3 Vectors and quadratic forms.** Sub-Gaussian vectors; tails of `‖X‖²` (the χ² bounds as the
  Gaussian case, the Laurent–Massart form for sub-Gaussian vectors, negative moments of χ²);
  Hutchinson mean and variance from isotropy and `m₄`; Hanson–Wright for `quadForm`. Consumers:
  `JL`, `SRHTFlattening`, `HutchinsonTail`, SLQ, CountSketch moments. Material: `P/ChiSquare`,
  `P/Concentration/QuadraticForms`.
- **P4 Concentration of functions.** Entropy and its tensorization, Herbst, Gaussian log-Sobolev,
  Lipschitz functions of a Gaussian vector, bounded differences (McDiarmid); all concluding
  `HasSubgaussianMGF` of the centred function. Material: `P/Concentration/Entropy`,
  `P/Gaussian/Concentration`.
- **P5 Matrix concentration.** `HasMatrixMGFBound`; the Laplace transform method, the master bound
  through Lieb's theorem (Matrix layer: `concaveOn_re_trace_exp_add_cfc_log`), Chernoff, Bernstein,
  matrix series with sub-Gaussian coefficients, intrinsic dimension, rectangular matrices through
  the dilation once; the CGF-level statements that sampling without replacement uses; trace
  moments and noncommutative Khintchine (one recursion for both laws); Freedman last. Consumers:
  leverage sampling and SRHT (Chernoff for sampling), sampling without replacement. Material:
  `P/Concentration/{Matrix,Martingales}`, `P/Gaussian/Moments`.
- **P6 Gaussian calculus and comparison.** Stein's identity (one statement), Slepian,
  Sudakov–Fernique, Gordon, as needed by R3. Material: `P/Gaussian/{Calculus,Comparison}`.
- **R1 Gaussian matrices.** `gaussianMatrix m n` as a law; unitary invariance on both sides,
  blocks and their independence, linear images, a.s. rank. Consumers: 13 files (7 in LowRank).
  Material: `R/Gaussian/{Basic,Invariance}`.
- **R2 Moments.** `E ‖S X T‖_F²` from isotropy of the entries, fourth moments, approximate matrix
  multiplication, conditioning on a block. Material: `R/Gaussian/Moments`.
- **R3 Extreme singular values.** Gordon's bounds and Gaussian concentration for a Gaussian matrix;
  the net argument for independent sub-Gaussian isotropic rows; Chevet. Conclusions in the Matrix
  layer's Loewner form on the Gram matrix (`a • 1 ≤ Xᴴ * X`, `Xᴴ * X ≤ b • 1`), which is what
  the next round's subspace-embedding predicate will be (§5). Material: `R/Gaussian/Spectral`,
  `R/SubGaussian`.
- **R4 Inverse moments.** `E ‖pinv G‖_F²`, `E ‖pinv G‖`, the block-and-pseudoinverse moment of the
  range finder (`E ‖Σ₂ Ω₂ Ω₁⁺‖²`), range frames. Consumers: the range-finder family (R1 to R6 of
  `inventory-sketching.md` §3). Material: the moment half of `R/Gaussian/InverseMoments`.
- **R5 Orthonormal frames (Haar).** `haarFrame n k` (D7), uniqueness, the QR and polar
  constructions, right invariance, the law of a column (uniform on the sphere), moments
  (`E [Q Qᴴ] = (k / n) • 1`, `E Q i j ^ 2 = 1 / n`, fourth moments), concentration of `‖Qᴴ x‖²`
  (Dasgupta–Gupta), and the transfer lemma: a function of `range Ω` has the same law under a
  Gaussian and a Haar test matrix, so the range-finder theorems hold for both. Mostly new
  mathematics: the prototype has 18 declarations here and no consumer. Material: `R/Haar`.

## 5. What the next round needs from this one

From `inventory-sketching.md` §2, §3, §8, §10. This round does not define the sketching
predicates, but its conclusions must be in the shape they will take:

- `IsSubspaceEmbedding S U ε` will be the Loewner sandwich on `(S * U)ᴴ * (S * U)` relative to
  `Uᴴ * U` (Matrix layer, `CONTRIBUTING.md` §5.3 "spectral equivalence"), with separate lower and
  upper parameters in the primary theorems. R3 and R5 state their conclusions in that form.
- Failure probabilities are tails per D3; a "subspace embedding for a fixed subspace with failure
  probability `δ`" and an oblivious version quantify over the subspace outside the tail.
- The moment interfaces the next round will define (`HasJLMoment`, `HasGramTraceMoment`) consume
  P1 and P3; the row-sampling theorem consumes P5's Chernoff for sampling.
- Exports used downstream (counts of prototype files): the Gaussian and Rademacher laws with
  coordinate moments; χ² tails; Hanson–Wright; matrix Chernoff for sampling; Gaussian rotation
  invariance and block laws; inverse moments; a.s. rank; random-start log-overlap moments; range
  frames.

## 6. Not ported

The `_of_hasLaw` twins, `_pmf` copies and per-law corollaries; the `p ≤ 18` moment and other
improvements already subsumed; the Hanson–Wright proof's leaf vocabulary; `lambdaMax`,
`gaussianCovarianceMatrix` and other duplicates of Matrix or Mathlib notions; `Stiefel` as a
bundled type; and, under D9, Wishart and the hard edge, the localized Freedman interface and
general-covariance Isserlis. Docstrings citing the prototype's unpublished project texts (98 of
them) are rewritten against published sources or cite nothing.

## 7. Done

The round is done when every stage is implemented, `NLAlib` and `NLAlibScaffold` build with no
warnings, `scripts/Audit.lean` and `scripts/Lint.lean` are clean, `check_refs.py` passes, the
ledger accounts for the prototype's `Probability/` and `RandomMatrix/`, `docs/port/status.md`
lists what is in `NLAlibScaffold` with a difficulty estimate each, and
`docs/design/Probability-REPORT.md` reports as `Matrix-REPORT.md` did.
