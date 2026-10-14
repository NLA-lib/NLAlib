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

Each with the alternatives and a recommendation; "rework" says what changing it later would cost.
Reviewed by a Fable agent on 2026-10-14; its corrections are folded in (D2, D3, D5, D6, D7) and
it added D10.

**D1. Scope.** (a) Probability and RandomMatrix in one round, as above, with a design checkpoint
for the maintainer after P3 (scalar, vector and quadratic-form concentration done, before matrix
concentration and the random-matrix stages); (b) Probability alone, RandomMatrix designed later.
*Recommendation (a):* the Gaussian and Haar laws, their invariance and their moments are the same
objects at vector and matrix level, and one interface per property is a cross-layer design.
*Rework:* low for the choice; high if (b) produces interfaces RandomMatrix cannot use.

**D2. How randomness appears in statements.** Every statement of the round follows these.
- Random variables, not canonical spaces: a theorem takes `X : Ω → E` with Mathlib's
  `HasLaw X ν μ` (or a property such as `HasSubgaussianMGF`); the measure form is `HasLaw.id`,
  never a twin (the prototype has 50). Discrete laws are measures; `PMF` is only a constructor.
- "i.i.d. with law `ν`" is the single hypothesis `HasLaw X (Measure.pi fun _ => ν) μ`, which
  Mathlib equates with independence plus marginals (`iIndepFun_iff_hasLaw_pi_pi`). A matrix with
  i.i.d. entries is `HasLaw X (gaussianMatrix m n) μ`, `gaussianMatrix` being the nested
  `Measure.pi`. Independent coordinates with a property (not a law) stay two hypotheses:
  `iIndepFun (fun i ω => X ω i) μ` and `∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ`.
- Proxies, variances and other scale parameters are `ℝ≥0`, as in Mathlib's `HasSubgaussianMGF`;
  everything else is `ℝ`. The prototype's `⟨K ^ 2, _⟩` (30 statements) is not used.
- `[IsProbabilityMeasure μ]` is assumed only when nothing else implies it (`HasLaw X ν μ` with a
  probability `ν` does, as a lemma).
- Measurability: `HasLaw` gives `AEMeasurable` only, so `Measurable X` beside it is not
  redundant when a proof needs it (`CONTRIBUTING.md` §5.2's example is corrected accordingly).
Alternative: state on the canonical measure with `_of_hasLaw` corollaries (the prototype).
*Recommendation:* as listed. *Rework:* every statement.

**D3. Tails and expectations.**
- Tails in failure form, real-valued, non-strict events: `μ.real {ω | t ≤ f ω} ≤ bound`,
  `μ.real {ω | f ω ≤ t}`, `μ.real {ω | t ≤ |f ω - m|}`. Never the success form `1 - δ ≤ …`. A
  non-strict event is the stronger statement, and `μ.real` of a non-measurable set is its outer
  measure, so no measurability hypothesis on the event. Mathlib's Chernoff bound
  `measure_ge_le_exp_mul_mgf` is in `ℝ≥0∞`; P0 provides the `μ.real` bridge.
- Expectations are Bochner integrals. **Every upper bound `∫ f ≤ B` comes with integrability**:
  as its own theorem (`integrable_…`, then `integral_…_le`, Mathlib's pattern), or as an API lemma
  when a hypothesis already gives it (`HasSubgaussianMGF` gives `MemLp`). Reason: the Bochner
  integral of a non-integrable function is `0`, so for nonnegative `f` the bound alone holds
  whenever `B ≥ 0` and says nothing, the same hazard as the out-of-range eigenvalue
  (`Mathlib-deviations.md` §1). Lower bounds `B ≤ ∫ f` are false, not vacuous, without
  integrability, so there integrability is a hypothesis. Alternative: `∫⁻` in `ℝ≥0∞` (no junk
  value, no subtraction or variance). *Recommendation:* Bochner with the companion; `∫⁻` only
  where finiteness is the question.
- A second junk value: `μ.real s = 0` when `μ s = ∞`, so a tail bound on a measure that is not
  finite is vacuous; probability or finiteness is a hypothesis wherever it is not implied (§3.2).
*Rework:* every quantitative statement.

**D4. Fields.** Random scalars and random vectors are real (`Ω → ℝ`, `Ω → n → ℝ`). Matrix
concentration is over `𝕜`: sums of random Hermitian matrices over `𝕜`, real random coefficients
times deterministic matrices over `𝕜`. Random-matrix laws (Gaussian matrices, Haar frames) are
defined over `ℝ` in this round; the interfaces they satisfy (isotropy, invariance, frames) are
stated over `𝕜`, so complex Gaussian and complex Haar laws are later instances, not redesigns.
*Recommendation:* as stated. *Rework:* high for the interfaces, low for the laws.

**D5. Numerical bounds and naming.** Bounds begin in this round; later improvements and new
proofs with incomparable bounds must fit without renaming. Proposed rules (to replace the
"constants" item of `CONTRIBUTING.md` §5.2 and extend §4 when approved):
1. **A name says what the statement is, never how good it is.** No `_sharp`, `_improved`,
   `_tight`, `_v2`. Classical names are kept where the subject uses them (`bernstein`,
   `hoeffding`, `mcdiarmid`, `hansonWright`, `freedman`, `gordon`).
2. **Constants and tail functions are definitions**: `hansonWrightConstant : ℝ`,
   `matrixBernsteinTail d v L t : ℝ`. The docstring gives the source's value, the value proved and
   the gap. Each comes with the API consumers are allowed to use, chosen to stay true when the bound
   improves: positivity, monotonicity where a consumer inverts the tail, and a one-sided explicit
   comparison (`1 / (256 * exp 2) ≤ hansonWrightConstant`;
   `matrixBernsteinTail d v L t ≤ 2 * d * exp (…)`). An improvement of the same shape changes the
   body and the comparison lemma, no statement and no name. *Sub-choice:* `irreducible_def`,
   which makes the API the only access (it works with `rw [foo_def]`, `norm_num [foo_def]`,
   `positivity` given `foo_pos`), or a plain `def` with the API kept by review (what Mathlib
   usually does). *Recommendation:* `irreducible_def`, because agents unfold what they can.
3. **Incomparable bounds coexist**, each named by what distinguishes it: its hypothesis
   (`_of_bounded`, `_of_variance_le`) or the parameter its bound is in (`_intrinsicDim` against
   the dimension form). Each docstring says in which regime it wins and names the other.
4. **No automatic "best of" statement.** A theorem whose bound is the minimum of two others is
   added only when both have identical hypotheses and side conditions. (The draft proposed one
   canonical minimum per result; the review showed it is unusable in general: matrix Bernstein's
   intrinsic form takes a matrix `V` and a threshold on `t`, so the minimum of the two tails needs
   the stronger hypotheses and a piecewise tail that no one can invert or cite.)
5. **A dominated result** (the new bound is at least as good in every regime) is reproved from the
   new one and keeps its name if consumers cite its simpler form; otherwise `@[deprecated]`, and
   removed after a release.
6. **Tail before sample size** (`CONTRIBUTING.md` §5.2): the sample size is a named definition with
   its API; a sufficient-size corollary of each tail.
*Rework:* every quantitative statement in this round and the next.

**D6. The property interfaces** (`CONTRIBUTING.md` §5.4). Every theorem of the round takes one of
these or a Mathlib notion, never a raw bundle. Names are proposals.

| Interface | Form | Instances | Consumers |
|---|---|---|---|
| sub-Gaussian scalar | Mathlib's `HasSubgaussianMGF X c μ`, `c : ℝ≥0` | Gaussian, Rademacher, bounded centred, Lipschitz images of a Gaussian | tails, maxima, Hoeffding, series |
| sub-exponential scalar | `HasSubexponentialMGF X v b μ`, `v b : ℝ≥0`, fields as Mathlib's: `exp (l * X)` integrable and `mgf X μ l ≤ exp (v * l ^ 2 / 2)` for `b * |l| < 1` (so `b = 0` is the sub-Gaussian case) | Bernstein condition, centred squares, ψ₁ | Bernstein, Hanson–Wright |
| sub-Gaussian vector | `IsSubgaussianVector X c μ` for `X : Ω → n → ℝ`: every `u ⬝ᵥ X ω` has `HasSubgaussianMGF` with proxy `c * ‖WithLp.toLp 2 u‖₊ ^ 2` | Gaussian, Rademacher, independent sub-Gaussian coordinates | χ²-type tails, nets (a matrix through its entries), JL, rows |
| isotropy | `IsIsotropic X μ` for `X : Ω → n → 𝕜`: `MemLp 2` coordinates and `∫ X i * star (X j) = if i = j then 1 else 0` | Gaussian, Rademacher, sphere of radius `√n`, rescaled Haar columns, SRHT rows | Hutchinson, `E ‖S X T‖_F²`, AMM |
| matrix MGF bound | `HasMatrixMGFBound X g A s μ`: a.s. Hermitian, `exp (θ • X)` integrable and `∫ exp (θ • X ω) ≤ exp (g θ • A)` in the Loewner order, for `θ ∈ s` (spelling of `∫` by D10) | bounded (Chernoff, Bernstein), sub-Gaussian coefficients (series) | one master tail; sampling without replacement; conditional form for Freedman as in Mathlib's `HasCondSubgaussianMGF` |
| unitary invariance | `IsLeftUnitarilyInvariant ν` (and right): `ν.map (U * ·) = ν` for every `U` with `HasOrthonormalCols U` square | Gaussian matrices, Haar frames | block laws, inverse moments, transfer, Haar moments |

Not interfaces, by design: random frames are three Mathlib-form hypotheses, `Measurable Q`,
`∀ᵐ ω, HasOrthonormalCols (Q ω)`, `IndepFun Q Ψ μ`, bundled nowhere; concentration of a function
concludes Mathlib's `HasSubgaussianMGF (fun ω => f (X ω) - ∫ f ∘ X)`; fixed moments
(`∫ X i ^ 4 = m₄`) and independence are parameters beside an interface. *Rework:* these are what
every later layer takes; the most expensive decision of the round.

**D7. Matrices with orthonormal columns (Haar).** (a) A measure `haarFrame n k` on
`Matrix n k ℝ`, defined as the law of `polarFactor G` for a standard Gaussian `G`
(`card k ≤ card n` where orthonormality is claimed); left invariance from `polarFactor_mul_left`
and Gaussian invariance; right invariance from a new Matrix lemma
`polarFactor (A * V) = polarFactor A * V` for unitary `V`; moments and the law of a column
derived from invariance alone (a matrix commuting with every unitary is scalar); uniqueness (Haar
on the unitary group, which needs `CompactSpace` proved and an averaging argument) only for the
theorem that the QR factor `gramSchmidtQ G` has the same law. (b) The QR factor as the definition.
(c) Mathlib's Haar measure on the orthogonal group pushed to `k` columns on a bundled Stiefel type
(the prototype). *Recommendation (a):* matrix-valued as consumers hold it, rectangular from the
start, literally the normalized Gaussian, and the transfer lemma is immediate because
`range (polarFactor G) = range G` at full rank. *Rework:* moderate.

**D8. Measurable space on matrices.** Keep the global instance `Matrix.instMeasurableSpace`
(product σ-algebra) in `ForMathlib`, with its Borel instance, mirroring Mathlib's own global
`TopologicalSpace (Matrix m n R)` (`Mathlib/Topology/Instances/Matrix.lean`). Alternative: no
instance, transport to `m → n → α` at each use. *Recommendation:* keep, and close entry 12 of
`Mathlib-deviations.md`. *Rework:* every measurability statement.

**D9. Cuts.** Not ported unless a consumer appears (§6): Wishart and the hard edge (about 190
declarations serving a `λ_min` tail nothing uses), the localized Freedman interface,
general-covariance Isserlis, the sparse embedding machinery (next round). Kept although no
survey consumer uses them, because a user expects them: matrix Bernstein and intrinsic-dimension
forms, Gaussian comparison (behind R3), Gaussian Lipschitz concentration (behind R3's tails).
Entropy in general and McDiarmid go to the end of the round (P7) and may be scaffolded.
*Rework:* low; listed for information.

**D10. Integrals and conditional expectations of matrix-valued functions** (added by the review).
`∫ ω, X ω ∂μ` for `X : Ω → Matrix m n 𝕜` needs a normed-space instance on matrices, and Mathlib
has only scoped ones (`Matrix.Norms.Frobenius`, `.Elementwise`, `.L2Operator`), so
`E [Q Qᴴ] = (k / n) • 1`, the matrix MGF bound and every matrix expectation depend on how this is
spelled. (a) **One library-wide scope, `open scoped Matrix.Norms.Frobenius`**, in every file that
integrates matrices: every shape, an inner product space, so Mathlib's integral, conditional
expectation and Jensen API applies directly; P0 adds the scope-independent bridges
(`(∫ X ∂μ) i j = ∫ ω, X ω i j ∂μ`, integrability iff entrywise). (b) **Entrywise**, the term
`Matrix.of fun i j => ∫ ω, X ω i j ∂μ` or a named `matrixIntegral μ X`, instance-free, with the
linearity, trace, Loewner and conditional-expectation API rebuilt entrywise. *Recommendation (a):*
the norm itself never appears in statements, only the integral, whose value does not depend on
which norm is chosen; Mathlib's conditional expectation and Jensen are too much to rebuild. It is
a deviation (statements under a scope) and gets an entry in `Mathlib-deviations.md`.
*Rework:* every matrix expectation and every matrix concentration statement.

## 3. Conventions the stages follow

Subject to §2; the working rules beyond it.

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
- **P4 Gaussian concentration of functions.** Lipschitz functions of a Gaussian vector, through
  the Gaussian log-Sobolev inequality and Herbst's argument, concluding `HasSubgaussianMGF` of the
  centred function. Consumer: R3's tails. Material: `P/Gaussian/Concentration`, the part of
  `P/Concentration/Entropy` the Gaussian proof needs.
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
- **P7 Remaining concentration** (D9). Entropy and its tensorization in general, bounded
  differences (McDiarmid), scalar Bernstein in ψ₁ form if P1 does not already give it; no
  consumer in either survey; may be scaffolded.

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
