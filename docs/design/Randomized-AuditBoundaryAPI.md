# Randomized boundary and query API repair

The audit repairs preserve the existing distribution and independence interfaces. No registered
program target, lower-bound quantifier, probability hypothesis, or algorithm is weakened.

## Objects and placement

* `Probability/SubExponential/Tail.lean` keeps the existing positive-scale headline and exposes
  its existing Gaussian regime when the scale is zero. A finite-sum corollary consumes this API
  for independent scale-zero subexponential summands. Mathlib's subgaussian MGF interface and
  `hasSubexponentialMGF_zero_iff_hasSubgaussianMGF` already supply the vocabulary bridge.
* `Estimation/Trace/HutchPlusPlusTail.lean` exposes the zero-tail event reduction independently
  of residual-probe laws. Strict thresholds may be zero; a non-strict threshold must be positive.
  The existing nuclear-relative-error theorem consumes the strict form in its zero-tail branch.
* `LowerBounds/QueryModel/TraceEstimation.lean` defines `girardHutchinsonQueryAlgorithm Ω` using
  `QueryAlgorithm`: query j is column j of Ω, and output is the averaged sum of each probe's
  inner product with its response. It has exactly as many query rounds as probe columns and
  never reads A. `Fin q` is required by the ordered history model, not a matrix restriction.
  This object lives at layer 5 because upper-bound layers cannot import LowerBounds.

## Statement shapes and consumers

The zero-tail Hutch++ statement, over finite real square matrices and a finite measure, is
`frobNorm (A - truncatedSVD A r) = 0 → 0 ≤ τ →
 μ.real {ω | τ < |A.trace - hutchpp A (S ω) (G ω)|} ≤
 μ.real {ω | K * frobNorm (A - truncatedSVD A r)^2 <
   frobNorm (A - rsvd A (S ω))^2}`.
It requires no independence: exactness is deterministic on the range-finder good event.

The scale-zero tail is
`HasSubexponentialMGF X v 0 μ → 0 ≤ t →
 μ.real {ω | t ≤ X ω} ≤ exp (-t^2 / (2*v))`.
The sum consumer takes `iIndepFun X μ`, a finite set, and scale-zero MGF hypotheses for its
members. At v=0 it retains the existing total-division convention; no claim about that separate
degeneracy is introduced.

The query bridge proves the nonadaptive property, seeded-family measurability and
`(girardHutchinsonQueryAlgorithm Ω).run A.mulVec = girardHutchinson A Ω` over RCLike.
The unbiasedness corollary integrates the oracle run under the existing isotropy interface,
by rewriting through that equality and applying `integral_girardHutchinson`.
This connects one concrete named estimator to the lower-bound model. It does not assert a new
trace-estimation minimax lower bound or padding theorem for the fixed-pass low-rank results.

## Search, sources and shared machinery

Searches in Mathlib's subgaussian moment API and NLAlib found the Gaussian-regime tail and the
MGF bridge already available; these are reused. No existing Girard–Hutchinson QueryAlgorithm
encoding was found. The run proof reuses `QueryAlgorithm.history_apply` and
`girardHutchinson_eq_sum`; measurable sums/products use Mathlib's standard measurable API.
Hutch++ event comparison uses `hutchpp_eq_trace_of_rsvd_eq` and `measureReal_mono`.
There are no new predicates, numerical constants, or competing spellings for a Mathlib object.

The accompanying documentation repairs state the guarded Gram sandwich, both CountSketch
empty cases, Hermitian-domain eigenvalue continuity, and the established late-GN upper rate.
The tested `measurable_pinv` automation rule receives a `fun_prop` registration.

## Reusable private helpers

The existing Gibbs variational inequality becomes public in `Probability/EntropyTensorization`;
its existing tensorization proof consumes the same declaration. The constant-section-law lemma
moves unchanged to `ForMathlib/MeasureTheory/Measure/Prod` as
`Measure.map_prod_eq_prod_of_ae_map_eq`, where general measure-theory users can find it; the
Gaussian coupling proof imports and consumes it. Mathlib and NLAlib were searched: none.
The concatenated-range equality moves to `ForMathlib/Data/Matrix/ColumnRowPartitioned` as
`Matrix.range_fromCols_eq_sup` and generalizes from real matrices to `CommSemiring`.
It reuses Mathlib's `fromCols_mulVec` and the existing left-range inclusion. Gaussian coupling
uses the new public equality. Mathlib had the action identity and one local public inclusion,
but no full range equality. No parallel declarations remain in the original topic file.

## Common approximate-multiplication to projection-cost bridge

`HasApproximateMatrixMultiplication S A B ε δ μ` is the strict-tail predicate
`μ.real {ω | ε * frobNorm A * frobNorm B <
 frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤ δ`.
It uses a strict event so a zero factor gives an empty failure event, without nonzero-factor
side conditions. The constructor from the existing non-strict tail handles these zero cases once.
There is no Mathlib counterpart (searched); the definition is a named interface for the existing
AMM event, with its constructor as bridge. It lives in Properties/MatrixMultiplication.

A shared `HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasApproximateMatrixMultiplication`
in Properties/ProjectionCost takes a frame, a head embedding, the two AMM properties of its
residual (against itself and the frame), and a JL moment for scalar Frobenius preservation.
It performs the repeated event normalization, frame Frobenius estimate and zero-residual split.
The real JL-moment constructor and the RCLike CountSketch constructor both consume it. Thus the
real-only constant-one polarization theorem is retained while the common geometric step is shared.
No program target, constant, or mathematical conclusion changes.

## Query-space transport and its dimension boundary

`QueryAlgorithm.mapQuery f` sends queries through f while preserving response histories,
round counts and outputs. `history_mapQuery` and `run_mapQuery` prove exact simulation against
the precomposed oracle. Measurability of an algorithm/seeded family and its existing pass labels
are preserved by the corresponding public constructors. No new hypothesis predicate is added.
The real consumer is the Girard–Hutchinson same-dimension reindexing theorem in TraceEstimation:
map queries along a coordinate equivalence, read responses back with comapResponse, and obtain
the original estimator exactly. Mathlib submatrix_mulVec_equiv supplies the matrix-oracle bridge.

This supplies reusable query-model transport needed by future lower-bound dimension wrappers.
By itself this is a same-dimension API. The full padding extension below also supplies factor
compression and optimal-tail transport, and consumes them in arbitrary larger finite dimensions.
Exact-range recovery already quantifies over arbitrary finite ambient d.

## Full sum-type padding extension

The next extension transfers the existing Frobenius Minimax lower bounds to any ambient space
`hard ⊕ extra`, where `hard = k ⊕ (Fin (r+1) × m)` and the same original multiplicity equation,
accuracy cutoff, seed measurability, pass labels and success probability are retained.
`Matrix/Spectral/LowRankPadding.lean` owns the deterministic compression-of-factor-error and
zero-padded-optimal-residual inequalities. They use arbitrary RCLike fields and finite indices;
no new matrix definition is introduced. Mathlib's fromBlocks, existing block-rank/PSD API,
frobNorm_submatrix_le and Eckart–Young are reused (searched, no padding residual theorem found).

`LowerBounds/LowRank/MinimaxPadding.lean` owns the oracle compression and the probability
transfer. Large queries are restricted to the hard summand, small responses padded by zeros,
and returned factors restricted to the hard rows/columns. Exact run simulation is proved using
mapQuery/comapResponse/mapOutput; measurability and pass structure use their public APIs.
PSD input padding is block diagonal. Every successful large-space output compresses to a
successful hard-space output because compressed error contracts and the padded best-rank
residual is at most the original residual. Each of the equispaced and Chebyshev Minimax results
then has a real padded-dimension consumer. This does not yet assert a dimension-free bound:
the ambient space must contain the selected hard dimension, with the original epsilon cutoff.

## Two-input testing through actual seeded transcripts

QueryModel/Testing uses the existing QueryAlgorithm and IsMeasurableFamily interfaces; it adds
no probability predicate. The observable is (seed, response transcript): retaining the seed is
necessary because the algorithm's final output may depend on it. The two input experiments
use the same independent seed law and their respective input laws. A public version of Basic's
existing jointly measurable history lemma makes these observation laws measurable. Le Cam is
then applied to the algorithm's actual decision region and rewritten to actual run errors;
Pinsker gives the second consumer from a finite ENNReal KL budget on those observation laws.
The existing ForMathlib TV/Le Cam/Pinsker tools are reused, with no toReal of an infinite KL.
This supplies a testing interface, not a trace-hard-law KL calculation or a numerical query bound.
