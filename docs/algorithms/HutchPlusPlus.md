# Hutch++ trace estimation

Hutch++ combines a low-rank trace contribution with a randomized estimate of the residual
trace. NLAlib provides one fixed Ops program, its exact stored-output certificate and a
Gaussian probability bound for that same counted execution.

## Pseudocode

`apply_columns(A,X)` applies the represented operator to each column. MGS is rank revealing:
dependent columns become zero columns and cause no division by zero.

```text
S = draw an n-by-k sketch matrix
Y = apply_columns(A, S)
G = draw an n-by-ell probe matrix
Q = modified_Gram_Schmidt(Y)
H = sweep each probe in G against the columns of Q
AQ = apply_columns(A, Q)
AH = apply_columns(A, H)
return sum_j dot(Q[:,j], AQ[:,j])
       + sum_j dot(H[:,j], AH[:,j]) / ell
```

In exact arithmetic, `H = (I - Q Qᴴ) G`. The
[mathematical bridge](../../NLAlib/Estimation/Trace/HutchPlusPlus/Math.lean) identifies the
actual sweeps and sum with the existing `hutchpp A S G`, including deficient sketch rank.
The [implementation](../../NLAlib/Estimation/Trace/HutchPlusPlus/Alg.lean) releases the temporary
sketch before allocating later workspaces. Its operator batches contain k and k + ell columns.

## Operation and representation choices

The standardized [ExactLinear collection](../../NLAlib/Ops/Profiles/ExactLinear.lean) combines
exact scalar arithmetic, Hermitian level-one operations, explicit-data matrix-vector
application, sampling and dimension literals. Its local functions jointly realize the
contracts; no primitive asserts the Hutch++ conclusion.

| Representation | Declared data | Matrix-vector meaning |
|---|---|---|
| Oracle | Empty data block | Apply the matrix fixed by the model |
| Dense | Column-major matrix words | Apply the matrix decoded from those words |
| Coordinate matrix | Values for a fixed public coordinate pattern | Sum matching entries, including duplicates |

The [stored-operator interface](../../NLAlib/Ops/Catalog/StoredOperator.lean) makes data an
explicit operand. [Dense](../../NLAlib/Ops/Profiles/StoredDense.lean) and
[coordinate](../../NLAlib/Ops/Profiles/StoredCOO.lean) implementations expose scalar loops and
spatial admission conditions. Dot outputs are separate from their inputs, and writable
vector regions do not overwrite broadcast coefficients. The high-level certificate charges
matrix-vector calls using the chosen profile; a linked implementation accounts for its lower
calls and temporaries.

## Total output and resources

The [canonical problem](../../NLAlib/Estimation/Trace/HutchPlusPlus/Specification.lean) supplies
raw operator words and one uninitialized output cell. Positive probe count is the admitted
dimension condition. Row count, sketch width and rank are unrestricted. No estimator is
computed while constructing initial buffers.

`HutchPlusPlus.Certification.algorithm` in the
[certificate](../../NLAlib/Estimation/Trace/HutchPlusPlus/Certification.lean) proves the actual
output is `hutchpp A S G` for its actual sample windows, consumes exactly `n*(k + ell)` words
and releases scoped storage. The hypotheses are the generated primitive contracts and a
common primitive-workspace ceiling, with no successful-run premise.

Its complete manifest bounds calls, comparisons and structural instructions. Work and
sequential span apply declared charges to that manifest. If every primitive workspace is
at most w, the [independent payload bound](../../NLAlib/Estimation/Trace/HutchPlusPlus/Resources.lean) is

```text
scratch  ≤ 2*n*(k + ell) + 2 + w
resident ≤ dataLength(n,n) + 1 + scratch_bound
```

Supplied operator storage and output capacity count toward resident payload. Cells and
charges are abstract; this exact real/complex model assigns no physical word encoding.

## Gaussian accuracy on the same run

The [probability theorem](../../NLAlib/Estimation/Trace/HutchPlusPlus/Probability.lean) assumes
independent standard real Gaussian matrices S and G. The
[sample constructor](../../NLAlib/Estimation/Trace/HutchPlusPlus/Samples.lean) packs S followed
by G, proving that the two adjacent consumed windows decode to precisely those matrices.
Unused positions and streams contain default words; no full infinite iid law is asserted
for this finite construction.

For a real square input A, choose rank r, δ > 0 and absolute tolerance t ≥ 0. The positive
sketch width meets the existing Gaussian embedding bound, and the probe count is positive.
With `E = A - truncatedSVD(A,r)`, `K = subgaussianRangeFinderFactor(1)` and
`c = hansonWrightConstant`, complete counted-run failure has probability at most

```text
δ + 2*exp(-c * min(ell*t² / (K*||E||F²), ell*t / (sqrt(K)*||E||F)))
```

Success includes a stored estimate v with `|trace(A) - v| < t`, the exact word result,
sample advance, cleanup and every count/work/span/payload bound. Total execution comes from
the certificate; the probability theorem adds numerical accuracy. This applies to arbitrary
real square A. Separate pure positive-semidefinite results give relative-trace forms.
