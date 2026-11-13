# Randomized spectral bisection

Spectral bisection approximates the diagonalization of a Hermitian matrix by repeatedly
splitting its spectrum. The implementation stores node matrices, bases and outputs in arenas,
processes one depth at a time, and assembles the children on the way back up.

The fixed [Ops program](../../NLAlib/Eigensolvers/SpectralBisection/Alg.lean) has a checked
[total execution theorem](../../NLAlib/Eigensolvers/SpectralBisection/Solve.lean) and
[output/resource certificate](../../NLAlib/Eigensolvers/SpectralBisection/WorkCertification.lean).
Its returned words equal the existing
[mathematical eigensolver](../../NLAlib/Matrix/FinitePrecision/SpectralBisection.lean)
using the same arithmetic,
matrix routines and tape. Numerical accuracy follows separately from the numerical reference
bound and its [transfer to the counted execution](../../NLAlib/Eigensolvers/SpectralBisection/ProbabilityTransfer.lean).

## Algorithm and implementation

At an active node with matrix A, radius R, tolerance ε and depth counter ℓ:

```text
if the node has size one:
    return an identity basis and the real diagonal values
if its window is sufficiently small:
    return an identity basis and zero values
choose a shift using the stored uniform sample and radius R/ℓ
B = sign(A - shift I), using capped Newton–Schulz iteration
P+ = (B + I)/2; P- = -(B - I)/2
k+ = clamp(floor(rounded_trace(P+) + rounded_half), 0, size(A))
if k+ is zero or size(A):
    continue with the corresponding shifted child
otherwise:
    form bases Q+ and Q- by sampled projection and QR
    compress A onto each basis and shift the two child matrices
process the children
assemble their computed bases and shifted values
```

Each scalar operation uses the supplied word function, including the computation of one-half
and accumulation of the trace. Matrix multiplication and full QR are matrix-level primitives.
Hermitian shifts, averages, scaling, conjugate transposes, traces, copies, sampling, metadata
writes and bounded conversions remain visible in the tree. Sign and node procedures expand
through frames; neither is an opaque primitive asserting the algorithm's conclusion.

Complex entries use adjacent real and imaginary words, stored by columns. For root size n,
a size-k node owns k slots in its level, each reserving 2n words. Its square matrix uses
2k² words within that reservation. Mathematical slot intervals supply memory separation and
the checked superadditive kernel-cost lemma.

## Total execution and the operation model

[DenseOp](../../NLAlib/Ops/Catalog/Dense.lean) combines scalar arithmetic, dimension literals,
multiplication/QR and explicit draws. Queries compare decoded scalar words or take their
natural floor. A bounded conversion checks its declared bound.

The generated dense functional model gives one jointly realized collection of local contracts.
`writes_solve` assumes these primitive contracts, readable matrix/parameter blocks, live handles,
separate source blocks, writable separate outputs, and exact decoding of natural literals
through `max n 4`. Outputs may overlap the source regions because the final copies follow all
source reads. Under those premises it guarantees total execution, the mathematical word result,
exact tape advancement and release of scoped scratch. It assumes no successful run.

The canonical problem supplies four separate buffers: raw matrix words, three parameter words,
and empty basis/value output capacity. Its initial memory performs no numerical preprocessing.
`workCertifiedAlgorithm` certifies this same fixed program for every admitted raw input and tape,
with the word result, full instruction count, independent storage bound and matrix-work estimate
below. The admitted root dimensions are at least two; bounded literal exactness and the stated
matrix-cost assumptions are explicit. No premise assumes a WP or successful execution.
The general `certifiedAlgorithm` adapter also supports other supplied resource bounds.

## Resources and their scope

Let n be the root dimension, L the depth parameter and cap the sign-iteration cap.
The certificate uses a monotone superadditive cost T that dominates each matrix primitive's
work at its largest dimension. Each nonleaf node of size k contributes at most
`(2cap + 9)T(k)` matrix-kernel work; reconstruction contributes at most `2T(k)`.
The actual nodes occupy disjoint slot intervals, so their costs sum to at most one root-size
cost per level. The complete bound is

```text
work, sequential span ≤ H(n,L,cap) + (L + 1)(2cap + 11)T(n)
```

Here H is the zero-matrix-work profile applied to `staticBudget`: it retains the conservative
charges for scalar arithmetic, samples, literals, queries, addressing, control flow, frames
and allocation. Matrix work is taken from the actual original-operation count of that same
instrumented execution. The full instruction budget remains conservative. This is a complete
certificate with a partition-sensitive matrix term; it does not assert an optimal total
complexity for fast matrix multiplication.

The matrix-cost domination is global over dimension lists, including empty and all-zero
lists. Superadditivity forces `T(0) = 0`, so matrix costs at those lists must vanish for this
certificate. `manifestAlgorithm` remains available for the full static manifest without
these additional cost assumptions.

The [independent storage bound](../../NLAlib/Eigensolvers/SpectralBisection/StoragePolynomial.lean)
for n ≥ 2 is

```text
scratch  ≤ 6n²L + 32n² + 4nL + 7n + 2L + 24 + E(n)
resident ≤ 6n²L + 36n² + 4nL + 8n + 2L + 27 + E(n)
```

`E(n) = MatrixOp.workspaceEnvelope W n` is one finite maximum of the chosen matrix-workspace
function W over multiplication triples and QR pairs with dimensions at most n. The fixed
program's static-support proof covers every such call, including all bounded query choices.
W needs neither monotonicity nor a global ceiling. Supplied buffers contribute `4n² + n + 3`
abstract cells to resident capacity. Neither storage polynomial grows with cap.

## Randomness, stopping and numerical accuracy

Every downward level draws n uniform words followed by 4n² Gaussian words, including levels
with no active nodes. The complete solver consumes exactly `(L + 1)(n + 4n²)` words. The
coordinate correspondence accounts for any fixed initial tape position. Independence and
distribution belong to the tape law and are separate from functional execution.

The sign iteration returns its current iterate at its cap. At the depth boundary, the program
writes identity bases and zero values. Both cases produce defined outputs; neither alone
establishes numerical accuracy. The numerical reference theorem requires its stated positive
dimension, Hermitian input, radius, precision, depth, sign-cap, sampler and tape-law assumptions.
The probability transfer retains the same actual output and all resource bounds, and includes
execution or resource failure in its failure event without assuming success.

The numerical bridge retains the original analysis's explicit nonnegative absolute-error floor
and its smallness bound. The standard relative-error specialization uses floor zero. A
bounded-exponent model must separately establish its primitive accuracy and range assumptions.
The resource profile counts abstract scalar cells and operation units. A physical IEEE
implementation additionally needs finite encodings, exceptional-value/comparison semantics
and an interpretation/resource proof; this certificate makes no such hardware claim.
