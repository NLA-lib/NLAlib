# Rank-revealing MGS and Hutch++ in Ops

The library implements full modified Gram–Schmidt and Hutch++ as fixed programs over
local operations. Their total certificates return the existing mathematical
`gramSchmidtQ` and `hutchpp`, together with cleanup, sample consumption and resource
bounds for the same counted execution.

## Algorithms and operation models

Full MGS sweeps each column against the previously normalized columns. It computes the
residual's Hermitian squared norm and compares its real part with zero. A zero residual
stays zero; a nonzero residual is divided by its positive real norm. Dependent columns,
empty matrices and matrices with more columns than rows are included. The theorem does
not require full rank or assume that execution succeeds.

The [exact BLAS model](../../NLAlib/Ops/Catalog/RCLikeBlas.lean) uses Hermitian `dot`,
`axpy` as `y + a*x`, and `scal` as division by `a`. Square roots embed the nonnegative
real square root; comparisons observe real parts. These contracts are jointly realized
for real and complex words. Reduction outputs are separate from their inputs. Maps
admit exact alias or disjoint views, and scalar coefficients remain separate from outputs.
This admission policy is an operation-model choice that supports streamed implementations.

The [scalar profile](../../NLAlib/Ops/Profiles/RCLikeScalar.lean) expands all six vector
operations into visible scalar loops. A Hermitian dot uses one temporary cell and explicit
scalar conjugation. Over real words, [conjugation lowers to copying](../../NLAlib/Ops/Profiles/RealStar.lean).
Complex words here are abstract field elements; this is not a physical complex-number
layout or an IEEE implementation. The [fully scalar MGS certificate](../../NLAlib/Matrix/Factorizations/MGS/ScalarCertification.lean)
retains the arbitrary-rank result with three scratch cells, independently of dimensions.

Hutch++ draws a sketch and a probe block, forms `A*S`, computes its full MGS basis, and
projects each probe away from that basis. It applies the operator to the basis and the
projected probes, then adds the low-rank trace term and the averaged residual term.
The canonical estimator requires a positive probe count; sketch width and matrix dimension
may be zero. Rank deficiency of `A*S` is allowed: zero basis columns preserve the identity
`Q*Qᴴ = rangeProjector (A*S)` used by the trace proof.

The [stored-operator interface](../../NLAlib/Ops/Catalog/StoredOperator.lean) declares both
matrix data and vector inputs. An oracle model needs no stored entries. Dense storage
supplies column-major entries. COO supplies values for a fixed public index pattern;
duplicates add, and entries outside the current shape are ignored. The pattern fixes one
program before runtime dimensions and values. Outputs are disjoint from data and input
vectors. The [dense](../../NLAlib/Ops/Profiles/StoredDense.lean) and
[COO](../../NLAlib/Ops/Profiles/StoredCOO.lean) implementations expose scalar arithmetic and
use one temporary cell. They do not hide matrix-vector multiplication inside a new primitive.

## Mathematical and storage proofs

A column-major width-one codec connects raw words to matrices. The MGS invariant is the
matrix whose completed columns equal `gramSchmidtQ A` and whose remaining columns are
unchanged. Its inner loop uses `mgsSweep`. The residual identity and the nonnegative
diagonal of `gramSchmidtR` justify normalization, including the zero branch.

The Hutch++ proof uses existing projector and trace identities. Invariants are ordinary
vectors, matrices and scalar sums. Shared column-update, loop, frame, allocation and
linking rules carry the storage bookkeeping. The temporary sketch is released before
the later operator-output matrix is allocated. Pure mathematical facts remain independent
of the execution language.

The checked implementations are in [MGS](../../NLAlib/Matrix/Factorizations/MGS/Alg.lean)
and [HutchPlusPlus](../../NLAlib/Estimation/Trace/HutchPlusPlus/Alg.lean).
Their [MGS](../../NLAlib/Matrix/Factorizations/MGS/Certification.lean) and
[Hutch++](../../NLAlib/Estimation/Trace/HutchPlusPlus/Certification.lean) canonical certificates
fix the program before dimensions, raw buffers and the tape. Primitive meanings, admitted
storage and dimensions are explicit premises; whole-program correctness and successful
execution are conclusions.

## Resources and probability

The Hutch++ source performs two batches totaling `2*k + ell` operator applications and
draws exactly `n*(k + ell)` words. Its independently proved scratch bound is
`2*n*(k + ell) + 2 + w` under a common primitive-workspace ceiling `w`. The stored
payload peak is exactly `2*n*(k + ell) + 2`; temporaries from earlier phases do not add
to it. Input data and the scalar output count separately toward resident memory.
The original BLAS-level MGS uses two scratch cells; its scalar lowering needs three.

Canonical resource bounds include scalar, vector and operator calls, samples, queries and
structural instructions. Complete static manifests provide conservative size-only work
and sequential-span bounds. These manifests are distinct from independent storage bounds
and exact primitive-count formulas. A lowering's own workspace and counted instructions
must be included when selecting the implementing operation model.

The [Gaussian probability theorem](../../NLAlib/Estimation/Trace/HutchPlusPlus/Probability.lean)
reuses the existing real Gaussian Hutch++ tail bound. Independent Gaussian matrices are
packed into adjacent tape windows, whose decoded matrices agree exactly with those used
in the numerical theorem. The total canonical certificate transfers the bound to actual
stored output and resource failure on the same execution. Gaussian laws and the numerical
dimension and tolerance assumptions remain explicit. This exact-arithmetic theorem does
not assert a rounded Hutch++ guarantee or physical IEEE execution.
