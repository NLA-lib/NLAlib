# Gram–Schmidt orthogonalization

NLAlib separates the algorithm's update order, its operation model and the implementations
of those operations. Modified Gram–Schmidt and two classical passes are different algorithms;
choosing rounded arithmetic is another, independent choice.

## Algorithms and update order

| Algorithm | Coefficients and updates | Checked use |
|---|---|---|
| Rank-revealing modified Gram–Schmidt (MGS) | Each coefficient uses the current residual, which is updated immediately | Full in-place matrix program; Hutch++ sketch basis |
| Two classical passes (CGS2) | Each pass forms its coefficients from that pass's input, applies the updates, then repeats | Reorthogonalized Lanczos and its rounded orthogonality bound |

Both include zero residuals. The exact MGS theorem accepts dependent columns and rectangular
matrices, including zero dimensions.

## MGS pseudocode

The dot products below are Hermitian. Their meaning, and that of vector updates and
normalization, comes from the selected operation model.

```text
Q = input matrix, stored by columns
for j = 0, ..., k-1:
    v = Q[:, j]
    for i = 0, ..., j-1:
        coefficient = dot(Q[:, i], v)
        v = v - coefficient * Q[:, i]
    squared_norm = dot(v, v)
    if squared_norm is nonzero:
        v = v / sqrt(squared_norm)
    Q[:, j] = v
return Q
```

The [Ops implementation](../../NLAlib/Matrix/Factorizations/MGS/Alg.lean) exposes every sweep,
dot, vector update, comparison and normalization. It overwrites the supplied matrix and uses
two scoped scalar cells. Coefficients are temporary; this endpoint returns Q.

The normalization guard is part of the program. Under the exact model, a zero self-dot
identifies a zero residual; a nonzero self-dot justifies square root and division. A zero
residual remains a zero column.

## Model and actual result

The [canonical certificate](../../NLAlib/Matrix/Factorizations/MGS/Certification.lean) uses
`RCLikeBlas`: exact real or complex field arithmetic, Hermitian level-one operations and
real-part comparisons. The local contracts are jointly realized by the declared interpreter.
Their spatial admission keeps reduction outputs separate from inputs. Vector maps permit
disjoint views or exact in-place aliasing, with broadcast coefficients separate from output.
The program's column views and fresh scalar workspace discharge those local conditions.
The initial buffer is the input's column-major storage; its construction runs no orthogonalization.

`MGS.Certification.algorithm` proves total canonical execution. The overwritten buffer equals
the existing mathematical `gramSchmidtQ` result. Nonzero columns are orthonormal, zero columns
represent dependence, and Q Qᴴ is the projector onto the input's column space. The
[mathematical bridge](../../NLAlib/Matrix/Factorizations/MGS/Math.lean) connects the actual
sweeps to that matrix theory. There is no full-rank or successful-run premise.

## Resources and rounded passes

The certificate bounds the complete instrumented manifest: primitive calls, comparisons,
loops, frames, addressing and allocation. Work uses the supplied BLAS costing. In its
zero-primitive-workspace model, an n-by-k matrix occupies `n*k` cells, scratch is exactly
`2` cells, and the resident bound is `n*k + 2`. The
[general workspace theorem](../../NLAlib/Matrix/Factorizations/MGS/Resources.lean) gives
`2 + w` scratch for a common primitive-workspace ceiling w. These are abstract scalar cells;
a linked implementation accounts for its own lower instructions and temporaries.

The [fully scalar implementation](../../NLAlib/Matrix/Factorizations/MGS/ScalarCertification.lean)
expands every vector call into scalar field operations and conjugation. Its operation model
contains no BLAS names. `MGS.ScalarCertification.algorithm` proves the same actual matrix output
with the complete lower instruction count, an independent three-cell scratch bound and
resident payload at most `n*k + 3`. The additional cell is reused by the scalar vector kernels.
Real conjugation can be [implemented by copying](../../NLAlib/Ops/Profiles/RealStar.lean).

The [two-pass implementation](../../NLAlib/Krylov/Lanczos/Reorth/Sweep.lean) used by Lanczos has
an [actual rounded orthogonality theorem](../../NLAlib/Krylov/Lanczos/Reorth/RoundedOrthogonality.lean).
Its dot and sequential-update witnesses, with explicit basis-quality and error-budget
inequalities, imply the existing `IsOrthErr` guarantee. The shared
[pure two-pass algebra](../../NLAlib/Matrix/FinitePrecision/ClassicalGramSchmidt.lean) contains
the one-pass and “twice is enough” results. That rounded CGS2 result and the exact full-matrix
MGS certificate state the guarantees of their respective algorithms and models.
