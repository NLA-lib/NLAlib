# Matrix sign iteration and randomized deflation

Matrix sign separates positive and negative spectral subspaces of a Hermitian matrix.
Deflation constructs a basis from a sampled matrix image. NLAlib exposes scalar arithmetic,
sampling and matrix calls as fixed Ops programs, with separate functional and numerical results.

## Capped Newton–Schulz sign

The [program](../../NLAlib/Eigensolvers/Sign/Alg.lean) uses supplied word arithmetic and matrix
multiplication. Complex entries occupy adjacent real/imaginary words, stored by columns.
Hermitian transforms explicitly compute an upper triangle and mirror it.

```text
eta = tolerance / literal(4*n)
X = HermitianScale(A, scale)
square = matmul(X, X)
bad = any component of HermitianShift(square, 1) lies outside [-eta, eta]
repeat at most cap times while bad:
    Y = matmul(X, -HermitianShift(square, 3))
    X = HermitianAverage(Y, 4)
    square = matmul(X, X)
    refresh bad using the same componentwise test
return X
```

The exact-arithmetic update is `X*(3I - X²)/2`. The word program specifies the rounded order
and Hermitian completion. It performs the initial square/test even at cap zero. Reaching
the cap returns the current iterate; the cap itself is not a convergence assumption.

The [canonical word certificate](../../NLAlib/Eigensolvers/Sign/Certification.lean) uses the
[dense functional model](../../NLAlib/Ops/Catalog/Dense.lean). Raw matrix and parameter words,
empty output capacity and distinct decoded zero/one control flags suffice for the exact
mathematical word result, unchanged tape position, cleanup and complete resources. No
successful-run premise is used.

The [accuracy theorem](../../NLAlib/Eigensolvers/Sign/Accuracy.lean) adds Hermitian input,
a positive spectral gap away from zero, a scale bounding the norm, a tolerance `0 < ε ≤ 1/2`,
a justified cap and explicit precision, underflow-floor and range inequalities. It proves
spectral-norm proximity to the matrix sign for the actual returned block, with the same
execution's resources. The [pure analysis](../../NLAlib/Matrix/FinitePrecision/NewtonSchulzSign/Accuracy.lean)
uses these same word functions and matrix routines.

## Randomized deflation

The [standalone program](../../NLAlib/Eigensolvers/Deflation/Alg.lean) draws a square stored
complex sample, calls multiplication and full QR, and copies the requested columns.

```text
Gstored = draw an n-by-n matrix of stored complex sample pairs
Y = matmul(P, Gstored)
(Q, R) = qr(Y)
return the first rank columns of Q
```

The admitted rank satisfies `rank ≤ n`. The word program accepts any square P. Its
[certificate](../../NLAlib/Eigensolvers/Deflation/Certification.lean) proves the actual
sample-dependent result, exactly `2*n²` consumed scalar words, cleanup and all resources.

The [Gaussian theorem](../../NLAlib/Eigensolvers/Deflation/Probability.lean) starts from an
ideal standard complex Gaussian G and supplies the actual stored pairs `normal(G[i,j])`
on the tape. Standard complex Gaussians have real and imaginary variance one-half. An
unscaled pair of standard real Gaussians is not that distribution: normalization, rounding
and sampler cost belong to the selected operation model and are explicit here.

For accuracy, stored P decodes within β of `A = U*S*Vᴴ`, U and V have orthonormal columns
and S is invertible. Primitive multiplication, QR and normal-sampler error contracts and
the original conditioning, precision, floor and range inequalities are explicit. For
`t ≥ 0`, `x > 0`, define

```text
mbar = (||S||₂ + 2) * ||S⁻¹||₂ * sqrt(2) * (2*sqrt(n) + t) / x
```

Under those inequalities, including `mbar*β ≤ 1/5`, full counted-run failure has probability
at most `2*exp(-t²/2) + rank²*x²`. Success includes a stored basis within `6*mbar*β` of `U*W`
in spectral norm for some unitary W, plus every word/resource guarantee of the same run.
Neither successful execution nor an unknown numerical failure bound is assumed.

## Models and resources

| Component | Declared operations | Additional numerical assumptions |
|---|---|---|
| Sign | Scalar words, comparisons, dimension literals, multiplication | Primitive accuracy, spectral gap, scale, precision/range and cap |
| Deflation | Samples, multiplication, full QR, copies | Primitive sampler/matrix accuracy; low-rank factorization, perturbation and conditioning |

Matrix routines act on explicit input blocks. Scalar transforms, tests and copies remain
visible. The [numerical machine adapter](../../NLAlib/Matrix/FinitePrecision/OpsMachine.lean)
exposes the same functions to the mathematics without invoking another evaluator.

Sign reserves `4*n² + 5` stored scratch cells, independently of cap. Its matrix-kernel term
is at most `(2*cap + 1)*T(n)` when T dominates multiplication work. Deflation reserves
`8*n²` stored scratch cells. Primitive workspace is additional and included by the
certificates' `staticPeak` fields.

Full manifests retain scalar loops, comparisons, samples, frames and allocation. Supplied
matrix, parameter and output capacity contributes to resident payload. These are abstract
scalar cells and declared operation charges; physical encodings and native costs are
separate model properties.
