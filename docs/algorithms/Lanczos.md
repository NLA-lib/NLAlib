# Lanczos

Lanczos builds a basis for a Krylov space and a small symmetric tridiagonal representation
of a symmetric operator. NLAlib separates the algorithm variant, the operation contracts,
the implementation of those operations, and the mathematical conclusions about stored output.
An eigenvalue theorem interprets the stored tridiagonal mathematically; the Lanczos program
itself does not run an eigensolver.

## Algorithm variants

| Variant | Order of an active round | Additional stored output |
|---|---|---|
| Ordinary Lanczos | Paige's three-term update, then normalization | Basis and tridiagonal coefficients |
| Full reorthogonalization | The same update, two classical Gram–Schmidt passes, then normalization | The norm of each residual before the passes |

Both variants initialize output tails to zero, accept an iteration cap, and stop when the
computed self-dot used for normalization is zero. Successful execution follows from the
operation and input hypotheses of their total-correctness theorems. The theorem statements
do not assume that an execution has already succeeded.

In exact arithmetic, the two variants produce the same ordinary basis and tridiagonal prefix
for symmetric matrices. Their programs and rounded computations remain distinct.

## Ordinary Lanczos pseudocode

The operations below are abstract. `dot`, `axpy`, `matvec`, square root and normalization have
the contracts selected by the operation model. Here `axpy(a,x,y)` means `y + a*x`.

```text
zero the requested basis and coefficient arrays
previous = 0
sigma = dot(b, b)
if sigma > 0:
    input_norm = sqrt(sigma)
    current = b / input_norm
else:
    return initialized zero outputs
beta = 0

for j = 1, ..., cap, while sigma > 0:
    work = matvec(current)
    work = axpy(-beta, previous, work)
    alpha[j] = dot(current, work)
    work = axpy(-alpha[j], current, work)
    sigma = dot(work, work)
    previous = current
    if sigma > 0:
        beta[j] = sqrt(sigma)
        next = work / beta[j]
    else:
        beta[j] = 0
        next = 0
    store next as the next basis column
    current = next
    beta = beta[j]
```

The implementation guards square roots and division with the positive self-dot branch.
Zero input, zero cap and early breakdown have explicit output meanings. A zero cap still
initializes and, for nonzero input, normalizes the initial basis column.

## Reorthogonalization pseudocode

The full-reorthogonalized variant inserts the following after the raw three-term residual and
before the final self-dot and normalization:

```text
save sqrt(dot(work, work)) if its self-dot is positive; otherwise save zero
repeat twice:
    for every current basis column i:
        coefficient[i] = dot(basis[i], work)
    for every current basis column i:
        work = axpy(-coefficient[i], basis[i], work)
```

Each classical pass forms all coefficients before applying its updates. The second pass uses
the vector produced by the first pass. Coefficient scratch is reused between the passes and
released on return. Local rounded pass results retain the actual coefficient witnesses even
though the program discards their words.

## Operation models

| Choice | Meaning |
|---|---|
| Exact operations | Exact scalar arithmetic, BLAS1 and matvec contracts |
| Abstract rounded BLAS and matvec | Scalar relative-error model, explicit BLAS error allowances, and an independent normwise matvec allowance |
| Sequential standard scheme | The BLAS allowances are proved from sequential reductions in the scalar standard model |
| Pairwise standard scheme | The allowances are proved from pairwise reductions, with the declared recursion-depth applicability condition |

The scalar standard model has unbounded exponents. Matvec accuracy is a separate assumption:
`norm(A*v - computed) ≤ em * specNorm(A) * norm(v)`. The dot-product contract scales its error
by `sum(abs(x[i]*y[i]))`; it is not a relative-error promise with respect to a possibly
cancelling dot-product result. Copy is exact. Storage format, arithmetic behavior and matvec
accuracy are separate choices. These models do not assert a native IEEE implementation.

## Operation counts and storage

For vector dimension `n` and cap `k`, the following are upper bounds on abstract calls.
Early termination can use fewer calls. Initialization is included.

| Operation | Ordinary | Full reorthogonalization |
|---|---:|---:|
| Matvec | `k` | `k` |
| Dot product of length n | `1 + 2k` | `1 + 3k + k(k+1)` |
| AXPY of length n | `2k` | `2k + k(k+1)` |
| Vector copy | `1 + 2k` | `1 + 2k` |
| Vector normalization by a scalar | `1 + k` | `1 + k` |
| Square root | `1 + k` | `1 + 2k` |
| Scalar negation | `2k` | `2k + k(k+1)` |
| Literal zero | `(k+2)n + 2k + 2` | `(k+2)n + 3k + 2` |
| Positivity query | `1 + 2k` | `1 + 3k` |

The basis output contains `(k+1)n` words. The coefficient output contains `2k+2` words for
ordinary Lanczos and `3k+2` words with reorthogonalization. The input contains `n` words.
Ordinary scoped scratch contains `2n+2` words plus the maximum declared primitive workspace.
The reorthogonalized workspace bound is `2n+k+3` words plus its declared primitive workspace
envelope. These quantities distinguish resident inputs and outputs from additional scratch.

The closed call budgets are `solveCount` in each variant's `Alg.lean`; `stmtCost_solve`
proves that each is the corresponding static call budget. Primitive costs depend on the
chosen operation model. Counting one matvec does not declare a dense matrix multiplication
unit-cost, and a matrix captured by an oracle is not certified as free physical storage.
Canonical certificates additionally account for structural instructions, query workspace,
work, span and total modeled memory in the same execution. Their total instruction manifests
are conservative syntactic bounds; a registered closed-form total-work target is a separate
statement. The original operation counts and resident/scratch formulas are explicit. Abstract `.cell` words need a
representation bridge before their charges describe physical machine storage.

## Reading the guarantees

Exact stored basis prefixes equal the canonical Arnoldi basis. Orthonormality applies only
through the Krylov grade; initialized zero padding is not an orthonormal extension.
Stored tridiagonal prefixes give the projected operator and support Ritz-value bounds with
the stated spectral and starting-vector hypotheses.

The ordinary rounded output identifies one actual active run, including every stored vector
and coefficient. Its bounds include matvec rounding and the actual initial-normalization
defect. A rounded Ritz residual bound controls the physical vector formed from the stored
basis and a unit tridiagonal eigenvector. The physical vector is not automatically unit;
turning its residual into an eigenvalue-error estimate requires the corresponding norm
information. Backward-error bounds use their explicit accumulated-precision conditions.

The rounded reorthogonalized total solver retains the actual two-pass intermediate vectors,
coefficient witnesses, local error bounds and saved preorthogonalization norms. Its complete
output uses exactly the executed rounds and initialized zero tails. The proved two-pass
orthogonalization interface derives its numerical allowance from the actual dot and AXPY
chains, with an explicit small-error budget. A small residual-representation defect alone
does not prove strong mutual orthogonality or justify substituting a different matrix-update
implementation's constants. Stronger numerical conclusions use their proved hypotheses.

## Source map

- [Ordinary program](../../NLAlib/Krylov/Lanczos/Alg.lean)
- [Reorthogonalized program](../../NLAlib/Krylov/Lanczos/Reorth/Alg.lean)
- [Packed exact outputs](../../NLAlib/Krylov/Lanczos/Spec.lean)
- [Exact total solver](../../NLAlib/Krylov/Lanczos/Exact.lean)
- [Exact reorthogonalized total solver](../../NLAlib/Krylov/Lanczos/Reorth/Exact.lean)
- [Rounded ordinary total solver](../../NLAlib/Krylov/Lanczos/RoundedSolve.lean)
- [Standard operation model](../../NLAlib/Krylov/Lanczos/RoundedModels.lean)
- [Rounded backward error](../../NLAlib/Krylov/Lanczos/RoundedStability.lean)

- [Exact stored-output Ritz bounds](../../NLAlib/Krylov/Lanczos/Basis.lean)
- [Exact reorthogonalized stored-output bounds](../../NLAlib/Krylov/Lanczos/Reorth/Basis.lean)
- [Rounded physical Ritz residual](../../NLAlib/Krylov/Lanczos/RoundedRitz.lean)
- [Rounded reorthogonalized total solver](../../NLAlib/Krylov/Lanczos/Reorth/RoundedSolve.lean)
- [Reorthogonalized standard models](../../NLAlib/Krylov/Lanczos/Reorth/RoundedModels.lean)
- [Actual two-pass error bound](../../NLAlib/Krylov/Lanczos/Reorth/RoundedOrthogonality.lean)

## Canonical certificates

Both ordinary and fully reorthogonalized Lanczos have `Certification.algorithm` constructors.
They use a fixed program and a jointly realized standard operation model. Their specifications
combine the actual rounded output with an independently computed, size-only instrumented
manifest. Work and sequential span apply the declared weights to that complete manifest.
Resident memory includes every supplied input and output slot, including uninitialized slots;
scoped scratch and the core query reservation are added separately.

The ordinary `Certification.ritzAlgorithm` strengthens the numerical postcondition with the
physical Ritz residual result using `Algorithm.mapPost`. It retains the same program and every
resource bound. Zero cap and zero input have their explicit original outcomes.

- [Ordinary canonical certificate](../../NLAlib/Krylov/Lanczos/Certificate.lean)
- [Reorthogonalized canonical certificate](../../NLAlib/Krylov/Lanczos/Reorth/Certificate.lean)
- [Canonical Ritz consequence](../../NLAlib/Krylov/Lanczos/RitzCertificate.lean)

These base certificates describe the abstract BLAS trees. Proved BLAS implementations derive
the model's accuracy contracts, while a canonical certificate for a scalar lowering separately
checks the fully lowered tree and recomputes its full instruction/workspace manifest.

The [actual sequential scalar certificate](../../NLAlib/Krylov/Lanczos/LinkedCertificate.lean)
checks the precise tree produced by the sequential implementation table. Its reduction error
budgets come from the scalar unit roundoff, independently of the high-level BLAS scheme. Its
Ritz postcondition is strengthened by `SequentialCertification.ritzAlgorithm`, preserving that
lowered tree's own full resource specification. Pairwise profile transfer retains its explicit
applicability and conditional budgets; this sequential certificate does not certify a different
pairwise scalar tree.

For rounded full reorthogonalization, the strongest run interface applies to the longest
leading prefix satisfying the selected strict test `tau * saved_raw_norm < beta`. This is an
analysis of the returned data; the program still uses its original zero-norm stopping rule.
The prefix may be empty or shorter than the executed history. The next excluded step has
`beta <= tau * saved_raw_norm`. Every retained numerical-run parameter and vector/coefficient
sequence refers to the same archived data. Size-only fixed-point and recurrence precision
windows support spectral bounds for the nonempty selected tridiagonal.

- [Actual admissible-prefix run](../../NLAlib/Krylov/Lanczos/Reorth/RoundedStability.lean)
- [Actual rounded prefix spectral bound](../../NLAlib/Krylov/Lanczos/Reorth/RoundedSpectral.lean)
