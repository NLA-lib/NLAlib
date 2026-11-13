# Conjugate gradient

Conjugate gradient solves a symmetric positive-definite system through matrix applications,
dot products and vector updates. NLAlib separates the algorithm's update order, the operation
model giving those operations meaning, and the implementations of individual operations.
The certificates describe the actual stored state and its counted execution.

## Algorithms and stopping rules

| Algorithm | Distinguishing choice | Exact total result |
|---|---|---|
| Fixed-horizon Hestenes–Stiefel CG | Recomputes the old residual self-product each round; executes the prescribed horizon | The CG state after k rounds, assuming k does not exceed the initial Krylov grade |
| Carried Hestenes–Stiefel CG | Retains the residual self-product between rounds and tests it before the next round | The CG state at the earlier of the cap and exact convergence |
| Full residual reorthogonalization | Sweeps each new residual against the archived nonzero residuals before forming the next direction | The same exact CG state at the earlier of the cap and exact convergence |
| Preconditioned CG (PCG) | Applies a separately declared inverse preconditioner B to each residual | The PCG state after k rounds under the corresponding grade bound |

These are different algorithm implementations even when their exact mathematical iterates
agree. Retaining a scalar, changing update order, adding projections or changing the stopping
rule changes the actual program and can change its rounded behavior. Choosing exact or
rounded arithmetic is a separate operation-model choice.

The **Krylov grade** is the dimension at which the initial residual's Krylov space stops
growing. For an SPD system, exact CG converges by that grade. A fixed-horizon theorem uses
`k ≤ grade` to justify all executed divisions. The carried and reorthogonalized solvers
instead test the computed residual self-product before another round; their exact theorems
allow any cap and stop at `min(cap, grade)`. A zero initial residual therefore needs no round.

## CG pseudocode

The following shows the carried variant. Operations are abstract; `axpy(a,u,v)` means
`v + a*u`. Canonical zero-start programs write the initial iterate themselves.

```text
x = 0
r = b - matvec(A, x)
p = r
rho = dot(r, r)

repeat at most cap times, while rho > 0:
    q = matvec(A, p)
    alpha = rho / dot(p, q)
    x = axpy(alpha, p, x)
    r = axpy(-alpha, q, r)
    rho_next = dot(r, r)
    beta = rho_next / rho
    p = r + beta*p
    rho = rho_next
return x, r, p, rho
```

The [fixed-horizon program](../../NLAlib/Krylov/CG/HSCG/Alg.lean) computes `dot(r,r)` at
the beginning of each round and uses a fixed loop. The
[carried program](../../NLAlib/Krylov/CG/HSCG/Carried/Alg.lean) stores `rho` and tests it.
The actual direction update uses a temporary vector and counted copies. Initialization
still executes its declared matrix application even when the canonical initial iterate is zero.

The rounded zero-start carried implementation has a separate initializer: after writing
`x = 0`, it copies the raw RHS into `r` and `p`, then computes `rho = dot(r,r)`. Its initial
residual is therefore the supplied RHS, with no rounded subtraction of a zero matvec. The
rounded stored certificate uses this copy initializer and its actual instruction count.

The [reorthogonalized program](../../NLAlib/Krylov/CG/Reorth/Solver.lean) saves the incoming
residual before a round. After the ordinary iterate and residual updates, it inserts:

```text
for each archived residual h:
    r = r - (dot(h, r) / dot(h, h))*h
rho_next = dot(r, r)
p = r + (rho_next/rho)*p
```

Each coefficient uses the currently updated residual: this is a sequential projection sweep.
The history contains nonzero residuals from executed rounds. Its denominators are justified
by the exact SPD analysis. This is distinct from the two classical passes used by
[reorthogonalized Lanczos](Lanczos.md).

## Preconditioning

The [PCG program](../../NLAlib/Krylov/CG/HSPCG/Alg.lean) treats the system A and applied
inverse preconditioner B as separate operators. B approximates the inverse; the program
applies B directly rather than solving a system with a stored preconditioner.

```text
x = 0
r = b - matvec(A, x)
z = matvec(B, r)
p = z
repeat k times:
    rho = dot(r, z)
    q = matvec(A, p)
    alpha = rho / dot(p, q)
    x = x + alpha*p
    r = r - alpha*q
    z = matvec(B, r)
    beta = dot(r, z) / rho
    p = z + beta*p
return x, r, z, p
```

Both matrices are SPD. For the zero-start fixed-horizon certificate, the explicit assumption
is `k ≤ krylovGrade(B*A, B*b)`. The two operator names have separate contracts and resource
charges in the matrix-free model. The stored implementation declares both raw matrices.

## Operation models and implementations

| Model or implementation | What is declared or executed |
|---|---|
| Exact matrix-free | Exact scalar arithmetic, exact BLAS1 and an exact mathematical operator action; PCG declares two actions |
| Exact stored dense | Raw column-major matrix words are supplied as buffers; every matrix application executes scalar multiply/add loops, while BLAS1 remains an explicit exact collection |
| Rounded matrix-free | Scalar relative-error contracts, selected BLAS error allowances and an independent normwise matrix-vector error allowance |
| Rounded stored scalar carried CG | Raw matrix and RHS words; dense matvec and sequential BLAS both execute scalar loops, and their errors follow from the supplied scalar model |
| Sequential or pairwise scalar BLAS profile | A fixed lowering proves the selected vector contracts from scalar operations; an actual linked-tree certificate accounts for that tree's instructions and workspace |

The exact stored target model has scalar and vector names, with no matrix-vector primitive.
A shared context transformation forwards the declared matrix buffer through every procedure.
Its proof reuses the numerical word theorem; the running program performs the dense arithmetic.
A proof-side reference interpretation does not add runtime guards or an alternate solver.

The [standard operation model](../../NLAlib/Ops/Profiles/Standard.lean) keeps scalar rounding,
BLAS reduction scheme and matrix-vector accuracy separate. Its dot allowance scales with the
sum of absolute products, rather than the possibly cancelling dot result. The scalar model
uses unbounded exponents. Storage formats and physical arithmetic require their own bridges;
these exact and standard-model certificates do not claim native IEEE execution.

## Output, assumptions and resources

The exact canonical programs start from supplied RHS words and uninitialized output capacity.
They return the stored iterate, residual and search direction; PCG also returns the
preconditioned residual, and the carried variant retains its self-product. Their output
relations identify the existing pure `cgState` or `pcgState`, rather than merely asserting
that some successful run has a good iterate.

For stored inputs, SPD and grade assumptions concern the decoder of the actual raw words.
The admitted size domain has a genuine joint raw-input witness. This witnesses nonemptiness;
it neither initializes the algorithm's output nor assumes a run succeeds. The fixed-horizon
and PCG grade restrictions differ from the unrestricted caps of carried and reorthogonalized CG.

| Stored endpoint | Supplied resident payload before scratch |
|---|---:|
| Fixed-horizon CG | `n² + 4n` |
| Carried CG | `n² + 4n + 1` |
| Reorthogonalized CG | `n² + 4n` |
| PCG with both dense matrices | `2n² + 5n` |

Scoped history and temporaries are additional scratch. Reorthogonalized CG reserves a residual
history of `cap*n` cells, and its projection budget includes the triangular sum
`cap*(cap+1)/2`. Early exit can execute fewer rounds. The canonical certificates use the
actual transformed tree's complete size-only manifest and peak, including scalar dense
leaves, queries, frames, addressing, allocations and releases. Work and sequential span use
the declared weights on that manifest; supplied matrix and output capacity remain part of
resident memory. These are conservative total bounds in abstract cells, not physical timing
or a sharp adaptive-work claim.

## Rounded guarantees

The [rounded carried certificate](../../NLAlib/Krylov/CG/HSCG/Carried/FinitePrecision/Certificate.lean)
uses the actual computed residual self-product and returned state. Under its explicit
symmetry, spectral interval, error-budget and precision-window assumptions, it gives residual-gap,
physical-energy and backward-model guarantees. Rounded stopping and the exact Krylov grade
are not interchangeable. A zero computed self-product stops the program; its numerical
meaning is supplied by the rounded theorem's hypotheses.

The [rounded stored certificate](../../NLAlib/Krylov/CG/HSCG/Carried/FinitePrecision/StoredCertificate.lean)
also provides `Rounded.Stored.scalarAlgorithm`. Its operation signature contains only scalar
operations: all dense matrix applications and sequential BLAS reductions are actual scalar
loops. The raw matrix is symmetric with spectrum in the admitted positive interval. The
matvec allowance is derived from the scalar roundoff and dimension, and the theorem states
the resulting common-error and accumulated-precision inequalities explicitly. Full instruction,
work, span, scratch and resident-memory bounds are recomputed after both lowerings.

The scalar standard model remains distinct from a finite-format model with overflow and
underflow. This certificate establishes standard-model stored execution, rather than native
IEEE execution. PCG has rounded zero-start initialization, active-step contracts, and
one-step `PCGRun` extraction with actual stored outputs. Spectral windows, precision and a
nonzero RHS supply that first step's guards. These results do not assert a total arbitrary-cap
rounded PCG solver. The reorthogonalized CG canonical certificates currently cover exact arithmetic.

## Checked sources

- Matrix-free exact certificates: [fixed horizon](../../NLAlib/Krylov/CG/HSCG/Certificate.lean),
  [carried](../../NLAlib/Krylov/CG/HSCG/Carried/Certificate.lean),
  [reorthogonalized](../../NLAlib/Krylov/CG/Reorth/Certificate.lean),
  [PCG](../../NLAlib/Krylov/CG/HSPCG/Certificate.lean).
- Exact stored certificates: [fixed horizon](../../NLAlib/Krylov/CG/HSCG/StoredCertificate.lean),
  [carried](../../NLAlib/Krylov/CG/HSCG/Carried/StoredCertificate.lean),
  [reorthogonalized](../../NLAlib/Krylov/CG/Reorth/StoredCertificate.lean),
  [PCG](../../NLAlib/Krylov/CG/HSPCG/StoredCertificate.lean).
- [Exact scalar/vector operation model](../../NLAlib/Ops/Profiles/ExactBlas.lean) and
  [scalar dense matrix application](../../NLAlib/Ops/Profiles/StoredDense.lean).

- Rounded stored scalar carried CG: [canonical certificate](../../NLAlib/Krylov/CG/HSCG/Carried/FinitePrecision/StoredCertificate.lean),
  [actual stored word theorem](../../NLAlib/Krylov/CG/HSCG/Carried/FinitePrecision/StoredWords.lean).
- Rounded PCG local execution: [initialization](../../NLAlib/Krylov/CG/HSPCG/FinitePrecision/Initialization.lean),
  [active step](../../NLAlib/Krylov/CG/HSPCG/FinitePrecision/Step.lean).
