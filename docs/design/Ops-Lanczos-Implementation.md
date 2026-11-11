# Lanczos over Ops

The ordinary and fully reorthogonalized programs share the existing pure Lanczos recurrence
and the operator/scalar/BLAS/decoded-comparison contracts. Old program proofs are not reused.
The ordinary implementation belongs to `NLAlib/Krylov/Lanczos`; reorthogonalization belongs to
its `Reorth` subfolder. All declarations are ordinary modules; target registration is excluded.

The complete header has dimensions `n,cap`, input `B[n]`, and outputs `V[n*(cap+1)]` and
`C[2*cap+2]`. V is column-major. C stores alpha at indices below cap, beta_j at cap+j for
0≤j≤cap, and the input norm at 2*cap+1. Reorthogonalization keeps this prefix and may extend C.
The Output predicate states these stored values against the established Lanczos recurrence.
A Hermitian-matrix corollary identifies V with the canonical Arnoldi/Lanczos basis.

Outputs are initialized to zero. Scoped Prev[n], Work[n], and t[2] hold the previous direction,
raw product/residual, squared-norm guard, and negative coefficient. Initialization computes
B·B. A positive guard permits sqrt, copying, and normalization; otherwise the initialized zero
column and norm remain. Each active round follows Paige's order: matvec, previous-direction
update, alpha dot, current-direction update, residual self-dot, save current as Prev, and the
same guarded normalization. Full reorthogonalization inserts its two classical passes before
the final self-dot. No zero norm is passed to sqrt or division.

A whileFuel loop stops before another active round at zero squared norm. Its invariant records
the computed prefixes, zero future entries, previous direction, and equivalence between a
positive guard and nonzero current direction. A zero-current/zero-beta recurrence has a zero
basis/coefficient tail, so early exit satisfies the full requested output, including initially
zero input and zero dimension. No theorem assumes that execution succeeded.

Block certificates isolate zero fill, guarded normalization, and the borrowed-workspace
three-term update. The final theorem composes those certificates, then derives operation and
workspace budgets by static evaluation and generic profile transfer. The first rounded slice
records standard-model local errors and safe normalization under explicit dot/sqrt margins;
transfers to old finite-precision analyses will be listed individually, not claimed wholesale.

## Implemented exact guarantees

`Exact.solve_spec` proves total success from the scalar exact model, exact BLAS and matvec
contracts, decoded comparisons, and ordinary readable/roomy blocks. It places no restriction
on the matrix or cap. The result equals the pure recurrence at every requested column; for
Hermitian matrices, `Output.basis_eq_arnoldiMatrix` identifies the canonical Krylov basis.
`Exact.runs_solve` adds the evaluator-derived abstract operation and workspace bounds.

`Profiles.seqSolveCount` evaluates the scalar budget of sequential BLAS. Each active round
uses at most 4n multiplications, 2(n−1)+2n additions, 2n+2·1[n>0] copies, n divisions,
two sign changes, one square root, two zero literals, and one primitive matvec. The round also
has its normalization test; the enclosing loop adds one continuation test. Natural-number
subtractions in these counts saturate at zero. Initialization
counts every zeroed basis/coefficient/previous-vector cell, its self-dot and guarded
normalization. Counts are upper budgets: early exit and the zero normalization branch do
less work. Scratch is bounded by 3n+3 scalar cells after sequential lowering, independently
of cap. Output storage is separate from scratch.

Focused evaluator guards exercise cap zero, input zero, dimension zero, one-step eigenvector
breakdown and two-step swap-matrix breakdown, with initialized zero tails. Sequential BLAS
lowering is checked against the unlinked outputs for active and zero-input cases.

## Rounded transfer boundary

`Rounded.update_writes` derives both componentwise axpy bounds and the diagonal dot bound
from the actual first-update/raw vectors and coefficient. `normalize_rounded_writes` exposes
actual output reads, norm and reciprocal-scaling contracts, and the zero-input result.
`Rounded.advance_writes` composes those facts into a complete successful round, using an
exact primitive matvec. Dot and square-root error parameters below one guard normalization.

The pure `Math.RoundedLocal` estimates convert componentwise bounds to Euclidean local
errors. If the self-dot and sqrt tolerances are ed and es, the relative norm tolerance is
g=ed+es(1+ed). With reciprocal-scaling tolerance ec, g<1 gives normalization residual at most
ec times the raw-vector norm and squared near-unit defect at most t(2+t), where
t=(ec+g)/(1−g). The terminal zero-norm case is included.

`Rounded.first_round_writes` uses these primitive-derived defects and the existing pure
`LanczosRun` constructor to tie a positive-length run to actual computed basis/coefficient
outputs. Its precision and initial near-unit premises are explicit. This does not yet transfer
an arbitrary-length rounded solver to the run model. In particular, Paige orthogonality,
Greenbaum backward-error and polynomial approximation results are not claimed for the new
whole rounded program merely because the old pure analyses remain available.
