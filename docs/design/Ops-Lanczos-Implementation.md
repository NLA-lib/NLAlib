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
