# Matrix-free CG program and shared execution proofs

Target and tree approved by the maintainer on 2026-11-04. The stored-entry CG program, its compiled tree, target and approved counts
remain unchanged. This development adds the separately reviewed oracle variant in
`CGOracleProgramTree.lean`, `CGOracleTargets.lean` and `CGOracleProgram.lean`.

## Program and access model

`cgOracleProg` has the same five declared buffers: b, x, residual, direction and status. It uses
the same cached squared residual, guards, update order and terminal statuses as `cgProg`.
Each active step calls `.apply o tag s 0 p 0 1` in place of the stored dense gemv. Matrix entries
are never read or materialized. The oracle is fixed before the unknown matrix and right-hand
side, as required by the existing `Computation.MatrixFree` model.

The scratch layout reserves an empty buffer at slot5, then product workspace N at slot6 and
nine scalars at slot7. This keeps the existing phase addresses and permits sharing the scalar
and update execution lemmas. The empty slot occupies zero numeric cells and O(1) host metadata;
all memory statements use the existing numeric-cell model. A later layout simplification can
remove the empty slot only through a separately reviewed program/tree change.

The approved target is `MatrixFreeConjugateGradient`, using the existing model and
`cgOracleProg.compiled`. Sizes are unrestricted. Every real matrix and RHS has a successful
guarded exact execution with preserved b and status0/1/-1; for SPD matrices all three output
vectors equal `cgState A b 0 q`, status1 iff the terminal residual is zero, and status-1 is
excluded. Zero dimension, zero RHS and zero budget are included.

## Resources

Per active iteration there is one oracle load and one one-column matvec. Upper counts at a
requested budget q are: load=q, matvec=q, mul/add=N+5qN each, conj=N+2qN, div=2q,
neg=q+1, lit=N+3+2q, cmp=1+3q, copy=2N+2q+2. Every other count is zero. Peak memory is
5N+11 cells at the arithmetic tag, zero elsewhere; it includes declared buffers and scratch.
The oracle implementation's internal memory and arithmetic are outside this black-box count
and must be included by any backend implementation certificate.

The generic StaticCost theorem certifies these resource bounds independently of exact or
rounded scalar correctness. It counts the actual `.apply` as one load plus one matvec.

## Reusing correctness

Reuse the existing `CGState`, scalar-frame and BLAS execution lemmas. The shared store context distinguishes a stored matrix from the zero-length reserved slot,
with the existing dense specialization retaining all its old conditions.
Common vector/scalar update phases apply to both backends. Curvature execution is the
backend-specific component: existing dense gemv versus the certified actual oracle application.
Loop invariants and mathematical guard facts are shared. No alternative CG recurrence or
arithmetic-error/run interface is introduced.

The rounded oracle theorem is now in `CGOracleProgramRounded.lean`. It takes the existing
scalar contract, an independent `IsMatvecErr` accuracy eta, and a chosen allowance v >= u
whose CG run budget covers eta. It proves actual compiled execution, all three decoded
vectors, status/input preservation, terminal skipping and original resources. Dense CG uses
the same phase/prefix/horizon proof with the dense kernel certificate; its prior full
execution and backward statements remain unchanged.
See [the common design](Krylov-Rounded-Oracles.md) for the precise allowance selection.

## Approval and validation

The maintainer approved the exact builder, compiled tree, count formula and target statement
in the draft `proposals/krylov/CGOracle.lean` (since removed).
Canonical placement splits the program tree, target and
proofs without changing those reviewed bodies. `CGOracleProgramStaticCost.lean` proves the resource
certificate separately from exact correctness. The final theorem proves the target constant.
The actual compiled tree passed eight Float execution cases, checking all output buffers,
operation kinds, cell/bit bounds and cleanup.

## Shared allocation wrapper

`Computation/Allocation.lean` names the existing allocation/release state updates as
`St.allocate` and `St.release`, and lifts an actual body execution through one scope using
`exec_alloc`. `CGProgramScope.lean` composes that same rule for the actual three allocations,
under arbitrary word carriers, charges and bit widths. The matrix-size expression remains an
`IExp`, preserving the literal stored AST rather than replacing `N*N` by a different constant
node. These are execution helpers, with no numerical postcondition or independent interpreter.

## Guarded binary64 curvature and step length

The matrix-free CG loop calls the matrix oracle on its stored direction, takes a dot
product, and tests the sign of the returned curvature before dividing. The public
`CGOracleImplementation.exec_product_of_isMatvecErrOn` links the stored oracle instruction to
the existing domain-restricted matrix–vector contract. Its accuracy premise covers the current
decoded direction. The proof also preserves the CG store context for the next instruction.

For the concrete binary64 implementation of twice the identity, let $R$ be the Euclidean norm
of that direction. If every exact doubled component is representable in the finite magnitude
range, the checked additions return a vector with error at most
$E=2uR+\sqrt{N}\eta$, where $u$ is the binary64 unit roundoff and $\eta$ is its
absolute underflow allowance. The dot-product certificate uses its input norm, this estimate
and the largest finite magnitude to bound the intermediate accumulations. The exact curvature
is $2R^2$. A strict margin against the derived error proves that the stored comparison selects
the positive branch, including when some input components are subnormal. The present interface
certifies a prefix starting from a well-formed CG store. Future iterations must establish the
range premises for their own directions and scalar operations.


Writing $Q=p^*Ap$ and $B$ for the proved curvature error, suppose $Q>B$ and the
stored residual-square numerator satisfies $|\nu|\le M(Q-B)$. Here $M$ is the largest
finite magnitude. The checked positive branch then executes the stored division and
returns its rounded step length. It has an absolute-plus-relative error bound. For a
positive lower bound $\tau$ on the magnitude of the exact quotient of the two stored
operands, its relative error is at most $u+\eta/\tau$.

`CGOracleImplementation.toStmt_cgOracleProg_compiled_eq_guarded_loop` identifies this prefix,
the curvature comparison and the division in the registered program. At decoded zero status,
`CGOracleImplementation.cmpStep_eq_some_true_of_sem_eq_finiteFloatSem_of_status_eq_zero` gives
the comparison charge. `CGOracleImplementation.exec_ite_eq_exec_of_sem_eq_finiteFloatSem_of_status_eq_zero`
uses that result to select the active arm before the first matrix product.
