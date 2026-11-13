# Concrete Krylov implementations and their guarantees

> Archived execution-system design. The former evaluator, programs, target registry and
> emission tooling are retired. The current interfaces are documented in
> [the Ops migration](Ops-Migration.md) and [the program guide](../contributing/programs.md).
> Mathematical analysis is retained; program and registry names below describe the historical system.

2026-11-05. Both stored-entry and matrix-free CG and Lanczos have approved exact targets and
complete program proofs. All four programs construct their finite-precision runs from primitive execution. Stored CG
and Lanczos also expose packaged backward-model corollaries; the same mathematical run
theorems apply to the oracle outputs.

## Programs and targets

| Program | Target and proof | Mathematical output |
|---|---|---|
| `cgProg.compiled` | `StoredEntriesConjugateGradient`, `storedEntriesConjugateGradient` | Preserved input and legal status for every real matrix; for SPD matrices, x/r/p equal the total exact CG recurrence |
| `cgOracleProg.compiled` | `MatrixFreeConjugateGradient`, `matrixFreeConjugateGradient` | The same guarded outputs with one oracle call per active step and no stored matrix |
| `lanczosProg.compiled` | `StoredEntriesLanczos`, `storedEntriesLanczos` | All basis columns, alpha/beta coefficients, input norm, previous vector and retained input |
| `lanczosOracleProg.compiled` | `MatrixFreeLanczos`, `matrixFreeLanczos` | The same outputs, using one oracle call per requested Paige step |

Builders and compiled trees live in the respective `CGProgramTree`, `CGOracleProgramTree`,
`LanczosProgramTree` and `LanczosOracleProgramTree` files. Target/count definitions live in
the corresponding `*Targets.lean` files; the final `*Program.lean` theorem has its target
constant as its entire type. Compilation/instantiation equations are kernel checked.
All targets include zero dimension, zero input, zero steps and terminal continuation.

Oracle memory is `5*N+11` cells for CG and `N*(q+4)+2*q+5` for Lanczos. Oracle internal storage
and arithmetic are outside this access model. The stored targets retain their original
ROM-inclusive bounds, adding `2*N^2` to these formulas. Counts distinguish each oracle load
from its column matvec and include actual scalar, copy and guard operations.

## Independent resource analysis and shared execution

`Computation/StaticCost.lean` folds the actual first-order tree into operation counts and
additional cell/bit workspace. It proves bounds for successful execution under arbitrary
scalar/oracle semantics; numerical correctness and success are proved separately.
`CGProgramStaticCost`, `CGOracleProgramStaticCost`, `LanczosProgramStaticCost` and
`LanczosOracleStaticCost` establish the approved closed-form bounds from those trees.
Read-only memory is added once by the existing resource interface.

Generic scalar/ROM and BLAS frames remain in Computation. The certified builder-composition
property applies to single-statement emitters and their certified compositions; it does not
assert that arbitrary builders with escaping allocations compose that way.
`Computation/Allocation.lean` and the two `*ProgramScope.lean` files describe actual scoped
allocations, arbitrary word widths and cleanup. Shared declared-state constructors and
Lanczos output-preservation lemmas avoid duplicating initialization/cleanup proofs.
Backend-specific matrix-vector prefixes reuse the same scalar and vector phases.
No replacement arithmetic semantics, recurrence or local-error run model is introduced.

## Shared rounded analysis and oracle guarantees

`Computation.IsMatvecRoutine` is the common execution certificate: success, decoded product
accuracy, the actual block-write frame and composition with the following program.
`IsMatvecErr.isMatvecRoutine` supplies it for external oracle access;
`IsRelErrSem.isMatvecRoutine_gemv` supplies it for the existing dense kernel from scalar
floating-point accuracy. The latter has operator-error coefficient
`roundingFactor N u * sqrt N * specNorm A`.

`CGOracleProgramRounded.lean` and `LanczosOracleProgramRounded.lean` prove actual compiled
oracle execution, all declared decoded outputs and their existing static resource bounds.
They take scalar roundoff u and oracle accuracy eta separately, plus an analysis allowance
v >= u whose run budget covers eta. The common CG and Lanczos phase, prefix and loop proofs
are instantiated by both backends. Dense completion and backward theorem statements are
unchanged; their numerical analysis now follows by supplying the dense backend certificate.
See [the design and allowance selection](Krylov-Rounded-Oracles.md).

## Complete rounded CG bridge

`CGProgramRounded.lean` proves `CGImplementation.exec_rounded_compiled` on the unchanged
stored-entry compiled tree. Inputs are actual declared buffer words, column-major ROM words,
their decodings and the existing `IsRelErrSem`/`AddsZeroExactly` contracts. It derives the
initializer, cached norms, guards, divisions, full loop, cleanup and decoded output ties.
It assumes no initialized numerical header, local defects or `CGRun` as input.

Write `epsilon = 4*N^2*u` and `kappa = a'/a`. The explicit conditions are `u < 1`,
`epsilon <= 1/100`, symmetric A with spectrum in `[a,a']`, `a > 0`, and
`q^2*sqrt(q)*epsilon*kappa^2 <= 1/10^5`. Zero input/dimension/steps are separate proved branches.
Otherwise the result supplies an existing `CGRun N m`, `0 < m <= q`, tied to the actual
returned x/r/p words. A shorter prefix has zero terminal residual; remaining iterations
execute the actual status-skip branch. Literal one decodes to a positive flag within u of one;
status statements retain that flag rather than silently replacing it with exact one.

`CGProgramRoundedBackward.lean` composes this execution theorem with the existing backward and
physical-energy theory. It gives the canonical SPD model, explicit perturbation radius,
exact matching model step lengths and computed residual norms, and a comparison of the actual
iterate's squared energy error with exact CG's error on the model. The model-distance term
`2*norm(b)^2*delta/a^2` and existing local `150*m^2*epsilon*kappa*norm(b)^2/a` remainder stay
separate. The comparison uses energy directly, without converting a residual-gap estimate.
See [the rounded bridge](CG-Rounded-Program-Bridge.md) and
[the backward theorem](CG-Rounded-Backward.md).

## Complete rounded Lanczos bridge

`LanczosProgramRounded.lean` proves actual compiled execution, all six decoded output buffers,
computed input norm/direction certificates and an existing active `LanczosRun`. Its primitive
contracts and explicit `16*(N+1)^2*u <= 1/100` local condition justify every operation; no
accumulated horizon is needed for completion. Zero input/dimension/steps and actual zero
continuation are separate cases, with no padded zero vectors in the near-unit run model.

`LanczosProgramRoundedBackward.lean` retains those outputs and the initial-direction mismatch
while exposing the canonical exact model of the active tridiagonal prefix. Its unconditional
geometric radius depends only on N, q, u and the matrix norm. It also gives the existing
`400*q^3*epsilon*norm(A)` bound under `q*epsilon <= 1/100`, and the sharper
`1000*q^2*epsilon*norm(A)` bound under `q^2*epsilon <= 1/1000`.
The model concerns the active prefix, not the extra zero eigenvalues of a padded T_q.
See [the complete Lanczos bridge](Lanczos-Rounded-Program-Bridge.md).

The arithmetic contracts use an unbounded range. Float smoke executions do not certify an
IEEE format, overflow/underflow behavior or arbitrary external oracle accuracy. Matrix-function
postprocessing, preconditioning and other algorithm families remain separately tracked in
[the coverage inventory](Implementation-Coverage.md).

## Preserved approvals and mathematical contracts

The maintainer approved both new oracle statements and trees. Their four program/tree/count/
target bodies are unchanged from each reviewed proposal. The registry contains nine targets
and seven trees; every pre-existing entry and build pin remains exactly unchanged.
The small naming-check correction for zero and conditional notation was separately approved;
checks, allowlists and ratchets were not bypassed.

The prior main integration retained the approved explicit `k*epsilon <= 1/100` conditions on
five Lanczos spectral/quadrature/function bounds, with unchanged conclusions. The run interface
keeps only its local accuracy condition. Primitive bridges use the primary product factor
`(1-u)^(-n)-1` and its existing rational upper comparison.
