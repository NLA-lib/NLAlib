# Completion of the operation-core migration

The library represents implementations as fixed Ops programs. Their published guarantees
combine a raw-input problem, a jointly realized operation model and a specification of the
actual output and resources. This migration removes the former `Computation` evaluator and
programs after their retained guarantees have corresponding Ops results.

## Retained behavior and ownership

| Development | Retained endpoint | Implementation owner |
| --- | --- | --- |
| CG, carried CG, PCG, reorthogonalized CG | Total raw-input execution, numerical output, complete canonical resources; rounded CG stability | CG certification lane |
| Rank-revealing modified Gram–Schmidt | Full matrix factorization for arbitrary rank, including zero columns | Gram–Schmidt/Hutch++ lane |
| Hutch++ | Oracle, dense and coordinate-matrix implementations, counts, storage and probability | Gram–Schmidt/Hutch++ lane |
| Sign and deflation | Capped stored-output computation and numerical probability under explicit numerical assumptions | Integration lane |
| Lanczos and reorthogonalized Lanczos | Existing canonical, rounded, linked and Ritz certificates | Integration lane, preserving existing results |
| Spectral bisection | Existing word/work certificates and same-run numerical probability transfer | Integration lane, preserving existing results |
| Quantization, matrix accuracy and tape laws | Existing mathematical statements independent of either evaluator | Numerical-separation lane |
| Explorer | Markdown pages and generic declaration APIs, source provenance and links | Explorer lane |

Stored-matrix CG, PCG and Lanczos use a shared context-forwarding transformation. It adds
declared raw data operands to the relevant calls and forwards them through frames and
allocation scopes. The transformed program is instrumented after transformation, so the
additional operand and frame work is counted. The matrix-free certificates alone do not
establish these stored-input guarantees. The new stored-matrix endpoints use exact arithmetic.
Rounded Krylov theorems use their numerical primitive models; finite-format cache and
scalar-word error theorems are recorded separately.

NumPy emission is retired. The new Explorer does not require it. Existing pure mathematics
is retained even when a historical filename contains `Program` or `Computation`.

## Certificate shape

For each retained implementation, `program : Program Op Tst r b` is fixed before the input
dimensions, input values, interpreter and tape. Its endpoint has the following existing shape:

```lean
noncomputable def algorithm (model : AccessModel Op Tst problem) ... :
    Algorithm model specification

theorem certifies ... : program.Certifies model specification
```

The omitted parameters are the implementation's explicitly stated primitive and input
assumptions, with no successful-run premise or arbitrary whole-program correctness callback.
`specification.good` describes actual stored output. `budget`, `scratch`, `work`, `span` and
`memory` bound the same canonical instrumented execution. Existing `Algorithm.ofWp` and
`Algorithm.ofWpActual` assemble these endpoints from total proofs. The spectral-bisection
`measureReal_not_accepts_le_of_wordSpecification` theorem already transfers numerical accuracy
to actual counted execution and remains part of the retained interface.

## Shared machinery

The migration reuses `Writes` block rules, tuple reads, footprint transport, scoped allocation,
counted loops and weighted loops. Algorithm-specific proofs contain the numerical recurrence
and invariants. Any repeated storage or execution argument is moved into the corresponding
Ops logic file before a second consumer uses it. Linking uses one fixed implementation table
and counts the complete lower program.

`Has.sumLeft` and `Has.sumRight` embed operation groups into larger signatures with their
projection laws. `Functional.modelWithAdm` generates every primitive contract and a joint
reference interpretation from an exhaustive local-function assignment and explicit operand
admission. `ExactLinear` supplies the standard collection for exact real or complex linear
algebra. Stored matrix-vector output is disjoint from its input spans; that separation is a
choice of this model, rather than a condition silently imposed on the execution.

`ExactScalarLinear` replaces the BLAS group by scalar conjugation. The fixed
`ExactLinearScalar.table` proves all six higher vector contracts from actual scalar
implementations. `ScalarOnly` also omits stored-operator names. `StoredScalar.fullDenseTable`
and `fullCOOTable` compose the vector and matrix lowerings into this signature. Their target
contracts contain no abstract BLAS or matrix-vector operation; complete local laws follow
from scalar arithmetic, conjugation and the chosen checked storage leaf.

`ScalarProducts.sum` streams scalar products with explicit strides and a caller-owned
temporary. `writes_fill_scratch` frames a persistent workspace while filling a vector.
`StoredDense` and fixed-pattern COO lowerings use those shared rules. Scoped output rules
include `writes_allocs_readBlock_at`, so sampling algorithms retain their exact tape advance
through allocation cleanup.

Numerical separation moves existing definitions and proofs, preserving their mathematical
content. Pure quantization and arithmetic-error results are separated from old `ScalarSem`
adapters; tape law and sample-tree mathematics are separated from old interpreter and store
adapters. New Ops consumers import only the pure mathematical pieces. Checked floor rounding and
nearest rounding with saturation remain separate policies. The logical native binary64
subnormal-square counterexample rules out an all-range relative-only multiplication model;
the retained finite-format results include their explicit absolute underflow allowances.

## Removal and validation

Removal proceeds after checking the retained endpoints, rather than treating a filename or
an old target as proof that a guarantee has been migrated. The old registry describes the old
program type; its checks and program-only tooling are retired together with that type. The
replacement retains canonical certification regression fixtures, strict compilation, whole
library axiom audit, environment lint, freshness, kernel replay, generic declaration extraction,
documentation checks and source checks. The new core's contract and accounting requirements
are enforced by its definitions, independently of a target registry.

The final dependency check requires no retained module to import the removed executor,
syntax, old programs or their interpreter adapters. Generated roots contain exactly the
retained modules. Numerical and execution regressions check arbitrary rank, early termination,
zero-size/cap cases where admitted, arithmetic breakdown assumptions and resource accounting.

The migration and check cleanup are prepared on feature branches. Main branches and site
deployment remain separate. Toolchain and Mathlib pins remain unchanged. The old program
checks, registry files and associated CI are replaced with checks for the Ops interfaces.

## Validation after retirement

The old reverse import closure contains 174 removed modules. The regenerated library contains
1,138 source modules and no retained import of the old execution directories. Mathematical
[module moves](../renames/2026-11-ops-modules.json) preserve the pure statements, including bounds
previously embedded in program files.

The required `scripts/stage_check.sh` completes with exit 0.
The full strict build passes 4,820 jobs with zero warnings. The whole-library axiom audit
checks 33,144 declarations with zero violations. Kernel replay checks 33,149 constants in
1,141 modules with zero violations. Freshness, both generated roots, replay rejection fixtures,
33 fixed-program declarations, 37 certificate declarations, 99 Python tests, 14 Node tests,
reference and constants checks, generated rule documents and LaTeX rendering pass.
The fresh Explorer preview contains 1,139 modules including the root and 10,989 declarations;
all source hashes match the working tree. It records the published commit as its base and
labels the uncommitted content as a working-tree preview. Explorer validation passes both
browser suites and 57 tests (eight optional skips), with zero missing targets among 223,998
local links across 26,019 pages. Six separate curated guide references accompany the declaration API.

The environment linter runs all 14 standard linters. Its simp-normal-form adapter recognizes
only compiler-generated constructor injectivity facts whose equality operands coincide by
reduction. Positive and negative fixtures check that ordinary generated facts and authored
redundant simp lemmas still receive the upstream test. All library declarations pass.

Source scanners recognize registered simp attributes, structural size projections, audit
commands and type-level let expressions. Naming, placement and semantic-use heuristics that
cannot reliably establish a violation are review warnings; they remain available with
`--warnings`. The full extracted-source scan has zero new hard errors, 73 existing baseline
findings and 3,062 review warnings. No allowance or baseline limit is increased. The standalone
naming checker and combined rule driver apply the same severities and scopes.

Reusable machinery includes context forwarding and protected-input total-proof transfer,
raw context problem layouts and payload accounting, exhaustive operation-model generation,
scalar BLAS and dense/coordinate implementations, and generic linked workspace bounds.
Measured strict elaboration examples are 1.3 seconds for context payload accounting,
2.5 seconds for the complete linear context bridge, 2.9 seconds for stored fixed-horizon CG,
and 2.4 seconds for each stored Lanczos certificate. These are build measurements, independent
of the algorithms' modeled resource statements.
