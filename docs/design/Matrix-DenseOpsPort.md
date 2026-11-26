# Dense factorization port to Ops

Status: implementation complete and full-stage validated, 2026-11-25. The user approved the complete Ops port after
review of the framework conflict. The checked legacy feature remains at `c4645b5f`; it is
provenance and a regression specification, not the current certificate interface.

## Preserved mathematical scope

The exact real input domains, canonical factors, actual current-position-to-original-position
pivot logs, source preservation, buffer shapes, zero/singular behavior and factorization/solve
postconditions remain requirements. Retain all current main results. Reuse canonical shared
concepts, especially `IsComponentwiseBackwardSolution` at zero floor, instead of introducing
the old duplicate solve-error predicate.

## Shared interfaces and proof order

Use the existing scalar codec's column-major layout, `j*N+i`. Routines have memory-free
specifications and one generic word-level judgment; arithmetic models derive numerical
consequences from that judgment. Scalar, comparison and exact-index operations are jointly
realized by the scalar/index profile. Input-only `Ops.Inputs` records declare the source matrix
and blank factor/log capacities. Domain wrappers connect those inputs to actual routine
interfaces. Certificate postconditions include actual factors/logs, retained input and shapes.
Closed counts/work and caller-plus-scratch memory must refer to the same canonical execution.

Shared spatial frames, matrix entry codecs, strided copies, scalar BLAS and triangular solves
replace the legacy Store/FStmt plumbing. The full-Schur update saves the original pivot row
and column before updating entries. PSD zero-pivot guards and independently permuted PLUQ logs
remain explicit. Rounded success and finite-range numerical accuracy are distinct: a total
word-machine trace alone does not prove the rejecting finite-range guarantee.

## Integration and validation

Preserve main's Ops core, trusted-base statements, checks and pins. Do not revive retired
target files or the old target registry. Validate pure mathematics, actual scalar fragments,
routine judgments, input domains, counted certificates and canonical runtime guards in that
order. Build through the existing host gate, serially. Run the complete current stage check
without exclusions before updating the authorized PR branch. A production explorer refresh
follows only the normal successful-main-CI publication pipeline.

## Integration evidence

Dense factorization integration decision — 2026-11-25

Checked branch: design/dense-factorization-routines, c4645b5ffaaaa3151dbba581a8502b185603a99d
Current main: 83c32ccbc1cadb2fd73c94081f5f9f6fe052a817
PR: https://github.com/NLA-lib/NLAlib/pull/163 (mergeable=false, dirty)
Live explorer: https://nla-lib.org/explore/api/v1/manifest.json (same current main)

The branch and main share base 7cbea9d1. Main has since removed the entire legacy
execution framework and retired the old target registry. The merge preview reports
122 file-location, 8 content and 7 modify/delete conflicts. Git's proposed moves of
legacy core files into Matrix/FinitePrecision do not produce a meaningful Ops port.

Approved scope: port the complete factorization feature to current Ops, retaining
the old checked commit in history. Preserve main's core, trusted base, checks and model
contracts. Add pure factorization/error mathematics without overwriting new upstream
Cholesky permutation/rank results. Translate actual scalar/pivot/block loops, frames,
nonbreakdown/error proofs, and solve compositions into current routine specifications,
judgments and certificates. State caller/scratch/full accounting using current Ops,
not the retired seven target definitions. Preserve input domains and actual factor/log
postconditions, including singular PSD and empty inputs. Keep total-machine Cholesky
trace success distinct from the branch's finite-range/rejecting arithmetic theorem.

Parallel work:
1. Pure algebra, LU/PLU/PLUQ/scaled/rook/threshold bodies and pivot-log contracts.
2. SPD/PSD/pivoted Cholesky, LDL, rounded/finite-range guarantees and solves.
3. Ops program/specification/counting certificates and native execution guards.
Root integrates current main, preserves existing APIs, runs the current full checks,
and updates the authorized feature branch without a force push.

Publication: after the integrated feature is merged and current-main CI succeeds,
the library's Explore data workflow publishes a new rolling release and dispatches
the website deploy. No website source edit is needed merely to include declarations.
Do not publish feature-branch data over the production main snapshot.

## Validation milestones

The initial strict build checks the joint scalar/index profile and shared framed-certificate
construction. Kernel-checked scalar product, rectangular copy, full rank-one/Schur update,
matrix multiplication, and triangular substitution routines provide the common execution
layer. Mathematical bridges identify their actual words with canonical elimination, matrix
products, and exact solves. The complete SPD and singular PSD routines, including genuine
in-place adapters, LDL, diagonal-pivoted PSD, partial/threshold/complete pivoting, and blocked
LU and Cholesky now pass strict integrated checks. Separate Cholesky relative-only and
rejecting finite-range theorems preserve their original input conditions and error budgets.
The represented binary backend instantiates the finite-range theorem. Rounded partial and
complete pivoting retain actual histories, all-input singular coverage, structural and
multiplier bounds for nonnegative roundoff, and the conditional componentwise budget
`roundingFactor (N + 4) u`. The exact integer range is a declared dimension restriction.

Exact partial- and complete-pivoted solves now use actual stored log replay and restore the
original coordinates, including genuine in-place RHS adapters. Their 296 execution cases
exercise independent row/column permutations, singular guards, aliases and invalid empty
headers. Exact and rounded rook search, its counted certificate and both execution suites pass the
strict integrated build. Partial and threshold policies also have integrated counted
certificates on the original all-matrix domain. The complete fixed-scale factorization and counted certificate also pass strict checks,
including transported original scales, singular/zero-scale inputs and the actual row log.
Its 73 execution cases retain the original selector regressions and test full factors, aliases
and invalid empty headers. The raw relative and mixed Cholesky theorems admit arbitrary
invalid handles and offsets in the empty case, matching the actual guarded no-op.
The complete stage check without exclusions is the required publication gate.
Other runtime regressions include 420 LU/Cholesky solve executions and empty, singular, tie,
clipped-panel, overlapping
source/output and sentinel cases; native floating-point accuracy is not inferred from them.

Resource proofs inspect the actual instrumented trees. Added routine frames change the
instruction polynomial even when the arithmetic is unchanged; counts are recomputed after
such refactors. Source preservation and original buffer extents are part of the framed
certificate, and caller memory includes blank output capacity. Float execution guards check
the actual trees on representative matrices and memory layouts without claiming universal
native floating-point accuracy.

## Final validation

`bash scripts/stage_check.sh` completed with exit 0 and no exclusions on 2026-11-25.
All 1,804 library modules are proved, with no unfinished modules and no strict-build warnings.
The axiom audit checked 62,758 reachable declarations without violations; all 14 environment
linters passed. Freshness checked all 5,547 build jobs. Kernel replay checked 62,965 constants
from 1,825 library and tools modules without violations, and all eight replay fixtures passed.
The certificate coverage, report fixtures and trusted-base checks passed. The trusted base
remains 107 declarations in 12 modules and 920 source lines; no checker, baseline, toolchain
pin or trusted-base file was changed. Only the normal certificate inventory was regenerated.

The 127 Python tests and 14 Node tests passed, as did reference, constant and LaTeX checks.
The full 106-rule audit reported zero new errors, 73 unchanged baseline errors and 6,153
advisory warnings across the whole library. The duplicate report found 14 existing classes.
The explorer extraction reached all 1,804 modules and produced 17,174 declarations. This is
local validation data; production publication follows successful main CI after PR merge.

The first whole-library run exposed two proof-call ambiguities and the tools-root import
format, which were corrected. The first environment lint exposed redundant unit-stride
simp registrations; the specialized facts now reuse the general packed-view identities.
The complete gate above passed after those fixes, with the Lean sources unchanged throughout.
