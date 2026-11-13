# Retiring the old execution and registry system

The library uses fixed `Ops.Program` values and total `Ops.Algorithm` certificates. The previous
Computation evaluator, compiler, program families and target registry are retired together;
reusable numerical mathematics is retained under its numerical topic. No compatibility aliases
are needed for the retired execution interfaces.

## Validation boundary

`scripts/OpsPrograms.lean` replaces the legacy Programs/Targets checks. It inventories the
current Program and Algorithm interfaces, rejects opaque/noncomputable/unsafe/partial program
definitions and implemented-by replacements, and rejects imports of retired execution modules.
Certificate validity remains a theorem checked by Lean, not a linter inference. Existing
canonical examples reject vacuous domains, empty word carriers, unrealizable contracts,
size-indexed tree families, liberal-only proofs and missing structural counts. Program fixtures
check complete accounting, formats, arities, allocation widths and query workspace.

The axiom audit, environment lint, freshness check, kernel replay and rejection fixtures remain
mandatory. Generic naming, source, documentation, constants, import-layer and ratchet checks
remain active; scanner corrections and review-warning classifications are documented in the
contributor guides. The old registry exemptions are removed from vocabulary review. No allowlist or
ratchet limit is relaxed.

E2 retains its program computability role. E3–E6 and E8–E9 refer exclusively to retired syntax,
semantics or target registration and are retired without reusing their identifiers. CI and stage
invoke OpsPrograms instead of the old checkers; the old target-approval workflow is removed.
CODEOWNERS protects the current certificate/model/accounting definitions and their checks.

## Numerical preservation

Binary formats, word decoding, quantizers, matrix-machine mathematics, tape laws and numerical
analysis remain independent of program evaluation. The move preserves mathematical declarations
and proofs, even where their historical namespace contains `Computation`. Dependency checks
operate on imported module paths, not that namespace spelling. Different arithmetic policies
remain distinct: optional floor-grid rounding is retained as mathematics, while the Ops finite
grid implementation uses nearest rounding and saturation. Native Float accuracy keeps its
explicit safe range and mixed absolute/relative error.

Deletion follows retained endpoint checks, source audits and dependency inspection. The generated
root and import-layer table are refreshed after the old modules are removed. The final validation
runs the current generic checks and kernel replay on the resulting retained library.
