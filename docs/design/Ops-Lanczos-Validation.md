# Lanczos integration validation

Validated on 2026-11-12 in `nlalib-ops-resources`. The resource/model work is included in the authorized feature-branch release.
No target-registry edits, check changes, exemptions, pins, CI changes or main-branch merge
accompany this work.

## Implemented behavior

- Exact ordinary and fully reorthogonalized output has shared packing decoders, canonical
  basis/compression facts, grade-correct orthonormality, and stored-coefficient Ritz bounds.
- Ordinary rounded output has physical Ritz residual guarantees, including explicit zero-cap
  and zero-input outcomes. The physical Ritz vector is not silently treated as unit.
- Full rounded reorthogonalization initializes every output slot, performs the actual two
  classical passes, normalizes safely and returns the complete executed history. Actual local
  operation, coefficient and norm witnesses refer to the same final packed archive.
- Actual sequential-AXPY pass bounds derive the existing orthogonalization-error interface.
  The pure mathematical step-to-run constructor is shared with the old execution module.
- Strong rounded reorthogonalization analysis selects the leading strict admissible prefix.
  It preserves the full executed output, allows an empty prefix only with its actual boundary,
  and reports the next failed coefficient test. The runtime stopping rule is unchanged.
  Explicit size-only precision windows transfer an upper spectral bound to the same stored
  tridiagonal. The returned run also exposes the existing pure backward/spectral API.
- Both abstract BLAS programs have canonical `Ops.Algorithm` certificates. Ordinary Lanczos
  additionally has a certificate for its actual sequential scalar lowering. Each certificate
  uses an independent syntactic full manifest and counts all supplied resident capacity.
  `Algorithm.mapPost` retains those exact resources while strengthening ordinary/actual
  sequential output with the Ritz residual guarantee.

## Shared proof infrastructure

`Ops/Certification.lean` supplies initial-buffer facts, total conditional-WP transfer, and
projection from mandatory instrumented static counts. `Lanczos/BufferProblem.lean` supplies
one explicit three-buffer layout parameterized by coefficient length. Ordinary and reorth
certificates specialize it. Initialization suffix preservation and archive framing are shared;
no algorithm tree is patched to obtain success. Existing ordinary theorem statements remain
available, and old pure mathematics is reused rather than old execution proofs.

## Checks

- All 990 proved source modules build with warnings fatal: 4,672 jobs, zero warnings.
- Regenerated library root builds with warnings fatal: 4,674 jobs.
- Library plus tooling builds and freshness checks pass: 4,688 jobs.
- Global axiom/unsafe/partial audit: 36,579 declarations, zero violations.
- Scoped environment lint: all 14 linters pass over 615 declarations and 1,397 generated ones.
- Kernel replay: 37,025 constants from 999 modules; strict NLAlib, zero violations and zero
  non-strict findings.
- Source rules over the Lanczos family and shared additions: zero errors/warnings.
- Declaration rules over the Lanczos family and new helpers: 109 rules, zero errors and
  115 advisory warnings. Including the entire modified shared PiL2 file additionally reports
  three unchanged naming errors in its pre-existing lemmas.
- Replay regression fixtures, program registry, target registry and access-model fixtures pass.
- References and registered numerical constants: zero problems.
- The curated Lanczos page has 20 valid local source links; whitespace checks pass.

The unchanged full stage script stops after its successful build/audit at the pre-existing
`Ops.CastOp` derived `DecidableEq` unused-argument lint. Scoped lint excludes no Lanczos code;
the failure is retained and reported without modifying a check or allowance. Remaining stage
checks pass separately against the same frozen source/build. The global declaration-rules
check reports 540 errors (73 in its baseline) and 2,763 warnings across the library; it is not
a passing release check. Existing policy and naming findings remain visible without waivers. Optional NumPy tooling comparisons
are skipped because NumPy is unavailable in that tooling environment.

## Guarantee scope

The named standard model uses unbounded exponents. These certificates do not assert native
IEEE arithmetic, physical storage encodings or parallel scheduling. Matvec remains a declared
operator with explicit work/workspace charges; captured backend storage needs its own model.
Abstract cell payload and supplied input/output capacity are accounted for explicitly.
The certificates use conservative syntactic full manifests. They do not register a closed-form
total-work target; their original-operation projection and resident/scratch formulas are explicit.

The strong reorthogonalized run can be shorter than the executed history. Its spectral theorem
bounds that actual selected prefix, not arbitrary padded columns or a later inadmissible
suffix. The exact and rounded programs return basis/coefficient data; an eigenvalue statement
about those data does not claim that the program executes an eigensolver.

See [the curated Lanczos guide](../algorithms/Lanczos.md) for pseudocode, call counts, storage,
operation-model choices and source entry points.
