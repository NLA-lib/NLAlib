> Historical six-wave checkpoint. Superseded by the current delivery report.

# Dense factorization sprint: implementation and validation record

Date: 2026-11-24. Base: `7cbea9d1`. Worktree:
`/home/ubuntu/work/nlalib-dense-factorizations`; branch:
`design/dense-factorization-routines`. No commits or pushes. The original worktree's
user-owned target approval change and `.claude/` directory are preserved.

The [48-hour plan](Matrix-DenseFactorizationRoutines.md) has 18 work packages with dependencies,
three parallel worker lanes and an integration lead, review gates and fallback priorities.
Three workers audited the mathematical algorithms, pivot policies and routine infrastructure,
then implemented separate reviewed slices and cross-reviewed the results. Four concurrent
agent slots were available; later lanes are successive waves rather than additional workers.

## Integrated result

Six reviewed waves are now integrated. Exact stored Cholesky under SPD and no-pivot LU under nonbreakdown, plus partial-pivoted
PLU and complete-pivoted PLUQ, have full successful execution theorems; pivoted drivers
include singular and empty inputs. Their routine certificates tie decoded factors to the
actual output blocks and actual recorded permutations. Complete pivoting exchanges prior
upper-factor columns as well as lower-factor rows.

The actual rounded partial-pivoted driver now has a generic-word/generic-charge success and
footprint theorem, exact triangular zeros/unit diagonal and multiplier bound `1+u`. For
`u<1`, the same execution supplies componentwise `IsLUErr` with the proved conservative
allowance `roundingFactor (N+4) u`, and an actual `IsPLURoutine` instance tied to the output
row log. The independent active-prefix recurrence counts the rounded negative literal,
coefficient division, both rank-one multiplies and inverse lower-column division correctly.
No successful-run premise or exact Gaussian trajectory substitutes for rounded execution.

Additional algorithms include first-max partial/complete choices, rectangular original-row
scales, an exact division-free scaled selector and matching matrix/scale pivot operation,
arbitrary-word row/column exchanges, rounded rank-one/Schur/local-column guarantees,
upper/adjoint triangular solves and exact factor-then-solve drivers. Complete/scaled choices
have explicit tie/zero conventions. Scaled cross-product policy correctness is exact-only;
no unweighted multiplier bound is asserted for it.

The nine dense tool modules contain 240 guards, including independent replay of both actual
logs, later swaps of two committed upper rows, singular/zero-column cases, empty dimensions,
shared-buffer disjoint windows, offset/sentinel/frame checks, division rejection and
perturbed-arithmetic residual budgets. Staged and normal repository runs pass; the
final whole-library checkpoint is recorded below. Float regressions do not
prove that the concrete tool backend satisfies the formal scalar/index assumptions.

Canonical QA split three overlong proofs, consolidated duplicate strided/zero-preparation
builders and storage proofs, and reused Mathlib's tail embedding rather than duplicating it.
Checked equality preserves the original emitted instruction sequences through these
refactors. Exact and rounded mathematical analyses retain distinct contracts. No checks,
allowlists, ratchets, approvals, registered targets or build pins were changed.

Global rounded Cholesky nonbreakdown/stability, full scaled-pivoted factorization, rook and
threshold drivers, LDL/semidefinite extensions, blocked operands and registered cost targets
remain later packages in the 48-hour plan. The current Cholesky driver explicitly zeroes its
upper factor entries; its full saved-row/column update still needs its own rounding analysis
or a reviewed symmetric update. No automatic 48-hour continuation or account quota was
reserved. The original checkout's user-owned changes remain preserved.

## Final combined validation

The corrected final checkpoint runs under
`TMPDIR=/tmp/nlalib-dense-factorizations-final-checked bash scripts/stage_check.sh`.
Its normal two-library warnings-fatal build passes (4,451 jobs), including all 240 dense
guards against the canonical Float backend. The stage's 798-module warnings-fatal build
passes (4,426 jobs, zero warnings). The 26,050-declaration axiom audit and all 14 environment
linters pass (12,811 user declarations plus 13,239 generated declarations). Generated imports
and both-library freshness pass (4,451 jobs). The 798-module/7,986-declaration extraction
passes all 109 rules except the four reviewed B1 builder-name false positives (`luFactor`,
`pluFactor`, `pluqFactor`, `swapRows`); the 73 baseline errors remain ratcheted. The initial
proof-length, simp-attribute, statement-proof-term and theorem-name findings were corrected
and rechecked without exemptions. Kernel replay passes for 26,661 constants across
815 modules, with zero violations or non-strict findings, and all eight replay fixtures
pass. Program checks pass for 118 programs, kernels and trees (75 called by others), with
zero violations or E9 warnings. The full stage exits 1 at exactly the inherited E3 approval-
hash mismatch (14 targets, 16 trees, one violation); this branch is not declared merge-ready.
No numerical, semantic, axiom, environment-lint or kernel-replay violations remain.

The independent duplicate-statement report also ran: 10,468 library theorems, 12 duplicate
classes, all private; zero private-versus-public or public-versus-public duplicates. The
canonical extracted rules retain 73 baseline errors and 1,448 warnings, mostly pre-existing
or reviewed heuristics; no exemptions, renamed algorithms or bogus constant entries were
used to hide the four B1 false positives.

References (143 bibliography keys, 91 asymptotic forms, 11 algorithm identifiers), all
79 registered constants, generated rules, LaTeX and 22 access-model fixtures also pass:
12,995 docstrings, 684 value markers on 662 spans and 42,943 math spans checked.
The earlier `/tmp/nlalib-dense-factorizations-final/` run is superseded: it found the
simp-attribute/API issues documented in the final review, which are now corrected.

## Review artifacts

The final complete patch is `/home/ubuntu/work/nlalib-dense-factorizations.patch`, also
preserved as `/home/ubuntu/work/nlalib-dense-factorizations-six-waves.patch`. It contains
53 new library modules, nine dense tool modules, shared proof changes, generated roots,
vocabulary and design/audit records. Read-only application checking against the original
checkout is logged at `/tmp/nlalib-dense-factorizations-final-checked/patch-check.log`.
It excludes all build/staging artifacts, protected approvals/targets/checks/pins and the
original checkout's `.claude/` directory. No commit or push was made.

Earlier validated wave2/wave3 patches remain available separately. The implementation
worktree/branch remains the one named at the top of this record.

## First implementation wave

| Module | Statement read-back | Limits |
|---|---|---|
| `Matrix/Perturbation/LinearSolveErr.lean` | A computed vector exactly solves a system with entrywise relatively perturbed coefficients; monotonicity, exact/zero bridges and componentwise residual bound | Pure mathematics over finite indices and `RCLike`; does not assert execution |
| `Matrix/Computation/LinearSolveRoutine.lean` | A typed certificate concludes successful in-place execution, exactly one output write and the decoded solve guarantee; actual `trsvLower` instance | Real decoding, all-values-in-range relative-error model, nonzero diagonal; matrix and RHS blocks disjoint, possibly same buffer |
| `Matrix/Perturbation/LUErr.lean` | Unit lower/upper factors have componentwise error scaled by products of their entry magnitudes; error composes with arbitrary solve residuals or two typed solve-error guarantees | Not an executable LU implementation; reindex the input explicitly for pivoted variants |
| `Matrix/Perturbation/CholeskyErr.lean` | Lower triangular positive-diagonal factor has an absolute spectral residual budget; exact bridges and residual bounds for two approximate solves | Does not assume input SPD or prove rounded nonbreakdown; budget is absolute |
| `Matrix/Computation/RowSwap.lean` | Actual three-copy-per-column routine succeeds for arbitrary stored-word carriers and interpretations, with one net packed block write of the row-permuted rectangular matrix | Row indices must exist; zero columns and coincident rows supported; zero rows excluded by row bounds |
| `Matrix/Computation/PivotScan.lean` | Actual sign/negation magnitude scan returns the first absolute maximum, stores an exact index literal, and releases its three-cell scratch; full scoped singleton-write theorem | Nonempty vector, distinct input/output buffers, standard real-decoding semantics and exact index literals through length |
| `Matrix/Computation/Cholesky.lean` | Actual square-root and reciprocal-scaling column step succeeds and writes exactly its two output blocks; exact instruction count and usage fields | Exact real semantics and standard operation charges; no Schur update or full Cholesky loop |

## Second implementation wave

The user authorized continuation. Three parallel workers implemented full factorization,
triangular adapters and pivoting, with root supplying shared execution infrastructure,
factorization certificates, runtime examples and integration. The sprint now adds 18 Lean
library modules (about 4,459 lines), two shared frame lemmas and one tools runtime-check file.

| Module | Checked behavior | Preconditions and limits |
|---|---|---|
| `Matrix/Computation/SchurUpdate.lean` | Saves pivot operands, runs the actual rank-one kernel and proves exactly one matrix write of `eliminationStep` | Exact real semantics, nonzero pivot, standard charges; scoped workspace |
| `Matrix/Computation/LU.lean` | Complete actual no-pivot driver, canonical factors, exact `IsLU`, two output writes, input retained | Every `gaussState` pivot nonzero; separate factors; source separation only for nonempty input |
| `Matrix/Computation/LURoutine.lean` | Typed LU certificate, monotonicity, footprint and exact driver instance | Generic output words, disjoint factor blocks; concrete exact instance has zero error |
| `Matrix/Computation/CholeskyColumns.lean` and `CholeskyFactorization.lean` | Complete actual Cholesky driver from SPD, canonical factor, exact `IsCholesky`, one factor write | Exact real semantics and standard charges; overlapping input/output and empty matrices supported |
| `Matrix/Computation/CholeskyRoutine.lean` | Typed Cholesky certificate, monotonicity, footprint and actual full-driver instance | Absolute spectral budget; concrete exact instance has zero error |
| `Matrix/Computation/CholeskyRounding.lean` | Actual rounded column success, positive computed diagonal, square-root/division relative errors and two output writes | Standard all-values-in-range real-decoding model, positive pivot and roundoff below one; local claim only |
| `Matrix/Computation/TriangularSolveFrames.lean` and `TriangularSolve.lean` | Actual upper/lower-adjoint/upper-adjoint solves, exact solutions and rounded routine certificates | Fully initialized matrix blocks; extra packed workspace; real decoding; original operands may overlap |
| `Matrix/Computation/FactorizationSolve.lean` | Full factorization and two actual solves, exact original-system solution, RHS-only write and zero-error certificates | SPD or nonzero exact Gauss pivots; exact semantics/standard charges; original matrix/RHS may overlap; empty case handle-free |
| `Matrix/Computation/PartialPivot.lean` | Actual scan, dynamic index binding, row exchange and absolute pivot recording; first-max and complete output frame | Standard scalar and exact-index contracts, nonempty suffix, separate index buffer; not full PLU |

`Store.BlockFrame.writeBlock_scratch` and `Holds.writable` are shared proof lemmas in the
existing store/routine-frame files. The solve error API also has general `RCLike` permutation
transport. No semantic primitive or existing mathematical factorization predicate changed.

`NLAlibTools/DenseFactorizationSmoke.lean` contains 37 passing guards running the actual
builders: independent multiplication of computed LU factors, known Cholesky factors and
solutions, full factor-then-solve, empty/singleton cases, expected zero-pivot failure, offsets,
overlapping operands, all-zero/tied pivot suffixes and scratch release. Pivot examples supply
an explicit tool-only natural-index conversion, since the existing Float tool interpreter
predates dynamic binders. These tests do not establish its formal arithmetic contracts.

New modules are included in the generated `NLAlib.lean`; public concepts have vocabulary rows.
No checks, allowlists, ratchets, build pins, registered targets or target approvals were edited.
No `sorry`, new axiom, unsafe implementation or assumed execution trace was added.

The numerical guarantees are independent of the implementation certificates. Upper and
adjoint solve runtime instances now exist and are consumed by the full solvers. Rounded
Cholesky cannot promise success
from exact SPD alone. Exact comparisons in pivot scans compare current decoded stored values,
not an unrounded elimination trajectory.

## Third implementation wave

The complete all-input partial-pivoted driver and its zero-error routine instance pass
warnings-fatal builds. Independent statement review found no material issue in singular
execution, empty inputs, pivot orientation or the original-store frame.

| Module | Checked result | Limits |
|---|---|---|
| `Computation/MatrixStorage.lean` | Rectangular packed readback and identity block writes shared by the concrete algorithms | Existing real/complex packing; empty blocks need no handle |
| `Matrix/Factorizations/LUPivoting.lean` | Completed factor and maximal-pivot prefixes transport under active row permutations; computable swap-log decoder | No nonzero-pivot or cleared-previous-row hypothesis |
| `Matrix/Computation/GuardedElimination.lean` | Actual zero guards make both LU column materialization and Schur steps succeed for any exact stored residual | A zero column is not assumed; standalone local steps do not claim a factorization |
| `Matrix/Computation/PLUFrames.lean`, `PLUPrefix.lean` and `PLU.lean` | Full actual partial-pivoted execution, actual-log `PA = LU`, multiplier bound one, factor/log reads, three original-store writes and source retention | Exact real semantics and standard charges; separate output buffers; includes singular inputs and handle-free empty cases |
| `Matrix/Computation/PLURoutine.lean` | Generic decoded row-pivoted certificate, monotonicity, three-block projection and actual zero-error driver instance | Row pivoting; complete pivoting needs its own column log |

`NLAlibTools/PLUSmoke.lean` adds 41 passing guards, bringing the two dense-factorization
tool modules to 78 guards. Independent actual-log replay checks the factor product, exact
triangular shapes, unit diagonal, active-index ranges and initialized output cells. Examples
cover signed ties, three swaps, a later swap that moves existing lower multipliers, rank-one
and zero-column singular inputs, singleton/empty cases, offsets, sentinels, retained source
and released workspace. A division-rejecting interpreter proves the zero branches actually
avoid division; corresponding nonzero cases fail, checking the instrumentation itself.
These finite Float tests do not replace formal numerical-error or range-safety theorems.

The full Cholesky driver now writes explicit upper-prefix zeros after forming each column.
A perturbed multiplication interpreter confirms that an actual residual cancellation leaves
noise while the returned upper factor entry is literal zero. The generic local-column API
is unchanged, and no global rounded-success or backward-error theorem follows from this fix.

The corrected third-wave whole-library checkpoint is complete. Logs are in
`/tmp/nlalib-dense-factorizations-wave3-final/`, including `stage.log` and the independent
post-target checks. All 770 proved modules built with zero warnings (4,398 jobs); the
25,441-declaration axiom audit and all 14 linters passed (12,558 user declarations plus
12,883 generated declarations). Generated imports and both-library freshness passed
(4,416 jobs). Kernel replay passed for 25,921 constants across 780 modules with zero
violations; all eight replay fixtures passed. Program checks passed for 104 programs,
kernels and trees (64 called by others), with zero violations or E9 warnings.

The extracted 770-module/7,897-declaration snapshot passes all rules except the three
reviewed B1 false positives for `luFactor`, `pluFactor` and `swapRows` (73 ratcheted baseline
errors remain). The initially detected general-lemma placement and conclusion/name errors
were fixed and rechecked, without exemptions. References, constants, generated rules,
LaTeX and all 22 access-model fixtures passed (12,861 docstrings, 42,919 math spans).
Target validation stops the stage command with exit 1 at exactly the inherited approval-hash
mismatch: 14 targets, 16 trees, one E3 violation. No checks, allowlists, ratchets, targets,
approvals or pins were changed. The branch is not declared ready to merge.

The preserved patch is `/home/ubuntu/work/nlalib-dense-factorizations-wave3.patch`; its
read-only application check against the original checkout is recorded separately. Later
staged sources below are outside this checkpoint until integrated and rechecked.

## Fourth wave: checked staging history

Five new library modules have passed isolated Lean and source checks, without
canonical source/build writes during the checkpoint:

| Staged module | Actual checked guarantee |
|---|---|
| `Matrix/Computation/CompletePivot.lean` | Successful active-column scans and strict global choice; exact absolute row/column outputs, first column-major maximum, unchanged source and two singleton writes; output cells may share a buffer |
| `Matrix/Computation/RowScales.lean` | Rectangular original-row infinity norms, one output vector write, generic safe model requiring only safe zero, empty rows/dimensions and guarded source separation |
| `Matrix/Computation/ScaledPivot.lean` | Successful exact division-free scan, explicit zero-scale handling, first absolute-value/scale maximum and one index write; exact policy, not a rounded cross-product policy |
| `Computation/BLAS/RankOneRounding.lean` | Actual rounded rank-one execution, complete matrix write and actual per-column/product/addition relative-error witnesses; correct empty dimensions |
| `Matrix/Computation/SchurRounding.lean` | Actual saved-pivot execution and frame; entrywise defect at most `u*abs(oldEntry) + roundingFactor 5 u*abs(colEntry*rowEntry/pivot)` for `u<1` |

Independent read-back found no material frame, alias, size or local numerical-model issue.
No full complete/scaled factorization driver or global rounded backward-error certificate is
claimed by these modules. The scale initializer computes fixed original scales; a later row
exchange must carry the scales with the matrix.

The integration lead's isolated runtime checks pass all 123 dense-factorization guards:
78 existing guards after sharing the identical bounded-index adapter, 31 new policy/row-scale
guards and 14 rank-one/Schur guards. The Schur tests deliberately perturb the negative literal
and arithmetic results, then show the five-factor budget holds while a four-factor budget
fails on an active entry. Private execution uses the identical existing Float backend
functions with a narrower import-only harness while high-level dependencies rebuild;
normal canonical builds/runs remain required after integration. The temporary harness is
not copied into the repository. The shared adapter is tool-only, not a scalar-model proof.

Staging roots are `/tmp/nlalib-dense-wave4-{routines,lu,cholesky,root}`. Their new module
artifacts include executable `.ir`/`.ir.sig` companions, which are required with `.olean`
files for isolated runtime imports. These sources have since been integrated into the main sprint worktree.
Fifth-wave source work is isolated separately and reviewed in the plan.

## Historical first- and second-wave verification

The preserved second-wave integration ran under
`TMPDIR=/tmp/nlalib-dense-factorizations-wave2 bash scripts/stage_check.sh`, with log
`/tmp/nlalib-dense-factorizations-wave2/stage.log`. All new modules pass targeted
warnings-fatal builds; source checks pass except the two B1 false positives for `swapRows`
and `luFactor`. The checkpoint had 35 passing runtime guards; two later perturbed-arithmetic triangularity guards also pass. Both generated root import files are updated.
Current whole-library results: warnings-fatal build of all 763 proved modules passed
(4,391 jobs, zero warnings), the 25,267-declaration axiom audit passed, all 14 linters passed,
both-library freshness passed (4,408 jobs), and kernel replay passed for 25,696 constants
across 772 modules with zero violations. All eight replay fixtures passed. The extracted
snapshot has 7,855 public declarations across 763 modules; its full rules check found only
the two expected new B1 false positives and 73 ratcheted baseline errors. References,
constants and LaTeX checks also passed (12,806 docstrings and 42,908 math spans).
Program checks passed for 101 programs/kernels/trees with zero violations or E9 warnings;
all 22 access-model fixtures passed. Target validation finished with exactly the inherited E3
approval-hash mismatch (14 targets/16 trees, one violation). The stage command exited 1 there;
no other new semantic, numerical or naming-rule failures were found. The branch is not declared
ready to merge because that mismatch and the two B1 false positives remain unresolved.

The preserved second-wave patch is `/home/ubuntu/work/nlalib-dense-factorizations-wave2.patch`;
it passes read-only application checking against the original checkout. The next PLU design
is reviewed in the plan; it has not yet been implemented at this checkpoint.

The following table is historical first-wave validation, not a claim that the second wave
has already completed the same whole-library checks.

The full stage check was launched without any worker build running, using
`TMPDIR=/tmp/nlalib-dense-factorizations bash scripts/stage_check.sh`. Its main log is
`/tmp/nlalib-dense-factorizations/stage.log`. Results available so far:

| Check | Result |
|---|---|
| Warnings-fatal build of all 752 proved modules | Pass, 4,380 jobs, zero warnings |
| Axiom/unsafe audit | Pass, 24,987 reachable declarations, zero violations |
| Environment linting | Pass, all 14 linters, zero errors |
| All-library build and generated root import check | Pass |
| Rehashed build freshness | Pass, 4,396 jobs up to date |
| Kernel replay | Pass, 25,396 constants across 760 modules, zero violations |
| Replay fixtures | Pass, eight expected verdicts |
| Program checks | Pass, 86 programs/kernels/trees, zero violations or E9 warnings |
| Target checks | Fail, exactly one E3 violation: inherited registry approval hash mismatch |
| Full stage check | Exit 1 at target validation; branch is not declared ready to merge |
| Declaration extraction | Pass, 753 modules and 7,797 declarations extracted |
| Full declaration/source rules including naming | Fail, one new error: the same B1 `swapRows` false positive; 73 ratcheted baseline errors reported separately |
| Access-model fixtures | Pass, all 22 theorem fixtures |
| Source rules for error modules, lower-solve certificate and Cholesky column | Pass, zero errors/warnings |
| Source rules for pivot scan | Pass, two heuristic S3 warnings on Boolean `decide` expressions in comparison semantics |
| Source rules for row swap | Fail, one B1 false positive described below |
| Bibliography/reference checks | Pass, 143 keys, 91 asymptotic forms, 11 algorithm identifiers, zero problems |
| Generated rule documents | Pass, 14 files current |
| Constants/docstring value checks | Pass, 79 constants, zero problems |
| LaTeX/docstring rendering | Pass, 12,732 docstrings and 42,890 math spans, zero problems |
| `git diff --check` | Pass |

The standalone read-only reference, constants and LaTeX checks were run while the full stage
was checking the library. No worker changed Lean sources or ran another build during it.

Independent read-only reviews found no material mathematical defect in the zero-error bridges,
the residual decompositions, negative-allowance cases, lower-solve empty dimension,
Cholesky-column aliasing, row-swap equal rows/zero columns, or stable first-maximum invariant.
Those reviews complement kernel checking; they are not numerical benchmark results.

Two known validation issues must remain visible:

1. `check_rules.py` classifies `Computation.swapRows` and `Computation.luFactor` as numerical
   bounds because its suffix regex includes `Rows` and `Factor`, despite their `Builder`
   result types. These are B1 false positives. The reviewed names were retained; no fake
   bound registration or checker
   workaround was introduced.
2. The isolated checkout inherits the committed target approval SHA
   `a414c7794a2c78d52d77b599f420e89faab79cbe166094c050cb51bf3ea84768`, while the unchanged
   registry hashes to `8342ffa0b3d299d6c525f50d395fe47d827851c2cd82ff2d0ddf84ebe097ea45`.
   The original checkout already has a user-owned uncommitted correction to the latter hash.
   The sprint did not modify or approve either registry or approval file.

Do not call the branch ready to merge unless the required stage check exits zero.

The declaration-level rules log is `/tmp/nlalib-dense-factorizations/rules.log`. The target
checker found exactly the inherited approval mismatch; its other target fixtures ran. The
remaining source/name blockers are the B1 false positives already identified independently.
The duplicate-statement report was not reached by the stage check and is not claimed run.

A reviewable patch is saved at `/home/ubuntu/work/nlalib-dense-factorizations.patch`. It
contains the new Lean modules, shared proof lemmas, runtime examples, generated root imports,
vocabulary additions and design/audit records. It excludes the target registry, approval file,
checks, pins, build
artifacts and the original checkout's `.claude/` directory. The read-only application-check
log is `/tmp/nlalib-dense-factorizations/patch-check.log`.

## Next algorithm work

The current result includes full exact Cholesky, no-pivot LU, partial-pivoted PLU and
complete-pivoted PLUQ, plus a full actual rounded partial-pivoted backward-error certificate.
The no-pivot driver retains its explicit nonbreakdown premise; Cholesky's exact driver
requires SPD input. Partial and complete exact pivoted drivers admit singular inputs.

Remaining numerical work includes global rounded Cholesky nonbreakdown/stability and
finite-range IEEE safety. The full Cholesky driver currently uses saved-pivot Gaussian
Schur updates while forming its columns with square roots. A future analysis must follow
that actual order or first review a symmetric update using computed normalized columns.

Scaled selection and the matching matrix/scale pivot operation are implemented; a complete
fixed-scale factorization driver still needs weighted-prefix/zero-row covariance. Full
rounded complete pivoting, pivoted factor-then-solve programs with actual RHS/solution
permutations, rook/threshold search, LDL/semidefinite cases and blocked operands also remain.
Blocked work must settle leading dimensions or panel packing before treating a trailing
matrix as a packed smaller matrix. Registered cost targets require maintainer review.

These later work packages and the full 48-hour schedule are not claimed complete. No account
quota or automatic 48-hour continuation was established or reserved.
