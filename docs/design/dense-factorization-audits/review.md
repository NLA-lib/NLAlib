# Dense factorization sprint: independent review

Reviewed the current sprint files on 2026-11-24. This review makes no code changes and does not stand in for the integration stage check. Source line numbers refer to the files as read during the review; PivotScan is still being extended by its owner.

## Findings

No blocking mathematical correctness defect found in the reviewed statements. Two validation/delivery distinctions require accurate reporting:

1. **Confirmed baseline registry approval mismatch.** In `/home/ubuntu/work/nlalib-dense-factorizations`, `docs/targets.approved` contains `a414c7794a2c78d52d77b599f420e89faab79cbe166094c050cb51bf3ea84768`, while `sha256sum docs/targets.toml` is `8342ffa0b3d299d6c525f50d395fe47d827851c2cd82ff2d0ddf84ebe097ea45`. `scripts/Targets.lean:1003` computes that hash and lines 1008–1010 emit E3 for mismatch. The original `/home/ubuntu/nlalib` has the same registry and an existing user-owned uncommitted approval-file change to the matching `8342ffa0…` value. The isolated checkout inherited the committed approval file. This issue predates the sprint. Do not edit protected approval files or blame the new routines for it. It will fail the target-check stage if execution reaches it under the default environment; an earlier check failure can stop the script first.

2. **Current pivot-loop theorem is not the full designed `argmaxAbs` routine.** `PivotScan.lean:251–287` certifies `pivotScanLoop` with caller-initialized magnitude, exact-zero and index cells, three-cell workspace of the prescribed shape, and separate input/workspace/index buffers. It preserves shape and cells outside those visible workspace/output locations. The design's scoped wrapper (`docs/design/Matrix-DenseFactorizationRoutines.md:243–265`) additionally promises workspace allocation/initialization and a single net output-word write. Those are meaningful further proof obligations, not consequences of the loop statement alone. Report the wrapper as complete only once its concrete success-and-write theorem is present and checked.

The known source-check B1 false positive on the builder `swapRows` is separate from both findings: the rule's suffix regex includes `Rows` and ignores the builder return type. The reviewed name remains unchanged; no bogus numerical-bound row or allowlist change was made.

## Row-swap edge cases

`RowSwap.lean:213–221` quantifies over an arbitrary word carrier and interpretation. It requires only initialized input entries and two valid row indices, then concludes actual execution success, one initial-to-final packed block write, and final `Holds` of `A.submatrix (Equiv.swap r s) id`.

* Equal row indices are valid: the temporary retains the original word and the three-copy sequence restores it.
* Arbitrary offsets and rectangular leading dimension are explicit. The address-injectivity proof uses quotient/remainder, preventing accidental column aliasing.
* Zero columns are valid. The input matrix read premise is vacuous, no source buffer existence is required, and the empty output block write is the original store.
* Zero rows are outside this theorem because no valid row index exists. This is the correct boundary for a requested row exchange, not a claim that all empty-matrix operations fail.
* Scratch is scoped and its net writes disappear. The final block-write equation preserves every other cell and shape. No scalar numerical contract, exact-literal assumption or zero value of the word carrier is smuggled in.
* It does not claim a cost certificate, dynamic pivot-index conversion, column swaps or a complete LU driver.

The author checked `lake lean` without warnings. This review inspected its statement and proof structure but did not rerun builds during the integration quiet period.

## Pivot-scan edge cases

At the reviewed snapshot, `copyAbs` uses a decoded sign comparison and exact negation, so it avoids rounded squaring and handles positive, negative and zero entries exactly under the scalar contract. Its destination may alias either source cell because comparison and source reads precede the one write.

`exec_pivotScanUpdate` retains the incumbent on equality. Its separate best/index cell premise is necessary; the candidate may alias another cell without falsifying its output relation because its original word is read before writing. The stronger disjoint-buffer hypotheses of the loop ensure its actual input and zero cells remain unchanged.

`exec_pivotScanLoop` explicitly assumes `0 < N`, initializes the incumbent specification to index zero, and scans in increasing order including zero. The invariant's strict inequality for all indices before the incumbent proves deterministic first-tie selection. Thus the singleton and all-zero cases select zero. The returned index lies in `Fin N`, its word decodes exactly to the natural index, and global maximality concerns the original decoded stored vector. No claim is made about the unrounded elimination state. The empty-vector case is intentionally outside the selected-index theorem.

The exact-index-literal bound `N ≤ B` is sufficient, though stronger than the largest literal used (`N-1`). No `toNat` claim follows from literal exactness alone; a later pivot driver using `bindIdx` still needs the existing conversion contract.

## Schedule and completion claims

The 48-hour table is explicitly an engineering estimate (`design:26–30`), uses only the three available worker slots plus integration lead, and has fallback gates at 12, 24 and 36 hours. It does not reserve account quota or promise automatic continuation (`design:346–348`). No overclaim is present if it is presented as the remaining execution plan.

Keep the following boundaries in the final delivery report:

* Current error interfaces and residual consumers are not full floating-point LU/Cholesky execution certificates.
* A Cholesky square-root/normalization column still needs the Schur update and global SPD/rounded nonbreakdown proof for a complete factorization.
* Exact partial-pivoting growth bounds on mathematical `gaussState` do not automatically hold for actual rounded elimination.
* Complete pivoting additionally needs column exchanges and active-submatrix traversal with a parent leading dimension. A contiguous vector scan alone does not supply that traversal.
* Scaled pivoting needs a chosen scale convention and zero-scale behavior. Rook pivoting requires termination/tie/fuel analysis. These remain stretch scope.
* The numerical cases listed under verification (`design:318–322`) are coverage requirements for future drivers; do not report them as a test suite that was already run unless those tests are actually created and executed.

No code, registry, check, allowlist or pin files were edited for this review.

## Integration review addendum

The LU and Cholesky workers independently reviewed the root-added linear-solve residual and
two-solve LU composition theorems. No material correctness issues were found. The generic
mathematical statements do not require nonnegative allowances: each inequality is multiplied
only by nonnegative norm weights. Both the factorization error and solve perturbations remain
explicit; neither theorem assumes invertibility or asserts execution by itself.

The final pivot wrapper, if included, must be validated separately from the earlier initialized
workspace scan reviewed above. The isolated checkout preserves the original worktree and its
user-owned changes.

## Final scoped pivot wrapper review

The LU/pivot worker subsequently reviewed the completed `IsRelErrSem.exec_argmaxAbs` and
`executionComposable_argmaxAbs` read-only. No blocking correctness or footprint issue was found.
The earlier caller-owned-workspace caveat is closed by the final wrapper: it proves actual
successful execution, one initial-to-final singleton block write, an index in `Fin N`, exact
decoded index, absolute maximality and strictly smaller magnitudes at earlier indices.
Initialization establishes zero, the first input magnitude and index zero; the scope/pop bridge
releases all three scratch cells. Separate input/output buffers preserve the original vector.
All-zero and singleton inputs select index zero; the empty input is explicitly excluded.
The literal bound `N ≤ B` is sufficient. No conversion to a dynamic index, cost bound,
strided scan or complete pivoted factorization is claimed.
