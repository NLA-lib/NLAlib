# Exact symmetric diagonal-pivoted semidefinite Cholesky

Frozen library sources and private artifacts; no canonical sources, shared caches, protected
checks/targets/pins, commits or pushes changed. Parent owns integration and full stage checks.

## Manifest

Copy only these seven new source files from this staging root:

- `NLAlib/Matrix/Factorizations/CholeskyPivoting.lean`
- `NLAlib/Matrix/Computation/DiagonalPivot.lean`
- `NLAlib/Matrix/Computation/PivotedCholeskyFrames.lean`
- `NLAlib/Matrix/Computation/PivotedCholeskyPrefix.lean`
- `NLAlib/Matrix/Computation/PivotedCholeskySteps.lean`
- `NLAlib/Matrix/Computation/PivotedCholeskyInitialize.lean`
- `NLAlib/Matrix/Computation/PivotedCholesky.lean`

The Cholesky worker separately owns the exact certificate and smoke tool in
`/tmp/nlalib-next-pivoted-cholesky-cert`; do not confuse those with dependency links here.
Dependency-only frozen selector overlays `StridedPivotScan` and `CompletePivot` come from
the earlier selector delivery and must not be recopied as new edits.

## Runtime and theorem

`pivotedCholesky tag n A ao L lo H ho` allocates a scoped N² residual, copies the original
matrix before output changes, zeros the entire factor, and executes N actual steps. Each
step packs/scans the active diagonal with `argmaxStridedAbs` at stride N+1, stores the first
maximum as an absolute current-position index, consumes that actual word to swap residual
and full factor rows, consumes the retained word to swap residual columns, then invokes
the existing total Cholesky-column and Schur builders. Zero pivots never divide or take a
square root. The two bounded conversions read the same retained actual log word.

`exec_pivotedCholesky I hI hc tag st n A ao L lo H ho M hPSD hinput hL hH hLH`
requires only original PSD input, readable source, writable factor/history and distinct
factor/history buffers. Source may coincide or overlap with either output. It returns an
actual successful run, the original store's two ordered full net writes, actual p with
j≤p(j), final factor Holds, actual history reads, lower triangularity, nonnegative diagonal,
and the exact identity

`M.submatrix (luPivotPermutation p N) (luPivotPermutation p N) = F * Fᴴ`,

where F is the canonical `choleskyLower` of that actually permuted input. The fold uses
current-position to original-row indices and the same permutation for both input axes.
The first-tie result belongs to the pre-swap local selector; no invalid retrospective tie
claim is made about the final permuted input.

`exec_pivotedCholesky_of_zero` works for arbitrary word carriers, scalar semantics and charge
monoids, with no carrier Zero/Inhabited instance, valid handle, alias or source assumption.
It proves actual success and restored scoped store even if every handle is invalid/equal or
an output equals the freshly allocated residual handle. Allocation metadata may change.

The implementation gives exact singular PSD success, not tolerance-based rank detection,
rounded PSD nonbreakdown, or native optimized BLAS performance. Existing strict-positive
`IsCholesky` / `IsCholeskyErr` predicates are unchanged and are not used to certify singular
PSD output. The separate new exact routine certificate uses raw lower/nonnegative/Gram facts.

## Proof and placement

The generic RCLike mathematical transport of completed canonical columns uses existing
`gaussState_submatrix` and the actual `luPivotPermutation_update` decoder. Actual storage
prefixes use the existing PLU frame with its two factor slots coincident, avoiding a second
generic frame vocabulary. New proof files separate symmetric swaps, initialized prefix,
total step, initializer and final driver. The existing lower/column/Schur primitives and
shared storage bridges are reused; no core GaussState/ForMathlib changes or copied pivot-scan
arithmetic proof family was needed. No scalar semantics or matrix factor predicate added.

All seven sources pass sequential private Lean with every project option and warnings as
errors. The final source scan passes 0 errors and 0 warnings. Private executable artifacts
were regenerated with `-o` only and every owned IR header checked as binary `olean`; an early
incorrect `-i .ir` invocation was caught before any smoke guard ran and fully corrected.
Artifacts for the frozen delivery live beside these sources; the identical-source QA output
tree `/tmp/nlalib-next-pivoted-cholesky-fullcheck` is not a second source delivery.

The independent Cholesky worker reports the exact routine certificate strict-clean and all
30 actual `PivotedCholeskySmoke` guards passing against the regenerated binary closure.
Cases include an exact dyadic three-cycle with log `[1,2,2]` and a late full-factor row swap,
rank-one/rank-two/zero PSD matrices, ties, offsets/sentinels, both source-output overlaps,
all-tag/scoped store framing, zero-branch success with division and square root rejected,
negative-input rejection, and empty all-invalid/all-aliased/fresh-handle collisions.

Public runtime vocabulary for parent integration: `diagonalPivotChoice`,
`PivotedCholesky.symmetricCholeskyPivot`, `pivotedCholeskyStep`, `pivotedCholeskyBody`,
`pivotedCholesky`, and `PivotedCholesky.State` (execution invariant). The separate certificate
worker owns `IsPivotedCholeskyRoutine`.
