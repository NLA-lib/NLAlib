# Third-wave statement and integration review

This records source review during integration. Final verification numbers belong in the
delivery record after the whole wave is frozen.

## Singular partial pivoting

The stored permutation is decoded from the actual pivot log, rather than independently
chosen. A log entry is the absolute current row position selected at that step. Decoding
composes each swap on current positions, yielding the convention `PA = LU` and the RHS
permutation `b ∘ σ` for a later solver. The generic routine certificate requires actual
final decoded log reads, three sized output arrays and their exact block-write equation.
The row-pivoting worker reviewed this formulation without finding a decoding or frame gap.

The prefix invariant retains total `gaussState`, not a stronger cleared-previous-row
condition. A singular zero column can have a pivot row with a nonzero suffix. Active row
permutations fix previous pivot positions, preserve completed upper rows, carry completed
lower columns and transport previous pivot maximality. Those pure transport lemmas make no
nonzero-pivot assumption. At a maximal zero pivot the active column is zero, which is the
compatibility condition needed by the existing total mathematical LU theorem.

The guarded local routines themselves have a weaker, explicit statement: they execute
successfully for any stored residual, even a zero pivot with nonzero entries below it.
They implement total division by zero as zero multipliers and skip the Schur update. They
make no standalone assertion that such an arbitrary residual has an LU factorization.
The global pivot invariant supplies the compatibility required for that conclusion.

The driver swaps complete initialized lower-factor rows. Thus committed columns follow
the row exchange and uncommitted values remain initialized. The upper factor and earlier
log entries survive each step by the four-block frame. Future log cells need not be
initialized. Empty dimensions do not justify reading any factor, source or log handle.

## Cholesky triangular storage

The full driver now explicitly writes zero literals above each newly formed diagonal.
The old generic column helper copies residual entries there, so cancellation noise could
otherwise enter the factor under rounded arithmetic. The exact execution proof treats
these zero writes as identity store updates. Runtime regressions separately establish
that perturbed Schur multiplication leaves residual noise and that the returned upper
factor entry is still exactly zero. This is a structural correction, not a global rounded
stability or success theorem; full Schur updates can still drift from symmetry.

## Storage reuse and remaining review

`Computation/MatrixStorage.lean` owns rectangular packed readback and identity writes,
shared by LU initialization and guarded elimination. The old private LU duplicate was
removed. No encoding, scalar semantics or allocation primitive was introduced.

The runtime reviewer independently replays recorded swaps and multiplies computed
factors, including singular zero-column examples. Final source checks, warnings-fatal
builds, runtime guards, whole-library audit and kernel replay must be recorded after
the integrated driver and its concrete routine instance have finished checking.

The Cholesky worker independently read the completed initializer, headline theorem and
routine instance without finding a material issue. The zero-dimensional proof takes the
empty-body path before the positive-capacity initializer. The public exact guarantee
also returns multiplier bounds, actual factor reads, actual log reads and retained source.
This review does not replace the final Lean build and kernel replay.

The full extracted rule check found two general finite-order swap facts in the runtime
prefix topic and one conclusion/name mismatch. The swap facts were moved to the existing
`ForMathlib/GroupTheory/Perm/Fin.lean` topic as `Fin.swap_apply_of_lt_of_le` and
`Fin.le_swap_apply_of_le`. The matrix identity is now
`PLU.submatrix_luPivotPermutation_update`. All actual uses were updated; no compatibility
aliases or checker exemptions were added. The corrected driver/certificate leaf chain passes
warnings-fatal builds, and the final whole-library rebuild/audit/replay is running.
