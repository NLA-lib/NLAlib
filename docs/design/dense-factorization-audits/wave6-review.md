# Final dense-factorization statement review

## Rounded partial-pivoted execution

The public generic-word theorem follows the actual stored `pluFactor` program. Backend
assumptions are the existing scalar relative-error model with all results in range and the
existing bounded exact-index model. Exact integer literals are needed for both numeric
branch controls and the lower factor's diagonal one; relative-error literals alone would
not give a unit diagonal. The theorem has no successful-run premise.

The runtime invariant stores actual decoded residual/factor matrices and actual history
reads. Its numerical field is conditional on `u < 1`, so success, triangular structure and
the multiplier bound `1+u` do not inherit an unnecessary small-roundoff premise. A selected
zero pivot is a zero decoded active column by the actual absolute-max scan. The total
materialization and Schur branches then avoid division. No nonsingularity premise is used.

The numerical prefix reconstructs the currently row-permuted input as an active residual
plus committed factor products. Inactive residual entries may contain cancellation noise;
a zero pivot row may retain a nonzero suffix. Only committed diagonal entries are one.
Row swaps transport both residual and factor/error data, preserving earlier upper rows.

For a nonzero step, the local product has four factors: negative literal, coefficient
division and two multiplications. Solving the update backward puts the inverse addition
factor into the next residual coefficient; the new factor-product coefficient gets the
inverse lower-division factor. Its count is `k+5`, while the next residual count is `k+1`.
At completion `t<N` implies `t+5≤N+4`. The resulting componentwise error is the existing
`IsLUErr` with `roundingFactor (N+4) u`, for `u<1`; no `N*u<1` condition is needed for this
library's rounding factor. Actual output arrays and the actual stored log feed the routine
certificate. Independent review found no material issue in this chain.

## Complete pivoting and scaled policies

Complete-pivoted LU uses independent current-position-to-original-index decoders for its
actual row and column logs. Its explicit convention is `A.submatrix σ τ = L * U`. The
runtime exchanges residual and prior lower rows, and residual and prior upper columns.
Omitting either factor exchange would be incorrect. Complete maximum prefixes and total
elimination support singular and empty input. Independent review covered both orientations,
the four-output frame and the concrete zero-error routine instance.

Runtime tests replay both logs independently of the library decoder. Examples force later
column swaps through two previously committed upper rows and use distinct row/column orders.
First ties refer to each actual pre-swap selection prefix, not an overstated final order.

Row scales are original-row infinity norms, including zero for empty rows. They follow
the same row exchange as the residual. The division-free selector explicitly handles zero
candidate and incumbent scales; blind cross multiplication against a zero incumbent fails.
Its policy theorem uses exact semantics. The pivot operation needs zero-scale compatibility
only in its active column, not an unstated whole-row-zero condition. No unscaled multiplier
bound or full scaled-pivoted factorization is claimed.

## Storage, helper reuse and validation boundaries

Actual generic-word arrays and scoped-pop reconstruction use shared matrix-storage lemmas,
with no artificial zero or algebraic structure on the word carrier. Exact and rounded Schur
analyses share strided copies and operand preparation. Row/column exchanges share the same
three-copy cell operation. Zero-pivot branches share their actual literal/copy builders.
Checked equalities preserve emitted instructions through these refactors.

Canonical checks caught proof lengths that isolated staging checks had missed. Those proofs
were split into named lemmas while preserving public signatures and executable definitions.
The three duplicate suffix views now use Mathlib's existing embedding and one value lemma
in the matching `ForMathlib` topic. No checker or allowlist was modified. Remaining
comparison-expression and exact-versus-rounded/axis-specific private-name warnings are
reported as heuristics, rather than hidden by renaming.

The tool Float runs are finite regression evidence. They do not instantiate the formal
scalar/index assumptions for arbitrary IEEE inputs. Full rounded Cholesky nonbreakdown and
stability remain future work: explicit upper-prefix zeros establish triangular storage, but
the saved-row/column update can still create skew under rounding. Registered cost targets,
blocked operands, LDL and further pivot-policy drivers also remain in the plan.

Final extracted API and environment checks additionally caught a simplifier-attribute
conflict, a constructed proof in the new finite-index lemma's statement, and one
conclusion/name mismatch. The value lemma now takes its bound proof as a parameter and
stays off the global simp set; pivot consumers use it explicitly. The column estimate is
`PLURounding.abs_column_le_one_add`. Actual targeted environment lint (all 14 linters) and
warnings-fatal builds pass after correction. No exemptions or alternate runtime definitions
were introduced; the final complete checkpoint is rerun on the corrected sources.
