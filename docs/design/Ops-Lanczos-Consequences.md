# Mathematical consequences of stored Lanczos data

The existing exact total solver outputs identify stored words with the pure Lanczos recurrence.
This work exposes the mathematical API that consumes those outputs, shared by ordinary and
full-reorthogonalized Lanczos. No execution semantics or primitive assumptions change.

## Objects and interfaces

Two computable packing decoders live in `Krylov/Lanczos/Spec.lean`:

```
basisMatrix (dec : K → ℝ) (n : ℕ) (vs : List K) (q : ℕ) : Matrix (Fin n) (Fin q) ℝ
tridiagonalMatrix (dec : K → ℝ) (cap : ℕ) (cs : List K) (q : ℕ) :
  Matrix (Fin q) (Fin q) ℝ
```

The first reads column-major words at `j*n+i`. The second reads alpha at `i` and beta at
`cap+i`, using the ordinary prefix shared with reorthogonalized output. Both are concrete
`Matrix.of` constructions. No new mathematical notion, numerical bound or hypothesis predicate
is introduced. Missing words use the existing total `Ops.vec` behavior; output contracts and
actual readable block sizes establish the intended meaning for admitted prefixes.

## Statements and consumers

`Output.basisMatrix_eq_arnoldiMatrix` takes Hermitian input and `q ≤ cap+1`, without a grade
restriction. `Output.hasOrthonormalCols_basisMatrix_iff` says a stored prefix is orthonormal
exactly when `q ≤ krylovGrade A b`; padded zero columns are never called orthonormal.
`Output.range_basisMatrix` identifies the Krylov space even beyond the grade.
`Output.tridiagonalMatrix_eq` takes `q ≤ cap` and equates actual stored coefficients to
`(basisMatrix dec n vs q)ᴴ * A * basisMatrix dec n vs q`, including breakdown and zero tails.

The ordinary and reorthogonalized exact `runs_solve_ritz` corollaries retain their total
successful execution and existing conditional budgets. They identify actual packed output and
apply the existing Kaniel–Paige–Saad bound to any stored prefix with `q+1 ≤ cap` and
`q+1 ≤ krylovGrade A b`. The start has positive spectral mass at the largest eigenvalue and
the remaining spectrum lies in `[a,c]` with `a<c<eigenvalue A 0`. The conclusion bounds
`eigenvalue A 0 - eigenvalue (tridiagonalMatrix dec cap cs (q+1)) 0` by the existing explicit
Chebyshev/tangent expression. The coefficient eigenvalue is a mathematical consequence of the
stored tridiagonal; the Lanczos program itself does not execute an eigensolver.

Output-level PSD gap-free bounds and separation are additional consumers of the same shared
compression bridge. Reorthogonalized output reuses `Output.toOrdinary`; no recurrence or
convergence mathematics is reproved. Full cap zero/input zero/breakdown remain accepted by
existing total solvers; eigenvalue convergence requires a nonempty admitted active prefix.

## Files and material

`Spec.lean` owns the common decoders and prefix/compression facts. `Basis.lean` owns ordinary
stored-output solver consequences. `Reorth/Basis.lean` owns the corresponding total reorth
consequences. The generated library root is updated by the integration owner.

Mathlib was searched for Lanczos/Arnoldi/Ritz material; no solver-specific material was found.
Existing NLAlib pure `Processes/Lanczos.lean`, `Processes/LanczosRecurrence.lean` and
`Eigenvalues/Ritz.lean` supply basis, grade, compression and convergence. Shared machinery is
`Output.toOrdinary`, `ConditionalRuns.mono`, and the new common decoder equalities. No new
frame, memory-layout execution or spectral proof is planned. No open design questions.

## Actual sequential-AXPY reorthogonalization

`Reorth/RoundedOrthogonality.lean` bridges the actual `PassOut`/`TwoPassOut` witnesses to the
existing `IsOrthErr` interface. It imports the pure `isOrthErr_of_two_passes` algebra and
reuses it with exact ghost coefficient addition (`u = 0`), not the old matrix-update program.
For dot allowance `ed ≥ 0`, axpy allowance `ea ≥ 0`, `B = 1 + eta`, and `k` columns, a safe
single-pass envelope is

```
(k + 1) * ed * B^2 + ((1 + ea)^k - 1) * (1 + k * (1 + ed) * B^2) ≤ c1.
```

The near-basis antecedent `specNorm (Qᵀ * Q - 1) ≤ eta` bounds each column norm and `specNorm Q`
by `B`. Cauchy–Schwarz bounds each computed coefficient and dot defect. The existing certified
AXPY-chain representation bound gives the update defect. Their sum gives all three single-pass
premises of `isOrthErr_of_two_passes`. For `0 ≤ eta ≤ 1/100` and `c1 ≤ 1/100`, actual two-pass
output therefore supplies exact summed ghost coefficients and
`IsOrthErr eta (2*c1) (3*c1) (2*(eta+c1)^2) Q w h w'`.

This theorem is local and unconditional with respect to execution or breakdown. Its basis
hypothesis is the antecedent inside `IsOrthErr`, not an assumption of algorithm success.
It does not derive strict `tau * nu_j < beta_j` for a complete Lanczos run. Such admissibility
selects a genuine prefix of actual history and can fail near breakdown; exposing that selection
and transferring global reorthogonalized spectral bounds remains a separate mathematical step.

`Reorth/RoundedAnalysis.lean` exposes the same local orthogonalization theorem from the final
executed `History`. The witness preserves the actual first/raw/reduced vector words, computed
pre/post norm words, normalized output words, update bounds, both norm contracts, scaling
contract and the ghost coefficient vector. Its basis is exactly
`LanczosReorthRun.basisOf z.v (j+1)` from the final archive. No execution or store theorem is
repeated, and no numerical transition is replaced by an unrelated existential run.

## Shared mathematical step and admissible-run construction

The existing pure `LanczosReorthImplementation.RoundedStep` record moves without renaming or
field changes from `Processes/LanczosReorthProgramRoundedStep.lean` to
`FinitePrecision/LanczosReorthStep.lean`. The former imports the latter; its execution proofs
remain unchanged. This removes the requirement to import an old execution development to
consume the same mathematical local-error interface.

The new pure `LanczosReorthImplementation.exists_run_of_steps` constructor takes a symmetric
matrix, fixed archived vector and coefficient sequences, a positive prefix length, a zero
previous vector/coupling, a nearly unit initial vector, nonnegative small error parameters,
strict `tau * nu(j+1) < beta(j+1)` on that prefix, and actual `RoundedStep` witnesses at each
step using `IsOrthErr`. It returns `LanczosReorthRun` with exact identities for the matrix,
archived vectors/coefficient sequences and all numeric parameters. Local witnesses are
chosen once; error sequences are their algebraic differences, without new execution proofs.
The prefix-selection layer supplies strict admissibility from a total first-failing test and
retains an explicit zero-prefix alternative; it does not assume full-run admissibility.

`IsNrm2Err.norm_error_bounds` in `Lanczos/Math/NormGuard.lean` extracts nonnegativity and the
relative norm bound from actual dot/sqrt witnesses. `Precision.norm_error_le` in
`RoundedPrecision.lean` proves the derived norm allowance is at most the common error envelope,
and its actual-word corollary provides the `RoundedStep` norm fields. Existing numerical
statements and algorithms are preserved.

## Placement of shared coordinate-vector estimates

The five pure componentwise update, dot, division, norm and normalization estimates move from
`Krylov/Lanczos/Math/RoundedLocal.lean` to the existing
`ForMathlib/Analysis/InnerProductSpace/PiL2.lean`, in namespace `EuclideanSpace`. They have no
NLAlib objects or program vocabulary and are upstream candidates for Mathlib's PiL2 API. Their
statements and proofs are preserved; Lanczos callers import and use this shared mathematical
home directly. The old module is deleted entirely, with no compatibility shim or aliases.
`docs/renames/2026-11-lanczos-vector-bounds.json` records the namespace moves.
