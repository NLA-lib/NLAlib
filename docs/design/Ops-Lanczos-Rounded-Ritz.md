# Ritz residuals from actual rounded Lanczos storage

The ordinary rounded solver already returns an `Output` containing a single extracted
`LanczosRun`, its actual packed values and the initial-normalization defect. This addition
exposes the standard Ritz residual bound directly in terms of those packed values. It does
not assert that rounded basis columns are mutually orthogonal or that the Ritz vector is unit.

Use the common `basisMatrix dec n vs q` and `tridiagonalMatrix dec cap cs q` decoders in
`Lanczos/Spec.lean`. `Rounded/PackedOutput` prefix facts equate these matrices to the same
extracted run's matrices. No new numerical object or bound is introduced. The run's existing
`norm_mulVec_basis_mulVec_sub_smul_le` supplies the entire residual estimate.

The main output consequence accepts `Output dec A rhs E cap vs cs`, positive cap, nonzero
input and `cap * E ≤ 1/100`. It returns a positive active length `m+1 ≤ cap` for which every
unit eigenpair of the decoded tridiagonal has physical Ritz residual bounded by
`sqrt(1+E) * decodedBeta * abs(lastCoordinate) + lanczosResidualFactor (m+1) * E * specNorm A`.
The residual factor is the existing `6q*sqrt(q)`; no new constants registry entry is needed.
Early breakdown uses the actual executed length; zero tails are excluded from the Ritz prefix.
The bound concerns an unnormalized physical Ritz vector. Converting it to an eigenvalue-error
bound would additionally require a lower bound on that vector's norm, so none is silently added.

`Krylov/Lanczos/RoundedRitz.lean` owns matrix readback bridges, `RitzResidual` stored-data predicate, output-level residual guarantee,
and a total `runs_solve_ritz` corollary using the unchanged ordinary rounded `runs_solve` and
`ConditionalRuns.mono`. All input-model/precision/buffer assumptions remain explicit; there
is no successful-execution premise. Zero input/cap remain handled by `runs_solve`; the Ritz
corollary uses explicit positive-cap/nonzero-input assumptions to state a nonempty eigenpair.
Mathlib and NLAlib were searched; the existing pure LanczosRun Ritz theorem is reused.
No primitive implementation, algorithm tree, target registry or core contract changes occur.

## Named models for the full reorthogonalized solver

`Reorth/RoundedModels.lean` supplies `wellTyped_program`, `runs_solve_of_model` and
`runs_solve_standard` for the same complete two-pass program and actual rounded history.
These reuse `Standard.Model.laws`, `Precision.of_budgets` and proved profile refinement.
The model wrapper retains the declared workspace; the lowering wrapper pushes the complete
primitive/query count through the chosen exact, sequential or pairwise implementation.
No matrix-symmetry premise is needed for this local-history guarantee. This wrapper does
not claim the stronger global orthogonality or spectral conclusions of LanczosReorthRun.
The ordinary full-solver wrappers provide the template; no execution proof is duplicated.

The total solver corollary uses `RitzOutput`, retaining the entire original `Output` plus
`cap = 0 ∨ rhs = 0 ∨ RitzResidual ...`. It therefore accepts zero cap/input as well. Only the
output-level nonempty Ritz lemma needs the explicit nonzero assumptions described above.
`Lanczos/RitzCertificate.lean` applies `Algorithm.mapPost` to the same output consequence,
retaining its original full count, work, span and memory bounds. `ritzSpecification` changes
only the numerical postcondition; `ritzAlgorithm` accepts the original certificate and the
size-only linear precision bound.
