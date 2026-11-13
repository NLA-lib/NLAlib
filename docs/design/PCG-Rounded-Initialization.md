# Rounded zero-start PCG initialization

The exact PCG solver's initializer evaluates the residual through a matrix product and an
axpy. Its rounded result need not equal the right-hand side even when the supplied iterate
decodes to zero. The numerical `PCGRun` model instead requires that equality.

`Krylov/CG/HSPCG/FinitePrecision/Initialization.lean` therefore supplies the zero-start
initializer as an explicit fixed tree: copy the raw right-hand side into the residual,
apply the tagged inverse preconditioner, and copy its actual output into the direction.
The supplied zero iterate is retained. This matches the first three vector conditions of
`PCGRun` without replacing a computed vector by an exact product.

The local preconditioner contract reuses `Ops.matvecErrorRel`; the allowance is absolute
in operator norm. The total `initialize_spec` takes rounded `IsBlas1` and that tagged
primitive contract. Its output relation states the decoded zero iterate, unchanged raw
residual, identical preconditioned residual and direction, and the normwise preconditioner
error. No positive definiteness, rank, nonzero right-hand side, or successful-run assumption
is needed. `initialize_writes` exposes those actual stored outputs for composition.
`initialize_count` and `initialize_peak` use the existing syntax evaluators and count two
copies and one preconditioner application, with no allocation in the tree.

The consumer is a rounded PCG round/solve extraction. That extraction is still missing:
ordinary CG's three-vector/cache recurrence does not supply PCG's fourth vector or tagged
operator calls. Residual-reorthogonalized CG likewise has only exact sweep/solve certificates;
a rounded sweep must retain every computed projection coefficient and its local dot,
division and axpy errors before connecting the archived basis to a numerical run.

Existing `InitializeOperands`, `decodedState`, `StoresState`, `cert_intro`, `step`, and shared
block-update/frame rules handle all memory bookkeeping. No new generic memory machinery
or Mathlib notion is introduced. Searched the existing Ops and PCG initializers; no rounded
PCG initializer exists. The new `IsPreconditioner` is the tagged spelling of the existing
rounded matvec primitive, parallel to `IsExactPreconditioner`. No printed source for these
execution bridges; the recurrence is [Saad2003, Algorithm 9.1].

`HSPCG/FinitePrecision/Preconditioner.lean` adds the functional bridge needed by
`PCGRun.z_eq`: `oracleRel` relates the actual real-word output to a supplied
`MatvecOracle.mulVec`, and `meets_preconditioner_oracle` derives that relation from the
local `matvecFn` primitive semantics. `isPreconditioner_of_oracle` recovers the normwise
contract. `initializeOracleRel` and `initialize_oracle_spec` identify the same actual
initial vectors with this fixed action. The oracle action need not be linear; its reference
matrix alone must be positive definite for `PCGRun`. Thus no mathematical model change is
needed, but a bare relational error contract cannot supply functional consistency by itself.

## Active rounded steps

`HSPCG/FinitePrecision/Step.lean` certifies the existing HSPCG step tree. `Margins` states
an incoming residual/preconditioned-residual dot margin and a curvature margin uniform over
products allowed by the system's matvec contract. These mathematical inequalities imply
positivity of both actual computed divisors; no success hypothesis is used. `RoundBounds`
records the actual product, pairings, scalar quotients and four updated vectors, including
identity with the fixed nonlinear oracle action. Scalar relative errors and componentwise
BLAS errors are retained separately. The target `step_spec` takes `IsScalar`, `StdModel`,
`IsBlas1`, system `IsMatvec`, and the local functional tagged preconditioner contract.
`step_writes` exposes the resulting stored state; the existing AST gives the resource counts.

A full `PCGRun` extraction must also identify a recomputed incoming dot with the preceding
round's final dot. The fixed scalar BLAS backend supplies this functionality; generic
relational rounded BLAS contracts alone do not. Final numerator nonnegativity must likewise
be derived from suitable input/precision assumptions before claiming a run certificate.
The active-step bridge deliberately asserts neither unproved fact. Existing decoded BLAS
bounds and scalar standard laws are reused, as are shared block and allocation proof rules.

`HSPCG/FinitePrecision/Guards.lean` derives both local input margins from separate spectral
windows and precision inequalities for the system and reference inverse preconditioner,
using the actual oracle identity and nonzero incoming residual/direction. It reuses the
ordinary CG curvature-margin theorem, so the nonlinear oracle needs no new positivity axiom.
These are local mathematical assumptions, not a complete full-loop nonbreakdown proof.

The missing global result is propagation of a nonzero search direction from a nonzero
residual throughout rounded PCG under raw-input spectral/precision assumptions. Existing
`PCGRun` assumes positive pairings/curvatures and does not prove this continuation fact.
Moreover, the existing fixed-horizon HSPCG tree has no residual-zero stopping guard; SPD
alone cannot justify arbitrary horizons, even at zero rounding error. A full rounded solver
certificate must use a stopping implementation and prove that continuation theorem, or prove
a quantitative raw-input horizon condition. Assuming an admitted computed trajectory is not
a substitute for either result.

A one-step extraction does not require the missing continuation theorem.
`Krylov/FinitePrecision/PCGRunConstruction.lean` supplies `PCGRun.ofOneStep`, a pure constructor
from the zero-start oracle recurrence's local normwise defects, SPD reference preconditioner,
Hermitian system, common error allowance, and nonnegative final pairing. A subsequent local
bridge instantiates it using `RoundBounds.exists_run_errors`; it preserves the same actual
output state and pairings. Final pairing nonnegativity follows from the preconditioner
spectral margin for a nonzero final residual, and the zero-input dot contract otherwise.
The constructor is mathematical support only and never assumes execution succeeds.

`HSPCG/FinitePrecision/Recurrence.lean` is the local extraction consumer: its
`RoundBounds.exists_pcgRun_one` returns the existing `PCGRun n 1`, with the same A, P,
oracle, right-hand side, error allowance, actual terminal four-vector state, and both actual
pairings. The spectral pairing-nonnegativity theorem supplies the final sign requirement.

`margins_zero_start_of_spectrum_subset_Icc` derives nonzero initial direction from the raw
nonzero right-hand side and inverse-preconditioner spectral precision bound.
`step_writes_pcgRun_one` composes this with the active-step execution proof and existing-run
extraction: it consumes the actual initializer state and raw A/P spectral/precision inputs,
then stores the terminal state of an existing one-step PCG run. It has no computed-trajectory,
execution-success or final-sign assumption. This is a scoped first-step endpoint, not a
canonical counted certificate for an arbitrary-cap PCG solver.
