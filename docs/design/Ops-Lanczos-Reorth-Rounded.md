# Rounded full reorthogonalized Lanczos

The fixed `Lanczos.Reorth.solve` uses Paige's raw update, a saved raw residual norm,
two classical passes against all stored current columns, and guarded normalization.
The current exact prefix proof is tied to the canonical exact recurrence. A rounded
reorthogonalized recurrence includes explicit projection corrections and is not an
ordinary rounded three-term `LanczosRun`.

## Objects and interfaces

No arithmetic or execution interface is introduced. The local contracts are existing
`IsBlas1 dec errors ok I`, `StdModel u dec M`, normwise
`IsMatvec dec A (em * specNorm A) I`, and exact `IsCmp dec I`.
`UpdateBounds`, `IsNrm2Err`, `IsScalErr`, and `TwoPassOut` retain actual words and
intermediates. No orthogonality, matrix symmetry, successful-execution premise, or
nonbreakdown assumption is required for execution of one initialized round.

Mathlib was searched for reorthogonalized Lanczos execution; none. NLAlib's
`Reorth.preNorm_writes`, `Reorth.cgs2_writes`, ordinary rounded `update_writes` and
`normalize_rounded_writes` already prove all primitive safety. The existing
`TwoPassOut.norm_sub_sub_sum_le` gives the representation defect of the actual
sequential axpy passes. These are reused instead of old Computation execution proofs.

## Statement shapes and consumers

New `NLAlib/Krylov/Lanczos/Reorth/RoundedAdvance.lean` contains in order:

- `Rounded.updateAndSweep_writes`, preserving the exact round buffer/capacity arguments,
  takes the models above and `errors.dot n < 1`, and returns `Writes .total` with
  actual `first`, `raw`, `reduced`, alpha and saved nu witnesses. Its numerical output
  is `UpdateBounds em (errors.dot n) errors.axpy ...`, `IsNrm2Err ... raw nu`, and
  `TwoPassOut dec (errors.dot n) errors.axpy n (j+1) basis raw reduced`.
- `Rounded.saveAndNormalize_writes`, with `u < 1` and `errors.dot n < 1`, returns
  actual next vector, beta and guard; it includes `IsNrm2Err`, `IsScalErr`, and
  zero residual implies zero next vector, covering the guarded zero branch.
- `Rounded.advance_writes` composes those statements for `Reorth.advance` and retains
  their actual intermediate witnesses and all external reads.

The consumer is a rounded reorthogonalized full-driver prefix invariant. The statement
shape follows the existing exact advance interface so archive/frame reasoning can be
shared. Actual round inputs are readable previous/current/basis words, initialized zero
next vector/beta/nu, and caller-owned output room. Buffer disjointness and footprints
remain explicit. No input accuracy assumption is disguised as success.

## Shared machinery and remaining full-run bridge

`Writes.seq_le`, `writes_frame`, `step`, `kept` and footprint inclusion supply composition.
The same pre-norm and two-pass interfaces are shared with exact code. The old
`LanczosReorthRun` additionally requires an `IsOrthErr` theorem for the chosen scheme
and strict tau-admissibility of each prefix. Current sequential-axpy pass bounds prove
representation error without this stronger orthogonality guarantee. A full bridge must
establish the applicable orthogonality conditions and keep the admissible prefix distinct
from the unconditional successful driver output. It must not silently reuse matrix-vector
CGS constants for the actual sequential-axpy implementation.

## Validation

Run warning-fatal module builds under the shared Lean gate, focused source rules and
reference checks, then root integration performs unchanged full stage/audit/kernel replay.
No program, targets, check scripts, or approval files are changed.

## Shared canonical packed-buffer problem

`Lanczos/BufferProblem.lean` defines `Lanczos.PackedProblem.problem coefficientLength
domain admitted : Problem K 2 3`, with raw right-hand-side words and explicitly supplied
uninitialized basis and coefficient capacity. Ordinary Lanczos uses `2*cap+2` coefficients;
full reorthogonalization uses `3*cap+2`. The shared initial read/liveness/room/bytes lemmas
are consumed by both canonical certificates. No input preprocessing is added.
The object is a library-specific buffer representation; its bridge is the existing
`Ops.Problem.initial` memory and its shared read/length theorems. No Mathlib analogue exists.
`Reorth/Certificate.lean` specializes the shared problem and `Algorithm.ofWp`, applying
the total rounded model theorem for actual History and the reorthogonalized full static
manifest and peak. All original/query/core work and sequential span, initial output
capacity and query/scratch reserve remain explicit.

## Full rounded history and driver

The implemented generic driver is split into `Reorth/RoundedState`, `RoundedRun`,
`RoundedInitialization`, `RoundedRounds`, `RoundedOutput` and `RoundedSolve`.
`Rounded.Local` stores the actual first/raw/reduced/output words, actual alpha/beta/nu words,
the rounded Paige update, both classical passes and guarded normalization. Its basis read
is tied columnwise to the same archived numerical sequence. `Rounded.History` starts at
the derived ordinary rounded initialization and appends exactly the executed transitions.
`Rounded.History.local` in `RoundedHistory` exposes each executed transition against the
final archived sequences, so downstream numerical analysis never reconstructs execution.

The total `runs_solve` statement takes `StdModel`, `IsBlas1`, normwise `IsMatvec`, exact
comparison, ordinary disjoint readable/writable buffers and the common
`Lanczos.Rounded.Precision` envelope. It needs no symmetry or orthogonality assumption for
successful execution and local error history. Output is
`Output dec A rhs em u E errors cap vs cs`: an executed length at most cap, its complete
history, every decoded packed basis/coefficient/raw-norm entry, and a zero latest computed
norm if execution stops before the cap. This includes zero dimension, zero cap, zero input,
and zero residual after reorthogonalization. Physical initialized tails are not counted as
extra steps or asserted nearly unit vectors.

Two shared ordinary helpers support the full driver without duplicating initialization or
archive proofs. `Lanczos.Rounded.initialize_writes_with_suffix` retains the actual zeroed
coefficient suffix; the original initializer name is a thin postcondition projection.
`Lanczos.Rounded.Packed.advance_of_disjoint` allows any footprint disjoint from unchanged
ordinary entries; the original ordinary advance specializes it, while reorthogonalization
uses its explicit raw-norm suffix footprint. Existing public signatures remain unchanged.

`Reorth/RoundedModels` provides standard exact/sequential/pairwise operation model wrappers
and type checking. Its actual workspace remains the declared model workspace. The generic
history is unconditional; `LanczosReorthRun` orthogonality and backward-error consequences
require the actual quantitative two-pass envelope and tau-admissibility of the chosen prefix.

## Total admissible-prefix analysis

The existing `reorthSteps` selects the first failing strict coefficient test. The pure
`FinitePrecision/LanczosReorthPrefix` API proves the selected length is at most the executed
horizon, every earlier step has `tau * savedRawNorm < beta`, and a first excluded step has
`beta <= tau * savedRawNorm`. Rounded histories use the adapter `fun j => nus (j+1)` because
the stored raw norm sequence in `History` starts at one while the existing selector starts
its raw-norm arguments at zero. The algorithm is unchanged and may continue past the selected
mathematical prefix. The strong numerical run, when the selected length is positive, must use
this prefix; zero length is a separate valid outcome. No future internal admissibility is
assumed in the total driver or total prefix conclusion.

The actual first continuation guard is part of `History.next`. A positive executed history
therefore has a nonzero initial norm and the derived initial near-unit direction. This guard
is obtained from the existing runtime test in `rounds_writes`; it is not an extra public solver
hypothesis or an algorithm modification. `History.initial_outcome` preserves the actual initial
normalization and `History.initial_data` supplies the zero previous vector/coupling and unit
bound used by the pure run constructor.

`Reorth/RoundedStability.History.exists_run` assembles the positive selected prefix from the
actual local numerical witnesses. `Output.exists_run_prefix` combines it with the total first
excluded test: either the admissible prefix is empty or it is a `LanczosReorthRun` with exactly
the final archive's basis, alpha, beta and saved raw norms. A next computed step, when present,
satisfies `beta <= tau * savedRawNorm`. The scalar common envelope and the actual sequential
axpy/dot two-pass envelope are separate parameters. This theorem requires symmetry and the
explicit size-only two-pass error envelope, rather than postulating global orthogonality or
admissibility of all future internal steps. Existing pure orthogonality, recurrence, backward
error and spectral results consume that same run with their own quantitative smallness bounds.
