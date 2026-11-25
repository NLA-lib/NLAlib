# Dense factorization routines: design and 48-hour execution plan

Status: implementation and approved target publication, 2026-11-25. Baseline `7cbea9d1`. The user requested broad parallel
coverage of dense Cholesky, LU and pivoted LU through the certified-routine model. This note
distinguishes planned algorithms from implemented and checked results. No target registration,
model extension, commit or push is authorized by this plan itself. The maintainer separately
approved the seven proposed cost targets and requested commit/push on 2026-11-25.

## Current implementation status

The expanded continuation has implemented full fixed-scale, rook and threshold pivoted LU,
rounded PLUQ, rounded and finite-range Cholesky, exact pivoted solves, zero-safe PSD Cholesky,
scalar-pivot LDL with a Mathlib bridge, actual blocked LU/Cholesky, and seven fixed-tree resource
summaries with closed scratch bounds. Symmetric diagonal-pivoted PSD Cholesky and its exact
routine certificate are now integrated too. The combined repository stage check exits zero; use the
[delivery report](Matrix-DenseFactorizationDelivery.md) for current evidence and limitations.

F15 publishes seven approved explicit cubic-count targets with execution, count and
nonvacuity proofs; the
[target review](Matrix-DenseFactorizationTargetProposal.md) records the approved scope.
The delivery report records the final registry and full-check results. The original design discussions below record decisions at their
respective implementation waves and do not override that current status.

## Objective and delivery order

Connect existing factorization mathematics to executable buffer programs whose certificates
prove successful execution, the exact output footprint, and a useful decoded error guarantee.
Then compose them with solves, derive rounded error bounds, and separately certify costs on
registered trees. A pure matrix recurrence or an existential permutation is not an executable
factorization. A certificate definition without an instance is not a certified algorithm.

Priorities, in order:

1. Shared solve guarantees and a real instance for the existing lower triangular solver.
2. Factorization error guarantees with exact bridges and useful solve consumers.
3. Unblocked LU and SPD Cholesky execution and frame proofs.
4. Deterministic pivot search, swaps and permutation bookkeeping; partial-pivoted LU.
5. Rounded factorization bounds and end-to-end solve guarantees.
6. Complete and scaled partial pivoting, LDL, blocked implementations and cost registration.
7. Rook, threshold and randomized policies after their additional termination/model work.

The first two items are the initial implementation wave. The 48-hour schedule below is an
engineering estimate, not a promise that every proof or approval will finish within that time.
The current session has four concurrent agent slots: one integration lead and three workers.
Use successive waves, retaining the lead for design review and integration. Additional logical
lanes are queued rather than represented as concurrently running agents.

The implementation and validation record is [the delivery report](Matrix-DenseFactorizationDelivery.md).
Supporting source inventories are in [the Cholesky audit](dense-factorization-audits/cholesky.md),
[the LU/pivot audit](dense-factorization-audits/lu-pivoting.md),
[the routine audit](dense-factorization-audits/routines.md) and
[the independent review](dense-factorization-audits/review.md).

## Existing material and reuse

| Area | Existing source | What can be reused | What remains |
|---|---|---|---|
| Exact Cholesky | `NLAlib/Matrix/Factorizations/Cholesky.lean` | `IsCholesky`, uniqueness, SPD and PSD factorization, pivoted existence | Stored executable and rounded success/error proof |
| Exact LU | `NLAlib/Matrix/Factorizations/LU.lean` | `IsLU`, `luLower`, `luUpper`, leading-minor conditions, row-permutation existence | Pivot scan, swaps and executable correctness |
| Partial pivot bounds | `NLAlib/Matrix/Factorizations/LUGeneral.lean` | Zero-pivot handling, bounded multipliers, rowwise growth | Link actual pivoted run to those hypotheses |
| Elimination | `NLAlib/Matrix/Factorizations/GaussState.lean` and `Elimination.lean` | Telescoping, Schur complement, pivot invariants, rank | Relate packed in-place factors to mathematical state |
| LDL | Mathlib `Analysis/Matrix/LDL.lean` | `Matrix.LDL.lower`, `diag`, `lower_conj_diag` for SPD inputs | Executable LDL and bridge to Mathlib; indefinite blocks are separate |
| Triangular solve | `NLAlib/Computation/BLAS/Triangular.lean` | Successful lower solve, exact write frame, componentwise backward error | Typed routine certificate and upper/adjoint solve |
| Footprints | `NLAlib/Computation/RoutineFrames.lean` | `IsBlockRoutine`, block writes, scopes and frame transport | Small factorizations-specific adapters only |
| Pivot control | `Syntax.lean`, `IndexBinder.lean`, `Contract.lean` | Comparisons, bounded dynamic indices and exact index contracts | Stable scan invariants and finite-representation hypotheses |
| Arithmetic | `Rounding.lean`, `Contract.lean`, scalar frame lemmas | Relative error, exact comparisons and accumulated factors | Factorization-specific trace and global error analysis |

The existing certified-routine design is `docs/design/Computation-CertifiedRoutines.md`.
Use its typed guarantee plus `composable`/`run` structure, with `toBlockRoutine` for footprints.
Do not introduce a generic untyped factorization certificate as a second abstraction.

Sources already used by these files include Higham (2002), Chapters 8--10, and Golub--Van Loan
(2013), Chapters 3--4. Locate the exact source statement before attaching a literature claim to
a new theorem. Mathlib and NLAlib searches are recorded in the worker audits accompanying this
plan. No new LDL predicate should duplicate Mathlib without an explicit bridge.

## Shared representation decisions

Use the library's existing column-major packed storage and offset convention. Begin with
separate output buffers when that reduces aliasing proofs; packed in-place factors are a later
instance of the same typed guarantee. State all output blocks and aliasing conditions explicitly.
Empty matrices and blocks must be valid, including the corrected empty-block disjointness rule.

Use arbitrary finite indices and `[RCLike 𝕜]` for pure mathematical guarantees where possible;
use `Fin N` for ordered executable recurrences. First scalar-word routine instances are real.
Complex execution needs the existing interleaved-real representation and componentwise
rounding, not an assumption that a real instruction computes complex arithmetic.

For permutation conventions, write the actual equality. Row pivoting means factorization of
`A.submatrix σ id`; row-and-column pivoting means `A.submatrix σ τ`. Avoid an ambiguous name
such as PLU without stating whether the permutation or its inverse is returned. Stored swap
logs and their decoded `Equiv.Perm` must be connected by a proved interpretation.

Pivot ties select the first eligible index deterministically. No-pivot LU requires a suitable
nonbreakdown hypothesis; singular partial-pivoted LU must explicitly skip all-zero active
columns. A successful singular factorization does not authorize division by zero in a solve.

The pivot-policy lanes have separate acceptance criteria; implementing a generic maximum
search does not establish all of them:

| Policy | Selection property | Additional execution/proof obligations |
|---|---|---|
| No pivoting | Use the current diagonal | Nonzero pivots or explicit compatible-zero-column skipping; distinguish factorization from solvability |
| Partial | Largest absolute entry of the active column | Scan the current rounded column; swap previous multiplier columns and pivot history; skip a wholly zero active column |
| Scaled partial | Largest absolute active-column entry divided by its row scale | Specify whether scales are fixed from the original input or recomputed; swap scales with rows; define zero-scale behavior without division by zero |
| Complete | Largest absolute entry of the whole active region | Two selected indices; row and column permutations; preserve earlier factor prefixes; a column scan alone is insufficient |
| Rook | Entry is a maximum in both its active row and active column | Alternating searches, deterministic ties, and termination or explicit fuel plus fallback; local maximality is weaker than complete pivoting |
| Threshold partial | Accept a candidate whose magnitude is at least a positive threshold times the active-column maximum | State the threshold range and stored representation; bound multipliers using its reciprocal only for nonzero pivots; comparison is on decoded operands |
| Symmetric diagonal Cholesky | Largest active diagonal, with paired row/column exchanges | Preserve symmetry and previous factor columns; PSD zero pivots need zero-column reasoning; tolerance-based stopping needs a separate residual statement |
| Randomized Cholesky | Sample according to nonnegative active-diagonal weights | Actual tape use/sampler, normalization and zero-total-weight behavior; expected mathematical elimination alone is not an executable sampler |

For each deterministic policy, test tied maxima and repeated exchanges and prove the selected
index stays in the active region. For complete pivoting spell the final result as a
factorization of `A.submatrix σ τ`; for a solve, transport both the right-hand side and solution
in the correct direction. A tolerance or small pivot flag is not by itself a numerical-rank
theorem. Indefinite block LDL needs a separate 1-by-1/2-by-2 pivot and block-solve design.

The model already has comparisons and dynamic index binding. Reuse these; do not extend the
instruction set. Exact comparison is about the decoded stored operands, not the corresponding
unrounded elimination state. Account for pivot-index literals and `toNat` through existing
exact-index contracts. Prefer signed comparisons or copy/negation for absolute value; squaring
introduces rounding and possible range obligations.

Existing packed `ger`, `gemm` and triangular operands cannot directly describe every trailing
submatrix with the parent leading dimension. Choose explicit scalar loops for the unblocked
first implementation. Later compare a shared leading-dimension operand API with packed panel
copies; neither choice is silently assumed to exist today.

## Reviewed first-wave interface

The integration lead reviewed the architecture worker's proposal before implementation.
Use `IsLinearSolveErr` and `IsLinearSolveRoutine`: the guarantee applies to a general fixed
matrix, so its name should not claim triangularity. The first concrete instance is triangular.

The pure guarantee has the following signature and field (a design signature, not an assertion
that this code has already landed):

```lean
structure IsLinearSolveErr {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    (η : ℝ) (T : Matrix n n 𝕜) (b x : n → 𝕜) : Prop where
  backward : ∃ ΔT : Matrix n n 𝕜,
    (∀ i j, ‖ΔT i j‖ ≤ η * ‖T i j‖) ∧ (T + ΔT) *ᵥ x = b
```

The raw constructor is the structure constructor. It does not require a second wrapper.
Prove monotonicity in `η`, an exact-solve constructor for nonnegative `η`, and recovery of the
exact solve when `η = 0`. A consumer gets a componentwise residual bound from the perturbation.
Do not duplicate a lower-triangular field: structural zeros transfer from the entrywise bound.

The routine uses a fixed decoded matrix `T`, backend precondition `pre`, output handle `xb`
and index expression `xo`. It has exactly the established two fields:

```lean
composable : ExecutionComposable I routine
run : ∀ (st : St P K C) (b : Fin N → ℝ),
  pre st.store → ReadsDecoded st.store dec tag xb xo.eval b →
  Writable st.store tag xb xo.eval N →
  ∃ (out : St P K C) (W : Fin N → K),
    exec I routine.run st = some out ∧
    st.store.writeBlock tag xb xo.eval (Array.ofFn W) = some out.store ∧
    IsLinearSolveErr η T b (fun i => dec tag (W i))
```

Instantiate it with the actual `trsvLower`, the standard relative-error semantics with all
values in range, `u tag < 1`, nonzero diagonal and lower triangular `T`. The backend precondition
holds the matrix at the declared offset; require disjoint matrix and solution blocks. The
parameter is the existing `roundingFactor N (u tag)`; do not introduce a second gamma formula.
Reuse `IsRelErrSem.exec_trsvLower_add_mulVec_eq`, not a new scalar-loop proof.

`IsLinearSolveRoutine.mono` and `.toBlockRoutine` make the guarantee usable inside later
factorization-and-solve routines. Costs remain outside the routine certificate.

## Reviewed Cholesky and LU error interfaces

The integration lead reviewed both proposals before implementation. The intended consumer
is an actual factorization followed by two solves. Preserve triangular structure in the
guarantee, and require the Cholesky diagonal convention to recover `IsCholesky` at zero error.
Use existing `IsLU` and `IsCholesky` for exact factorizations rather than parallel predicates.

Over `[RCLike 𝕜]` and arbitrary finite ordered indices, LU uses the classical componentwise
scale, allowing downstream analysis to retain the growth information:

```lean
structure IsLUErr (ε : ℝ) (A L U : Matrix n n 𝕜) : Prop where
  isUnitLowerTriangular : IsUnitLowerTriangular L
  isUpperTriangular : U.IsUpperTriangular
  residual : ∀ i j, ‖(A - L * U) i j‖ ≤ ε * ∑ k, ‖L i k‖ * ‖U k j‖
```

Prove `IsLU.isLUErr` at zero error, `IsLUErr.isLU` at zero error, and monotonicity. The general
consumer has the explicit statement shape

```lean
‖(A *ᵥ x - b) i‖ ≤
  ε * ∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖) +
  ∑ k, ‖L i k‖ * ‖(U *ᵥ x - y) k‖ + ‖(L *ᵥ y - b) i‖
```

Integration adds the direct consumer of two `IsLinearSolveErr` guarantees: for
`hL : IsLinearSolveErr ηL L b y` and `hU : IsLinearSolveErr ηU U y x`, the bound is

```lean
‖(A *ᵥ x - b) i‖ ≤
  (ε + ηU) * ∑ k, ‖L i k‖ * (∑ j, ‖U k j‖ * ‖x j‖) +
  ηL * ∑ k, ‖L i k‖ * ‖y k‖
```

This uses `IsLinearSolveErr.norm_sub_mulVec_le`, a componentwise residual consequence added
in the same integration wave. These additions live with their owning error predicates;
`LUErr.lean` imports `LinearSolveErr.lean`, not the executable layer.

Cholesky uses an absolute spectral residual budget. This avoids prematurely requiring either
a relative-to-input scale or a relative-to-factor scale from every implementation. A future
componentwise algorithm theorem can imply a spectral budget; that conversion must be proved.

```lean
structure IsCholeskyErr (ε : ℝ) (A L : Matrix n n 𝕜) : Prop where
  isLowerTriangular : L.IsLowerTriangular
  apply_self_pos : ∀ i, 0 < L i i
  residual : specNorm (A - L * Lᴴ) ≤ ε
```

Prove exact/zero-error bridges, monotonicity and an exact `IsCholesky (L * Lᴴ) L` consequence.
The general solve consumer is

```lean
‖WithLp.toLp 2 (A *ᵥ x - b)‖ ≤ ε * ‖WithLp.toLp 2 x‖ +
  specNorm L * ‖WithLp.toLp 2 (y - Lᴴ *ᵥ x)‖ + ‖WithLp.toLp 2 (b - L *ᵥ y)‖
```

In both contracts the factorization error is exact minus computed. Neither contract itself
proves rounded nonbreakdown. Exact-solve corollaries specialize the solve residuals to zero.
The new names concern algorithm error guarantees: searched Mathlib and NLAlib, no existing
factorization-error predicate was found. Bridges use existing `IsLU`/`IsCholesky`, Mathlib
matrix arithmetic and `specNorm_eq_norm`; no alternate matrix factorization notion is added.

Unpivoted rounded Cholesky success requires a quantitative positivity margin or an explicit,
separately named nonbreakdown premise about the rounded recurrence. `A.PosDef` alone does not
justify it. A partial-correctness theorem assuming a successful run must be labeled as such
and kept separate from the success certificate. The same distinction applies to LU pivot
division and rook-search fuel.

## Work packages and acceptance criteria

| ID | Package | Dependencies | Reviewable completion criterion |
|---|---|---|---|
| F0 | Baseline inventory and architecture | None | Existing declarations and gaps recorded with paths |
| F1 | Solve guarantee and lower-solve routine instance | F0 | Exact/zero/mono API, footprint, actual instance compiles |
| F2 | LU and Cholesky backward-error consumers | F0 | Reviewed typed contracts, exact bridges, residual consequences |
| F3 | Copy, swap, stable pivot scan | F0 | Success and frame proofs; tie/range/empty cases explicit |
| F4 | Unblocked no-pivot LU | F0 | Executable loops, state invariant, success under stated conditions |
| F5 | Unblocked SPD Cholesky | F0 | Executable loops; exact success links to existing factorization |
| F6 | Upper and adjoint triangular solve | F1 | Actual reverse-loop execution and frame certificate |
| F7 | Partial-pivoted LU | F3, F4 | Swap log/permutation invariant; all-zero-column behavior |
| F8 | Rounded LU analysis | F2, F4 | Componentwise error of actual stored program under standard model |
| F9 | Rounded Cholesky analysis | F2, F5 | Nonbreakdown separated; explicit factorization error and success |
| F10 | End-to-end solve | F1, F2, F6, F8/F9 | Factorization and solve residual compose; matrix/RHS framing |
| F11 | Scaled partial and complete pivoting | F3, F7 | Correct policy selection and row/column permutation orientation |
| F12 | Rook and threshold pivoting | F3, F11 | Search termination/fuel and threshold acceptance proved |
| F13 | SPD LDL and pivoted semidefinite Cholesky | F5 | Mathlib LDL bridge; rank/tolerance behavior stated honestly |
| F14 | Blocked factorization | F4/F5, operand design | Panels and updates preserve scalar specification and frame |
| F15 | Concrete costs and registered trees | Stable implementations | Maintainer-reviewed targets; counts/memory on fixed trees |
| F16 | Examples and export | Executable slices | Exact examples plus tool Float comparison, labeled appropriately |
| F17 | Independent review and integration | Every completed slice | Statement read-back; rules, build, audit, replay and stage checks |

F15 proposes target statements for maintainer review. Agents must not edit `*Targets.lean`,
`docs/targets.toml` or `docs/targets.approved`. A proposed work package is not an approved target.
Do not evade registration by renaming a top-level program; primitive subroutine certificates
and their local execution infrastructure follow the existing routine precedent.

## Reviewed executable row-swap slice

After F2, the LU worker owns `NLAlib/Matrix/Computation/RowSwap.lean`. The approved builder
operates on an arbitrary rectangular `m × n` packed column-major matrix, with index expressions
for dimensions, offset and row numbers:

```lean
swapRows (tag : P) (m n : IExp VI) (A : VB) (ao r s : IExp VI) :
  Builder P ι VB VI Unit
```

Allocate one scoped scratch word. For each column `j`, copy `A[ao+r+m*j]` to scratch,
`A[ao+s+m*j]` to `A[ao+r+m*j]`, and scratch to `A[ao+s+m*j]`. The success theorem is word-level,
for any carrier and scalar semantics: readable matrix storage and row bounds imply successful
execution whose net effect is one full packed matrix block write of
`M.submatrix (Equiv.swap r s) id`. Equal row indices are valid. No rounding or exact-index
literal hypothesis is needed, since the caller supplies index expressions. A later pivot
driver must justify how its decoded pivot index becomes an expression through `bindIdx`.

Reuse the existing packing convention and scalar-copy/loop/frame lemmas; do not introduce a
second matrix encoding. Prove composability, scoped scratch and unrelated-memory preservation.
This is a concrete instruction routine, not a registered cost program. Its downstream
consumers are partial/complete-pivoted LU and symmetric pivoted Cholesky (which also needs a
column swap). Mathlib `LinearAlgebra/Matrix/Swap.lean` supplies permutation mathematics;
searched Mathlib and NLAlib, no existing buffer row-swap execution certificate was found.

## Reviewed executable pivot scan

The architecture worker owns `NLAlib/Matrix/Computation/PivotScan.lean` with the proposed
entry point

```lean
argmaxAbs (tag : P) (n : IExp VI) (x : VB) (xo : IExp VI) (dst : Cell VB VI) :
  Builder P ι VB VI Unit
```

The certified case has `0 < n.eval`. Initialize the index to exact zero and the incumbent
magnitude from the absolute value of input zero. Scan the input in index order; construct each
absolute magnitude by a decoded sign test, copy and exact negation, then update the magnitude
and exact index literal only on strict improvement. A scope contains the magnitude/candidate/
zero scratch cells. This permits an all-zero input and chooses the first tied maximum.

Require the standard scalar contract at `safe := True`, an exact-index-literal contract through
`n.eval`, readable input, writable destination and disjoint input/output blocks. The theorem
must conclude success, one net output-word write, an index in `Fin n.eval`, exact decoded
index, maximal input magnitude, and strictly smaller magnitudes at every earlier index.
The selected index refers to the stored decoded input, with no hypothesis about an exact
elimination order. No conversion is needed until a caller uses the output in `bindIdx`.
An empty scan has no selected finite index and is outside this success theorem; no-pivot or
empty active-region drivers handle that case explicitly. No squaring-based proxy is used.
The first implemented instance strengthens disjointness to distinct input/output buffers;
the builder accepts index expressions but the theorem instantiates length as `.const N`.
Same-buffer disjoint regions can be generalized later if a pivot driver needs them.

## Reviewed executable Cholesky column

After its error API, the Cholesky worker owns `NLAlib/Matrix/Computation/Cholesky.lean`.
The approved `choleskyColumn` first computes a scalar square root into a declared diagonal
cell, then normalizes a stored below-diagonal column through the existing `rscl` routine.
The inputs are a positive decoded Schur pivot and a readable real vector; the diagonal and
vector output blocks are writable and disjoint. A scope makes the builder composable.

Under `I.sem = exactSem`, conclude successful execution and exactly the two declared writes:
the square root in the diagonal cell and the divided vector in its output block. Reuse the
existing reciprocal-scaling run theorem, including its available count-type assumptions.
This proves an actual column operation; it does not include the Schur rank-one update or
claim a complete factorization. Public names are `choleskyColumn`,
`executionComposable_choleskyColumn` and `exec_choleskyColumn`.

## Reviewed second implementation wave

The user authorized continuation after the first-wave report. The integration lead reviewed
the following designs before proof implementation. The two existing validation blockers remain
reported; continuation does not change checks or the target registry.

### Shared exact Schur step

Root owns `NLAlib/Matrix/Computation/SchurUpdate.lean`. The entry point is

```lean
schurStep (tag : P) (n : IExp VI) (R : VB) (off pivot : IExp VI) :
  Builder P ι VB VI Unit
```

Save the pivot column and row in a scoped `2*n+1`-word buffer, compute the coefficient
`-1 / R[pivot,pivot]` in its last cell, then invoke the existing exact `ger` on the full
packed matrix. The initial instance is real, under `I.sem = exactSem` and standard operation
charges, matching the existing BLAS execution theorems. A valid pivot index, a nonzero pivot
and `Holds` of the matrix imply execution success, one net full matrix block write, and
`Holds` of `eliminationStep M pivot`. Updating the whole matrix clears the pivot row/column
and allows both factorization invariants to use the existing `gaussState` exactly. No
additional mathematical elimination recurrence or alternate matrix encoding is introduced.
Two shared frame additions support both consumers: `Store.BlockFrame.writeBlock_scratch`
belongs beside scalar scratch writes in `Computation/Store.lean`; `Holds.writable` belongs
beside the writable-block interface in `Computation/RoutineFrames.lean`. Both restate existing
store-read/write consequences, not a new storage predicate. A nonempty readable matrix gives
capacity for the corresponding flat block; empty blocks require no handle. A whole scratch
block write preserves a destination frame when the nonempty destination is a different buffer.

### Full no-pivot LU

The LU worker owns new `Matrix/Computation/LU*.lean` files. The approved entry point is
`luFactor tag n A ao L lo U uo`: scope a residual matrix copied from `A`, then for each pivot
materialize a full unit-lower column and upper row and call `schurStep`. The initial instance
requires distinct source, lower-output and upper-output buffers, and writable full output
blocks. It assumes `∀ k : Fin n.eval, gaussState A k k k ≠ 0`, an explicit exact nonbreakdown
condition. The theorem concludes successful execution, exactly the two original-to-final
output block writes of `flatten (luLower A)` and `flatten (luUpper A)`, corresponding `Holds`
facts, and existing `IsLU A (luLower A) (luUpper A)`. The empty case is included. Loop invariants
track `gaussState A k`, completed lower columns and upper rows, store shape and unrelated cells.
Singular/pivoted drivers need subsequent proofs; no preselected existential permutation is input.

### Full exact SPD Cholesky

The Cholesky worker owns `Matrix/Computation/Cholesky*.lean`. The approved `cholesky` entry
point copies the full input matrix into scoped residual storage. At step `k`, copy the residual
column into the output column, use `choleskyColumn` to write the square root and normalize the
suffix, then call `schurStep`. SPD supplies positive `gaussState` pivots. The invariant combines
the residual matrix with completed columns equal to `choleskyLower A` and a block frame.
The exact theorem takes `A.PosDef`, readable input and writable factor storage and concludes
success, exactly one original-store block write of `flatten (choleskyLower A)`, final `Holds`
and existing `IsCholesky`. Copying the full input before output writes permits source/output
aliasing when the final proof discharges it. Rounded SPD nonbreakdown remains separate.

### Upper and adjoint solves

The solve worker owns `Matrix/Computation/TriangularSolve*.lean` and the permutation transport
API in the existing `Matrix/Perturbation/LinearSolveErr.lean`. A gather adapter constructs a
packed transformed coefficient matrix and RHS in scoped workspace, calls the existing lower
solve, and copies the solution back. `trsvUpper` reverses both axes and RHS;
`trsvLowerAdjoint` transposes/conjugates then reverses; `trsvUpperAdjoint` transposes/conjugates
without reversal. Reindex backward error with a finite equivalence, using Mathlib matrix
permutation identities. The concrete real-decoding instances use actual conjugation
instructions and exact copy operations, and give existing `IsLinearSolveRoutine` with
`roundingFactor N (u tag)` under the standard all-values-in-range model. Exact instances
specialize zero rounding. Matrix/RHS disjointness and empty dimensions are explicit.
The adapter costs `N²+N` extra storage plus lower-solver scratch; no direct constant-scratch
upper solve or complex runtime is claimed. Pure permutation transport stays general over
`RCLike`, with no new lower/upper error predicate.

### Typed factorization certificates

The Cholesky worker reviewed and approved the root's proposal before implementation.
`Matrix/Computation/CholeskyRoutine.lean` and `LURoutine.lean` connect the full exact drivers
to the same two-field certified-routine pattern. Fix the decoded input matrix `A`, error
allowance and backend precondition. Their `run` fields take the precondition and writable
full factor blocks and conclude success, exact original-to-final factor writes and
`IsCholeskyErr` or `IsLUErr` on decoded outputs. Words are arrays of the declared `N*N` size;
decode with existing `unflatten N N (W.map (dec tag))`. This permits arbitrary carriers
without adding another packing function or assuming floating-point words form an `RCLike` field.
The LU run additionally requires disjoint output blocks, so the second factor write cannot
invalidate the decoded first factor. Empty output blocks retain the existing disjointness rule.

Both certificates get `mono` and `toBlockRoutine`; the exact driver instances take exact
semantics, standard charges and the algorithm's mathematical nonbreakdown/SPD hypotheses,
use backend `pre := Holds input`, real words with identity decoding, and zero error allowance.
Those hypotheses belong to the instance, not to the certificate itself. No rounded stability
instance is asserted before its proof. LU and Cholesky solve composition are foreseeable
consumers; the same certificate can later accept a rounded or kernel implementation.

### Rounded column and full solve consumers

The Cholesky worker's reviewed local rounded theorem reuses the actual `choleskyColumn`:
under `IsRelErrSem u dec (fun _ _ => True) I.sem`, `u tag < 1`, a positive decoded pivot,
readable vector and writable/disjoint diagonal/vector blocks, the routine succeeds and writes
exactly those two blocks. Its decoded diagonal is positive, has `RelErr` with respect to the
true square root, and each vector output has `RelErr` with respect to division by the computed
diagonal. Charges are arbitrary. This is not a global Cholesky backward-error theorem: the
full driver's saved-pivot Gaussian Schur instruction order needs its own rounding analysis.

The solve worker's reviewed `FactorizationSolve.lean` runs full factorization into scoped
factor storage, then the actual triangular solves. `choleskySolve` uses the lower and lower
adjoint routines; `luSolve` uses lower and upper. Exact success hypotheses are SPD or the
no-pivot LU nonbreakdown condition, stored input and RHS, exact semantics and standard charges.
Conclude one net RHS write and `A *ᵥ x = b`, then a zero-error `IsLinearSolveRoutine` instance.
No factorization is assumed instead of executed. All input is consumed before the RHS output,
so source/RHS aliasing is admissible if proved. Empty dimensions remain explicit.

The integration lead adds `NLAlibTools/DenseFactorizationSmoke.lean` to run the actual builders
under the existing `NLAlibTools.floatInterp`. Checks compare independent matrix products or
known factors/solutions and inspect scratch release and offset/alias behavior. These are
runtime regression examples, not a finite-range floating-point correctness proof.

### Executable partial pivot operation

The Cholesky worker's reviewed `PartialPivot.lean` joins the first-wave primitives:
`partialPivot tag n k R off index` scans the active suffix of column `k`, uses `bindIdx`
to consume the exact relative index, calls `swapRows` on rows `k` and `k+relative`, and
stores that absolute row index. The theorem is generic in stored words and charges, under
the standard scalar model and `IsIndexExactSem dec n.eval I.sem`. It requires `k.eval<n.eval`,
full decoded matrix input and a writable index in another buffer. It concludes success,
exactly the original matrix-block and index writes, a valid selected active row, the decoded
row-permuted matrix, maximal absolute column value and first-tie behavior. The scan's temporary
relative index write is commuted and overwritten in the final frame proof.

This is not a full PLU driver. That driver must also exchange previous lower-factor rows,
maintain the accumulated permutation orientation and handle zero active columns without
division. Singular all-input PLU needs guarded total column/elimination operations; an
invertible-input driver needs a proved nonbreakdown argument from the selection invariant.
No existential mathematical permutation is substituted for this actual pivot operation.

The existing tool Float interpreter has no dynamic-index conversion. Pivot runtime examples
therefore supply a tool-only finite nonnegative conversion within binary64's exact-integer
range, and do not assert that this test interpreter satisfies the formal arithmetic contracts.

## Reviewed third-wave PLU design

The integration lead reviewed the three workers' proposals during the second-wave validation
freeze. Implementation begins only after that checkpoint's source checks finish. The goal is
full exact partial-pivoted LU on all square real matrices, including singular inputs. It needs
no nonsingularity or nonzero-pivot hypothesis. No cost target or model extension is introduced.

Root also implements the reviewed rounded-shape prerequisite in
`Matrix/Computation/CholeskyFactorization.lean`: after forming each column, explicitly zero
its upper prefix with scalar zero literals. The generic residual-column helper remains
unchanged. Under exact execution this is an identity store update because the canonical
column already has zeros there; under rounded execution it prevents upper residual noise
from becoming part of the factor. A deliberately perturbed-multiplication runtime regression
checks literal zeros, not merely a small triangular residual. This does not establish global
rounded success, symmetry or backward error.

### Pure prefix and swap-log mathematics

The LU worker owns `Matrix/Factorizations/LUPivoting.lean`, importing existing `LUGeneral`.
For arbitrary fields and a row permutation `τ` fixing indices below `k`, the reviewed lemmas
transport completed lower columns and preserve completed upper rows:

```lean
luLower (A.submatrix τ id) i j = luLower A (τ i) j  -- j.val < k
luUpper (A.submatrix τ id) i j = luUpper A i j      -- i.val < k
```

The proofs reuse `gaussState_submatrix_left` at the earlier pivot, without assuming pivots
nonzero. A generic weight-max-prefix transport lemma preserves
`∀ j i, j.val < k → j ≤ i → w (gaussState A j i j) ≤ w (gaussState A j j j)` under the
same permutation. The PLU consumer uses absolute value, which implies zero-column
compatibility and later bounds multipliers by one. No cleared-previous-row invariant is used:
a zero pivot can leave nonzero entries to its right.

The computable decoder `luPivotPermutation (p : Fin N → Fin N) (k : ℕ)` folds swaps along
the first `k` entries of `List.finRange N`, starting at identity. Each new swap is composed as
`(Equiv.swap j (p j)).trans σ`. Its API includes zero, successor, prefix congruence and
function-update laws. In particular, updating only entry `r` then decoding through `r.val+1`
appends the actual swap to the old prefix. This ties the final permutation to the stored log,
with no unconstrained mathematical choice of a permutation.

### Total guarded local execution

The Cholesky worker owns `Matrix/Computation/GuardedElimination.lean`.
`luColumnTotal` and `schurStepTotal` allocate a scoped zero tester and branch on the actual
stored pivot. Nonzero branches reuse the checked `luColumn` and `schurStep`.
At a zero pivot, column materialization zero-fills the lower column, writes its unit diagonal,
zero-fills the upper-row prefix and copies its residual-row suffix, avoiding division. This
matches the existing mathematical total division convention, even when the column below the
pivot is nonzero. The Schur zero branch skips, matching `eliminationStep` at zero.

The exact success theorems remove the local nonzero-pivot premise while retaining initialized
factor inputs, output shapes, `Holds` and complete write frames. They do not themselves claim
that an arbitrary zero pivot yields a valid LU factorization. Global maximal selection supplies
the needed compatibility. The existing successful LU initializer is promoted/documented only
because these concrete consumers need it; private entry functions need not become public.

### Shared matrix storage bridge

Three concrete consumers need the former LU-private matrix-to-flat readback proof. The
LU worker owns new `Computation/MatrixStorage.lean`, a storage topic extending existing
`Holds`/`flatten` without another encoding or value semantics. `Holds.read_flatten` is general
over rectangular finite real/complex matrices; `Holds.writeBlock_self` proves that rewriting
the readable packed matrix with the same values leaves its store unchanged. Both reuse
existing entrywise flatten and block-write APIs. The old private LU readback proof is removed
in favor of this common lemma. Keeping generic storage API out of the LU topic follows the
placement rule and allows guarded execution and PLU frames to share the actual same fact.

### Full stored PLU driver

The solve worker owns `Matrix/Computation/PLU.lean`, splitting meaningful proof topics if
needed to keep file sizes within the contribution rules. The approved driver shape is:

```lean
pluFactor tag n Ab Lb Ub Pb ao lo uo po := scope do
  let S ← alloc tag (n * n)
  -- Copy A to S, initialize L and U, leave future history cells uninitialized.
  forRange n fun k => do
    partialPivot tag n (.var k) S 0 ⟨Pb, po + .var k⟩
    bindIdx tag ⟨Pb, po + .var k⟩ n fun selected =>
      swapRows tag n n Lb lo (.var k) (.var selected)
    luColumnTotal tag n (.var k) S Lb Ub 0 lo uo
    schurStepTotal tag n S 0 (.var k)
```

At iteration `k`, the log prefix decodes exactly to `σ = luPivotPermutation p k`; residual
storage holds `gaussState (A.submatrix σ id) k`; completed lower columns and upper rows equal
the existing canonical factors for that permuted input; committed pivots are maximal in
magnitude in their columns; and all unrelated cells retain the original frame. Fully initialized
uncommitted factor entries may be arbitrary, since whole lower rows are exchanged.

The exact headline returns the actual recorded `p : Fin N → Fin N`, `k ≤ p k`, successful
execution, exactly three original-store writes for the factors and natural-valued pivot log,
and `IsLU (A.submatrix (luPivotPermutation p N) id)` for the returned factors. Source retention
requires separation only when the matrix is nonempty. The current first implementation may
require distinct output buffers even for empty blocks; valid handle capacity is still vacuous
when the dimension is zero. Final maximality also permits use of existing multiplier/growth
theorems. No whole-program successful-run assumption substitutes for execution.

The factorization convention is **PA = LU**. The permutation maps current row positions to
original row indices; each log entry is a current position at its own stage. A later solve must
permute the RHS forward in recorded swap order, equivalently use `b ∘ σ`. First-tie guarantees
refer to each pre-swap prefix state, since subsequent active row permutations can reorder ties.

### Routine certificate and integration review

Root owns `Matrix/Computation/PLURoutine.lean`. The reviewed `IsPLURoutine` records
successful execution and exactly three disjoint output writes. It requires both square
factor sizes, the length-$N$ log size, actual final `ReadsDecoded` log values, active-suffix
indices, and `IsLUErr` for the input reindexed by that same log's `luPivotPermutation`.
It adds neither an independent free permutation nor a successful-run premise. The generic
contract has monotonicity and a three-block routine projection. A concrete zero-error
instance is added only after the full actual driver's success theorem is checked.

The row-pivoting reviewer confirmed the decoding and footprint formulation. Runtime review
independently reconstructs the logged permutation and multiplies the computed factors,
including singular zero-column inputs where a previously processed row can remain nonzero.
Policy-specific first-tie statements belong to actual scan prefixes; the certificate itself
allows later row-pivot policies. Complete pivoting will need a separate column log.

## Reviewed fourth-wave numerical and pivot-policy slices

After preserving the third-wave build/audit/replay checkpoint, the workers have separate
ownership of the following concrete additions. Checks, approvals, targets and cost registries
remain untouched. Each lane must finish a successful actual execution theorem and its frame
before claiming a policy or numerical result.

### Complete pivot choice

The routine worker owns new `Matrix/Computation/CompletePivot.lean` (and a meaningful helper
file if required). `completePivotChoice` scans the contiguous active suffix of each active
column using existing `argmaxAbs`, consumes the selected relative row via `bindIdx`, and
compares that column winner with a global incumbent. Strict improvement preserves the first
column-major maximum: earliest column, then earliest row. Two exact singleton outputs record
absolute current row and column positions. The input is unchanged and all scratch is scoped.
The nonempty active block is explicit. No packed $N^2$ workspace or missing dynamic quotient
index operation is needed. This is a complete-pivot selection operation, not a complete-pivot
factorization driver.

A later driver needs both row and column logs, the convention
`A.submatrix rowPermutation columnPermutation = L * U`, swaps of prior lower-factor rows
AND prior upper-factor columns, and mixed row/column prefix transport. It cannot reuse the
row-only driver invariant unchanged. An all-zero active maximum remains a valid singular case.

### Fixed-scale row initializer and exact scaled selection

The LU worker owns new `Matrix/Computation/RowScales.lean` and
`Matrix/Computation/ScaledPivot.lean`. First compute each original row scale as its maximum
absolute original entry, with a complete vector-write frame, arbitrary rectangular dimensions and only zero in the
backend safe set. Then implement an actual exact
scaled scan returning the first maximum of `abs(columnEntry) / rowScale`. Inputs and scales
are read-only, the output is one exact index word, and all scratch is scoped. Require
nonnegative scales and zero-scale compatibility, and handle both candidate/incumbent zero
scales explicitly. For positive scales, cross multiplication is a valid exact comparator;
blind cross multiplication against a zero-scale incumbent is incorrect.

The first policy theorem uses exact semantics. Rounded products compare their computed
values and can reverse near ties, so they do not prove exact ratio selection. Fixed initial
scales must later follow row swaps; recomputed active scales define a different policy.
Scaled pivoting does not imply the unweighted multiplier bound one. A later driver needs
weighted prefix covariance and zero-row compatibility, not the existing unweighted maximum
hypothesis copied without change.

### Rounded rank-one update and actual saved-pivot trace

The Cholesky worker owns new `Computation/BLAS/RankOneRounding.lean` and, after its consumer
is available, `Matrix/Computation/SchurRounding.lean`. Reuse the existing arithmetic model,
`RelErr`, `IsRoundingProduct`, scalar execution lemmas and store frames. The first theorem
proves actual `ger` success and output writes with local relative-error witnesses; there is
currently no rounded `ger` theorem to substitute for this instruction order. Do not introduce
a second generic trace language or assume a successful run.

For the actual saved-pivot Schur code, account for `fl(-1)`, coefficient division, the
per-column multiply, the per-entry multiply and final add. The proposed local active-entry
defect is `u * abs(oldEntry) + roundingFactor 5 u * abs(colEntry * rowEntry / pivot)`;
the proof must audit this count rather than silently assume the negative literal is exact.
Full rounded PLU additionally needs exact integer literals for unit lower diagonals and a
new decoded active-entry invariant rather than exact `gaussState` equality. Global error
constants are not approved until their recurrence and inverse factors are checked.

Classical Cholesky stability is deferred pending a decision on a symmetric active update
using computed normalized columns. The current full Schur update can create skew, even
though explicit upper-prefix zeroing guarantees the returned factor's triangular storage.
A conservative input-margin success theorem remains possible for the current algorithm;
it must state numerical input margins and entry bounds rather than assume execution.

## Reviewed fifth-wave continuations

Fourth-wave sources remain frozen while their independent runtime checks and integration
finish. New work proceeds in separate staging roots, so it cannot invalidate the shared
checkpoint under validation.

* The routine worker owns a reviewed `Computation/SwapCells.lean` extraction and new
  rectangular `Matrix/Computation/ColumnSwap.lean`. A three-copy `swapCells` builder uses
  caller-owned scratch distinct from both input cells; the input cells may coincide. Its
  arbitrary-word execution/write/frame theorem has no numerical assumptions. The actual
  row and column builders share this helper and allocate one word for the whole exchange.
  Adapt the existing row proof instead of duplicating it. The column theorem exchanges
  columns in the existing packed encoding; zero rows need no source read. A separate empty
  execution theorem may admit arbitrary unused column expressions, including zero columns.
  Reuse existing Mathlib address arithmetic. Preserve the row builder's instruction order
  and public execution guarantee; no costs or registered trees are introduced.
* The Cholesky worker owns `Matrix/Computation/LUColumnRounding.lean` and a separate
  `GuardedEliminationRounding.lean` if needed. Prove successful actual existing column/total
  column code under the standard scalar model plus exact integer literals. Return the
  actual two factor writes, exact zeros/unit diagonal and below-diagonal division `RelErr`
  witnesses. The total branch avoids zero division. Compose the already checked rounded
  Schur result to prove total Schur success. No new runtime implementation, successful-run
  premise, duplicate trace language or global backward-error constant is permitted.
* The LU worker owns reviewed `Matrix/Computation/ScaledPartialPivot.lean`: consume the
  exact suffix selector's relative index, swap both residual and scale-vector rows, then
  record the absolute current row position. Its exact three-block frame returns the row-
  permuted matrix, identically permuted scales and actual index word. Matrix and scale
  windows may share a buffer if disjoint; the index buffer is separate. Require nonnegative
  scales and zero-scale compatibility only in the active column. Retain active zero-scale
  compatibility after the common row swap. First-ratio-max/ties refer to the pre-swap input.
  Fixed scales follow the same permutation; no rounded or unweighted-multiplier guarantee
  is asserted. Full weighted-prefix factorization remains a separate task.

A later full rounded PLU success theorem should track actual decoded residuals, structural
factor prefixes and the actual log, rather than exact `gaussState` equality. Guarded local
success and exact comparisons give triangular factors, unit diagonal and multiplier bound
`1+u` without requiring `u<1`. Such a theorem must not instantiate `IsPLURoutine` until a
product/backward residual allowance is proved. The latter numerical bound uses `u<1` and
must account for inverse multiplier factors as well as the five update factors.

## Reviewed sixth-wave factorization endpoints

The next two concrete endpoints consume the checked selector/exchange and local rounding
work. Their source work remains isolated until integration; none is claimed complete here.

### Full exact complete-pivoted LU

The routine worker owns new `Matrix/Factorizations/LUCompletePivoting.lean` and computation
`PLUQFrames.lean`, `PLUQPrefix.lean`, `PLUQ.lean`, splitting meaningful proof topics. The
runtime `pluqFactor` initializes residual and factors, chooses both actual absolute indices,
swaps residual and previous lower rows, swaps residual and previous upper columns, then
runs the existing total column and Schur steps. Track independent current-to-original row
and column log decoders, canonical prefixes and complete maximum-prefix dominance.

The exact headline returns actual successful execution, four original-store writes (two
factors and both logs), their stored reads, range, retained separate source and
`IsLU (A.submatrix rowPermutation columnPermutation) L U`, including singular and empty
inputs, plus the unweighted multiplier bound one. First ties refer to selection prefixes.
The new mathematical topic proves independent prefix-fixing row/column transport directly;
existing core `GaussState.lean` and `ForMathlib/GroupTheory/Perm/Fin.lean` are not modified.
A later solver must undo the column permutation on the solution, in addition to permuting
the right-hand side by the row log. No four-output routine certificate precedes the actual
runtime theorem.

### Full rounded partial-pivoted LU and componentwise backward error

The LU worker owns a dedicated pure `Matrix/Perturbation/LURoundingPrefix.lean` interface,
`IsLURoundingPrefix`, reviewed independently for the actual instruction order. This is the
concrete algorithm prefix invariant used by the runtime loop and final `IsLUErr` extraction,
not a new general trace language or replacement factorization predicate.

At step `k`, the identity for every entry of the currently row-permuted input `B` is

```text
B[i,j] = (if i,j ≥ k then S[i,j]*(1+θ[i,j]) else 0)
         + sum_{t<k} L[i,t]*U[t,j]*(1+η[t,i,j]).
```

The active residual coefficient has `k` rounding factors; coefficient `η[t]` has `t+5`.
Track triangular zeros and diagonal one only in committed factor prefixes. Row exchanges
transport `B,S,L,θ,η` together, leave prior `U` rows unchanged, and fix completed positions.
For a nonzero pivot, solve the actual update backward:

```text
S_old = S_new/(1+δ_add) + L_new[i,k]*U_new[k,j]*Q4/(1+δ_division).
```

`Q4` contains the negative literal, coefficient division and both GER multiplications. The
addition error cancels from the new factor-product coefficient. Its count is `k+5`; the new
residual count is `k+1`. Retired rows use exact diagonal one and upper-row copies; retired
columns use the inverse multiplier factor. A zero maximal pivot has a zero active column,
so guarded skip/zero multipliers require no pivot inversion. Ignore residual cancellation
noise outside the active block; structural zeros make new terms vanish for older entries.
At `k=N`, every count is at most `N+4`, yielding the reviewed conservative allowance
`roundingFactor (N+4) u`. The proof, not this design note, must establish the constant.
Use existing `IsRoundingProduct` product/ratio/padding/bound lemmas; `0≤u<1` suffices and
no `N*u<1` premise is needed. Nonzero `1+δ` is required for reconstruction.

The rounded-runtime worker owns a separate computation prefix/driver proof consuming this
pure invariant, actual column/total Schur witnesses, exact decoded partial-pivot selection
and the actual log. It proves actual full `pluFactor` success and framing under the standard
scalar and exact-index contracts, then the componentwise factorization allowance and
`IsPLURoutine` instance. Empty input takes the explicit empty-body path. The existing runtime
builder is unchanged. A preliminary structural success theorem may omit `u<1`, but it must
not be substituted for the full backward-error certificate. Rounded scaled cross-products
are not covered by this unscaled decoded-maximum argument.

## Forty-eight-hour schedule

| Elapsed window | Worker A | Worker B | Worker C | Integration lead |
|---|---|---|---|---|
| 0--4h | Cholesky audit, F2 design/consumers | LU/pivot audit, F2 design/consumers | F1 shared solve certificate | Inventory, design review, isolated worktree |
| 4--12h | F5 exact Cholesky loops/invariant | F4 no-pivot LU loops/invariant | F3 swap and pivot scan | Review first slices; targeted builds; settle storage API |
| 12--24h | F9 trace/nonbreakdown decomposition | F7 partial pivoting | F6 upper/adjoint solve | Integrate exact vertical slices and adversarial cases |
| 24--36h | F9 rounded Cholesky bound | F8 rounded LU bound | F10 solve composition; then F11 | Independent statement review, cost proposals |
| 36--44h | F13 LDL bridge if core stable | F11 complete/scaled pivoting | F14 prototype or F16 examples | Stop adding interfaces; fix integration failures |
| 44--48h | Review another worker's numerical claims | Review permutation/zero-pivot claims | Review footprints/degenerate dimensions | Full stage check, kernel replay, report and handoff |

Reserve the final four hours for verification. At 12 hours, if neither exact executable slice
is complete, prioritize one and queue the other. At 24 hours, if the shared pivot scan is not
certified, finish no-pivot LU and record pivoted implementation as unfinished. At 36 hours,
if global rounded proofs are incomplete, finish exact certificates and local rounded lemmas;
do not publish an unproved stability claim. Rook, blocked variants, complex instances and
indefinite block LDL are stretch work, not prerequisites for the first useful delivery.

## File ownership and integration

The architecture worker owns `Matrix/Perturbation/LinearSolveErr.lean` and
`Matrix/Computation/LinearSolveRoutine.lean`, plus their vocabulary rows. The LU worker owns
`Matrix/Perturbation/LUErr.lean`; the Cholesky worker owns
`Matrix/Perturbation/CholeskyErr.lean`. Each is ordered definitions, basic API, residual
consumers and exact-solve corollaries. No additions to existing library modules are needed for
this wave. The lead integrates additional vocabulary
rows, the generated `NLAlib.lean`, this note and the delivery report. New arithmetic syntax,
global model contracts and the existing target closure are outside the first wave.

Each worker provides the exact theorem statement, a plain-language read-back, validation
commands/results, and remaining assumptions. No worker runs a full stage check while another
is building. Targeted `lake lean` checks can run in parallel. Full integration runs once all
edits stop, with a dedicated `TMPDIR` to keep logs separate from other repository work.

## Verification and evidence

For every executable certificate inspect success, exact output writes, input preservation,
scratch lifetime and aliasing. Numerical tests cover empty and singleton dimensions, nonzero
offsets, singular and zero matrices, pivot ties, zero active columns, successive swaps,
ill-conditioned SPD inputs and rounded zero pivots. Tests supplement kernel-checked statements;
they do not substitute for them. Avoid adding implementation-mirroring tests for elementary API.

Run `python3 scripts/check_rules.py --files <changed Lean files>` while implementing. Then
regenerate the root import file through `lake exe mk_all --module --lib NLAlib` if files were
added, build affected modules with warnings fatal, and run `bash scripts/stage_check.sh`.
Record failures as failures, including pre-existing baseline issues; never modify the checks,
allowlists, toolchain pins or target registry to obtain a green result.

The baseline worktree has a user-owned uncommitted approval-hash correction and `.claude/`.
The sprint uses `/home/ubuntu/work/nlalib-dense-factorizations` on
`design/dense-factorization-routines`, preserving that state. The isolated checkout initially
inherits the committed approval file, whose hash differs from the current registry. Report
this baseline discrepancy if it blocks stage validation; do not fabricate an approval.

## Decisions still needed for later waves

1. Leading dimensions versus panel copies: begin with scalar loops; review an operand design
   only when F14 has a concrete consumer.
2. Pivot output: prefer a swap log with a proved permutation interpretation, compatible with
   the existing bounded index model. Do not pass an existential chosen permutation as input.
3. Cholesky nonbreakdown: first prove exact SPD success; design the quantitative rounded
   condition from the recurrence, with a downstream usable margin rather than a tautology.
4. Cost registration: submit concrete statement shapes after trees stabilize, then ask for
   maintainer registration only for those trees. Continue independent proof work meanwhile.
5. Resource use: keep the three worker slots occupied on independent proof obligations.
   Actual remaining account quota and automatic 48-hour continuation are not established by
   this repository or this plan; do not imply either has been reserved.
