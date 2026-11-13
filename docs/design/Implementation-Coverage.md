# Implementation coverage audit

> Archived execution-system design. The former evaluator, programs, target registry and
> emission tooling are retired. The current interfaces are documented in
> [the Ops migration](Ops-Migration.md) and [the program guide](../contributing/programs.md).
> Mathematical analysis is retained; program and registry names below describe the historical system.

Audit baseline: `d2e02916`, branch `feat/implementation-bridges`, 2026-11-04.
This is a source/interface audit, not a new kernel replay or a machine-execution certificate.
The baseline audit did not approve or register targets. The current integration below records
subsequent maintainer approval and complete implementation proofs.

## Current implementation coverage, 2026-11-05

The stored and oracle variants now have complete exact execution proofs:

| Program | Registered target and proof | Output scope |
|---|---|---|
| `cgProg.compiled` | `StoredEntriesConjugateGradient`, proved by `storedEntriesConjugateGradient` in [CGProgram.lean](../../NLAlib/Krylov/LinearSystems/CGProgram.lean) | Successful guarded execution for every real matrix and RHS, input preservation and legal status; for SPD matrices, all three vectors equal `cgState A b 0 q`, including zero termination |
| `lanczosProg.compiled` | `StoredEntriesLanczos`, proved by `storedEntriesLanczos` in [LanczosProgram.lean](../../NLAlib/Krylov/Processes/LanczosProgram.lean) | Basis, diagonal and subdiagonal coefficients, input norm, previous vector and preserved input agree with the total recurrence for every real matrix and RHS |
| `cgOracleProg.compiled` | `MatrixFreeConjugateGradient`, `matrixFreeConjugateGradient` in [CGOracleProgram.lean](../../NLAlib/Krylov/LinearSystems/CGOracleProgram.lean) | The same guarded CG outputs with oracle matrix-vector access |
| `lanczosOracleProg.compiled` | `MatrixFreeLanczos`, `matrixFreeLanczos` in [LanczosOracleProgram.lean](../../NLAlib/Krylov/Processes/LanczosOracleProgram.lean) | The same Lanczos outputs with oracle access and no matrix ROM |

The stored proofs cover actual ROM loads; the oracle variants execute actual oracle calls.
All four cover scalar operations, guards, allocations, complete loops, cleanup and approved
operation/memory bounds. There are **nine targets and seven concrete trees**, covering the
same four exact families: Gram–Schmidt, Hutch++, CG and Lanczos. Oracle internal costs remain
outside the matrix-free model; the sparse Hutch++ pattern family is additional to these trees.

Stored CG now has a complete primitive-execution-to-`CGRun` theorem in
[CGProgramRounded.lean](../../NLAlib/Krylov/LinearSystems/CGProgramRounded.lean) and a direct
actual-output backward/physical-energy corollary in
[CGProgramRoundedBackward.lean](../../NLAlib/Krylov/LinearSystems/CGProgramRoundedBackward.lean).
Its input-only precision and spectral conditions are explicit, including zero cases and
actual stopping. No desired local-error run or initialized numerical header is assumed.

Stored Lanczos now has the corresponding complete execution-to-`LanczosRun` theorem in
[LanczosProgramRounded.lean](../../NLAlib/Krylov/Processes/LanczosProgramRounded.lean) and
[compiled backward corollary](../../NLAlib/Krylov/Processes/LanczosProgramRoundedBackward.lean).
Local precision suffices for completion; geometric growth and the sharper horizon-dependent
backward radii are explicit. Actual zero continuation is separate from the active run.
The compiled oracle variants now construct the same rounded run models in
[CGOracleProgramRounded.lean](../../NLAlib/Krylov/LinearSystems/CGOracleProgramRounded.lean) and
[LanczosOracleProgramRounded.lean](../../NLAlib/Krylov/Processes/LanczosOracleProgramRounded.lean).
Their accuracy is supplied through `IsMatvecErr`, separately from scalar roundoff. Dense
numerical execution instantiates the shared backend-parametric analysis with its proved
floating-point product bound. Certifying an external backend's accuracy, matrix-function
postprocessing, preconditioning and IEEE endpoints remain separate obligations.
The [integration record](Krylov-Implementation-Integration.md) gives the current source map.
Twenty-eight Float cases execute the actual stored/oracle trees and check outputs and
resources. They do not certify the Float arithmetic contract.

The finite-format prototype is described in
[Finite-Precision-Arithmetic.md](Finite-Precision-Arithmetic.md). It adds the mixed
absolute-relative error relation `AbsRelErr` to the existing arithmetic interface and
analyzes the actual CG self-dot kernel with absolute underflow errors. A computed zero
cache certifies a small decoded recursive residual, rather than an exactly zero vector.
The checked Float backend proves finite binary64 representation, an injective 64-bit
encoding and correspondence to core's logical model. Its finite-word carrier now has a
proved [mixed-error accuracy and forward range-success contract](../../NLAlib/Computation/IEEE.lean).
The [bounded binary model](../../NLAlib/Computation/BinaryFloatSem.lean) independently
supports variable normal spacing, uniform subnormals and conservative checked overflow.
The [general CG residual-kernel theorem](../../NLAlib/Krylov/LinearSystems/CGProgramUnderflow.lean)
discharges every intermediate range condition from the input norm, dimension and format
parameters. Concrete specializations cover the bounded binary model and actual Lean Float;
they prove successful execution, the final store write/read and an explicit zero-cache bound.
This is a residual-kernel guarantee; whole-program IEEE CG, true-residual accuracy and
native backend runtime remain separate obligations. Fixed point remains a secondary
interface example. Exact-word regression tests execute the registered CG tree under Float
and bounded fixed-point arithmetic. Existing approved targets and static resource bounds
are unchanged.

The [mixed-error extension](Mixed-Error-Krylov.md) now adds successful, input-range-certified
axpy, gemv and gemm execution with relative-plus-absolute vector/matrix error bounds, actual
CG division and direction-update certificates, and actual checked Float square-root accuracy
and success. Norm estimation and normalization retain explicit absolute contributions.
Generic residual-gap and direct quadratic-update bounds allow arbitrary local defects,
including zero step lengths. Existing relative CG and Lanczos identities now consume these
shared algebraic results.

`CGRun.ofAbsRelErr` transfers an actual-data prefix to the existing relative run theory when
every absolute defect fits its explicit local scale margin. Cache/curvature positivity is
separate, and a terminal zero cache with nonzero residual does not satisfy this transfer.
Measured mixed Lanczos defects feed the existing recurrence and adjacent-inner-product API;
normalization and nonzero-column certificates remain explicit. These are kernel, defect and
conditional prefix results. They do not yet derive a complete bounded-format CG/Lanczos run,
its full no-overflow invariant, or all underflow/zero-continuation behavior from program inputs.

The tables and review history below describe the explicitly identified audit baseline;
they are historical evidence, not current coverage totals.

## Finding and scope

The library has substantial theory about mathematical algorithm outputs, exact recurrences,
conditional local-error runs, and specified scalar kernels. Those are distinct guarantees.
At the audited baseline, the complete program-to-exact-output chains are Gram–Schmidt and
Hutch++. Neither chain has an algorithm-level rounded or verified IEEE implementation theorem.
CG and Lanczos have strong conditional finite-precision output bounds but no program execution
constructor for their local-error run interfaces. `MatrixFreeRounded` exists as a model and has
no consumer outside its defining file at this baseline.

This is a coverage gap, not a defect in the conditional mathematical theorems. Matrix
inequalities, perturbation bounds, approximation theory, concentration, and adversarial query
lower bounds should remain reusable. A statement about an abstract matrix or certified vector
does not need to select one implementation. A claim about a returned implementation output
must identify the execution and the theorem connecting its decoded output to that statement.

Key entry points are [the target registry](../targets.toml),
[CGRun](../../NLAlib/Krylov/FinitePrecision/CGRun.lean),
[LanczosRun](../../NLAlib/Krylov/FinitePrecision/LanczosRun.lean), and
[arithmetic contracts](../../NLAlib/Computation/Contract.lean).

The inventory was obtained by searching every library Lean file for `Algorithm:`, program and
compiled-tree declarations, registered targets, `exec_`, `IsRelErrSem`, `IsArithErrSem`,
`MatrixFreeRounded`, `CGRun`, and `LanczosRun`, and checking the relevant declarations and
hypotheses. It also includes the untagged specifications in the family table below. Lack of a
link means no source declaration was found, not a theorem that such a link cannot be proved.

## What each link means

| Link | Evidence required | What it does not establish |
|---|---|---|
| Mathematical output | A definition such as `cgIterate`, `rsvd`, `slq`, plus theorems about that object | An evaluation strategy, buffer layout, rounding order, cost, or returned machine result |
| Exact recurrence | A specified vector/scalar operation order and correspondence to the mathematical output | A scalar-loop or buffer implementation of the primitive operations |
| Concrete program | One first-order `Prog` tree, explicit buffers, branches, loop order and oracle calls | Correctness merely from its existence or `Algorithm:` tag |
| Exact correspondence | A theorem about `exec`/`Prog.exec`, identified inputs, output cells, failures, and the specified arithmetic interpretation | Rounded arithmetic, even when the same tree can run under `Float` |
| Arithmetic contract | A proved `IsRelErrSem`/`IsArithErrSem` instance, successful operations, alias/range premises, and kernel execution theorems | Automatic composition into a whole solver or a machine-format instance |
| Per-step bridge | Decoded execution data construct `CGRun`, `PCGRun`, or `LanczosRun`, with one explicit accuracy parameter and stop horizon | Unproved positivity, nonbreakdown, normalization or oracle-accuracy assumptions |
| Finite-precision output | The run theorem is instantiated at the actual decoded returned vectors, including final postprocessing | A machine implementation if its semantics/decoding has no verified format correspondence |
| Machine implementation | A finite-word format, exceptional/underflow behavior, primitive semantics and execution-refinement theorem | Certification supplied by a demo, a chosen bit width, emitted Python, or an unbounded-exponent real model |

The first-order/run connection is proved by `FStmt.exec_eq_exec_toStmt` and
`Prog.exec_eq_exec_toStmt` in `Computation/FirstOrder.lean:169,211`. The compiler is not a trusted
correctness shortcut: the targets name the resulting trees, and their instantiation equations
are checked. `RunsWithin.subst`, `RunsWithin.substOracle` and the implementation certificates
in `Computation/Subst.lean` provide genuine composition, subject to their interpretation,
store, read-only-data and cost hypotheses. None changes exact arithmetic into rounded arithmetic
by itself.

## Complete inventory of Algorithm tags

There are **27 tagged declarations, grouped into seven ids** at the baseline. A tag is catalogue
metadata; it is not evidence of a program or a realization theorem.

| Id | Tagged declarations | Source evidence |
|---|---|---|
| `cg` (5) | `cgIterate`; `CGState`, `cgStep`, `cgState`; `CGRun` | `Krylov/LinearSystems/CG.lean:85`; `CGRecurrence.lean:49,68,79`; `Krylov/FinitePrecision/CGRun.lean:72` |
| `pcg` (5) | `pcgIterate`; `PCGState`, `pcgStep`, `pcgState`; `PCGRun` | `Krylov/LinearSystems/PCG.lean:81`; `PCGRecurrence.lean:56,75,85`; `Krylov/FinitePrecision/PCGRun.lean:53` |
| `lanczos` (9) | `LanczosState`, `lanczosAlpha`, `lanczosStep`, `lanczosState`, `lanczosMatrix`, `lanczosTridiagonal`; `LanczosRun`; `LanczosRun.normalizedFunctionApprox`, `LanczosRun.functionApprox` | `Krylov/Processes/LanczosRecurrence.lean:50,63,74,81,87,93`; `Krylov/FinitePrecision/LanczosRun.lean:47`; `LanczosFunctions.lean:65,72` |
| `gram-schmidt` (3) | `gramSchmidtQ`, `gramSchmidtR`, `gramSchmidtProg` | `Matrix/Factorizations/GramSchmidt.lean:156,163`; `GramSchmidtProgramTree.lean:54` |
| `hutchpp` (2) | `hutchpp`, `hutchppProg` | `Estimation/Trace/HutchPlusPlus.lean:92`; `HutchPlusPlusProgramTree.lean:50` |
| `randomized-svd` (2) | `rsvd`, `earlyTruncatedRSVD` | `Matrix/Factorizations/SketchedLowRank.lean:94,323` |
| `sketch-and-solve` (1) | `sketchAndSolve` | `Matrix/Pseudoinverse/LeastSquares.lean:345` |

All paths in the tables, unless prefixed otherwise, are relative to `NLAlib/`. Line numbers
identify the baseline; declarations are the stable lookup keys after edits.

## Registered programs and exact targets at the audit baseline

`docs/targets.toml` contains **three registered concrete trees and five targets**. The sparse
Hutch++ tree is additionally a function of a public COO pattern; its target has `trees = []` and
freezes that function through the target closure. This is the documented nonuniformity in the
public sparse pattern, not a fourth registered concrete tree or an absent sparse proof.

| Target | Tree and exact output | Proof and important scope |
|---|---|---|
| `MatrixFreeGramSchmidt` | `gramSchmidtProg.compiled`; declared input buffer becomes `gramSchmidtQ Y` | `matrixFreeGramSchmidt`, `Matrix/Factorizations/GramSchmidtProgram.lean:876`; no rank hypothesis; zero-column branches save operations; counts are upper bounds |
| `MatrixFreeHutchpp` | `hutchppProg.compiled`; output cell equals `hutchpp A S G` for the identified tape slices | `matrixFreeHutchpp`, `Estimation/Trace/HutchPlusPlusProgram.lean:1229`; positive residual-probe count; exact oracle and exact arithmetic |
| `MatrixFreeProbHutchpp` | Same tree and output, plus its Gaussian-tape error tail | `matrixFreeProbHutchpp`, same file:1256; explicit sketch-size, positive failure parameter and nonnegative threshold; tape law is mathematical, not a verified sampler |
| `StoredEntriesDenseHutchpp` | `hutchppProg.compiledDense`; exact dense entry implementation replaces oracle calls | `storedEntriesDenseHutchpp`, same file:1271; entries counted as read-only memory and reads |
| `StoredEntriesCooHutchpp` | `hutchppProg.compiledCoo pattern`; exact COO matrix from stored values | `storedEntriesCooHutchpp`, same file:1289; pattern entries in bounds; host index-pattern storage is outside the numeric-cell memory model |

The exact meanings are explicit in `Computation/Model.lean:117,134,154`:
`storedInterp` uses `exactSem`; `MatrixFree` uses `exactInterp`; `StoredEntries` uses
`storedInterp`. The probabilistic model in `RandomMatrix/Tape.lean` also uses exact arithmetic.
The five targets appear in `docs/targets.toml:1142–1261` and are declared in
`Matrix/Factorizations/GramSchmidtTargets.lean` and
`Estimation/Trace/HutchPlusPlusTargets.lean`.

Program correspondence is substantial: `exec_orthAgainst`, `exec_gramSchmidtProg`,
`gramSchmidtProg.toStmt_compiled`, `matrixFree_hutchppProg`, and
`hutchppProg.toStmt_compiled` identify the buffer results. The Gram–Schmidt program is
**modified** Gram–Schmidt; `mgsSweep_eq_sub_sum` connects its exact sequential sweep to the
mathematical Gram–Schmidt definition. It does not establish their floating-point equivalence.
The Hutch++ program explicitly draws the sketch, applies the oracle, draws the residual probes,
orthogonalizes the sketch result, projects the probes, applies the oracle again, then
accumulates and divides the trace sum.

## Family coverage, including untagged specifications

In the status column, **spec** means a mathematical output or exact vector recurrence;
**program/exact** means a concrete program with an exact execution theorem;
**local/fp** means a conditional local-error run and finite-precision analysis.
No row below has a verified finite-word IEEE endpoint at the baseline.

| Family and existing theory | Strongest established implementation link | Missing link / priority | Declaration and path evidence |
|---|---|---|---|
| CG polynomial, minimax, residual, physical energy and delayed estimator | spec + exact recurrence + local/fp | Program and decoded whole-run constructor; initialization, positivity and stopping; **P1** | `Matrix.PosDef.cgState_x_eq`, `Krylov/LinearSystems/CGRecurrence.lean:354`; `CGRun` in `FinitePrecision/CGRun.lean:72`; output theorems in `CGAccuracy.lean`, `CGEnergyEstimator.lean`, `CGSpectralConvergence.lean` |
| PCG and inexact preconditioner applications | spec + exact recurrence + local model | No PCG buffer program or execution-to-`PCGRun` theorem; no universal convergence claim for arbitrary Euclidean-error preconditioners; **P1/P2** | `Matrix.PosDef.pcgState_x_eq`, `LinearSystems/PCGRecurrence.lean:238`; `PCGRun.state_eq_pcgState`, `FinitePrecision/PCGRun.lean:259`; `CGRun.toPCGRun`:278 |
| Lanczos, Paige, backward spectrum | spec + exact recurrence + local/fp | Paige A(1) buffer order, norm/normalization composition, initialized decoded run and breakdown; **P1** | `Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix`, `Processes/LanczosRecurrence.lean:373`; `LanczosRun`, `FinitePrecision/LanczosRun.lean:47`; `BackwardSpectral.lean` |
| Physical Lanczos function approximation | conditional output from raw or normalized run columns | Exact initial-direction/scaling match is additionally assumed by the scaled baseline corollaries; small function/basis/scaling postprocessing needs its own error; **P1/P2** | `LanczosRun.functionApprox`, `FinitePrecision/LanczosFunctions.lean:72`; `norm_cfc_mulVec_sub_le_of_norm_sub_smul_functionApprox_le`; `norm_cfc_mulVec_sub_smul_functionApprox_le_of_precision` |
| SLQ trace and spectral density | spec, exact equality to per-probe Lanczos mathematics | Repeated-probe execution, rounded quadrature/postprocessing and final accumulation; **P2** | `slq`, `Estimation/Trace/StochasticLanczosQuadrature.lean:78`; `Matrix.IsHermitian.slq_eq_sum_lanczosFA`:105; `slqMeasure`, `Estimation/Spectral/SpectralDensity.lean:98` |
| Gram–Schmidt / QR by MGS | program/exact, no rank hypothesis for program output | Rounded orthogonality/range/QR quality and numerical zero/pivot policy; **P1/P2** | `gramSchmidtProg.compiled`, `Matrix/Factorizations/GramSchmidtProgramTree.lean:67`; `matrixFreeGramSchmidt` as above |
| Hutch++ | program/exact, exact dense/COO substitution and Gaussian tail | Rounded MGS/projections/trace sum and resulting estimator perturbation; concrete sampler law; **P2** | Four Hutch++ targets above; `HutchPlusPlusProgramTree.lean:50–95`; `HutchPlusPlusProgram.lean` |
| Girard–Hutchinson | spec; used internally by exact Hutch++ correspondence | Standalone probe/matvec/dot/accumulation program and rounded estimator; **P2** | `girardHutchinson`, `Estimation/Trace/GirardHutchinson.lean`; `girardHutchinson_eq_sum` |
| RSVD / early-truncated RSVD | projector/truncation specs with deterministic and probabilistic guarantees | Sketch, range basis, projection, small SVD and returned low-rank factors; no standalone program; **P2** | `rsvd`, `earlyTruncatedRSVD`, `Matrix/Factorizations/SketchedLowRank.lean:94,323`; `LowRank/Gaussian/RangeFinder*.lean`, `EarlyTruncationRSVD.lean` |
| Nyström, generalized Nyström, early-truncated GN | exact algebraic specs, including implementation-friendly factor identities | Concrete solve/factorization/truncation selection, singular/rank-deficient behavior and rounded factors; **P2** | `nystrom`, `Matrix/Factorizations/NystromGram.lean:79`; `generalizedNystrom`: `SketchedLowRank.lean:199`; `generalizedNystrom_eq_mul_sketchAndSolve`:285; `earlyTruncatedGeneralizedNystrom`:371 |
| Randomized block Krylov / Nyström BKI | block-space/polynomial specs with bounds | Orthonormalized block iteration, rank decisions, storage and rounded recurrence; **P2** | `rbki`, `nystromBKI`, `LowRank/Structural/BlockKrylov.lean:85,95`; `rbki_eq_rangeProjector`:111 |
| Arnoldi / GMRES | exact MGS recurrence linked to mathematical basis; projected solve formulas | Buffer Arnoldi, Hessenberg QR/back substitution and rounded/returned solver; **P2** | `mgsArnoldiMatrix_eq_arnoldiMatrix`, `Processes/ArnoldiRecurrence.lean:210`; `gmresIterate`, `LinearSystems/GMRES.lean:82`; `Matrix/Factorizations/GivensHessenberg.lean:240` |
| MINRES / preconditioned Lanczos | exact recurrences and split-system identities | Their own operation order and error bridge; CG/Lanczos contracts cannot silently cover them; **P2** | `Matrix.IsHermitian.minresState_x_eq`, `LinearSystems/MINRESRecurrence.lean:544`; `preconditionedLanczosMatrix_eq`, `Processes/PreconditionedLanczos.lean:243` |
| Richardson / iterative sketching / Landweber specializations | exact stationary iteration and filter identities | Matvec/update program and perturbation accumulation; factorization setup for sketching; **P2** | `richardsonIterate`, `LinearSystems/Richardson.lean:71`; `iterativeSketching`, `Regression/IterativeSketching.lean:76`; shifted-Gram powers in `Matrix/Spectral/PowerBounds.lean:489` |
| Sketch-and-solve | pseudoinverse spec and least-squares guarantees | A selected QR/SVD/iterative solver, sketch multiplication and returned-vector certificate; **P2** | `sketchAndSolve`, `Matrix/Pseudoinverse/LeastSquares.lean:345`; `isLeastSquaresSolution_pinv_mulVec`, `mul_sketchAndSolve` |
| Sketch-and-precondition | exact reduction to PCG and QR/SVD coordinate formulas | Preconditioner construction and application, finite-precision setup and PCG execution; **P2** | `sketchAndPrecondition`, `Regression/SketchAndPrecondition.lean:93`; `IsQR.sketchAndPrecondition_eq_mulVec_cgIterate`:137; `pcgState_x_eq_sketchAndPrecondition`:201 |
| Sketch-and-project / Kaczmarz | exact row-action recurrences and i.i.d.-sequence expectation guarantees | Row sampler, row norm setup, finite-precision update, zero-row/termination policy; **P2** | `sketchAndProjectIterate`, `Regression/SketchAndProject.lean:93`; `kaczmarzIterate`, `Regression/Kaczmarz.lean:89`; `kaczmarzIterate_succ`:172 |
| Triangular solves | exact functional recurrences and a concrete lower-triangular kernel, including rounded backward error | Connect selected high-level solve/factorization pipeline; no separate rounded upper-solve kernel found; **P1/P2** | `forwardSubst_eq_inv_mulVec`, `Matrix/Factorizations/Triangular.lean:462`; `backSubst_eq_inv_mulVec`:473; `IsRelErrSem.exec_trsvLower_add_mulVec_eq`, `Computation/BLAS/Triangular.lean:459` |
| Gaussian elimination / LU / Cholesky | exact recurrences and factorization realization | Buffer order, pivot selection and numerical breakdown, rounded factorization/solve; **P2** | `gaussState`, `Matrix/Factorizations/GaussState.lean`; `isLU_luLower_luUpper`, `LU.lean:279`; `Matrix.PosDef.isCholesky_choleskyLower`, `Cholesky.lean:284` |
| Householder / Givens QR / Hessenberg reduction | exact reflector/rotation recurrences and QR identities | Stable coefficient generation, buffer kernels and rounded transformations; **P2** | `isQR_householder`, `Matrix/Factorizations/Householder.lean:361`; `isQR_givensHessenberg`, `GivensHessenberg.lean:83`; `Hessenberg.lean` |
| Power/inverse iteration and Ritz eigenvalue estimates | powers, Rayleigh quotients, exact Krylov basis/recurrence theory | Repeated normalized products or solves, Ritz solve and returned-pair residual certificate; **P2** | `Krylov/Eigenvalues/PowerIteration.lean:57,159,221`; `Krylov/Eigenvalues/Ritz.lean`; `Estimation/Spectral/RandomStart.lean` |
| Gaussian/Rademacher/Haar sketches; sampling, CountSketch, SRHT | mathematical distributions and matrix constructions; tape slice laws | Finite sampler/transform programs, seed law and distribution-error bridge; **P2** | `RandomMatrix/{Gaussian,Rademacher,Haar}/Basic.lean`; `RandomMatrix/Tape.lean`; `Sketching/{Sampling,Sparse,Structured}` |
| SVD/truncated SVD, GSVD, Schur, polar, regularization and spectral functions | mathematical decompositions, chosen witnesses and exact filter/optimality theorems | Do not advertise these as eigensolver/SVD implementations. A selected numerical endpoint needs a separate realization/perturbation contract; **P2 when consumed** | `svdU`, `svdV`, `Matrix/Spectral/SVD.lean:513,527`; `truncatedSVD`, `Spectral/LowRank.lean:82`; `Factorizations/{GeneralizedSVD,Polar}.lean`; `Pseudoinverse/{RegularizedLeastSquares,GeneralTikhonov,Tikhonov,TruncatedSVD}.lean` |
| Scalar approximation, orthogonal polynomials, quadrature and query lower bounds | reusable pure mathematics / abstract information-access model | No obligation to implement every lemma. Numerical coefficient/quadrature evaluation or a claimed executable query strategy needs its own bridge; **not an unconditional implementation gap** | `Polynomial/Approximation`, `Polynomial/Orthogonal`, `LowerBounds/QueryModel`; `Krylov/Functions/Quadrature.lean` |

## Arithmetic and kernel evidence

`Computation/Contract.lean:86` defines `IsRelErrSem` with both accuracy **and success** clauses.
It covers literals, four arithmetic operations, square root, exact real negation/conjugation/
real-part extraction, decoded comparisons and conversion. `IsArithErrSem` at line 193 admits
other arithmetic error relations, including a possible absolute underflow term;
`AddsZeroExactly` is separate. The generic kernel run theorems retain range and alias premises.
The headline standard-model kernel bounds usually specialize to `safe := True`, so they are
not finite-exponent overflow/underflow theorems. `MatrixFreeRounded` itself hardcodes this
all-range relative-error success contract (`Computation/Contract.lean:299`). A finite-exponent
IEEE semantics cannot generally instantiate it on every operand: a machine endpoint needs
proved range invariants and a safe/error-aware algorithm statement, or a precisely restricted
format domain. The generic `IsArithErrSem` kernel layer offers a starting point. The model
also accepts a size-indexed statement family; a new registered algorithm target should identify
`Prog.toStmt` of its fixed tree explicitly when claiming first-order uniformity.

| Concrete kernel | Exact execution evidence | Rounded execution evidence at baseline |
|---|---|---|
| `dot` | `Computation/BLAS.lean:370` | `IsArithErrSem.exec_dot`, `BLAS/RoundingErrors.lean:379`; `IsRelErrSem.exec_dot_eq_sum_mul_one_add`, `exec_dot_eq_sum_mul_one_add_isRoundingProduct`, `exec_dot_abs_sum_mul_sub_le` at 693,719,745; requires exact zero addition and explicit small `n u` |
| `axpy` | `BLAS.lean:423` | `IsArithErrSem.exec_axpy`:424; `IsRelErrSem.exec_axpy`:770; in-place exact aliasing allowed by explicit hypotheses; no partial-overlap shortcut |
| `rscl` | `BLAS.lean:529` | `IsRelErrSem.exec_rscl`, `BLAS/RoundingErrors.lean:794`; explicit nonzero decoded divisor |
| `gemv`, `gemm` | `BLAS/MatrixKernels.lean:379,602` | Trace/run theorems and `IsRelErrSem.exec_gemv_eq_add_mulVec`, `exec_gemv_abs_mulVec_sub_le`, `exec_gemm_abs_mul_sub_le` in `BLAS/RoundingErrors.lean:848,894,934` |
| `trsvLower` | `BLAS/Triangular.lean` | `IsArithErrSem.exec_trsvLower`:366; `IsRelErrSem.exec_trsvLower_add_mulVec_eq`:459; lower triangular, nonzero diagonal, `n u < 1`, disjoint matrix/vector storage |
| `scal`, `copyv`, `nrm2`, `ger` | `BLAS.lean:486,573,611`; `BLAS/MatrixKernels.lean:459` | No corresponding rounded public execution theorem found. Copy is nonarithmetic, but its general-semantics frame/execution bridge still needs evidence; `nrm2` composition is especially important for Lanczos/MGS |
| Dense/COO oracle implementations | `implementsOracle_denseImpl`, `Computation/Dense.lean:324`; `implementsOracle_cooImpl`, `Sparse.lean:363` | Their existing certificates specialize to exact arithmetic. No theorem found that instantiates `IsMatvecErr` for a rounded dense/COO implementation |

`IsMatvecErr` (`Computation/Contract.lean:264`) is a separate success-and-normwise oracle
contract. `MatvecOracle` (`Matrix/Basic/MatvecOracle.lean`) is a mathematical action with a
normwise certificate. They are not interchangeable execution objects. In particular, a
componentwise `gemv` error bound must be converted into the stated normwise tolerance, including
its dimension/matrix dependence; `epsilon = unit roundoff` cannot be assumed.

## Conditional finite-precision endpoints

The `CGRun` fields explicitly fix the Hestenes–Stiefel order, a zero initial iterate, unrounded
initial residual/direction, computed residual squared norms, positive numerator/curvature at
steps taken, and a possibly zero final numerator. A sound program bridge must derive these
facts for a successful prefix, not obtain execution by assuming the entire conclusion record.
A zero-step or initially solved execution needs a separate case because `CGRun.k_pos` is strict.

`LanczosRun` fixes Paige A(1) order: matvec, subtraction of the previous vector, dot product,
subtraction of the current vector, then normalization. Its nearly-unit hypotheses are part of
the interface, not consequences of the scalar contract alone. A bridge must derive the
normalization defect and squared-norm bounds, nonbreakdown before the terminal step, and a
safe terminal case without division by zero.

`PCGRun` correctly separates the preconditioner oracle tolerance from arithmetic tolerance and
uses the oracle at initialization as well. Its zero-error theorem recovers `pcgState`; it does
not claim that every approximate preconditioner produces exact PCG or converges.

The scaled baseline Lanczos corollaries also assume
`hb : b = ‖WithLp.toLp 2 b‖ • L.normalizedV 1`. A nearly-unit computed initial vector does
not imply this exact directional identity. Actual rounded `nrm2` followed by componentwise
rounded division can perturb direction, and the computed scaling value can differ from
`‖b‖`. To connect such an initializer, a transfer theorem should accept the actual scale `s`
and a certificate `‖b - s • L.normalizedV 1‖ ≤ τ`, adding a term `M * τ` when
`specNorm (cfc f L.H) ≤ M`, plus the scaled approximation and final-output error.
The root integration task is addressing this gap; it is **not counted as proved coverage**
until the theorem and its actual normalization consumer are present and checked.

The CG energy estimator's scalar decrement sum is evaluated exactly. A rounded reduction of
that sum requires its own error budget. Physical Lanczos function outputs use exact `cfc f T`
and exact final vector multiplication/scaling; the theorem with an extra returned-vector error
hypothesis provides a composition point, not an implementation of that postprocessing.

`overRelaxedCGRun` is an explicit admissible mathematical local-error run, constructed under a
horizon and nonzero-residual assumptions. It is not an execution of IEEE round-to-nearest or a
concrete scalar semantics producing that error pattern.

## Machine and randomness boundary

* `Computation.gridSem` is a proved nonzero-roundoff contract witness:
  `isRelErrSem_gridSem`, `Computation/Grid.lean:78`, and `addsZeroExactly_gridSem`. It uses a
  **real carrier, noncomputable rounding and unbounded exponent**. This is meaningful floating
  arithmetic theory, not a verified finite-word IEEE implementation or an executable backend.
* `NLAlibTools/Float.lean:28` defines `floatSem`; its own module docstring says nothing there is
  proved about `Float`. The builder/tree `#guard` comparisons test examples, not all executions.
* `NLAlibTools/NumPy.lean` emits the first-order tree and supports named and inlined kernels.
  Its module docstring correctly calls the translation unverified. In named mode the NumPy/BLAS
  implementation may choose a different reduction/FMA/parallel order than the scalar tree.
* `NLAlibTools/FixedPoint.lean:346,369` proves `implementsInstr_fxImpl` and
  `fxSem_mul_abs_sub_le`. Its integer carrier is unbounded, its arithmetic subset is limited,
  and it does not establish the full relative-error contract or finite-word IEEE semantics.
* `RandomMatrix/Tape.lean` connects ideal tapes to sketch distributions and independence.
  No verified concrete Gaussian generator, PRNG seed law, or approximation-of-law transfer to
  a machine sampler was found. Exact-program probability theorems retain their tape-law scope.
* The registered exact targets use width zero. Their numeric-cell counts and read-only memory
  accounting are genuine properties of that model, not CPU runtime or a verified bit-memory
  bound for a finite-word implementation. The documented initial `curW`/`peakW` and sparse
  host-index-storage limitations must remain visible when making a future bit-cost claim.

## Prioritized follow-up and target proposals

These are proposals for maintainer review, not declarations, approvals, registrations or claims
that a new implementation is already verified. New/changed targets need docs/contributing/programs.md
review of their exact statements, trees, closures, counts, memory and pins.

| Priority | Concrete work | Acceptance evidence |
|---|---|---|
| **P0** | Correct source docs that point to absent local programs/proofs; preserve historical/provenance citations as history | Current source docs name only present declarations or label the desired future bridge explicitly; see discrepancy list below |
| **P1** | Supply a decoded norm-kernel/normalization bridge and vector norm bounds for existing `dot`/`axpy`/division executions | Actual operation-order hypotheses, dimension/unit-roundoff constants, full products of errors, zero/nonzero branches, storage/frame preservation; no assumed `CGRun`/`LanczosRun` conclusion |
| **P1** | Implement a selected Hestenes–Stiefel CG first-order program and exact correspondence | Proposed `MatrixFreeCG` target family: declared input RHS, zero start, explicit maximum steps and returned stop count/iterate/residual, guarded zero residual/curvature, and a correspondence to `cgState` on its stated SPD/success domain. Include all returned cells and failure/early-stop behavior. Choose a suitable approved preconditioned access model or a genuinely total guarded program; the existing `MatrixFree` has no matrix precondition argument |
| **P1** | Prove execution-to-`CGRun` for that same tree and operation order | Proposed rounded target: fix that same tree and quantify every interpretation satisfying the `MatrixFreeRounded` scalar and matvec contracts; derive one explicit accuracy parameter from scalar `u`, dimension and the matvec certificate; identify the successful prefix, positive pivots and terminal case; instantiate the physical residual/energy/minimax/estimator results at the decoded returned data |
| **P1** | Implement Paige A(1) Lanczos with explicit normalization and stopping | Proposed `MatrixFreeLanczos`/basis-output target family: declared starting vector, scalar coefficient buffers, optional returned basis, explicit normalization and zero-vector/terminal branches; exact result equals `lanczosState`/`lanczosTridiagonal` and basis where returned; counts and footprints for the selected storage strategy |
| **P1** | Prove decoded execution-to-`LanczosRun` for that tree | Proposed rounded target: derive all five local defects and nearly-unit bounds from the executed kernels, with initialization and terminal nondivision; recover the matrix-function approximation bound only after certifying its small-matrix solve and returned-vector postprocessing |
| **P2** | Extend existing Gram–Schmidt/Hutch++ registered trees to rounded correctness | New rounded targets require perturbed QR/range/projection and trace-accumulation guarantees, with conditioning/rank/pivot policy and sampler assumptions. Reuse existing exact trees; do not advertise exact `gramSchmidtQ` equality after rounding |
| **P2** | Connect dense/COO rounded oracle calls and PCG preconditioning to execution contracts | Prove `IsMatvecErr` from the actual nested loops and decoded ROM/inputs; then connect it to the mathematical oracle interface and derive the solver's chosen tolerance |
| **P2** | Cover other algorithm families incrementally | Prioritize realization of shared QR/triangular/SVD/small-eigensolver endpoints used by RSVD, Nyström, GMRES, sketch-and-solve and SLQ; each algorithm reuses certified subprograms, plus its own output/rounding composition |
| **P2** | Establish a finite-word machine and sampler endpoint | A format-specific semantics and decoding, IEEE exceptional/range/underflow conditions, a safe/error-aware algorithm theorem or justified restricted domain, verified primitive/back-end refinement and a sampler law or quantified law error; only then transfer the algorithm guarantee |

Before any new target is registered, write out its exact Lean signature and review the selected
operation order, branching, input representation, index/control/ROM accounting, and output.
A target must not simply assume an execution or a complete local-error record whose existence
is the missing proof. A successful-prefix theorem may legitimately be conditional, provided
its conditions and early/zero-step cases are explicit and a separate theorem addresses success
on the desired input domain.

## Documentation discrepancies and false positives

1. **Absent local CG rounding file.** `Krylov/FinitePrecision/CGRun.lean:26–27` presents
   `NLAlib/Krylov/LinearSystems/CGRounding.lean` as the program rounding analysis. That file is
   absent at the baseline. The local-error interface and its stability analysis exist; the
   cited execution bridge does not.
2. **Absent CG program and exact proof names.** `Krylov/FinitePrecision/OverRelaxedCG.lean:33–43`
   names `NLAlib.cgProg` and `NLAlib.exec_cgProg_exactInterp` while explaining a future perturbed
   execution proof. Neither declaration exists. Preserve the distinction between its proved
   `CGRun` constructor and an unproved execution witness, and label the proposed program as such.
3. **Lanczos constructor wording.** `Krylov/FinitePrecision/LanczosRun.lean:21–23` says the
   program rounding analysis constructs a run from program execution. No such theorem is found
   at the baseline. Describe this as the intended consumer/producer interface until proved.
4. **Computation design history versus inventory.** `docs/design/Computation.md:128,193,520–577`
   and its §11 table name a `Krylov/Processes/LanczosProgram.lean` and show skeleton code with
   admitted realization statements. The file is absent; its table at line 765 also says stage
   1b is not started. Keep the historical draft, but place a current-status warning before
   present-tense statements so readers do not count those examples as library code.
5. **Superseded design snapshot.** The F10 history in `docs/design/Computation.md` describes a
   tree emitter as later work and approval-file existence as pending; the later migration
   section and current files supersede those observations. Its emitter is now a first-order
   tree emitter, still unverified, and `docs/targets.approved` exists. Current coverage should
   use the source/registry, not an early historical table in isolation.
6. **Not broken local references.** The old `Matrix/Basic/{GeneralTikhonov,Tikhonov,Landweber,
   TruncatedSVDRegularization}.lean`, `GeneralTikhonovEndpoints.lean` and
   `ForMathlib/Analysis/PenaltyLimits.lean` paths in recent regularization docs explicitly refer
   to proof material in external `tchen-research/NLAlib` at a named commit. Their absence in this
   checkout is not a local missing-implementation finding.
7. **Already accurate boundaries.** `NLAlibTools/Float.lean` and `NLAlibTools/NumPy.lean`
   explicitly describe their testing/unverified status. `LanczosFunctions.lean` explicitly
   scopes exact postprocessing, `CGEnergyEstimator.lean` scopes exact scalar sums, and
   `PCGRun.lean` avoids an unconditional convergence claim. Preserve these qualifications.

## Audit validation and handoff

No Lean build was run for this audit and no source, target, check, pin, registry or allowlist was
edited. Source searches and the registry inventory above are the evidence for coverage, not a
substitute for the root agent's integration/build/replay checks. Any bridges added during the
parallel implementation pass should be recorded in a dated amendment with their actual
executed program, theorem hypotheses and output cells; do not promote a planned link to
verified coverage merely because a file or definition was added.

## Checked amendment, 2026-11-04: local arithmetic and input transfer

`NLAlib/Matrix/Computation/BLAS.lean` now connects the existing actual `dot`,
`axpy` and rectangular `gemv` executions to Euclidean norm error bounds. The
checked declarations are `IsRelErrSem.exec_dot_abs_dotProduct_sub_le`,
`IsRelErrSem.exec_dot_self_relErr`, `IsRelErrSem.exec_axpy_norm_sub_le`,
`IsRelErrSem.exec_gemv_norm_sub_le_frobNorm_mul`, and
`IsRelErrSem.exec_gemv_norm_sub_le_specNorm_mul`, all in
`NLAlib.Computation`. Each returns successful `exec` and the same destination
word or `writeBlock` witness as its componentwise kernel theorem. Dot and gemv
assume exact addition of zero and the dimension-dependent small-roundoff window;
axpy assumes the two-operation window. All retain decoded-input, writable-output
and disjointness premises. Self-dot permits zero input, and gemv permits empty or
rectangular dimensions.

This closes the local normwise dot/axpy/gemv part of the first P1 row, under the
existing input-only relative-error contract. It does not itself establish a
complete Krylov execution-to-run bridge, normalization/initial-direction
correspondence, matrix-function postprocessing, or a verified finite-word IEEE
instance. The declared output errors are consequences of the executed kernels,
not assumptions. The axpy proof retains its full two-operation error expression,
including products of errors.

The new module and its reusable pointwise Euclidean norm comparison in
`ForMathlib/Analysis/InnerProductSpace/PiL2.lean` passed a serialized targeted
`lake --wfail build` (2467 jobs), with no admitted proof. See
[the design record](Matrix-Rounded-BLAS.md) for the precise interfaces and proof
reuse. No program tree, target, pin or approval was added by this amendment.

`NLAlib/Computation/BLAS/Normalization.lean` also has checked actual-kernel
guarantees: `IsRelErrSem.exec_nrm2_abs_norm_sub_le` executes the stored self-dot
followed by the actual rounded square root, returning a nonnegative decoded norm
and relative bound `roundingFactor (n+1) u`. The separate
`exec_nrm2_eq_zero` and `exec_nrm2_pos` cover zero inputs, including zero length,
and positive-norm inputs respectively. `exec_nrm2_rscl` then executes the actual
componentwise divisions for a nonzero input, retaining both intermediate states,
the norm-cell write and the vector-block write. It gives the rescaling residual
bound, the full squared normalization defect `normalizationRoundingFactor n u`,
and the initial-direction mismatch bound described next. These require the
existing decoded-input/storage/disjointness hypotheses, `(n+1)u<1` and
`roundingFactor (n+1) u<1`; no division-by-zero success is assumed.

Rounded componentwise division generally changes direction, so the old exact
identity between the original input and a scaled normalized initial column is
not an execution invariant. The checked
`RelErr.norm_sub_smul_inv_norm_le` bounds this mismatch by
`(2*u+g)*‖WithLp.toLp 2 x‖` when the nonnegative stored scale approximates the
input norm with relative error `g` and componentwise rescaling has relative
error `u`. Actual `exec_nrm2_rscl` supplies `g = roundingFactor (n+1) u` and this
mismatch certificate. The checked
`LanczosRun.norm_cfc_mulVec_sub_le_of_norm_sub_smul_le` in
`Krylov/FinitePrecision/LanczosFunctions.lean` transfers a run guarantee to an
input with mismatch `τ`, computed scale `s`, and returned-vector error `ζ`, giving
the explicit sum `M*τ+s*E+ζ` for a function bounded by `M` on the spectral
interval. Its input and postprocessing errors remain explicit premises to be
discharged by a complete program bridge and concrete postprocessor.

Root reported warning-free targeted builds for the normalization/mismatch
certificate and function-output transfer. Together these close local norm and
initialization arithmetic obligations. They do not yet prove that the complete
proposed Lanczos tree constructs a `LanczosRun` with those particular initial
columns or returns a certified matrix-function vector.

## Proposal review, 2026-11-04

The `proposals/krylov/` drafts named here were removed once the library held their
counterparts; `git log -- proposals` finds them.

`proposals/krylov/ConjugateGradient.lean` fixes a guarded, square-root-free,
stored-matrix CG tree and defines `StoredEntriesConjugateGradient`.
`proposals/krylov/Lanczos.lean` fixes Paige-order stored-matrix Lanczos and defines
`StoredEntriesLanczos`. Both use the existing `StoredEntries` access model with
a `True` size predicate, so the proposed targets quantify all sizes, real ROM
entries and real input vectors after binding the compiled tree. Their output
claims are postconditions, not assumed local-error records. CG's output
correspondence is conditional on the ROM matrix being positive definite; its
non-SPD postcondition constrains status alone. Lanczos's target gives the total
recurrence for arbitrary real matrices and zero continuation, without asserting
orthogonality for nonsymmetric inputs. Their proposed counts are componentwise
upper bounds, not exact executed counts or machine cycle counts.

At this review the CG definitions, symbolic tree and elementary scalar budget
comparisons have been checked; the Lanczos proposal is awaiting its targeted
build. Neither complete solver realization nor execution-to-run theorem has
been proved. No target is approved or registered. The separate initialization
and inline-direction proposal lemmas are partial proof infrastructure, not
realization of the entire tree.

The supporting `IsRelErrSem.exec_cg_direction_update` in
`proposals/krylov/CGDirectionUpdate.lean` now additionally has a checked exact
state/count guarantee: the final state differs from the initial state only in
its store and in the count increment
`n • (charge multiplication + charge addition)`. The proof uses the actual
multiply-then-add loop, retaining its scalar relative-error traces, shape and
outside-cell frame. It handles zero length and requires only `AddMonoid` for
the charge carrier. The importable proposal `.olean` was produced with Lean
warnings treated as errors. This is a local loop execution theorem, not a
whole-solver target proof or registration.

Review follow-ups for the proposal owners:

- Both descriptions promise an unchanged input buffer. The Lanczos target has
  now added the input-buffer `Holds` fact after review, awaiting the current
  proposal check; the CG target should include the same preservation promise.
- The CG design lists a `cgStepProg` declaration while the current program
  inlines that body. Align the design with the actual declaration inventory.
- The rounded CG sketch should expose actual stopping index/status and every
  promised output also in the zero-step branch. Its displayed zero-step branch
  currently certifies only the zero iterate.
- Keep the whole-run bridges, guard-success proofs, normalization-to-initial-column
  identification, final postprocessing, target approval and machine refinement
  as separate outstanding obligations. Successful checking of a proposed target
  definition does not prove its proposition.

The registered baseline targets were rechecked for accidental empty domains and
overstated output scope. `MatrixFreeGramSchmidt` uses a `True` size predicate and
returns the total `gramSchmidtQ` with dependent columns zero; it does not return
a full pair of QR factors. The Hutch++ exact targets require a positive residual
sample count. The COO version additionally requires the finite public pattern
to lie inside the chosen dimension. These conditions admit ordinary inputs and
do not hide full-column-rank assumptions. `MatrixFreeProbHutchpp` additionally
requires positive sketch sizes and its displayed embedding threshold; choosing
large enough sketches gives a nonempty domain. Its failure bound may exceed
one for some permitted parameters, including zero error threshold. Such choices
give no useful confidence and must not be advertised as a nontrivial success
probability. The target's ideal Gaussian tape is a probability-law assumption,
not a certified machine random-number generator. These qualifications follow
from `Matrix/Factorizations/GramSchmidtTargets.lean`,
`Estimation/Trace/HutchPlusPlusTargets.lean` and the exact access models in
`Computation/Model.lean`.

## Approval amendment, 2026-11-04

After the initial proposal review above, the user explicitly approved both exact
program/target statements: `StoredEntriesConjugateGradient` and
`StoredEntriesLanczos`. Approval is therefore complete for those unchanged
statements and their associated programs; no repeat approval is needed. Root
integration will register them once their complete realization proofs are
checked. Approval alone does not establish either proposition, rounded
execution-to-run correspondence, or a machine arithmetic certificate. Earlier
references to pending approval in this audit describe the preceding review
state and are superseded by this amendment.

## Executed smoke checks, 2026-11-04

`proposals/krylov/Smoke.lean` runs the actual compiled CG and Lanczos proposal
trees with the existing `NLAlibTools.floatSem` and stored column-major ROM.
Fourteen guards passed: eight CG cases cover zero input, zero requested steps,
diagonal and off-diagonal SPD early termination, a nonterminal active step,
negative and zero curvature rejection, and zero dimension. Six Lanczos cases
cover zero input, zero requested steps, terminal beta and subsequent zero
continuation, a nonzero beta followed by termination, a nonsymmetric matrix
that detects transposed ROM addressing, and zero dimension.

Every guard rejects failed execution and missing or uninitialized output cells.
It checks all declared buffers and input preservation, all 23 operation kinds
including zero-count bounds, peak memory plus ROM, released workspace and no
tape consumption. The harness's executable count formulas are proved equal to
the actual `cgCount` and `lanczosCount` formulas; its operation-kind list has a
coverage lemma. Fresh CG initialization, CG and Lanczos proposal `.olean` files
were produced before the run. The final Smoke check exited successfully with
an empty warning/error log.

These tests cover selected concrete executions. They do not prove either
whole-program target, an execution-to-`CGRun`/`LanczosRun` theorem, a Float
relative-error contract, or an IEEE machine certificate. The count and memory
checks use the DSL's charged operations and scalar-cell footprint, not host
machine cycles or object sizes.

## Foundation checkpoint before whole-program integration, 2026-11-04

The maintainer subsequently approved both exact target statements and their identified
programs: “Approve both exact target statements.” `StoredEntriesConjugateGradient` and
`StoredEntriesLanczos` are therefore approved statements awaiting their full realization
proofs and registration. The counts remain proposed guarantees until proved. Earlier
approval-pending language above records the baseline and initial review, not a remaining
permission requirement for these two exact targets. Their code and statements are fixed;
rounded targets and finite-word refinement have not been approved by this exchange.

The foundation passed the full stage check with 536 proved modules, zero build warnings,
16,318 declarations audited without axiom violations, and 16,548 constants replayed through
the kernel. Program/target, metadata, source, citation, bound-value and LaTeX checks pass.
Separately, fourteen actual compiled-program Float examples pass, checking all declared
outputs, stopping branches, all 23 operation-count kinds, peak memory including ROM,
workspace release and tape nonuse. The executable count formulas are proved equal to the
proposed target formulas. These examples do not establish either whole-program proposition
or a scalar Float rounding certificate.
