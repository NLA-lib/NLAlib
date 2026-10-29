# Port status

Updated at every stopping point. Newest entry first within each section.

## Finite-precision Lanczos: integration (2026-10-28)

Branch `design/lanczos-fp` (local). Design `docs/design/Krylov-LanczosRounding.md` (status:
implemented for the analysis; §3.7 records the integration). The re-proof of the stability
analysis of *A simple stability analysis of Lanczos in finite precision* (T. Chen, draft) is in
the library, `NLAlib/Krylov/FinitePrecision/`: the interface `LanczosRun`, the generic
three-term recurrence `LanczosData`, local errors, the perturbed recurrence and Ritz residual,
Paige's Gram commutator and loss-of-orthogonality bound, the normalised run, the Greenbaum-type
backward model ($\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}} \le
2000k^4\varepsilon\|\mathbf{H}\|_2$; exact Lanczos on it computes $\mathbf{T}_k$), and its
spectral consequences (localization, containment, $W_1$ closeness of the spectral measures).
Constants are named bounds (`lanczos…Factor`, six entries in `docs/constants.toml`). General
facts moved to their topics: the orthonormal dilation (`Matrix/Subspaces/OrthonormalDilation`),
Kittaneh's Frobenius Lipschitz bound (`Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le`,
`Matrix/Functions/HermitianCalculus`), `Matrix.IsUpperTriangular.frobNorm_sub_diagonal_le` and
`frobNorm_le_card_mul_of_forall_abs_le` (`Matrix/Norms/Frobenius`), "an orthonormal three-term
recurrence is Lanczos" (`Krylov/Processes/LanczosRecurrence`), `HasOrthonormalCols.norm_toLp_col`;
the projector bound is the library's `IsStarProjection.specNorm_le_one`. The Lanczos program, its
exact specification, the rounding bridge and the new end-to-end headline
`IsRelErrSem.exists_lanczosBackwardModel_of_lanczosBasisDenseProg` (the dense program in the
standard model has the backward model with $\varepsilon = \max(\sqrt{N}\gamma_N, \gamma_{N+4})$)
stay in `NLAlibScaffold/Krylov/Processes/` (proved, no `sorry`): `lanczosBasisProg` and
`lanczosBasisDenseProg` are `<spec>Prog`s and need registered targets (E3/E4, maintainer). Tier-1
review: `nlalib-harness/reports/Lanczos-FP-Tier1.md`. Headline axioms: `propext`,
`Classical.choice`, `Quot.sound`.

## Rounding-error analysis of the BLAS kernels: integration (2026-10-28)

Branch `design/fp-toolkit`, based on `main` at `c4ff3d9`. Design
`docs/design/Computation-Rounding.md` (now implemented; §9 records the integration). The
standard-model layer is in the library: $\gamma_n$ (`Computation.roundingFactor`) and its
algebra (Lemmas 3.1, 3.3 of Higham), the arithmetic part of a contract (`IsArithErrSem`,
`AddsZeroExactly`), a witness with $u = 2^{-t} > 0$ (`gridSem`, rounding to nearest on a binary
grid, ForMathlib `Real.roundNearest`), straight-line usage independence, the kernel
`trsvLower` with its exact specification, the trace bounds for inner products and forward
substitution, run lemmas for `dot`, `axpy`, `gemv`, `gemm`, `trsvLower` under any error relation,
and the standard-model headlines (each asserts success): backward and forward error of `dot` and
`gemv`, `axpy`, forward error of `gemm`, backward error of `trsvLower` (Theorem 8.5). Statements
unchanged from the reviewed skeleton; the scaffold is empty again. Layer 2 (bounded exponent
range, R6) is designed, not started; R4 (fold `AddsZeroExactly` into `IsRelErrSem`) is pending.
Headline axioms: `propext`, `Classical.choice`, `Quot.sound`. Equation numbers (3.4)–(3.13) are
still to be checked against the book.

## Computation fixed-point demo: proof repair (2026-10-27)

Branch `fix/computation-fixedpoint`, based on PR #31 (`computation/stage1`, `d0ee823`). The
maintainer requested fixing and proving the two fixed-point demo statements, then committing and
updating the PR. Both statements in `NLAlibTools/FixedPoint.lean` are now proved with their
original signatures; the tools' two deferred proofs recorded in the older entries below are
closed. No new prototype ports; no ledger mappings or protected target statements change.

The audit found that `fxImpl` kept fixed-point subtraction and negation unchanged even though
`wordSem` rejects those instructions. Subtraction now uses three scratch integer cells and
negation two, with the corresponding conversions and integer operations recorded in `fxCost`.
The weighted demo count also charges integer negation. The four-cell/256-bit scratch bound is
unchanged. The original dot-product example and its counts are unchanged; a second example checks
subtraction, negation, negative sub-ulp product rounding toward negative infinity, and in-place
negation, including its counts and scratch peak.

Read-back: for every pair of interpretations satisfying the original semantics, common-tape,
standard concrete-charge and 64-bit-width hypotheses, every successful abstract instruction has
a successful implemented run with exactly the same whole store and tape positions. It restores
current memory, costs at most `fxCost` of the instruction kind, and raises the peak only within
the certificate's maximum of the old peak and current memory plus four integer cells/256 bits.
For every integer fixed-point product, decoding the rounded word gives absolute rational error
at most `1/65536`, including negative products. The word carrier remains unbounded integers;
these results do not add a finite-width overflow guarantee.

Validation: full warning-fatal build of all three libraries; the single-file check with an
8000 MB cap; both theorem signatures mechanically compared with the PR head; both proof axiom
lists contain only `propext`, `Classical.choice`, `Quot.sound`. Independent tier-1 review accepts
the implementation, counts, memory, aliasing and rounding. Freshness, generated tools root,
approved target registry, references, constants, generated rules, ledger and source rules pass;
all 65 Python regression tests pass. Kernel replay checks 13,831 constants across 481 modules,
with zero violations and zero findings in the non-strict tools library (previously two).

## Chebyshev fixed-batch lower bounds (2026-10-27)

Branch `stage/lbc-chebyshev`, based on `main` at `96d9f77`. Design
`docs/design/LowerBounds-ChebyshevBatches.md`. The fixed-batch Frobenius and nuclear arguments
are stated for a general level spectrum with an extrapolation constant; the equispaced headline
theorems keep their statements, and new Chebyshev headline theorems prove
`q > |k|/(12544*(r+1)^3*ε)` in both norms (squared Frobenius error, unsquared nuclear error), for
`ε ≤ 1/(25088*(r+1)^3*(r+2))` and `|m| = ⌊|k|/(16ε(r+1)^3)⌋`. The extrapolation constant four
comes from the existing Chebyshev dual weights (new `Polynomial/Chebyshev/ExtremaEvaluation`).
Full build clean; both new proofs use only `propext`, `Classical.choice`, `Quot.sound`.

## Fixed-batch nuclear-norm extension: proofs (2026-10-26)

Branch `stage/lbc-nuclear`, based on fixed-batch Frobenius commit `7cbaf1f`. The maintainer
authorized the proposed trace-based Schatten-one extension. Design
`docs/design/LowerBounds-Nuclear.md` and actual source passed independent mathematical/API
review. Structural proofs compile; the minimax consumer and complete checks are in progress.

Read-back: under the same positive-rank, fixed-batch, accuracy, floor and PSD dimension
hypotheses as the Frobenius extension, a measurable randomized algorithm attaining relative
nuclear error `1+ε` with probability at least one half on every PSD input must use
`q > |k|/(256*4^(r+1)*(r+1)*(r+2)*ε)` products. No claim for other Schatten exponents.

The new nuclear optimum and missed-head-mass estimate live in `FiniteSpectrum`;
`NuclearMinimax` reuses the original Gaussian capture and K7/Yao arguments. The general
projected-residual trace bound is in `Matrix/Norms/Nuclear`; the shared Haar joint-event
helper moved to `RandomMatrix/Haar/Basic`. Existing Frobenius headline signatures are unchanged.

## Fixed-batch Frobenius extension: proofs (2026-10-26)

Branch `stage/lbc-fixed-batches` (started as `design/lbc-fixed-batches`), based on completed
`stage/lbc` at `668dcd5`. The maintainer approved `docs/design/LowerBounds-FixedBatches.md` on
2026-10-26. All proposed structural and headline statements are proved and moved into `NLAlib`;
the scaffold is empty again. The three headline signatures were compared with the approved
note, ignoring whitespace only, and are unchanged. Commit and PR publication were authorized by the maintainer after implementation.

Read-back: for every natural batch budget `r`, nonempty rank index `k`, and
`0 < ε ≤ 1/(512*4^(r+1)*(r+1)*(r+2)^2)`, choose
`|m| = floor(|k|/(ε*(r+1)*(r+2)))`. Every measurable randomized algorithm that uses at most `r`
batches and attains squared relative Frobenius error `1+ε` with probability at least `1/2`
on every PSD input of dimension `|k|+(r+1)|m|` must use
`q > |k|/(256*4^(r+1)*(r+1)*(r+2)*ε)` products. This is the fixed-`r` Frobenius lower rate in
chosen dimensions, not an all-dimension or optimized-round-dependence theorem. It includes
`r=0` without additional hypotheses and preserves the existing stronger two-pass constants.

`Polynomial/Interpolation/DividedDifference` supplies scalar extrapolation. New
`LowerBounds/LowRank/FiniteSpectrum` proves tail energy, PSD, exact optimum, loss and Krylov
interpolation for arbitrary `r`; `LowerBounds/LowRank/Minimax` proves Gaussian capture, the
K7 reduction, Yao's worst-case bound and the explicit query count. K7 is reused unchanged.
The five numerical factors are registered. Four shared helpers now live in `Matrix/Basic/Gram`,
`Matrix/Basic/Projector` and `ForMathlib/MeasureTheory/Measure/Prod`; temporary aliases are removed.
Root imports are regenerated.

Validation: full `lake build --wfail NLAlib NLAlibScaffold` passes with zero warnings. All 14
environment linters pass, and the axiom audit checks 11,776 declarations with zero violations.
Extraction-backed checks run 102 rules with zero errors (advisories concern the existing file
size/doc conventions and real-only helper statements). Constants, references, ledger and both
generated import lists pass; the duplicate report finds no new duplicates. Independent final
review accepts the constants, PSD premise, floor arithmetic and degenerate cases.

## LB-C hidden-rotation lower bounds: proofs (2026-10-26)

Branch `stage/lbc`. **All 57 targets are proved**, statements unchanged against the approved
skeleton (checked textually, every target). K7, the Krylov coupling
(`QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame`), was proved last
(by Codex); with it K8, Shamir's bound (SH2–SH6) and the low-rank bounds (L4–L9) moved into
`NLAlib/LowerBounds/` by D8, and `NLAlibScaffold` is empty.

The K7 proof exposes, in each pass, the hidden query directions one at a time before the pass's
products, and couples each new direction with one Gaussian column through its normalized
component outside the span already revealed (a zero component keeps its independent seed
column). `LowerBounds/QueryModel/GaussianCoupling.lean` holds the probabilistic part: the
one-step stabilizer law, almost-sure capture, and the joint Gaussian law of the coupled block
with every measurable summary of an initial transcript prefix
(`exists_measurable_gaussianBlock_of_ordered_queries`). The pass simulation and depth count are
private in `HiddenRotation.lean`. No hypotheses were added.

Validation (after merging `origin/main` a82169e): `lake build --wfail NLAlib NLAlibScaffold`, 0
warnings; `stage_check.sh`: 448 proved modules, 0 axiom violations in 11705 declarations, 14
linters, references, constants and LaTeX clean, `check_rules` 0 errors. `#print axioms` for K7,
K8, SH2–SH6 and L4–L9: `propext`, `Classical.choice`, `Quot.sound`. Advisory: GaussianCoupling,
HiddenRotation and FewPasses are over 1000 lines (F10, below the 1500 ceiling).

## LB-C hidden-rotation lower bounds: design (2026-10-26)

Branch `design/lbc` (worktree `nlalib-design-lbc`, from `origin/main` 79f8cc2). Design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md`, awaiting approval: the pass model
`QueryAlgorithm.IsPassStructured`, the hidden-rotation oracle and its Krylov coupling
(`IsKrylovCoupling`, OP5 Lemma C / Shamir Lemma 4 for $p$ passes), Shamir's
$\Omega(\kappa\log(1/\varepsilon))$ with explicit constants, and the two-pass (and one-pass)
$\Omega(k/\varepsilon)$ for low-rank approximation from the OP5 research note. Eight definitions
written in `NLAlib` (build `--wfail`); 52 sorried statements in `NLAlibScaffold` (S 29, M 20, L 2,
H 1); targets `~/nlalib-harness/pilot/lbc-targets.json`. No proof dispatched.

Approved 2026-10-26 (APPROVE and OQ1–OQ10 all (a)) and revised after the Fable review: K7's proof
plan (augmented simulation revealing $\mathbf{U}^{\mathsf{H}}\mathbf{B}$ and the frame padding;
the wide-pass case), five new sorried tools (KB2, KB3 in `Krylov/Basic/BlockSpace`; GZ2–GZ4 in
`RandomMatrix/Haar/Uniqueness`), the stabilizer randomizer `stabRand` of `HiddenHaar.lean` and its
law lemmas made public, SH6 sharpened to $\kappa\log(1/\varepsilon) \le 4(q + 1)$. Now 57 sorried
statements (S 31, M 23, L 2, H 1).

## Documentation and validation audit fixes (2026-10-26)

Branch `codex/fix-audit-validation`, based on `79f8cc2`. The weighted Haar-block docstring now
uses the almost-sure pseudoinverse envelope from the integrability proof, replacing the false
comparison with the unweighted integrand. No Lean declaration or proof changed; the port ledger
has no new or renamed targets.

The constant-body check retains indented continuations after blank lines. The documentation
scanners handle nested comments and skip Lean string literals. Regression tests cover stale
constant values and invalid mathematics that the previous scanners missed. Metadata test fixtures
use explicit LF bytes, and `.gitattributes` keeps Lean sources and generated root modules at LF.
CI runs documentation regression tests on Windows as well as Ubuntu.

Validation on Windows: the full warning-fatal library build, both root-module checks, axiom audit
(11,197 declarations, zero violations), environment linters, extraction, references, ledger,
constants, generated rules and LaTeX checks pass. All 61 Python and 14 Node regression tests pass.
The 102-rule check, including names, reports zero errors with the existing 73 baseline violations
and 221 warnings unchanged. Independent review also checked the identifier-prime/character-literal
boundary and outdented-comment regressions. The scanners remain bounded lexical tools, not parsers
for arbitrary Lean syntax extensions or interpolated terms.

## Research: Druskin–Knizhnerman / Knizhnerman 1996 bounds for finite-precision Lanczos (2026-10-29)

Branch `research/dk-bounds` (worktree `nlalib-research-dk`), from fb84945. All 16 statements of
`docs/design/research/Krylov-LanczosFunctionsRounding.md` are proved (one agent, by hand), with
statements and constants unchanged: `NLAlibScaffold/Krylov/FinitePrecision/LanczosFunctions.lean`
(quadrature $2E_{2k-1}(f; I_c) + Lc$ on `LanczosData` and `LanczosRun`, bounded/Jackson/unnormalised
forms, the Chebyshev-recurrence stability lemma, Lanczos-FA $(2+\sqrt k)E_{k-1} +
16k^{9/2}\varepsilon\|\mathbf H\|_2M/(a'-a+2c)$, end to end for the dense program). The
sorry-free polynomial facts moved to `NLAlib/Polynomial/Chebyshev/Interval.lean` (new),
`NLAlib.norm_chebyshevCoeff_le` and the now public `NLAlib.abs_eval_U_le`. Record: §7 of the note.

## Research: truncated generalized Nyström with $O(k/\varepsilon)$ sketches (2026-10-26)

Branch `research/tgn-upper` (worktree `nlalib-research-tgn`), from `origin/main` (79f8cc2). All
22 statements of `docs/design/research/TruncatedGN-Upper.md` are proved (workflow harness: haiku
and opus; L33, L34b, P36, C45 and M1 integrated by hand), cleaned up and tier-1 reviewed, and
moved from `NLAlibScaffold` into `NLAlib` with their `Proof:` lines removed (D8; placement in the
note's §7): the new `Matrix/Perturbation/{TruncationWindow, BestRankApprox}.lean` and
`LowRank/Gaussian/TruncatedGeneralizedNystromRate.lean`, and T1–T3, G1, G2, R51 in
`LowRank/Structural/Truncation`, `RandomMatrix/Gaussian/BlockMoments`,
`Regression/SketchAndSolve`, `LowRank/Gaussian/RangeFinder`. The scaffold is empty again. No
statement changed except the scalar generalization of the 13 deterministic statements to
`RCLike` (Fable review); C45, M1, M2 gained explicit theorems. Private helpers made public (rule S5), copies deleted:
`IsBestRankApprox.rangeProjector_self_mul`, `IsStarProjection.frobNorm_sq_eq_add_mul_right`,
`IsBestRankApprox.frobNorm_sub_sq_sub_le_two_mul_frobInner`,
`IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm` (formerly private in
`LowRank/Structural/Truncation`) and R51 (formerly private in
`LowRank/Gaussian/TruncatedGeneralizedNystrom`). Reports: `reports/Stage-TGN-Upper.md` in the
harness repository.

## LB-A matvec query model: proofs (2026-10-25)

Branch `cleanup/lba` (worktree `nlalib-cleanup-lba`), over `integrate/lba` with `origin/main`
(40c9704, reorg/layers) and `cleanup/s10` (9ba7a44, the `LowerBounds/` layer) merged. All 41
LB-A statements are proved (workflow harness: haiku; opus on the six L targets and H2, three
haiku escalations to opus), cleaned up and tier-1 reviewed, and moved from `NLAlibScaffold` into
`NLAlib` with their `Proof:` lines removed (D8). Placement (decision LOWERBOUNDS-FOLDER (a); the
design note's `Probability/QueryModel/` (layer 1) is superseded):
`LowerBounds/QueryModel/{Basic, Yao, DeferredDecision, HiddenHaar}.lean` (the model and
`gramSimulation`, formerly `NLAlib/Probability/QueryModel/Basic.lean`; Yao's principle; the
Gaussian deferred decision with `resample`, formerly `NLAlib/RandomMatrix/DeferredDecision.lean`;
the adaptive stabilizer form H2) and `LowerBounds/LowRank/RangeRecovery.lean` (R4a, R4b, R4–R6).
Tools that are not lower bounds joined their topic files: the non-adaptive stabilizer form H1 in
the new `RandomMatrix/Haar/Stabilizer.lean`, G1 in `RandomMatrix/Gaussian/Invariance`, Z1 in
`RandomMatrix/Gaussian/Rank`, the freezing lemma F1–F2 in
`ForMathlib/Probability/Independence/Basic`, T1–T4 in `ForMathlib/InformationTheory/TotalVariation`.
The scaffold's `RandomMatrix/DeferredDecision` (1738 lines) was split by topic before the move.
The scaffold is empty again. No statement changed. One private helper became public (rule S5):
`HasOrthonormalCols.hasOrthonormalCols_one_add_mul_sub_one_mul_conjTranspose`
(`RandomMatrix/UnitaryInvariance`, formerly private there and copied in the H1 file). Ratchet: T9
for `history_gramSimulation` (proof term in its statement; decision T9-GRAM); allowlist: N9 for
R4b (decision NAME-R4B). Reports:
`reports/Review-LBA-Cleanup.md` and `reports/Stage-LBA.md` in the harness repository.

Maintainer decisions (`Review-LBA.json`, 2026-10-26), one commit each:
- UNUSED-HE1 (a): G1 `identDistrib_mul_mul_of_hasLaw_gaussianMatrix` drops its unused
  `hE₁ : IsStarProjection E₁` (statement change: a weakening of the hypotheses); its two linter
  suppressions are gone, and D2's step passes one argument fewer.
- T9-GRAM (a): new definition `QueryAlgorithm.gramDecode`, used by `gramSimulation`; R1a
  `history_gramSimulation` is restated through it (statement change, definitionally equal; the
  proof term in its `Fin` literal is gone) and, by N2, renamed `gramDecode_history_gramSimulation`.
  The T9 ratchet entry is removed.
- RANK-STEP-HOME (a): R4a is now `Matrix.rank_mul_of_snoc_eq_rank_of_snoc` in
  `ForMathlib/LinearAlgebra/Matrix/Rank` (was `NLAlib.rank_mul_of_snoc_eq_rank_of_snoc` in
  `LowerBounds/LowRank/RangeRecovery`); statement unchanged.
- PUBLIC-HELPERS (a): new public declarations
  `MeasureTheory.Measure.map_prod_eq_of_forall_map_eq` (ForMathlib Independence),
  `Measurable.finSnoc` (new ForMathlib `MeasureTheory/MeasurableSpace/Pi`),
  `NLAlib.Measurable.twoSidedMulVec`, `QueryAlgorithm.IsMeasurable.measurable_history`,
  `QueryAlgorithm.queryAt_gramSimulation_two_mul`, `…_two_mul_add_one` (QueryModel/Basic),
  `QueryAlgorithm.IsMeasurable.measurable_resample` (DeferredDecision), and the H2 corollary
  `QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant_of_indepFun`
  (randomized stabilizer, for Shamir Lemma 4); `@[fun_prop]` on `Measurable.matrix_mul`,
  `Measurable.matrix_mulVec`. Private copies deleted; no statement changed.
- CONTRIBUTING §5.3 (Fable review item 1): rows for the query algorithm, the matrix–vector oracle
  (`twoSidedMulVec`, per-side query matrices and counts, `IsOneSided`, `IsNonAdaptive`) and the
  Gram simulation / truncation / resampling; the stage's V7 warnings are gone.

## S10 lower bounds for specific estimators: proofs (2026-10-25)

Branch `cleanup/s10` (worktree `nlalib-cleanup-s10`), over `integrate/s10` with `origin/main`
(40c9704, reorg/layers) merged. All 29 S10 statements are proved (workflow harness: haiku; opus on
five L/H targets, E8 and L1 finished by Opus continuations; seven haiku escalations to opus),
cleaned up and tier-1 reviewed, and moved from `NLAlibScaffold` into `NLAlib` with their `Proof:`
lines removed (D8). New top layer `LowerBounds/` (decision LOWERBOUNDS-FOLDER (a); CONTRIBUTING §2,
`check_rules.LAYER` 5, `NLAlib/LowerBounds/RULES.md`): `LowerBounds/LowRank/{EarlyTruncation,
EarlyTruncationBlock, EarlyTruncationBlockGaussian, TruncatedGeneralizedNystrom,
RotationInvariant}.lean` (EarlyTruncation, 1731 lines, split into $k = 1$, the deterministic block
step and the Gaussian block bound) and
`LowerBounds/Regression/SketchAndSolve.lean`. The tools joined their topic files:
`Probability/Distributions/ChiSquareMoments`, `LowRank/Structural/Truncation`,
`LowRank/Gaussian/TruncatedGeneralizedNystrom`, `Matrix/Pseudoinverse/NormBounds`,
`RandomMatrix/Haar/Blocks`, and the new `ForMathlib/Probability/Moments/PaleyZygmund.lean`. W6
(Epperly–Webber Lemma 6.2) went to `LowerBounds/LowRank/RotationInvariant` rather than
`LowRank/Gaussian/RotationInvariantFactor`, and W3–W5 to `LowerBounds/Regression` rather than
`Regression/SketchAndSolve` (lower bounds live in `LowerBounds/`). The scaffold is empty again. One
statement changed: E7 (`frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational`) drops
its unused hypothesis `s ≤ 1` (a pure weakening; Fable review). New public helpers: `exists_hasOrthonormalCols_frames_range_compl` and
`obliqueProjector_mul_one_sub_rangeProjector_mul_eq` (`Matrix/Subspaces/ObliqueProjector`; they
replace the private `exists_compl_frames`/`obliqueProjector_mul_eq_frames` of
`Regression/SketchAndSolve` and three S10 copies), `measurable_obliqueProjector_mul_sub_rsvd`
(formerly private in `LowRank/Gaussian/TruncatedGeneralizedNystrom`) and
`integrable_frobNorm_pinv_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame` (Blocks). New import:
`NLAlib.Matrix.Norms.Projector` (NormBounds). Reports: `reports/Review-S10-Cleanup.md` and
`reports/Stage-S10.md` in the harness repository.

Maintainer decisions (`Review-S10.json`, 2026-10-26): LB-PLACE-ADDITIONS (a) and PZ-LOCATOR (a)
keep things as they are; SPLIT-GAUSSIAN-TGN (a): the oracle section of
`LowRank/Gaussian/TruncatedGeneralizedNystrom` (1089 lines; G1–G3 and their private helpers)
moved to the new `LowRank/Gaussian/TruncatedGeneralizedNystromOracle` (779 + 347 lines), names
unchanged; `LowerBounds/LowRank/TruncatedGeneralizedNystrom` imports the new file.

## Library layers follow the imports (2026-10-25)

Branch `reorg/layers` (worktree `nlalib-reorg`), from `origin/main`. Maintainer decision on library
organization, option (b): `Solvers/{Kaczmarz, SketchAndProject}.lean` moved to `Regression/`
(modules `NLAlib.Regression.{Kaczmarz, SketchAndProject}`; no declaration renamed), `Solvers/` and
its `RULES.md` deleted. CONTRIBUTING §2 and `check_rules.LAYER` now give Krylov 1, Probability 1.5,
Regression 3.5 and Estimation 4.5, so each folder imports only lower layers; P1 also fails a
top-level folder that has no layer, and a test keeps `LAYER` equal to the §2 table.

## KS8 quadrature remainders: proofs (2026-10-25)

Branch `cleanup/ks8` (worktree `nlalib-cleanup-ks8`), over `integrate/ks8` with `origin/main`
(47b95ab) merged. All 67 KS8 statements are proved (workflow harness: haiku; opus on five L targets and
one escalation), cleaned up and tier-1 reviewed, and moved from `NLAlibScaffold` into `NLAlib` with
their `Proof:` lines removed (D8): `Polynomial/Orthogonal/{Zeros, Gauss}.lean`, the new
`Polynomial/Orthogonal/{Radau, Lobatto, RadauJacobi}.lean` (one file `RadauLobatto` at the move,
split by decision SPLIT-RADAULOBATTO),
`Krylov/Functions/Quadrature.lean`, `Estimation/Trace/StochasticLanczosQuadrature.lean`, and the
new `Polynomial/Interpolation/Hermite.lean`, `Krylov/Functions/QuadratureBounds.lean`,
`Krylov/LinearSystems/CGQuadrature.lean`, `ForMathlib/{Algebra/Polynomial/Derivative,
Analysis/Calculus/Deriv/Polynomial, Analysis/Calculus/LocalExtr/Rolle,
MeasureTheory/Integral/MeanValue}.lean`. The scaffold is empty again. No statement changed.
API change in `NLAlib/` (design note §5): KS7's `integral_eval_eq_sum_of_degree_lt` is public;
KS7's `IsOrthogonalPolynomial.integral_eval_eq_sum` is now the case $m = \lvert s\rvert$ of
`IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add` (proof only). New imports:
`NLAlib.Polynomial.Interpolation.Hermite`, `NLAlib.ForMathlib.MeasureTheory.Integral.MeanValue`
(Gauss), `NLAlib.Polynomial.Orthogonal.{Radau, RadauJacobi}` (Krylov/Functions/Quadrature),
`NLAlib.Polynomial.Orthogonal.Lobatto` (Krylov/Functions/QuadratureBounds),
`Mathlib.Analysis.Calculus.{ContDiff.Polynomial, IteratedDeriv.Lemmas}`,
`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` (Hermite). `ae_mem_Icc_radauMeasure` and
`ae_mem_Icc_lobattoMeasure` dropped their unused `[IsFiniteMeasure μ]` (decision UNUSED-FINITE).
New public helpers (decision SHARE-HELPERS): `mem_gaussNodes`,
`exists_orthogonalPolynomial_eq_X_sub_C_mul` (Zeros), `exists_integral_sub_integral_eval_eq`
(Gauss), `ae_eq_zero_of_integral_mul_sub_eq_zero`, `integral_eval_basis_nonneg_of_exact` (Radau). Report:
`reports/Review-KS8-Cleanup.md` and `reports/Stage-KS8.md` in the harness repository.

## Poly-Best best polynomial approximation: proofs (2026-10-25)

Branch `cleanup/polybest` (worktree `nlalib-cleanup-polybest`), over `integrate/polybest` with
`origin/main` merged. All 43 Poly-Best targets are proved (workflow harness, mostly haiku),
cleaned up and tier-1 reviewed, and moved from `NLAlibScaffold` into `NLAlib` with their `Proof:`
lines removed (D8): `Polynomial/Approximation/{MinimaxError, Equioscillation, Inverse, Jackson,
AnalyticApproximation}.lean`, `Polynomial/Orthogonal/Gauss.lean`,
`Krylov/Functions/{LanczosFA, Quadrature}.lean`,
`Estimation/Trace/StochasticLanczosQuadrature.lean`, and the new
`ForMathlib/{Analysis/Normed/Module/FiniteDimension, Topology/ContinuousMap/Compact,
Topology/Order/IntermediateValue}.lean`. The scaffold is empty again. No statement changed. New
imports: `NLAlib.Polynomial.Approximation.MinimaxError` (Inverse, Jackson, AnalyticApproximation,
Gauss, LanczosFA, Quadrature, StochasticLanczosQuadrature), Mathlib's `Topology.ContinuousMap.
{Polynomial, Weierstrass}`, `Topology.MetricSpace.HausdorffDistance`, `RingTheory.Polynomial.Basic`,
`Topology.Algebra.Polynomial` and `NLAlib.ForMathlib.Analysis.Normed.Module.FiniteDimension`
(MinimaxError), Mathlib's `Analysis.SpecialFunctions.Trigonometric.Chebyshev.{Extremal,
RootsExtrema}`, `LinearAlgebra.Lagrange`, `NLAlib.Polynomial.Approximation.MinimaxError` and the two
new `ForMathlib/Topology` files (Equioscillation). Reports: `reports/Review-PolyBest-Cleanup.md`
and `reports/Stage-PolyBest.md` in the harness repository.

## SLQ and Probability-Beta: proofs (2026-10-25)

Branch `cleanup/slq-beta` (worktree `nlalib-cleanup2`), over `fix/ks7-fable` with `integrate/slq`
and `integrate/beta` merged. Every statement of the two stages is proved, cleaned up and moved
from `NLAlibScaffold` into `NLAlib` with its `Proof:` line removed (D8):
`RandomMatrix/Haar/Sphere.lean`, `Probability/Distributions/ChiSquare.lean`,
`Estimation/Spectral/SpectralDensity.lean`, `Estimation/Trace/{StochasticLanczosQuadrature,
GirardHutchinson}.lean`, `ForMathlib/Probability/Distributions/ChiSquared.lean`, and the new
`ForMathlib/{Topology/MetricSpace/Lipschitz, Probability/Distributions/Beta,
Analysis/Calculus/Deriv/MeanValue, MeasureTheory/Integral/Bochner/SumMeasure}.lean`. The scaffold
is empty again. Statement change (maintainer, D18-FIX): the asymptotic form
`exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le`
(D18) gains the hypothesis `0 < c`; without it, it is false for `m` empty and `c = 0`.
Statement change (maintainer, UNUSED-HA): `Matrix.IsHermitian.ae_mem_Icc_slqMeasure` and
`Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure` drop their unused `hA` and
become `NLAlib.ae_mem_Icc_slqMeasure` and `NLAlib.matchesMoments_probeSpectralMeasure_slqMeasure`
(T13, N18). New imports: `NLAlib.ForMathlib.Probability.Distributions.Beta`
(Sphere), `NLAlib.ForMathlib.Probability.Distributions.ChiSquared` (ChiSquare),
`Mathlib.Probability.HasLaw` (ChiSquared), `NLAlib.Estimation.Trace.GirardHutchinson`,
`NLAlib.Polynomial.Approximation.AnalyticApproximation`, `NLAlib.Krylov.Functions.Quadrature`
(StochasticLanczosQuadrature), `NLAlib.Estimation.Trace.{GirardHutchinson,
StochasticLanczosQuadrature}`, `NLAlib.ForMathlib.MeasureTheory.Integral.Bochner.SumMeasure`,
`NLAlib.RandomMatrix.Haar.Sphere` (SpectralDensity). Split (maintainer,
SPLIT-SPECTRALDENSITY): `Estimation/Spectral/SpectralDensity.lean` keeps the definitions and the
deterministic results; its sub-Gaussian tails are in `SpectralDensitySubgaussian.lean` and its
sphere-probe tails, which alone import `NLAlib.RandomMatrix.Haar.Sphere`, in
`SpectralDensitySphere.lean`. Public additions: the instance
`isFiniteMeasure_empiricalSpectralMeasure` (Matrix/Spectral/SpectralMeasure) and
`Matrix.IsHermitian.ncard_spectrum_le` (stated with `Set.ncard`; it was the private
`card_toFinset_spectrum_le`), used by both halves of the split.

## KS7 orthogonal-polynomial structure: proofs (2026-10-25)

Branch `cleanup/ks7` (worktree `nlalib-cleanup`), over `integrate/ks7`. All 67 KS7 statements are
proved (workflow harness: haiku, sonnet and GLM workers), cleaned up and tier-1 reviewed, and moved
from `NLAlibScaffold` into `NLAlib` with their `Proof:` lines removed (D8):
`Polynomial/Orthogonal/{Moments, Basic, Recurrence, Zeros, Gauss}.lean`,
`Matrix/Spectral/SpectralMeasure.lean`, `Krylov/Functions/Quadrature.lean` and the new
`Krylov/Processes/LanczosPolynomials.lean`. New imports: `Mathlib.LinearAlgebra.Lagrange`
(Moments, maintainer 2026-10-25), `Mathlib.Analysis.Polynomial.Order` (Zeros),
`NLAlib.Polynomial.Approximation.Jackson` (Gauss), `NLAlib.Krylov.Processes.LanczosPolynomials`
(Quadrature). Public addition: `exists_ae_mem_Icc_spectralMeasure`. Report:
`reports/Review-KS7-Cleanup.md` and `reports/Stage-KS7.md` in the harness repository.
## Computation stage 1: replay audit fixed (2026-10-24)

Branch `computation/stage1`, after `328eb35`. An audit of `scripts/Replay.lean`; findings and fixes
in `docs/design/Computation.md`, "Final audits, 2026-10-24", "Replay audit". Blocking: the replay
trusted every import outside its roots as base, modules this package builds included, so a lemma
added in `NLAlibScaffold` with `addDeclCore … (doCheck := false)` and reached by `NLAlib` through
`NLAlibTools` passed every check. Fixed: every base module must be read from `.lake/packages/` or
the toolchain's `lib/lean`; the roots are every `lean_lib` of `lakefile.toml`, strict for
`NLAlib` and any library it imports; the stage check replays as CI does; rule P12 (`NLAlib`
imports no other library of the package); S9 also matches `addDeclCore` and `doCheck`.
Non-blocking, done: strict modules fail on an axiom or a use of `sorryAx`, `ofReduceBool`,
`ofReduceNat` or `trustCompiler`; freshness by `lake build --no-build --rehash` before the replay,
and CI no longer restores `.lake` from the GitHub cache (`use-github-cache: false`); the stage
check runs `mk_all --lib NLAlib --check`; the `_unsafe_rec` docstrings. The auditor's fixtures are
`scripts/replay_fixtures/` with `scripts/replay_fixtures.sh` (CI and stage check): FxA, FxBase,
FxB, FxC, FxD, FxE and FxF each fail for their own reason; FxF passes when not strict.

Checks (logs in the session scratchpad, `comp-build/replay-fix/`): `lake build --wfail NLAlib` 4018
jobs, 0 warnings; replay of the package 11871 constants of 425 modules, 0 violations (15
auxiliaries `_unsafe_rec`); replay rooted at `NLAlibTools` alone fails on 215 `NLAlib` modules read
from `.lake/build`; full `scripts/stage_check.sh` (the approval read from a scratch hash file): 419
proved modules, 4016 jobs 0 warnings, audit 11760 declarations 0 violations, lint 0 errors, `mk_all
--lib NLAlib --check` clean, freshness 4031 jobs up to date, replay 0 violations, replay fixtures 8
verdicts as expected, `Programs.lean` 18 programs 0 violations, `Targets.lean` 5 targets 0
violations, access-model fixtures 9 theorems, constants and LaTeX 0 problems, rules 0 errors (73 in
the baseline), duplicates 0 classes (the rules step first failed on V6, a backquoted `lean_lib` in
the new CONTRIBUTING text, reworded; it and the duplicates step were rerun on the same extraction);
script tests 50 OK.

## Computation stage 1: final audits fixed (2026-10-24)

Branch `computation/stage1`, after `0bd2567`. Two independent final audits; findings and fixes in
`docs/design/Computation.md`, "Final audits, 2026-10-24". Blocking (the whole library): an
`unsafe` definition used by a theorem under `set_option debug.skipKernelTC true` forged any
theorem past every check. Fixed by the kernel replay `scripts/Replay.lean` (Lean core's
`Environment.replay` over every `NLAlib` constant from the `.olean` files; in CI with
`NLAlibTools` and in `scripts/stage_check.sh`), rule S9 (no `unsafe`, `partial`, `implemented_by`,
`extern`, `debug.` or kernel options), and `scripts/Audit.lean` failing on unsafe or partial
constants. Replay of the whole library: 11760 constants of 420 modules, 0 violations (13
compiler auxiliaries `_unsafe_rec` exempt); the forgery, built outside the library, is rejected.
Non-blocking: the target lint follows constructors and reads instances and `Prop` definitions
(item 2), pins the SHA-256 of `lake-manifest.json` and `lakefile.toml`, has the kernel check each
registered tree against its normal form, erases proofs and numbers hygienic names in its hashes,
and prints each tree's normal form into the registry; CODEOWNERS covers the check scripts, CI,
the stage check and the build pins; `IExp.mod` by zero documented; G34, the trusted base, G61 and
G62 in the note. `docs/targets.toml` regenerated by `TARGETS_UPDATE=1` only (every hash changed,
no printed statement). **Approved by the maintainer, 2026-10-27** ("yes these are fine"): the
docstring rewording of `MatrixFreeHutchpp` and `MatrixFreeGramSchmidt` (the bound includes the
output cell), the `OpKind.…` spelling of `hutchppCount` (no hash changed) and the registry
(`docs/targets.approved`).

**Pending maintainer items** (added by the final audits):
* Confirm the CODEOWNERS handle `@tchen01`; turn on branch protection with code-owner review.
* Adding `lean4checker` is not needed (Lean core's `replay` sufficed).

Checks (logs in the session scratchpad, `comp-build/final-fix/`): `lake build --wfail NLAlib`
4018 jobs, 0 warnings; `mk_all --check` clean (NLAlib, NLAlibTools); replay of NLAlib with
NLAlibTools 11871 constants of 424 modules, 0 violations; full `scripts/stage_check.sh` (the
approval read from a scratch hash file): 419 proved modules, 4016 jobs 0 warnings, audit 11760
declarations 0 violations, lint 0 errors, replay 0 violations, `Programs.lean` 18 programs and 3
trees 0 violations, `Targets.lean` 5 targets 0 violations (the kernel accepts the 3 trees),
fixtures 9 theorems, constants and LaTeX 0 problems, rules 0 errors (73 in the baseline),
duplicates 0 classes; without the scratch approval `Targets.lean` fails on the approval item
alone; script tests 49 OK; `lake build NLAlibTools` clean.

## Computation stage 1: first-order programs, migration closed (2026-10-24)

Branch `computation/stage1`, steps A, B and C done (`381f02d`, `f571a5f`, `e9f4fa5`, `8e3ce63`,
`570be03`); this entry closes the migration. `HutchPlusPlusProgram.lean:1237` is rewrapped (a
value marker began a docstring line; no change of mathematics), and the design note's "Changes
during the migration" lists every departure of A to C. Checks: `lake build --wfail NLAlib` 4018
jobs, 0 warnings; `mk_all --check` clean; full `scripts/stage_check.sh` (the approval read from a
scratch copy of `docs/targets.toml`'s hash): 419 proved modules, 4016 jobs 0 warnings, audit 11760
declarations 0 violations, lint 0 errors, `Programs.lean` 18 programs and 3 registered trees 0
violations, `Targets.lean` 5 targets 0 violations, fixtures 9 theorems, constants 0 problems,
LaTeX 0 problems, rules 0 errors (73 in the baseline), duplicates 0 classes; without the scratch
approval `Targets.lean` fails on the approval item alone; script tests 48 OK; `lake build
NLAlibTools` clean. Open for the maintainer: create `docs/targets.approved`
(`sha256sum docs/targets.toml > docs/targets.approved`); confirm the CODEOWNERS handle
(`@tchen01` is a guess); turn on branch protection with code-owner review on `main`; approve or
decline respelling `hutchppCount` (no hash change); the Lanczos targets; the uniform sparse
stage; the stage 2 note.

## Computation stage 1: first-order programs, migration step C (2026-10-24)

Branch `computation/stage1`, after step B (`f571a5f`). Step C of the migration
(`docs/design/Computation.md`, F11; departures in "Changes during the migration"): the target lint
`scripts/Targets.lean` (rule E3: one proof per registered target, `Result:` theorems about runs
prove registered targets, SHA-256 closure hashes with the registered trees as leaves, printed
statements, toolchain and Mathlib pins, Q5, the Q3 approval; fixtures on copies of a target), the
registry `docs/targets.toml` (five targets, three trees, filled by `TARGETS_UPDATE=1`),
`.github/CODEOWNERS`; `scripts/Programs.lean` with E1 and the old E3 retired, E4 against the
registry, E9 a warning, `forgeNat` a compiler fixture; `scripts/AccessModelFixtures.lean` on
trees; the NumPy emitter of first-order trees with a differential test against the `Float` run of
the registered tree; rules E3, E4, E8 (theorems exempt), E9 rewritten, E1 retired; CONTRIBUTING
§5.3, §5.5, §9, §11; CI and `scripts/stage_check.sh` run the target lint; the rename map
`docs/renames/2026-10-computation.json`. Open for the maintainer: **the registry approval**
(`sha256sum docs/targets.toml > docs/targets.approved` in his commit; until then
`scripts/Targets.lean` fails on that item alone), the CODEOWNERS handle `@tchen01`, and branch
protection with code-owner review on `main`. Checks (`scripts/stage_check.sh`, the registry
approved by a scratch copy of the approval file): 419 proved modules, build 4016 jobs 0 warnings,
audit 11760 declarations 0 violations, lint 0 errors, `Programs.lean` 18 programs, kernels and
trees, 0 violations, 0 E9 warnings, `Targets.lean` 5 targets and 3 trees 0 violations (about 20
seconds), fixtures 9 theorems; `check_constants.py` fails on step B's
`HutchPlusPlusProgram.lean:1237` (a value marker begins a docstring line), so the rest was run by
hand: LaTeX 0 problems, rules (with the extraction, N1–N18 included) 0 errors, 73 in the
baseline, duplicates 0 classes; script tests 48 OK; `lake build NLAlibTools` clean.

## Computation stage 1: first-order programs, migration step A (2026-10-23)

Branch `computation/stage1`. Step A of the migration (`docs/design/Computation.md`, F11): the
first-order syntax `FStmt`, `Prog` and the structural maps (`Syntax.lean`), the compiler and
`toStmt` (new `Compile.lean`), the run `FStmt.exec`, `Prog.exec`, the bridge
`FStmt.exec_eq_exec_toStmt`, `Prog.RunsWithin` and the run invariants for programs (new
`FirstOrder.lean`), the models `MatrixFree`, `StoredEntries` (`Model.lean`) and `MatrixFreeProb`
(`RandomMatrix/Tape.lean`) on `Prog`, the old ones renamed into namespace `ProgFamily` with
transfer lemmas `ProgFamily.*.prog`, `ProgFamily.compile`, the composition theorems renamed into
`ProgFamily.MatrixFree`, and Q4 (`exactSem` fails on `lt`, `le` of non-real values). Departures
and the files of steps B and C touched: the note's "Changes during the migration". Checks:
`lake build --wfail NLAlib` 4014 jobs, 0 warnings; `scripts/stage_check.sh` 415 proved modules,
audit 11638 declarations 0 violations, lint 0 errors, `scripts/Programs.lean` 0 violations (10
results in an access model), fixtures 9 theorems, rules 0 errors, 73 in the baseline;
script tests 48 OK; `lake build NLAlibTools` clean; `mk_all --check` clean. Next: steps B and C,
in parallel (briefs from the orchestrator).

## Computation stage 1: guarantees (2026-10-23)

Branch `computation/stage1` (worktree `nlalib-block`), from `056f9ed`. The maintainer's change
("this stuff needs to be watertight … Are we relying on checks or are we provably guaranteed about
the costs. Make this change"): results about programs are instances of access models, so that the
program cannot depend on the data and the counts and memory are functions of the sizes by
definition, checked by the kernel. New `Computation/Model.lean` (`ProgFamily`, `MatrixFree`,
`StoredEntries`, `storedInterp`); `MatrixFreeProb`, `tapeLaw`, `Dist.law` in
`RandomMatrix/Tape.lean`; the invariants of the run in `Exec.lean` (counts grow, every allocation
freed, peaks grow, no uncharged write or draw, a run with no oracle call is the same for every
oracle); the composition at the level of the models in `Dense.lean`, `Sparse.lean`. Results:
`matrixFree_gramSchmidtProg`, `matrixFree_hutchppProg`, `matrixFreeProb_hutchppProg`,
`storedEntries_substOracle_hutchppProg_denseImpl`, `storedEntries_substOracle_hutchppProg_cooImpl`;
the old realisations are private. E3 is now the lint "results about runs are instances", E4 asks
for a result in a model, E1, E2, E9 are hygiene; `scripts/AccessModelFixtures.lean` proves the
cheating realisations false as instances. Classification of every claimed property, and what is
trusted: `docs/design/Computation.md`, "Guarantees" (55 properties: 37 proved, 8 trusted, 10
modelling choices); the changes: its last section. Checks: `lake build --wfail NLAlib` 4012 jobs,
0 warnings; `scripts/stage_check.sh`: 413 proved modules, 0 not yet, audit 11418 declarations 0
violations, lint 0 errors, `scripts/Programs.lean` 14 programs and kernels (6 called by others), 7
results in an access model, 0 violations, every fixture rejected or flagged;
`scripts/AccessModelFixtures.lean` 9 theorems; references, constants, LaTeX 0 problems; rules 0
errors, 73 in the baseline, 876 warnings (unchanged); duplicates 0 classes; script tests 48 OK;
`lake build NLAlibTools` (2 `sorry` in `FixedPoint.lean`, expected); `mk_all --check` clean.

Open items for the maintainer:
* An adjoint oracle (a second matrix derived from $\mathbf{A}$) needs a model of its own (G32).
* The analogue of the oracle-independence theorem for the tape and the read-only data is cheap
  and not yet stated (G30).

## Computation stage 1: proofs (2026-10-23)

Branch `computation/stage1` (worktree `nlalib-block`), base `88016e3` rebased onto `c31f6c0`
(note `0f8d8a9`, skeleton `9c57c62`, review follow-ups `1dd6409`). Every statement of the
skeleton is proved; `NLAlib` has no `sorry` (the tools' `FixedPoint.lean` keeps its 2). Proved:
the two tape laws (`RandomMatrix/Tape.lean`), the nine kernel specifications (`BLAS.lean`, the
level-2 and level-3 ones now in `BLAS/MatrixKernels.lean`), the dense and COO certificates
(`Dense.lean`, `Sparse.lean`), `exec_orthAgainst`, `exec_gramSchmidtProg` and
`runsWithin_gramSchmidtProg` (`Matrix/Factorizations/GramSchmidtProgram.lean`), and
`runsWithin_hutchppProg`, with the Gaussian tail and the dense and sparse totals over it
(`Estimation/Trace/HutchPlusPlusProgram.lean`). Public additions, all dated in the note's
"Changes during the proofs": the store and run lemmas of proof agent A in `Exec.lean`; at the
close, the new `Computation/Store.lean` (the store moved out of `Exec.lean`, 15 new store lemmas
and the frame invariant `Store.BlockFrame` with 7 lemmas, replacing the private copies
in `Dense.lean`, `Sparse.lean` and `BLAS.lean`), `exec_seq_of_exec_eq_some` and
`exec_forRange_draw` (`Exec.lean`), `exec_apply_exactInterp` (`Exact.lean`),
`exec_forRange_dot_add` and `run_gemv`, `run_ger`, `run_gemm` (`BLAS.lean`) and
`exec_forRange_orthAgainst` (`GramSchmidtProgram.lean`), the last four groups the generic run
lemmas of the Hutch++ proof. The close deletes every private copy (net about 450 Lean lines
fewer): `BLAS.lean` 743 lines (1492), `BLAS/MatrixKernels.lean` 653, `HutchPlusPlusProgram.lean`
976 (1270), `Store.lean` 775, `Exec.lean` 455. `IExp.eval_ofNat` drops an unused
`[n.AtLeastTwo]` (linter); `Store.getElem?_shape` is allowlisted for N2 (the checker misreads
`s.shape[b]?`).

Checks: `mk_all --check` clean for `NLAlib` and `NLAlibScaffold`; `lake build NLAlibTools` (2
`sorry` in `FixedPoint.lean`, expected); `scripts/stage_check.sh`: 412 proved modules, 0 not yet;
build 4009 jobs, `--wfail`, 0 warnings; audit 11342 declarations, 0 violations; lint 6845
declarations, 0 errors; `scripts/Programs.lean`: 14 programs and kernels (6 called by others), 5
realisations, 0 violations, every fixture rejected; references 88 keys, 86 asymptotic forms, 0
problems; constants 34, 429 value markers, 0 problems; LaTeX 27467 math spans, 0 problems; rules 0
errors, 73 in the baseline, 876 warnings (876 at `1dd6409`, when 6 modules were not yet checked;
S5 0, the round's F10 warnings gone; new: V7 for `Store.BlockFrame`, awaiting the maintainer; the
T11 false positive and the N2 allowlist entry are gone with two checker fixes); duplicates 6044 theorems, 0 classes; script tests 48, OK; ledger
0 targets missing.

Open items for the maintainer:
* Rule E9 (scope discipline): the maintainer is deciding whether it stays an error or becomes a
  warning; unchanged here. `hutchppProg`, which no program calls, is reported and not counted.
* `Store.BlockFrame` has no §5.3 row (V7): store API, not statement vocabulary; a row if wanted.
* Lanczos is stage 1b (`Krylov/Processes/LanczosProgram.lean`, `lanczosState_reindex`).
* Stateful oracles and integer index memory are deferred to a later stage.

## Computation stage 1: skeleton (2026-10-23)

Branch `computation/stage1` (worktree `nlalib-block`), from `d5c207b` (the approved note
`docs/design/Computation.md`; its last section lists the changes during the skeleton). New layer
`NLAlib/Computation/` (layer 0): `Syntax`, `Exec` (with the store and run lemmas), `RunsWithin`,
`Subst`, `Exact`, `Contract`, all proved (the substitution theorem, the tail transfer and the
contract results included); `BLAS` (9 kernel specifications, `sorry`), `Dense`, `Sparse` (1
certificate each). Topic files: `Matrix/Factorizations/GramSchmidtProgram.lean` (3), `RandomMatrix/Tape.lean`
(2), `Estimation/Trace/HutchPlusPlusProgram.lean` (1, the realisation; the Gaussian tail and the
dense and sparse totals are proof terms over it). Proved additions to existing files:
`hutchpp_reindex`, `ProbabilityTheory.HasLaw.comp_of_injective`,
`Nat.add_mul_eq_add_mul_iff_of_lt` (new `ForMathlib/Data/Nat/Init.lean`). 17 `sorry` in all.
Tools library `NLAlibTools` (new `lean_lib`, plain files): `Float.lean`, `NumPy.lean`,
`FixedPoint.lean` (2 `sorry`). Checks E1 to E4 in `scripts/Programs.lean` (CI step), E5, E6, E8 in
`scripts/check_rules.py`; CONTRIBUTING §2 row, §5.3 rows, §5.5.

Checks: `lake build NLAlib` with 17 `declaration uses sorry` warnings and no other;
`lake build NLAlibTools` (its `#guard`s reproduce the §6 Hutch++ rows and the §7.4 words; 2 more
`sorry`); `mk_all --check` clean for the three libraries; `scripts/Programs.lean`: 14 programs
and kernels, 5 realisations, 0 violations, every fixture rejected; `scripts/stage_check.sh`: 403
proved modules, 6 not yet, `--wfail` build 0 warnings, audit 10680 declarations 0 violations,
lint 0 errors, references 0 problems, constants 0 problems, rules 0 errors (876 warnings),
duplicates 0; full extraction `check_rules.py`: 0 errors; script tests 47, OK. The emitted NumPy
Hutch++ reproduces the `Float` values (19.326978, 15.0).

Rebased 2026-10-23 onto `sketching/moments` at `c31f6c0` (note `0f8d8a9`, skeleton `9c57c62`).
Skeleton review follow-ups: E3 checks the tape, E2 rejects opaque, `unsafe` and implemented-by
programs, new rule E9 (a callee closes its allocations in `scope`), each with a fixture; E6 says
"in the library"; `stage_check.sh` runs `Programs.lean`; two count docstrings spelled out; the
note's "Changes during the skeleton" states the D2, D4 and D11 changes plainly.

Proof plan: two agents on disjoint files. Agent A: `BLAS` (level 1, then `gemv`, `ger`,
`gemm`), then `GramSchmidtProgram`, then `HutchPlusPlusProgram`. Agent B: `RandomMatrix/Tape.lean`,
then `Dense` and `Sparse` (they need only `Exec` and `Exact`; a store lemma either needs goes to
`Exec`, coordinated with A). Lanczos is stage 1b.

## Sketching moments round: proofs (2026-10-22)

Branch `sketching/moments` (worktree `nlalib-block`), from `46f78ab`. Every statement of the
skeleton is proved; no `sorry` remains, and all of the round's files count as proved modules:
`Probability/MatrixConcentration/BernsteinWithoutReplacement.lean` (matrix Bernstein and the
rectangular form without replacement), `Sketching/Gaussian/ProjectionCost.lean` (the Gaussian,
sub-Gaussian and Haar PCPs with their $\log(1/\delta)$ twins and asymptotic forms),
`Sketching/Sampling/MatrixMultiplication.lean` (spectral AMM by row sampling, with and without
replacement), `Sketching/Structured/SRHTMultiplication.lean` (the SRHT JL tails, sizes, JL moment
at $p = 2$, spectral AMM and PCP, both sampling models), `Regression/{Gaussian, SubGaussian, Haar,
SRHT}.lean` (sketch-and-solve with high probability, Haar sketch-and-precondition) and
`LowRank/Oblivious/{Gaussian, SubGaussian, Haar, SRHT}.lean` (randomized SVD and early truncation
to $1 + \varepsilon$). Public additions, all dated in the note's "Changes during the proofs":
`measureReal_le_one_of_hasLaw_srht` made public, `samplingEmbeddingDim_srhtRowBound_le` and
`samplingInjectionDim_srhtRowBound_le` (`Sketching/Structured/SRHT.lean`), and at the close the two
shared $(1 + \varepsilon)$ forms `HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le`
(`LowRank/Oblivious/EarlyTruncation.lean`) and
`HasJLMoment.measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_one_add_mul_le`
(`Regression/Oblivious.lean`), which now carry the bodies the family twins repeated (net 65 Lean
lines fewer). `hasProjectionCostPreserving_of_isEmpty` was made public and moved to
`Sketching/Properties/ProjectionCost.lean`, over any `RCLike` field. `SRHTMultiplication.lean`
also imports `Probability/QuadraticForm/Moments.lean`. One statement changed: the sub-Gaussian PCP
twin loses an unused `[Nonempty k]` (linter; in the rename map's `statementChanged`). Two private
helper docstrings of `ProjectionCost.lean` got their value markers.

Final review (2026-10-22): the duplicated helpers become public lemmas (rule S5),
`HasOrthonormalCols.hasOrthonormalCols_mul_diagonal` and `srhtRowBound_div_two_le`
(`Sketching/Structured/Flattening.lean`), `row_eq_zero_of_norm_sq_le`
(`Sketching/Sampling/RowSampling.lean`), `Real.log_two_le_log_one_div` and
`Real.log_two_div_le_two_mul_log_one_div` (`ForMathlib/Analysis/SpecialFunctions/Log/Basic.lean`),
with their private copies deleted (net 30 Lean lines fewer); the C9, D13 and Haar D3 warnings the
review named are cleared. The new Matrix-vocabulary lemma in `Flattening.lean` adds one P10
warning.

Checks: `mk_all --check` clean; `scripts/stage_check.sh`: 396 proved modules, 0 not yet; build
3993 jobs, `--wfail`, 0 warnings; audit 9951 declarations, 0 violations; lint 6388 declarations, 0
errors; references 88 keys, 86 asymptotic forms, 0 problems; constants 34, 425 value markers, 0
problems; rules 0 errors, 73 in the baseline, 871 warnings (880 before the final review: C9 -2,
D3 -3, D13 -3, F10 -1, P10 +1; 849 at `46f78ab`); duplicates 5842 theorems, 0 classes; script
tests 46, OK.

Open items for the maintainer:
* `KaneNelson2014` in `docs/references.bib` has surnames, title, journal and year only; given
  names, issue, article number and DOI are to complete, and the declaration docstrings say
  "locator to check".
* The SRHT asymptotic threshold shapes (JL, PCP, sketch-and-solve, randomized SVD, early
  truncation) were chosen during the skeleton, since the note gave none (note, "Changes during the
  skeleton", "Asymptotic thresholds"); they await the maintainer's look.

## Sketching moments round: skeleton (2026-10-22)

Branch `sketching/moments` (worktree `nlalib-block`), from `46f78ab` (rebased from `1e5334f`
after the Krylov-spectral review follow-ups). Statement skeleton of
`docs/design/Sketching-Moments.md` (approved 2026-10-22, MD2–MD4 as recommended, full scope; the
note's last section lists the changes during the skeleton). Statements with `sorry` (48 in all):
`Sketching/Structured/SRHTMultiplication.lean` (new, 12), `Sketching/Gaussian/ProjectionCost.lean`
(new, 7: the twins, the Haar PCPs and the three asymptotic forms),
`Probability/MatrixConcentration/BernsteinWithoutReplacement.lean` (new, 6),
`LowRank/Oblivious/{SubGaussian, SRHT, Gaussian, Haar}.lean` (4, 4, 2, 2; `Haar` new),
`Regression/{Haar, Gaussian, SubGaussian, SRHT}.lean` (3, 2, 2, 2; `Haar` new),
`Sketching/Sampling/MatrixMultiplication.lean` (2). Proved and sorry-free: the ForMathlib Gamma
and log bounds, everything added to `Probability/Tail.lean`, `SubExponential/Tail.lean`,
`MatrixConcentration/{Bernstein, ChernoffWithoutReplacement}.lean`, `JohnsonLindenstrauss.lean`,
`Sketching/Gaussian/{Gaussian, Haar, HaarEmbedding, SubGaussian, Rademacher}.lean` (the JL moments
at every order with sizes and asymptotic forms, the Haar $1 \mp \varepsilon$ OSE/OSI) and
`Flattening.lean`. Six asymptotic forms change statement (MD4), listed in
`docs/renames/2026-10-sketching-moments.json`. Next: proofs, two agents on disjoint files (the
report of the skeleton gives the order).

## Krylov spectral round: proofs (2026-10-22)

Every statement of the skeleton is proved; no `sorry` remains in the round's files, and all of
them count as proved modules (`scripts/proved_modules.py`): `Matrix/Spectral/SpectralMeasure.lean`,
`Polynomial/Orthogonal/{Moments, Basic, Gauss}.lean`, `Polynomial/Chebyshev/EvenFilter.lean`,
`Krylov/Functions/Quadrature.lean`, `Krylov/Eigenvalues/{Ritz, PowerIteration}.lean`,
`Estimation/Spectral/RandomStart.lean`, and the new
`ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/ChebyshevGauss.lean`. No statement
changed. The public helpers the proofs added (`integrable_eval_of_ae_mem_Icc`,
`Polynomial.Chebyshev.sumZeroes_def`, `rayleighQuotient_cfc_mulVec_eq_integral_div`) and the
`Bochner.Set` imports are recorded with dates in the note's "Changes during the proofs". KS3c
(the Ritz values as Gauss nodes, positive weights) is proved from the compression alone, without
tridiagonal theory. `scripts/leansrc.py` now reads `import all X` as an import of `X` (it took
`all` for a module, a false P11 error); test added.

Checks: `lake build --wfail NLAlib` 3990 jobs, 0 warnings; `scripts/stage_check.sh`: 391 proved
modules, 0 not yet; build 3988 jobs, 0 warnings; audit 9615 declarations, 0 violations; lint 6245 declarations, 0
errors; references 87 keys, 70 asymptotic forms, 0 problems; constants 30, 336 value markers, 0
problems; rules 0 errors, 73 in the baseline; duplicates 5706 theorems, 0 classes.

Open items:
* The printed constants of Kuczyński and Woźniakowski (`KuczynskiWozniakowski1992`) are not yet
  checked. The power constant $\lambda_0\log(1 + \tan^2)/(2q + 1)$ is proved
  (`Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le`). Only the docstrings of the
  named bounds `randomStartPowerBound` and `randomStartLanczosBound`
  (`Estimation/Spectral/RandomStart.lean`) say that the printed constant is to be compared. The
  theorem docstrings in `Krylov/Eigenvalues/PowerIteration.lean`
  (`Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le`) and
  `Krylov/Eigenvalues/Ritz.lean`
  (`Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq`) never mention
  the paper's constant: they cite it with a locator from the quarry, "to check", and the
  skeleton entry below overstates them. Each of the four must be checked against the paper, and
  its docstring must state the source's value, the value proved and the gap (CONTRIBUTING §5.2,
  rule 2).
* KS7 (orthogonal-polynomial structure theory: existence and real-rootedness, three-term
  recurrence, Christoffel–Darboux, `jacobiMatrix`, interlacing of zeros) stays deferred, note §8;
  no consumer this round.

## Krylov spectral round: skeleton (2026-10-22)

Branch `krylov/spectral` (worktree `nlalib-block`), from `375e005`. Statement skeleton of
`docs/design/Krylov-Spectral.md` (approved 2026-10-22, SD1–SD7 as recommended, SD4's rule named
`interpolatoryQuadrature`; the note's last section lists the changes during the skeleton). New
files with `sorry` statements: `Matrix/Spectral/SpectralMeasure.lean`,
`Polynomial/Orthogonal/{Moments, Basic, Gauss}.lean`, `Polynomial/Chebyshev/EvenFilter.lean`,
`Krylov/Functions/Quadrature.lean`, `Krylov/Eigenvalues/{Ritz, PowerIteration}.lean`,
`Estimation/Spectral/RandomStart.lean` (50 `sorry` in all). Proved and sorry-free: the additions to
`Polynomial/Approximation/Jackson.lean` (Jackson on $[a, b]$), `Krylov/Functions/LanczosFA.lean`
(the two KS4 rates), `Matrix/Spectral/SingularValues.lean` (the frame-conjugation eigenvalue
lemma, flagged: intended home `Eigenvalues.lean`), `Probability/Distributions/Gaussian.lean`,
`Probability/Measurability/{Matrix, Krylov}.lean`. Next: proofs, one file at a time, in the
order of the note's §6 adjusted by the skeleton report.

Open item, before the round closes: the printed constants of Kuczyński and Woźniakowski
(`KuczynskiWozniakowski1992`) are not yet checked. The docstrings of `randomStartPowerBound` and
`randomStartLanczosBound` (`Estimation/Spectral/RandomStart.lean`),
`Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le`
(`Krylov/Eigenvalues/PowerIteration.lean`) and
`Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq`
(`Krylov/Eigenvalues/Ritz.lean`) cite the paper with locators from the quarry and say only that
the printed constant is to be compared. Each must be checked against the paper, and the
docstring must state the source's value, the value proved and the gap (CONTRIBUTING §5.2, rule
2).

## Consolidation round complete (2026-10-22)

Branch `cleanup/consolidation` (worktree `nlalib-block`), from `dd2eaf7`. Design note
`docs/design/Consolidation.md` (approved 2026-10-22, D1 option (a); its dated amendments record the
few unforeseen imports and statement spellings). No new mathematics: re-proved private helpers became
the 49 public lemmas of §3 in the file of their topic (Phase A, 27 commits), and every consumer
dropped its copies (Phase B, one file per commit). Private declarations 1731 → 1646. One public
declaration removed (`NLAlib.integral_comp_eq_integral_integral_of_indepFun`, in favour of
`ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral`) and one statement change
(`conjTranspose_mul_mul_le_conjTranspose_mul_mul` drops `[Finite n]`), both in the rename map
`docs/renames/2026-10-consolidation.json`; `rademacherMatrix` moved to
`RandomMatrix/Rademacher/Basic.lean` under the same name. The CONTRIBUTING §5.3 row "independent
test matrices" names the F1 conditioning lemmas as the preferred route (bridge column only, D1).

Checks: `lake build --wfail NLAlib` 3979 jobs, 0 warnings; `check_rules.py --only S5 --warnings`
0 (was 17 same-name pairs); `scripts/stage_check.sh`: 381 proved modules, build 3977 jobs, 0
warnings; audit 9363 declarations, 0 violations; lint 6106 declarations, 0 errors; references 86
keys, 68 asymptotic forms, 0 problems; constants 28, 324 value markers, 0 problems; rules 0 errors,
73 in the baseline; duplicates 5582 theorems, 0 classes (was 4). `scripts/Reuse.lean` on the 181
public theorems whose proofs changed: each consumer calls the new public lemma. Copies kept as
recorded in the note: the single-use privates of §6 and the Hanson–Wright MGF.

## Sketch-and-precondition and randomized Kaczmarz: proofs (2026-10-20)

Every statement of the skeleton is proved; no `sorry` remains in the round's files, and all of
them count as proved modules. No statement changed. Maintainer decisions of 2026-10-20 applied:
the i.i.d. law is `NLAlib.iidSequence` with `_of_hasLaw_iidSequence` names (N9), and
`IsSubspaceEmbedding.pos_right_of_injective` moved to `Sketching/Properties/SubspaceEmbedding.lean`
(P10). Helpers added: `EuclideanSpace.norm_le_norm_toLp` (ForMathlib PiL2),
`Matrix.integral_mulVec` (ForMathlib SpecificCodomains.Matrix), `Real.mul_pow_le_of_mul_log_le`
(ForMathlib Log.Basic), and the tail
`HasSubspaceEmbedding.measureReal_norm_sub_mulVec_sketchAndPrecondition_sq_gt_le_of_one_sub_one_add`
in `Regression/SketchAndPrecondition.lean`, which the four family files apply.

## Sketch-and-precondition and randomized Kaczmarz: skeleton (2026-10-20)

Branch `regression/sketch-precondition` (worktree `nlalib-block`), rebased onto `rules/stage3`.
Statement skeleton of `docs/design/Regression-SketchPrecondition.md` and
`docs/design/Regression-Kaczmarz.md` (both approved 2026-10-19; each note's last section lists the
changes during the skeleton). New files with `sorry` statements:
`Krylov/LinearSystems/Richardson.lean`, `Regression/{SketchAndPrecondition, IterativeSketching,
SubGaussian, SRHT}.lean`, `Solvers/{SketchAndProject, Kaczmarz}.lean`; the family forms added to
`Regression/{Gaussian, CountSketch}.lean` are `sorry` too. Proved and sorry-free: the additions to
`ForMathlib/Probability/Independence/{Basic, InfinitePi}.lean`, `Probability/Law.lean`,
`Matrix/Pseudoinverse/{Pinv, ConditionNumber}.lean`, `Matrix/Norms/Frobenius.lean` and
`Regression/Embedding.lean`. Next: proofs, one file at a time, Richardson first.

## Naming grammar and renames (2026-10-19)

Branch `naming/grammar` (worktree `nlalib-block`), from `origin/main` at bc72b8d. Design note
`docs/design/Naming.md` (the audit, the maintainer's decisions of 2026-10-19, the dot-notation
scope addition); grammar CONTRIBUTING §4, rules N1–N18. 311 public declarations renamed (194 by
the grammar rules, 117 more by N18 dot notation) and 37 statements changed (28 scalar tails stated
positively, 9 trace-estimation errors flipped to `tr A − estimate`), no aliases (before `v0.1`);
rename map `docs/renames/2026-10-naming.json` for the explorer's `#d/` redirects. No exception
kept; 5 checker false positives on `scripts/names_allow.toml`. `scripts/check_names.py` runs on the
extraction in CI (error mode) and in `scripts/stage_check.sh`. Private helpers keep their names.

Checks: `lake build NLAlib NLAlibScaffold` 3954 jobs, 0 warnings; `lake exe mk_all --check` clean;
`scripts/stage_check.sh`: 354 proved modules, build 3950 jobs, 0 warnings; audit 9164
declarations, 0 violations; lint 5983 declarations, 0 errors; references 77 keys, 61 asymptotic
forms, 0 problems; constants 28, 306 value markers, 0 problems; names 4105 declarations, 0
violations, 5 allowlisted; duplicates 5464 theorems, 0 classes; LaTeX 22889 spans, 0 problems;
no `sorry`. Open: `docs/design/Naming.md` §4 (`norm_toLp`, `truncatedGNFactor`, explorer
redirects and its two TOML citations; the rules-enforcement stage absorbs `check_names.py`).

## Hutch++ round complete (2026-10-18)

Branch `probability/trace-estimation` (worktree `nlalib-block`), uncommitted on top of `e2b2d91`.
Stages TE-0 to TE-5 of `docs/design/Estimation-HutchPP.md` are proved; `import NLAlib` has no
`sorry`. The last one, P1 `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral`
(`ForMathlib/Probability/Independence/Basic.lean`), is three rewrites: the joint law is the
product of the laws (`indepFun_iff_map_prod_eq_prod_map_map`), then `integral_map`,
`integral_prod`; Mathlib has only the product forms (`IndepFun.integral_fun_comp_mul_comp`,
searched). `HutchPlusPlusTail.lean` now builds in the full library (it had been checked only
against a scratch olean). Fixes from the checks: a 100-character line in the module docstring of
`Probability/QuadraticForm/Moments.lean`; value markers for `subgaussianRangeFinderFactor c` and
`hansonWrightConstant` in the `HutchPlusPlusTail.lean` module docstring. In
`Probability-TraceEstimation.md` two `\rvert` that had become carriage returns are restored. The asymptotic `C = 20000`
stays existential (CONTRIBUTING §5.2 rule 3; the docstring says "the proof takes $C = 20000$", as
the other asymptotic forms do). The note's Implementation has "What was proved", "Deviations"
(Skeleton changes 1 to 12) and "Later targets" (XTrace, NA-Hutch++, complex probes, the TE4 probe
interface). CONTRIBUTING §5.3: rows for independent test matrices (`IndepFun S G μ`),
`girardHutchinson` and `hutchpp`; `subgaussianRangeFinderFactor` gets none (a named factor with a
registry entry, like the others). Ledger: twenty prototype entries from
`Estimation.Trace.Unbiased` and `Estimation.Trace.HutchinsonTail` (stages TE-0, TE-1, TE-2); the
prototype's XTrace declarations and Gaussian/Rademacher corollaries of the Hutchinson tail remain
unported.

Checks: `lake build NLAlib` 3952 jobs, 0 warnings; `lake exe mk_all --check` clean;
`scripts/stage_check.sh`: 354 proved modules, build 3950 jobs, 0 warnings; audit 9153
declarations, 0 violations; lint 5983 declarations, 0 errors; references 77 keys, 61 asymptotic
forms, 0 problems; constants 28, 306 value markers, 0 problems; duplicates 5464 theorems, 0
classes; LaTeX 22889 spans, 0 problems; `ledger_check.py` only the documented `IsSVD.eq` false
positive. NLAlibScaffold not rebuilt.

## Trace estimation variances (2026-10-18)

Branch `probability/trace-estimation` (worktree `nlalib-block`), uncommitted on top of `b1d21fa`
(the Hutch++ design note). Design and implementation: `docs/design/Probability-TraceEstimation.md`
(decisions D1 to D8; D2, D3, D8 moot; **[maintainer]** flags on D5 suffix `_hermitianPart`, D6 name
`girardHutchinson`). Proved, no `sorry`:

- `RandomMatrix/Haar/Moments.lean`: exact variance of `tr (Qᴴ A Q)` for Haar frames (multiplied
  form for every `n`, divided for `n ≥ 2`, any real `A`), real sphere `2n/(n+2)(‖A‖² − tr²/n)`.
- `Probability/QuadraticForm/Moments.lean`: real Gaussian/Rademacher for any real `A`, Rademacher optimality.
- New `Estimation/Trace/GirardHutchinson.lean`: `girardHutchinson`, unbiasedness, `v / m` for
  independent probes (𝕜 and real `variance` forms), orthonormal Haar probes.
- `Matrix/Spectral/HermitianPart.lean`: `quadForm_hermitianPart`,
  `trace_conjTranspose_mul_hermitianPart_mul` (the Hutch++ note's A3).

Deferred, maintainer request: the complex probe laws (Gaussian, Steinhaus, sphere) were removed
(recoverable from `f1d3e75`; see "Deferred: complex probes" in the design note). Later target: the
sphere's worst-case optimality.
Ledger: `hutchinsonEstimate`, `integral_hutchinsonEstimate_eq_trace`. Not mine and not touched:
the concurrent edit of `Probability/SubGaussianVector/Basic.lean` (Hutch++ P8).

Checks: `lake build NLAlib` 3952 jobs, 0 warnings; `scripts/stage_check.sh`: 354 proved modules,
build 3950 jobs, 0 warnings; audit 9133 declarations, 0 violations; lint 5969 declarations, 0
errors; references 74 keys, 0 problems; constants 28, 0 problems; duplicates 5439 theorems, 0
classes; LaTeX 22523 spans, 0 problems; `mk_all --check` clean (NLAlib); `ledger_check.py` only
the documented `IsSVD.eq` false positive. NLAlibScaffold not rebuilt. (Counts include the
concurrent Hutch++ work in the same worktree.)

## Krylov block round complete (2026-10-18)

Branch `krylov/block` (worktree `nlalib-block`), uncommitted on top of `657cd18` (B7). Stages B0 to
B7 of `docs/design/Krylov-Block.md` are proved: block Krylov spaces, `rbki` and `nystromBKI`, TW
Lemma 9.5, TW Theorem 9.2 (gapped) and Theorem 9.1 (gapless) for RBKI and RSI, the Musco–Musco
$(1 + \varepsilon)$ gapless form with its truncated lines and asymptotic depth, the Nyström variants.
The note's Implementation now has "What was proved", "Wrap-up amendments", "Deviations" and
"Later targets" (next: BCW arXiv:2202.05120 Theorem 5.1, upper bound only); `PORT_KRYLOV.md` has the
2026-10-18 directions and progress. CONTRIBUTING §5.3: rows for `singularGapRatio` and
`HasSupportingLineOn` (BD9; `rangeFinderTailRatio` needs none).

Wrap-up placement pass (no statement changed): the private attainment helper of `TraceFunctions.lean`
is public as `IsStarProjection.exists_mulVec_eq_self_and_re_quadForm_eq_specNorm_mul_sq` in
`Matrix/Spectral/CourantFischer.lean`; the private "$\sigma_t = 0$" helper of
`Gaussian/BlockKrylov.lean` is replaced by the public `truncatedSVD_of_singularValues_eq_zero`
in `Matrix/Spectral/LowRank.lean`; `Polynomial/Chebyshev/Filter.lean` is deleted, its one fact now
`Polynomial.Chebyshev.hasSupportingLineOn_mul_eval_T_sq` in ForMathlib's Chebyshev growth file;
`Real.exp_two_mul_le_one_add_div_one_sub` moved to `ForMathlib/Analysis/SpecialFunctions/Log/Deriv.lean`;
three private copies of $0 \le t/(\ell - t - 1)$ (Duplicates) replaced by the public
`natCast_div_sub_sub_one_nonneg` in `Gaussian/RangeFinder.lean`. No placement flag open. Ledger:
eleven prototype entries (B0, B1b, B3).

Checks (`scripts/stage_check.sh`): 351 proved modules, build 3947 jobs, 0 warnings; audit 8924
declarations, 0 violations; lint 5848 declarations, 0 errors; references 73 keys, 41 asymptotic
forms, 0 problems; constants 27, 0 problems; duplicates 5332 theorems, 0 classes; LaTeX 21703 spans,
0 problems; `lake build NLAlib` 3949 jobs; `mk_all --check` clean (NLAlib). `ledger_check.py`
reports only its documented `IsSVD.eq` false positive. NLAlibScaffold not rebuilt.

## Krylov K1, K2, K2b complete (2026-10-17)

Branch `krylov/brief`, uncommitted on top of `1908a3f` (K1 checkpoint 5): `WorstCase.lean`
(Greenbaum for CG and MINRES), the new `Krylov/Functions/Optimality.lean` (Chen–Persson Theorem 2,
its fixed-shift form and CG case), `NLAlib.lean`. K1 (`Krylov-LinearSystems.md`) checkpoints 1 to
5, K2 (`Krylov-Functions.md`) C1 to C5 and K2b (`Krylov-Sharpness.md`) KB1 to KB3 are proved; K2
C6 (quadrature) is open. Docstring follow-ups of `Krylov-Sharpness.md` §10 done (no "stage K2b"
forward references remain). Placement flags closed: `exists_hasOrthonormalCols_range_eq_krylovSpace`
public in `Krylov/Basic/Grade.lean`; `Matrix.IsHermitian.preconditionedLanczosState_z_eq_zero_of_le`
and `…_beta_eq_zero_of_le` public in `Processes/PreconditionedLanczos.lean` (the private conjunction
split); the private grade identity in `MINRESRecurrence.lean` replaced by `krylovGrade_mul_mulVec`;
`mgsArnoldiHessenberg_apply_eq_zero_of_le`, `injective_mulVec_mgsArnoldiHessenberg_iff` public in
`Processes/ArnoldiRecurrence.lean`; `Matrix.mulVec_eq_submatrix_castLE_mulVec` in
`ForMathlib/Data/Matrix/Mul.lean`. No statement changed. `Greenbaum1979`, `GreenbaumGurvits1994`
checked against Crossref (DOIs added); theorem locators still to verify. Notes amended (all three
design notes, `PORT_KRYLOV.md` "Progress"). Ledger: one missing K1 entry added
(`krylovSpace_mul_mulVec_eq_map`); the K2b files port nothing.

Checks (`scripts/stage_check.sh`): 342 proved modules, build 3938 jobs, 0 warnings; audit 8696
declarations, 0 violations; lint 5706 declarations, 0 errors; references 72 keys, 0 problems;
constants 26, 0 problems; duplicates 5195 theorems, 0 classes; LaTeX 20845 spans, 0 problems;
`mk_all --check` clean (NLAlib, NLAlibScaffold). `ledger_check.py` reports only its documented
`IsSVD.eq` false positive. NLAlibScaffold not rebuilt.

## Krylov K0 (CG slice) complete (2026-10-17)

Branch `krylov/brief`, uncommitted on top of checkpoint `71fb07c`. All eight Krylov files of
`docs/design/Krylov-CG.md` §6 are proved and registered in `NLAlib.lean` (`lake exe mk_all`).
Placement pass (CONTRIBUTING §8 item 5): `conjTranspose_mul_apply` and
`conjTranspose_mul_mul_apply` now public in `Matrix/Basic/Gram.lean` (two private copies deleted);
`HasOrthonormalCols.star_col_dotProduct_eq_zero_of_mem_span` public in
`Matrix/Basic/Orthonormal.lean`; `krylovGrade_le_of_mem_of_mulVec_eq` public in
`Krylov/Basic/Grade.lean`. A private `conjTranspose_mul_mul_apply` in
`Sketching/Properties/Isotropic.lean` clashed and is renamed `conjTranspose_mul_mul_apply_eq_sum`.
Note amended ("Implementation (2026-10-17)": added lemmas, the direct Lanczos and
Hestenes–Stiefel routes, the moves, counts); no statement changed. Ledger: 9 K0 entries.

Checks (`scripts/stage_check.sh`): 322 proved modules, build 3913 jobs, 0 warnings; audit 7784
declarations, 0 violations; lint 5282 declarations, 0 errors; references 61 keys, 0 problems;
constants 26, 0 problems; duplicates 4848 theorems, 0 classes; LaTeX 18643 spans, 0 problems;
`mk_all --check` clean. Open: the note's Saad2003/Saad2011/TrefethenBau1997 locators still to be
checked against the books before the PR; NLAlibScaffold not rebuilt in this pass.

## Stronger Jackson bound complete (2026-10-16)

The public `isUniformApproxOn_jacksonApprox_of_lipschitz` now exposes the proved error
πL/(N+2) for the same polynomial, interval Lipschitz hypotheses and RCLike values. It uses
`jacksonApproximationConstant`, currently π, with positivity and ≤π API, following the HMT
Gaussian pseudoinverse precedent and CONTRIBUTING §5.2. The earlier final weakening is removed.
The design amendment and actual source/registry/instruction changes passed independent review.
CONTRIBUTING explicitly says not to discard an already-proved stronger bound merely to match a
source constant or an earlier draft. Same theorem/result names; no unused weaker companion.
Twenty-three explicit public additions in the combined Jackson work; the irreducible definition
also generates its body equation. Kernel, coefficients and hypothesis interfaces are unchanged.

Added `Rivlin1981` and `ShahUrschelWest2026` (arXiv:2607.23375v2) as requested, with module
background citations. Documentation distinguishes improvement over the cited CTU v1 bound from
optimality: the newer paper's sharper asymptotic constants/remainder are not formalized here.

Final stronger-source checks: target build and capped file check clean; full build 3909 jobs/0
warnings; audit 7501 declarations/0 violations; 14 linters on 5116+2385 declarations/0 errors;
duplicates 4709 theorems/0 classes; root import and proof-reuse checks pass. References (59 keys),
constants (26), and LaTeX (18199 spans) pass. Explorer extraction has 315 modules/3534 declarations,
all source fingerprints match, headline displays πL/(N+2), and the named factor has support role.
Logs/artifact: `/tmp/nlalib-jackson-stronger-{target,lean,build,audit,lint,duplicates,reuse,explore}.log`
and `/tmp/nlalib-jackson-stronger-explore.json`. No active build or proof gap at handoff.
The prototype ledger remains unchanged for the previously reviewed source-coverage reasons.

The report below records the prior `c769e96` source-bound commit; this section and the latest
design amendment supersede its numerical guarantee. J1, moments and OP remain later stages.

## Jackson kernel and constructive approximation complete (2026-10-16)

The user-approved stages 1 and 2 are complete and independently reviewed. Design, exact APIs,
source relation and mathematical read-back: `docs/design/Polynomial-Jackson-Moments.md`.
`Polynomial/Approximation/JacksonKernel.lean` has 2 definitions and 11 theorems;
`Polynomial/Approximation/Jackson.lean` has 1 definition and 5 theorems. One shared finite
Chebyshev-expansion coefficient theorem in the existing coefficient owner replaces both private
consumer inductions. Twenty public additions total; prior truncation API unchanged. All three
CONTRIBUTING vocabulary rows and the shared-owner placement passed independent review.

The canonical approximant has degree at most N, its full coefficients are exactly the damped input
coefficients and each contracts. For an interval-Lipschitz real- or complex-valued function the
uniform error on [-1,1] is at most π²L/(2(N+2)), including N=0/L=0 and endpoints. Kernel positivity,
normalization and first cosine moment are proved. Source is Chen–Trogdon–Ubaru arXiv:2204.01941v1
Appendix C; no new coefficient spelling, global Lipschitz or analytic assumption is introduced.

Combined checks: full build 3909 jobs/0 warnings; axiom audit 7502 reachable declarations/0
violations; 14 linters on 5112+2390 declarations/0 errors; duplicates 4707 theorems/0 classes;
root import checks, references, constants, LaTeX and proof reuse pass. Affected-target builds and
capped file checks are clean. Logs: `/tmp/nlalib-jackson-{build,audit,lint,duplicates,reuse}.log`,
`/tmp/nlalib-j0-checks/`, `/tmp/nlalib-j2-checks/`. Explorer extraction contains 315 modules,
3530 declarations and the documented `jackson-lipschitz` result, with all source hashes checked.
Artifact: `/tmp/nlalib-jackson-explore.json`; this is extraction validation, not site deployment.

The unchanged textual ledger checker reports its documented false positive for the generated
`IsSVD.eq` field; a direct Lean check confirms the field exists. No genuine prototype dispositions
apply: the prototype's sharper existential/sawtooth Jackson results remain outstanding, so the
ledger is unchanged. No new scaffolds or remaining proof gaps; no active builds at handoff.
Available-agent fallback continues. J1 coefficient decay, noisy moment comparison and finite OP
results remain later exact-design checkpoints. No Wasserstein/duality identity is claimed.

## Polynomial Poly3 (2026-10-16)

Complete and independently reviewed: `docs/design/Polynomial-Analytic.md`. All five proof steps
and eleven public declarations are approved: focal ellipse definition, ten theorems for canonical
coefficient bridges/decay, generic reconstruction, inclusive truncation error and affine existence.
Four new modules plus the coefficient-owner extension preserve the approved generic f/compatible
complex-extension interface, open-domain hypotheses, endpoints, N=0 and M=0. Four root imports,
one vocabulary row/addition note and two genuine headline successor mappings are recorded;
previous mappings unchanged, no object aliases or unproved ellipse equivalence claimed.

Final-source full two-thread build passed (3907 jobs, zero warnings), both root checks passed,
audit 7398/zero violations, 14 linters 5069 plus 2329 generated/zero errors, duplicates 4667
and zero classes. Refs (56 keys/40 forms), constants (25), KaTeX (5516 docstrings/18168 spans),
11 metadata tests and eleven reuse targets passed. Prior target/capped checks passed. The reviewed
period amendment reuses Mathlib `Polynomial.instTwoPiPos` locally, with no new public Fact witnesses;
final gates were rerun against those sources. Logs: `/tmp/nlalib-poly3-checks`.
Fresh extraction `/tmp/nlalib-poly3-explore.json`: 313 modules/3510 public declarations, all source
hashes matching and eleven additions proved. Strict unchanged Explorer build: 312 visible modules,
254 results/172 enriched definitions; Rates unchanged at 32 rows/nine guarantees/three families.
No UI/Rate edits, redundant browser/stage build, active validation process, commit or push.
Root handles commit and extraction restamp; later stages retain exact design checkpoints.

## Polynomial Poly2 (2026-10-16)

Complete and independently reviewed: `docs/design/Polynomial-Series.md`. Both files/all nine
public declarations are approved: one canonical full RCLike coefficient, four coefficient facts,
inclusive degree-N truncation, evaluation/degree and exact arbitrary-polynomial reproduction.
Two root imports, two approved vocabulary rows and one genuine real-coefficient prototype mapping
are recorded; prior ledger entries are unchanged. Analytic contour/real-part objects remain
unmapped pending true representation bridges. No numbered Mathlib deviation or proof changes.

Full two-thread build passed (3900 jobs, zero warnings), both root checks passed, audit 7300/zero
violations, 14 linters 5033 plus 2267 generated/zero errors, duplicates 4632 theorems/zero classes.
References (56 keys/40 asymptotic forms), constants (25), KaTeX (5501 docstrings/18134 spans),
11 metadata tests and nine reuse targets passed. Prior target/capped checks passed; no redundant
stage build or browser run. Logs: `/tmp/nlalib-poly2-checks`.
Fresh extraction `/tmp/nlalib-poly2-explore.json`: 309 modules/3499 public declarations, all source
hashes matching and nine additions proved. Strict unchanged Explorer build: 308 visible modules,
252 results/171 enriched definitions; Rates remains 32 rows/nine guarantees/three families.
No active validation process, commit or push; root handles commit and extraction restamp.
The subsequently approved Poly3 interface is implemented in the completed stage above.

## Polynomial Poly1 (2026-10-16)

Complete and independently reviewed: `docs/design/Polynomial-Minimax.md`. Both files/all six
new statements are approved: external modulus comparison, monic minimax and exact normalized
residual minimax, preserving Poly0 API and including q=0. One new root import and six genuine
prototype mappings were recorded; previous ledger entries are unchanged. No new vocabulary,
Mathlib deviation or proof edits during mechanical validation.

Full two-thread build passed (3895 jobs, zero warnings), both root checks passed, audit 7278/zero
violations, 14 linters 5020 plus 2258 generated/zero errors, duplicates 4621 theorems/zero classes.
References (56 keys/40 asymptotic forms), constants (25), KaTeX (5490 docstrings/18117 spans),
11 metadata tests and six reuse targets passed. Prior target/capped checks passed; no redundant
stage build. Logs: `/tmp/nlalib-poly1-checks`.
Fresh extraction `/tmp/nlalib-poly1-explore.json`: 307 modules/3490 public declarations, all source
hashes matching and all six additions proved. Strict unchanged Explorer build passed: 306 visible
modules/251 results/169 enriched definitions; Rates remains 32 rows/nine guarantees/three families.
No active validation process, commit or push; root handles the commit and extraction restamp.

Poly2 full coefficient normalization, one generic RCLike API and inclusive degree-N truncation
(0 through N) are explicitly user-approved. These choices are implemented in the completed Poly2 stage above. Available-agent fallback continues.

## Polynomial Poly0 (2026-10-16)

Complete and independently reviewed; user-approved roadmap and stage design:
`docs/PORT_POLYNOMIAL.md`, `docs/design/Polynomial-Chebyshev.md`. Five new modules provide
18 public declarations for the shared metric approximation interface, Chebyshev growth,
normalized residual, generic degree-controlled factorization and inverse approximation,
including q=0. The existing Matrix approximation theorem now consumes the named interface
in place. All six topic reviews approved; no proof edits during mechanical validation.

Five root imports, two approved CONTRIBUTING vocabulary rows and eleven genuine prototype
ledger mappings are recorded. The Mathlib comparison records additions with existing `dist`,
`Chebyshev.T` and `ContinuousMap.dist_le`, without a competing spelling or numbered deviation.
No future-stage prototype dispositions were added. Full two-thread build passed (3893 jobs,
zero warnings), both root checks passed, audit 7267 declarations/zero violations, 14 linters
5012 plus 2255 generated/zero errors, duplicate report 4613 theorems/zero classes. References
(55 keys, 40 asymptotic forms), constants (25 bounds), KaTeX (5483 docstrings/18083 spans),
11 metadata tests and all nineteen reuse targets passed. Target/capped file checks had already
passed. Logs: `/tmp/nlalib-poly0-checks`; no redundant overlapping stage build was run.

Fresh extraction `/tmp/nlalib-poly0-explore.json`: 306 modules, 3484 public declarations,
all source hashes matching and all nineteen changed/new targets proved. The unchanged actual
Explorer metadata passes a strict build (305 visible modules, 248 results, 169 enriched
definitions); its 32 Rates rows/nine guarantees/three families remain unchanged. No Explorer
edit or new Rates family. Final source/read-back and verified Saad2003 locators are in the design
report. No active build/process and no validation-agent commit or push; root handles the commit.
The already-approved roadmap's next exact stage receives bounded design review before proofs;
important lasting changes retain user assessment. Available-agent fallback continues.

## Regression rates (2026-10-16)

Complete and independently reviewed on `feat/regression-rates`; design, source read-back and
validation report: `docs/design/Regression-Rates.md`. Eleven new public declarations provide
Gaussian/Haar expected relative squared-residual pairs, a generic RCLike AMM-tail consumer,
and Gaussian/CountSketch high-probability relative-residual pairs. The existing factor helper
was moved unchanged to its RandomMatrix owner; no new object, interface, constant or prototype
mapping. Both new Regression modules are registered. Available-model fallback continues.

Full two-thread build passed (3873 jobs, zero warnings), as did both root checks, axiom audit
(7235 declarations, zero violations), 14 linters (4994 plus 2241 generated, zero errors), duplicate
report (4597 theorems, zero classes), references (55 keys, 40 asymptotic forms), constants,
KaTeX and all-eleven-target reuse. Prior capped module/single-file checks passed. The import
DAG is acyclic with no Regression→LowRank import; ledger dispositions are unchanged. A second
overlapping stage build was omitted after the equivalent root gates passed.
Fresh extraction: `/tmp/nlalib-regression-rates-explore.json`, 301 modules, 3466 declarations;
all source hashes match and all eleven additions are proved. Logs:
`/tmp/nlalib-regression-rates-checks`. Explorer integration uses this extraction separately.
No validation-agent commit or push; root handles the requested local commit.

## Regression organization (2026-10-16)

Completed user-approved whole-file relocation on `feat/regression-organization`:
`Regression/{Embedding,Oblique,Oblivious,SketchAndSolve}.lean`, with consumers and root imports
updated. Names, statements and proof bodies are unchanged; the import DAG is acyclic and
Sketching core does not import Regression. No aliases or ledger edits are needed. Public direct
module imports migrate according to `docs/design/Regression-Organization.md` (design/read-back/report).
Validation passed: full two-thread build (3871 jobs, no warnings), four moved-file Lean checks,
root generation/audit/lint/duplicate checks, references/constants/LaTeX. The redundant stage
script was omitted because the root checks cover its gates. Fresh extraction has 299 modules,
3455 declarations and validated Regression source hashes; old paths are absent.
Logs: `/tmp/nlalib-regression-checks`; extraction: `/tmp/nlalib-regression-explore.json`.
Validated for the requested local commit; no push requested.

## Standing instructions

- 2026-10-14, maintainer: no approval stop for the Matrix layer. Each stage's design note is
  written, sent to a Fable review, amended, and implemented without waiting. Decisions that would
  have been approval questions are recorded in the note under "Open questions" with the choice
  taken, for review after the fact. When very unsure: commit a checkpoint, then continue.

- 2026-10-14, maintainer: **the orchestrator does less itself** (its context runs out). It keeps
  the decisions, the agent briefs, the reading of agent reports, and commits. It delegates: design
  notes are drafted by an Opus agent from a short brief (scope, consumers, decisions already made)
  and reviewed by Fable; skeletons are written by the proof agent's predecessor or by an Opus
  "skeleton" agent from the reviewed note; file splits, ledger entries (prototype-key lookup and
  `ledger_add.py`), `NLAlib.lean` registration, status-table updates and `stage_check.sh` runs go
  to Sonnet agents; proofs to Opus as before. The orchestrator reads reports, not files, and checks
  builds only through `stage_check.sh` output.
- 2026-10-14, orchestrator rule for skeleton agents: never add a `sorry` statement to a proved
  file (above all a registered one); new statements go in a new skeleton file, merged at wrap-up.
  (A P6/R3 skeleton agent added two to `Isotropic.lean` and one to `ChiSquareMoments.lean`; a proof
  agent was sent to prove them.)
- 2026-10-14, maintainer: files up to about 1000 lines (Mathlib's 1500-line linter is the hard
  ceiling); proofs under about 80 lines (`CONTRIBUTING.md` §1, §8, §10).

- 2026-10-14, maintainer, approval for the Probability round: the maintainer weighs in on
  serious design decisions, meaning those that would need substantial rework to change once the
  round is finished (an interface every later theorem takes, a definition's carrier or indexing,
  a naming scheme, a global instance). The orchestrator collects these, with the alternatives
  and a recommendation, and stops for them before building on them. Everything else proceeds
  without a stop and is recorded in the design note, as in the Matrix layer.

- 2026-10-14, maintainer, for the Probability layer and above (inputs to its brief, not yet
  designed):
  1. Measurability belongs to Probability, not Matrix (done: `Probability/Measurability/`).
  2. Numerical bounds start here. Before statements are written, fix how a later improvement of
     a bound, and a new proof whose bound is incomparable with the old one (mostly better, worse
     in edge cases), are handled, above all in naming.
  3. Results that repeat across distributions go through shared interfaces; nothing is derived as
     a one-off for a single distribution.
  4. Random matrices with orthonormal columns (normalised Gaussians) are a first-class
     distribution alongside Gaussian, sub-Gaussian, sparse and structured ones.

## Explorer documentation follow-up (2026-10-16)

- Complete on `feat/explorer-docs` in the existing library and explorer checkouts; the user
  requested separate local commits after validation.
  All 28 asymptotic forms have paired explorer views, 24 named bounds are supporting API,
  and 21 Lean files received comment-only corrections. No theorem statements or proofs changed.
- Design, read-back, independent reviews, residual citation follow-up and validation:
  `docs/design/Explorer-Documentation.md`. Full build and per-file checks, root checks,
  audit/lint/duplicate report, documentation checks, 19 regression tests and browser checks pass.
  Logs: `/tmp/nlalib-explorer-checks/`. Merge library changes before deploying the stricter
  explorer parser. No prototype work was added, so ledger dispositions are unchanged.
- Unrelated untracked files are untouched and excluded: the preexisting
  `docs/design/LowRank-S7.md` and the concurrently added
  `NLAlib/Sketching/Sparse/CountSketchEmbedding.lean`. Concurrent CountSketch source and
  constant-registry refactoring is also preserved in the working tree, outside this commit.

## Gaussian fourth-moment follow-up (2026-10-16)

- **Complete and independently reviewed**, branch `feat/gaussian-fourth-moments`, base
  `0daf947`; execution worktree `/tmp/nlalib-gaussian-fourth-moments`. User authorized exact
  Gaussian fourth moments and useful fourth-order Wick, then requested a local commit.
  No push was requested.
- Delivery worktree: `/home/tyler/Documents/NLA-lib/nlalib-gaussian-fourth-moments`, relocated
  after validation; the main checkout's ongoing work was preserved.
- `Probability/Distributions/GaussianMoments.lean` (182 lines, four public theorems) and
  `RandomMatrix/Gaussian/FourthMoment.lean` (300 lines, eight public theorems) are proved and
  registered. Headline results: fourth-order Wick, Gaussian vector linear-image fourth moment,
  sandwich fourth moment with factor-three bound, centered Gram error, exact normalized AMM
  error with factor-two bound. Normalized expectation formulas require nonempty sketch type;
  integrability includes empty sketch types. Full arbitrary-order Wick remains outside scope.
- Design and full statement read-backs: `docs/design/Gaussian-FourthMoments.md`, including the
  final stage report and honest available-model fallback for unavailable requested aliases.
  Independent bounded design/file/stage reviews approved; no new enduring interface, global
  instance, object, or placement deviation. R2's old scope cut has a dated follow-up amendment.
- Added verified `Isserlis1918`; reconsidered exactly twelve existing R2-cut ledger entries,
  preserving every other entry. Prototype coverage is zero missing of twelve declarations;
  generic Fubini and second-moment wrappers remain explicitly not reproduced via existing APIs.
- Checks: full `NLAlib NLAlibScaffold` build 3860 jobs, zero warnings; required stage check
  287 proved modules, zero unproved, build 3856 jobs, zero warnings; audit 6950 declarations,
  zero violations; 14 linters, 4856 plus 2094 generated declarations, zero errors; 55 reference
  keys, zero problems; constants and KaTeX clean; duplicate report 4461 theorems, zero classes.
  Both root checks passed; targeted reuse covers all twelve public theorems. Individual module
  and `lake lean` checks passed. Logs: `/tmp/nlalib-gaussian-fourth-checks`; see the stage report
  for exact checks and read-backs. Final `git diff --check` and ledger structural checks clean.

## Current

**Probability round started, 2026-10-14.** The maintainer decided §2 of `docs/PORT_PROBABILITY.md`
(all ten as recommended; D4 revised: `RCLike` wherever the proof allows, Gaussian and Haar matrix
laws real for now with complex analogues in view). `CONTRIBUTING.md` §5.1 and §5.2 ("Numerical
bounds") and `Mathlib-deviations.md` entries 12 and 13 are updated to match. Design checkpoint
for the maintainer after P3. Now: P0.

**P3 checkpoint passed (maintainer, 2026-10-14).** P0 §7 Q1 decided: `Matrix.Norms.L2Operator`
for matrix integrals (D10 amended; `Mathlib-deviations.md` entry 13; `CONTRIBUTING.md` §5.1 rule).
P4 proceeded on the orchestrator's recommendations (Lipschitz as `LipschitzWith` on
`EuclideanSpace`; the log-Sobolev route with constant `L²`), open to the maintainer's correction.

**Queue (orchestrator, 2026-10-14, latest):**
- **Probability round complete, 2026-10-14.** Every Probability and RandomMatrix stage proved and registered; round report `docs/design/Probability-REPORT.md`; final stage check in its §7.
- P5b, P5c, P5d proved (P5b mean constant 8; P5d bridge for deviation 17 proved); P7 in progress.
- P5b/P5c/P5d/P7 notes Fable-reviewed; findings and decisions in `/tmp/claude-1000/p0/review_p5bcd7.txt` (to be copied into each note's §8). P5d Q1 decided: conditional matrix MGF bound spelled with `μ[·|m]` (a.e. per θ), not `condExpKernel`; deviation entry 17; bridge from Mathlib's `HasCondSubgaussianMGF` needs `StandardBorelSpace` only there. P5b+P5c skeletons in progress; P5d+P7 skeletons next.
- R3 complete: `RandomMatrix/Gaussian/SpectralNorm.lean` and `RandomMatrix/Gaussian/ExtremeSingularValues.lean` proved and registered in `NLAlib.lean`; ledger R3 entries added.
- R3 `RandomMatrix/SubGaussian/ExtremeSingularValues.lean` proved (constant 24 reached) and registered. Stage check 2026-10-14: 200 proved modules (1 not yet), 0 warnings, audit 4681 declarations 0 violations, lint 0 errors (14 linters), 38 bib keys 0 problems.
- Proved and registered: P0–P5a, R1, R2 (stage checks green at 185 modules, before R4–R5).
- R4 `ChiSquareMoments.lean`, `InverseMoments.lean`, `InverseMoments/Spectral.lean` proved (split at 1490 lines); P6 `GaussianIntegrationByParts.lean`,
  `GaussianComparison.lean` (Opus).
- R5 complete: all six files proved (`PolarFrames`, `UnitaryInvariance`, `Haar/{Basic,Uniqueness,Moments,Transfer}`); deviation bridges 15 and 16 proved.
- P6 proved: `GaussianIntegrationByParts.lean`, `GaussianComparison.lean` (1035 lines, slightly over the soft limit); R5 `PolarFrames.lean`, `UnitaryInvariance.lean` proved.
- R4 complete: `RandomMatrix/Gaussian/BlockMoments.lean` proved and registered (with a transposed form for Nystrom that needs the rank hypothesis and gives the closed value); ledger R4 block entries added.
- Ledger keys are full prototype names with `NLAlib.` (fixed 2026-10-14; `ledger_missing.py NLAlib.Probability. NLAlib.RandomMatrix.` reports coverage: 302 of 921). Pending bookkeeping (Sonnet): ledger lines in `/tmp/claude-1000/p0/ledger_pending.txt` (may be
  lost on reboot: re-derive from agent reports in the design notes' stage reports if so) and the
  R4/P6/R3/R5 entries as they finish; register modules in `NLAlib.lean` once sorry-free;
  `stage_check.sh` after each stage.
- Wrap-up items (2026-10-14): done (R3 helpers public, Procrustes, unitary-group compactness in ForMathlib, P5a and P4 moves; the skeleton-era merges LaplaceGeneral into Laplace, RademacherSymmetry into Rademacher, GaussianIntegrationByPartsGrowth into GaussianIntegrationByParts (the bounded Stein identity now its `k = 0` corollary), EntropyExpBounded into Entropy; the P5b copies deleted for public originals `exp_div_rpow_rpow_eq_exp` (Chernoff, was `chernoff_base_rpow_eq`), `exp_integral_le_integral` (Laplace), `dilationCLM`, `memLp_dilation`, `iIndepFun_dilation`, `integral_dilation_eq_zero` (Bernstein, replacing `dilation_hypotheses`) and `Matrix.sum_fromBlocks` (new `ForMathlib/Data/Matrix/Block.lean`, replacing `sum_fromBlocks_diagonal` and its copy in Freedman); `bernsteinCoeff_nonneg` split into `mul_lt_three_of_mem_Ioo` and `sq_div_two_div_nonneg_of_mem_Ioo`; `condExp_cfc` public as `Matrix.IsHermitian.condExp_cfc` in `MatrixConditionalExpectation.lean`; Orlicz and BoundedDifferences registered in `NLAlib.lean`; P5b §8 records the mean constant 8, P7 §8 the reached constants and the entropy-lemma route); the P5a row is in the table.
  ForMathlib; `|s log s| ≤ s² + 1` duplicated (P4).
- Then to design (drafted by Opus agents from a brief): P5b (intrinsic dimension), P5c
  (Khintchine), P5d (Freedman, with matrix conditional expectations), P7 (bounded differences,
  Orlicz bridges, entropy extras); then the round report `docs/design/Probability-REPORT.md` and
  the ledger accounting for all prototype `Probability/`, `RandomMatrix/` declarations.

| Stage | File | Owner | State | Notes |
|---|---|---|---|---|
| P0 | design note `docs/design/Probability-P0.md` | orchestrator | written, Fable-reviewed | Q1 to the maintainer |
| P0 | `Probability/Law.lean`, `Tail.lean` | Opus agent | proved | `measureReal_abs_ge_le` needs no finiteness. Note for R1: `HasLaw.isProbabilityMeasure` does not find the `Measure.pi` instance at type `Measure (Matrix m n α)`; consider an instance for the nested product on matrices |
| P0 | `Probability/Isotropic.lean` | Opus agent | proved | `of_iIndepFun` needs no probability hypothesis (`iIndepFun` implies it) |
| P0 | checks on the proved part | orchestrator | done | `stage_check.sh`: 147 modules, 0 warnings, audit 3537 declarations 0 violations, lint 2714 clean, 34 keys; ledger +9 |
| P1 | design note `docs/design/Probability-P1.md` | orchestrator | written, Fable-reviewed | |
| P1 | `SubGaussian/Basic.lean`, `Moments.lean` | Opus agent | proved | `HasSubgaussianMGF.isFiniteMeasure` made public |
| P1 | `SubExponential/Basic.lean`, `Tail.lean` | Opus agent | proved | split at the skeleton (file budget); `measureReal_ge_le_of_le_mul` lost a redundant `0 ≤ t` |
| P1 | `SubGaussian/Square.lean` | Opus agent | proved | reached the literature's constants `32 c²`, `4 c`, now literals in the statement; stage report in the note |
| P2 | design note `docs/design/Probability-P2.md` | orchestrator | written, Fable-reviewed (§8 amendments) | |
| P2 | `Distributions/Rademacher.lean`, `Sampling.lean` | Opus agent | proved | `samplingMeasure_singleton` public |
| P2 | `Distributions/Gaussian.lean` | Opus agent | proved | |
| P0–P2 | checks | orchestrator | done | `stage_check.sh`: 155 modules, 0 warnings; audit 3697, 0 violations; lint 2818 clean; ledger +69 |
| P3 | design note `docs/design/Probability-P3.md` | orchestrator | written, Fable-reviewed (§8) | maintainer checkpoint after P3 |
| P3 | `SubGaussianVector/Basic.lean`, `Norm.lean` | Opus agent | proved | `IsSubgaussianVector.aemeasurable` public over `𝕜` |
| P3 | `Distributions/ChiSquare.lean`, `QuadraticForm/Moments.lean` | Opus agent | proved | Hutchinson's variance over `𝕜` with moment parameters |
| P3 | `QuadraticForm/HansonWright.lean` (+ `HansonWright/{LinearImage,OffDiagonal}.lean`) | Opus agent | proved | constant `1/196` (prototype `1/(256e²)`); 884 lines against 3,400 |
| P0–P3 | checks | orchestrator | done | `stage_check.sh`: 162 modules, 0 warnings; audit 3809, 0 violations; lint 2900 clean; `Result:` ids on the headline theorems; ledger +35 |
| P0–P3 | wrap-up (one public Gaussian linear-form MGF, `HasSubexponentialMGF.add`, tail-prefix rename) | Opus agent, orchestrator | done | stage review by Fable; ledger targets qualified (0 missing) |
| P0 | `Probability/MatrixIntegral.lean`, `ForMathlib/Analysis/CStarAlgebra/Matrix.lean` | Opus agent | proved | the Loewner closedness instance already existed (`ForMathlib/LinearAlgebra/Matrix/PosDef.lean`); the planned `Order.lean` dropped |
| P4 | design note `docs/design/Probability-P4.md`, skeletons | orchestrator | written, Fable-reviewed (§8); skeletons compile | |
| P4 | `Probability/Entropy.lean`, `EntropyTensorization.lean`, `ForMathlib/MeasureTheory/Constructions/PiUpdate.lean` | Opus agent, orchestrator | proved | split from one 722-line file |
| P4 | `Distributions/GaussianLogSobolev.lean`, `GaussianLogSobolevOneDim.lean` | Opus agent | proved | Gross's two-point route through Mathlib's CLT (the prototype's Ornstein–Uhlenbeck files not needed); wrap-up: one `ForMathlib` copy of `|s log s| ≤ s² + 1` |
| P4 | `LogSobolev.lean` (+ `ForMathlib/Analysis/Calculus/BumpFunction/Convolution.lean`) | Opus agent | proved | Lipschitz approximation by convolution |
| P4 | `Distributions/GaussianConcentration.lean` | Opus agent | proved | P4 complete; stage report and checks at the next quiet point |
| P5a | design note `docs/design/Probability-P5a.md`, skeletons `MatrixConcentration/*` | orchestrator | written, Fable-reviewed (§8); skeletons compile | |
| P5a | `MatrixConcentration/{Laplace,Subadditivity,MGFBound}.lean` (+ `ForMathlib/Analysis/Convex/Integral.lean`) | Opus agent | proved | Jensen on a non-closed convex set; wrap-up: move `continuousOn_cfc_log` to the Matrix layer, `measurableSet_posDef` to Measurability |
| P5a | `MatrixConcentration/{Chernoff,ChernoffSum}.lean` | Opus agent | proved | skeleton bug fixed: `∀ θ` had elaborated as `θ : ℕ` (rule added to CONTRIBUTING §5.2) |
| R1 | design note `docs/design/RandomMatrix-R1.md`, skeletons `RandomMatrix/Gaussian/*` | orchestrator | written, Fable-reviewed (§8); skeletons compile | `frobNorm_eq_norm_toLp_uncurry` proved in the Matrix layer |
| R1 | `RandomMatrix/Gaussian/{Basic,Invariance}.lean` | Opus agent | proved | |
| R1 | `RandomMatrix/Gaussian/{Rank,Concentration}.lean` | Opus agent | proved | |
| R2 | design note `docs/design/RandomMatrix-R2.md`, skeleton `RandomMatrix/Gaussian/Moments.lean` | Opus agent | proved | |
| R4 | design note `docs/design/RandomMatrix-R4.md`, skeletons | orchestrator | written, Fable-reviewed (§8); skeleton check pending a slot | |
| P5a | `MatrixConcentration/{Bernstein,Series}.lean` | Opus agent | proved | |
| P5a | wrap-up | orchestrator, Opus agent | done | moved the duplicated private `le_sqrt_of_forall_le_div_add_mul` (Bernstein, Series) to ForMathlib; `integrable_and_integral_cfc` (Series) to `MatrixIntegral.lean`; `continuousOn_cfc_log` to the Matrix layer; `measurableSet_posDef` to Measurability; note: under `Matrix.Norms.L2Operator`, `Continuous.measurable` finds no `BorelSpace (Matrix …)` |
| P5a | `MatrixConcentration/{Laplace,Subadditivity,MGFBound,Chernoff,ChernoffSum,Bernstein,Series}.lean` | Opus agents | proved | P5a complete: all seven files proved and registered, nothing in the scaffold library |

**Matrix layer complete, 2026-10-14** (branch `scaffold`, local commits, not pushed): stages M0 to
M10 proved, 144 files, nothing scaffolded, all checks green. Read `docs/design/Matrix-REPORT.md`
first. No design note was approved by the maintainer; the decisions to confirm are in §3 of the
report.

| Stage | File | Owner | State | Notes |
|---|---|---|---|---|
| M0 | bootstrap | orchestrator | done | see "M0 findings" |
| M1 | all 15 files | Opus agents | **done** | `docs/design/Matrix-Foundations.md` with stage report; not maintainer-approved |
| M2 | all 8 files | Opus agents | **done** | `docs/design/Matrix-Norms.md` with stage report; not maintainer-approved |
| M3 | all 10 files | Opus agents | **done** | `docs/design/Matrix-Spectral.md` with stage report; not maintainer-approved |
| M3a | all 7 files | Opus agents | **done** | `docs/design/Matrix-Majorization.md` with stage report; not maintainer-approved |
| M3b | all 8 files | Opus agents | **done** | `docs/design/Matrix-InvariantNorms.md` with stage report; not maintainer-approved |
| M5 | design note `docs/design/Matrix-Subspaces.md`, skeleton of 5 files under `Matrix/Subspaces/` | orchestrator | done, Fable-reviewed, not maintainer-approved | distance is `(1 - Q) * P` in a norm; `principalAngle`; `tangentMatrix` |
| M5 | `Subspaces/ProjectorPair.lean`, `Frames.lean` | Opus agent | proved | |
| M5 | `Subspaces/PrincipalAngles.lean`, `Oblique.lean` | Opus agent | proved | `PrincipalAngles.lean` is 530 lines: split tangents and frame alignment off at wrap-up; publish four helpers |
| M5 | `Subspaces/CSDecomposition.lean` | Opus agent | proved | wrap-up: drop `card p ≤ card q` where unused, add `singularValues U.toBlocks₁₂ = singularValues U.toBlocks₂₁` |
| M6 | `Perturbation/Sylvester.lean`, `Inverse.lean`, `Relative.lean` | Opus agents | proved | `specNorm_sub_smul_one_le_of_le` was false for size zero with `b < a`; `(hab : a ≤ b)` added |
| M6 | `Perturbation/Residual.lean`, `Pseudoinverse.lean` | Opus agent | proved | golden-ratio block lemma moved to `Norms/Projector.lean` |
| M6 | `Perturbation/DavisKahan.lean` | Opus agent | proved | 752 lines: split the gap forms off at wrap-up |
| M6 | `Perturbation/LeastSquares.lean`, `Continuity.lean` | Opus agent | proved | `isLeast_matrixNorm_sub_of_rank_le` moved to `Norms/UnitarilyInvariant.lean` |
| M6 | `Perturbation/Wedin.lean`, `SimpleEigenvalue.lean` | Opus agent | proved | simple eigenvalue branch by the implicit function theorem on the characteristic polynomial |
| M5, M6 | wrap-up (file splits `Subspaces/Tangent.lean`, `Perturbation/DavisKahanGap.lean`; published helpers; review follow-ups) | Opus agent | done | build, audit (1827 declarations), lint (1461) and references clean; stage reports in the two notes; the ledger accounts for every prototype `Subspaces/` and `Perturbation/` declaration (368 lines added by a bookkeeping agent: 185 mapped, 183 null with reasons) |
| M7 | `Inequalities/Order.lean`, `Block.lean` | Opus agent | proved | two condition-number bounds were false for size zero with `b < 0`; `(hb : 0 ≤ b)` added |
| M7 | `Inequalities/Determinant.lean`, `Kantorovich.lean` | Opus agent | proved | `Determinant.lean` is 582 lines: split the Minkowski section off at wrap-up |
| M7 | `Inequalities/SchurHorn.lean` | Opus agent | proved | Horn's converse by induction with plane rotations, not the prototype's descent |
| M7 | `Inequalities/PrincipalMinors.lean`, `HadamardProduct.lean`, `ForMathlib/LinearAlgebra/Matrix/Hadamard.lean` | Opus agent | proved | Oppenheim by a new induction through Schur complements |
| M7 | `Inequalities/EntrywiseFunctions.lean` and stage wrap-up | Opus agent | done | `Inequalities/Minkowski.lean` split off `Determinant.lean`; majorization companions published; build, audit (1979 declarations), lint (1583) and references clean; stage report in the note; ledger completion for the prototype `Inequalities/` leftovers in progress |
| M9 | `Factorizations/Triangular.lean`, `Elimination.lean` | Opus agent | proved | `Elimination.lean` is 743 lines: the `gaussState` part moves to `GaussState.lean` |
| M9 | `Factorizations/LU.lean`, `Cholesky.lean`, `GaussState.lean` (split off `Elimination.lean`) | Opus agent | proved | the rank pattern of pivoted Cholesky, unproved in the prototype, is proved |
| M9 | `Factorizations/QR.lean`, `GramSchmidt.lean` | Opus agent | proved | existence from Mathlib's `gramSchmidtOrthonormalBasis` on zero-padded columns |
| M9 | `Factorizations/Householder.lean`, `Givens.lean` | Opus agent | proved | |
| M9 | `Factorizations/Hessenberg.lean`, `RankRevealing.lean`, `ColumnVolume.lean` (split off) | Opus agent | proved | Hessenberg reduction, the Hessenberg QR and the implicit Q theorem, unproved in the prototype, are proved |
| M10 | `Spectral/Schur.lean`, `EigenvalueListing.lean` (split off), `Structured/Walsh.lean`, `Structured/Cauchy.lean` | Opus agent | proved | unitary Schur from the field similarity plus a QR factorization; Hilbert matrix positive definite through `posDef_iff_eliminationStep` |
| M10 | `Spectral/Normal.lean`, `Simultaneous.lean`, `Diagonalizable.lean`, `EigenvectorPairing.lean`, `SylvesterEquation.lean` (split off) | Opus agent | proved | commuting families over `𝕜` with split characteristic polynomials; simple-eigenvalue pairing over any field |
| M10 | `Spectral/Inertia.lean`, `InertiaElimination.lean`, `SylvesterCriterion.lean`, `RankOneUpdate.lean`, `InterlacingConverse.lean` (two split off) | Opus agent | proved | Sylvester's criterion by interlacing, no pivots; both interlacing converses proved |
| M10 | `Spectral/Congruence.lean`, `ForMathlib/MeasureTheory/Matrix.lean`, `Measurability/Basic.lean` | Opus agent | proved | all M10 files proved, nothing in the scaffold library; QZ by Schur of `B⁻¹ A` and a compactness limit |
| M10 | stage wrap-up | Opus agent | done | |
| all | gap-closing additions from the downstream audit | Opus agent | done | `docs/port/matrix-downstream-audit.md`; new files `Spectral/LeastSingularValue.lean`, `Basic/ComplementaryProjector.lean` |
| all | final checks and report | orchestrator | **done** | full build of `NLAlib` and `NLAlibScaffold` with no warnings; audit 3493 declarations, 0 violations; lint 2680 clean; 32 bibliography keys, 0 problems; ledger 2734 of 2734 accounted; `docs/design/Matrix-REPORT.md` |
| M5 to M9 | follow-up additions from the ledger passes | Opus agent | done | idempotents in oblique form, invariance of principal angles, `Spectral/ProjectedLowRank.lean` (truncation step of the randomized SVD), compression determinant bound, `frobInner_polarFactor`, `givens_apply` |
| M10 | `Spectral/Gershgorin.lean`, `HermitianPart.lean`, `Structured/Kronecker.lean`, `Circulant.lean` | Opus agent | proved | |
| M10 | `Spectral/SpectralRadius.lean`, `PowerBounds.lean`, `QuasiTriangular.lean`, `RealSchur.lean`, `RealSimilarity.lean` (three split off) | Opus agent | proved | real Schur, the real normal form and real QZ by one deflation through a one- or two-dimensional invariant subspace |
| M8 | `Functions/HermitianCalculus.lean`, `ForMathlib/Analysis/RCLike/ToComplex.lean`, `ForMathlib/Analysis/Calculus/Deriv/Matrix.lean` | Opus agent | proved | diagonalisation lemmas to be restated for a frame `U : Matrix n r 𝕜` with `card r = card n`, the shape the spectral theorem of M3 produces |
| M8 | `Functions/Polynomial.lean`, `Exponential.lean` | Opus agent | proved | |
| M8 | `Functions/Complexification.lean`, `TraceFunctions.lean` | Opus agent | proved | convexity of trace functions through Jensen for quadratic forms (Peierls), Klein from the generalized Klein inequality |
| M8 | `Functions/OperatorMonotone.lean`, `GoldenThompson.lean` | Opus agent | proved | Golden–Thompson by the Lie product formula over `𝕜` (the prototype derived it from Lieb's theorem); `OperatorMonotone.lean` is 596 lines, split at wrap-up |
| M8 | `Functions/Perspective.lean`, `Lieb.lean`, `OperatorConvex.lean` (split off `OperatorMonotone.lean`) | Opus agent | proved | Lieb's concavity theorem over `𝕜` on any index type; joint convexity of the relative entropy through Kronecker products |
| M8 | `Functions/TracePowers.lean`, `LogDet.lean`, `AbsoluteValue.lean` | Opus agent | proved | all thirteen M8 files proved; wrap-up pending |
| M9 | `Factorizations/Polar.lean`, `Procrustes.lean` and stage wrap-up (`Nystrom.lean`, `LUGeneral.lean`) | Opus agent | done | all sixteen M9 files proved, nothing in the scaffold library; stage checks and ledger completion pending |
| M8 | stage wrap-up | Opus agent | done | stage report in `Matrix-Functions.md` §9 |
| M8, M9 | stage checks | orchestrator | done | build no warnings; audit 2963 declarations, 0 violations; lint 2280 clean; refs clean; ledger complete for prototype `Functions`, `Calculus`, `Factorizations`, `Basic` |
| M6 | design note `docs/design/Matrix-Perturbation.md`, skeleton of 10 files under `Matrix/Perturbation/` | orchestrator | done, Fable-reviewed, not maintainer-approved | Davis–Kahan in residual form at three levels; one review proposal rejected (false under repeated eigenvalues) |
| M7 | design note `docs/design/Matrix-Inequalities.md`, skeleton of 8 files under `Matrix/Inequalities/` | orchestrator | done, Fable-reviewed, not maintainer-approved | spectral equivalence as a Loewner sandwich; `principalMinor`; determinants through `RCLike.re` |
| M8 | design note `docs/design/Matrix-Functions.md`, skeleton of 12 files under `Matrix/Functions/`, `ForMathlib/Analysis/Calculus/Deriv/Matrix.lean`, `ForMathlib/Analysis/RCLike/ToComplex.lean` | orchestrator | done, Fable-reviewed, not maintainer-approved | `cfc f A` is the spelling of `f(A)`; no `matrixExp`/`traceExp`/`lambdaMax` names; results over `𝕜` through `complexify`; entrywise derivatives |
| M9 | design note `docs/design/Matrix-Factorizations.md`, skeleton of 11 files under `Matrix/Factorizations/` | orchestrator | done, Fable-reviewed, not maintainer-approved | step-indexed recursions with breakdown as a value; `eliminationStep`/`gaussState` shared by LU and Cholesky; leading minors as `principalMinor A (Finset.Iic i)`; `polarFactor`; `IsLocalMaxVolume` certificate for rank-revealing column selection |
| M10 | design note `docs/design/Matrix-Structured.md`, skeleton of 18 files under `Matrix/Structured/`, `Matrix/Spectral/`, `Matrix/Measurability/`, `ForMathlib/MeasureTheory/` | orchestrator | done, Fable-reviewed, not maintainer-approved | eigenvalue listings `IsEigenvalueListing A d`; `inertiaPos`/`inertiaNeg` through `eigenvalue`; real-valued `specRadius`; `IsDiagonalizable`; `fourierMatrix`, `walshHadamard`; `Matrix.instMeasurableSpace` |
| M4 | all 6 files | Opus agents | **done** | `docs/design/Matrix-Pseudoinverse.md` with stage report; not maintainer-approved. One designed statement was false (empty column type) and gained `0 ≤ b` |

Stage order after M3, changed by the M3 and M4 notes: **M4** (pseudoinverse, least squares) →
**M3a** (majorization, Ky Fan sums, von Neumann trace inequality, Hoffman–Wielandt, Mirsky,
Lidskii) → **M3b** (Schatten, nuclear, Ky Fan and unitarily invariant norms) → M5 → M6 → M7 (the
rest of the inequalities) → M8 → M9 → M10.

While a stage is being proved, `import NLAlib` contains `sorry` and `scripts/Audit.lean` fails.
That is the expected state between a stage's skeleton and its last proof.

## M2 result (2026-10-14)

- 8 files, 2022 lines under `Matrix/Norms/` plus
  `ForMathlib/Topology/MetricSpace/CoveringNumbers.lean`: `Frobenius`, `Spectral`, `Compare`,
  `Loewner`, `Block`, `Projector`, `Net`.
- Checks on M1 + M2 + the two proved M3 eigenvalue files (25 modules): build with no warnings;
  axiom audit, 563 constants, 0 violations; `#lint` clean on 468 declarations; `check_refs.py`
  clean.
- Nothing in `NLAlibScaffold`. The volumetric net bound, expected to be scaffolded, was proved.
- `frobSq` is gone from the vocabulary; CONTRIBUTING §5.3 was amended (Frobenius row, scalar
  multiples of the identity, Loewner form of spectral bounds, nets).
- Ledger: every declaration of the prototype's `Norms/{Core, Frobenius, SpectralNormBounds,
  BlockNormBounds, EntryBounds, EuclideanOperatorBounds, RayleighNorm, Net, ColumnNorms, Reindex}`
  is accounted for. The Schatten, nuclear, Ky Fan, invariant-norm and rectangular-diagonal files
  wait for M3b.

## M1 result (2026-10-14)

- 15 files, 2707 lines, 229 declarations: `ForMathlib/LinearAlgebra/Matrix/{Rank, PosDef,
  Adjugate, SchurComplement, CauchyBinet}`, `ForMathlib/Analysis/InnerProductSpace/PiL2`,
  `Matrix/Basic/{Orthonormal, QuadForm, Gram, Projector, OrthonormalBasis, SchurComplement,
  Selection, Dilation, PlaneRotation}`.
- Checks on the M1 modules alone: build with no warnings; axiom audit, 282 constants, 0
  violations; `#lint`, 14 linters, clean; `check_refs.py` clean.
- Nothing in `NLAlibScaffold`.
- `Projector.lean` is 510 lines after the split.
- Ledger: 165 prototype declarations accounted for. Left for later stages: Moore–Penrose,
  pseudoinverse, least squares, generalized Schur complement (M4); leading minors and the pivot
  Schur step (M9); projector norm lemmas (M2).
- `scripts/check_refs.py` rejected the docstring ending `Result: id -/` that CONTRIBUTING §6 shows
  as the example. The script was fixed to accept it.
- New scripts: `scripts/ledger_add.py` (add entries from `old -> new` lines) and
  `scripts/ledger_missing.py` (list prototype declarations the ledger does not account for).
- `docs/port/proof-agent-brief.md` is the standing brief given to every proof agent.

## M0 findings (2026-10-14)

- `lake update` resolves Mathlib tag `v4.33.1` to commit `0df444a3`, the prototype's pin. The
  Mathlib cache was already on the machine; `lake exe cache get` decompresses it in half a minute.
- **Lake 5.0.0 has no `-j` flag.** `lake build -j 4` fails with `unknown short option '-j'`. The
  cap that works is the environment variable: `LEAN_NUM_THREADS=4 lake build <targets>` runs at
  most 4 Lean processes (measured 1, 2, 4 for values 1, 2, 4 on a ten-file test project; 10
  without it). CONTRIBUTING §9 and §10, AGENTS.md, README, the PR template and the port brief were
  changed from `lake build -j N` to `LEAN_NUM_THREADS=N lake build`.
- **`mk_all` needs `--module` the first time.** Without it the root file is generated with plain
  `import`. With `lake exe mk_all --module --lib NLAlib` it is `module` plus `public import`.
  Later runs infer the style from the existing file, so `--check` in CI needs no flag. `mk_all`
  exits 1 when it rewrites a file; that is not a failure.
- **`lake env lean <file>` ignores `lakefile.toml` options.** `autoImplicit` is then on and the
  Mathlib linter set is off, so a skeleton can look clean and be wrong. The single-file check is
  `LEAN_NUM_THREADS=2 lake lean <file> -- -M 8000`. The docs were changed to this form. The
  scripts `Audit.lean` and `Lint.lean` are still run with `lake env lean`.
- The file template of CONTRIBUTING §3 compiles as written: `module`, `public import`,
  `@[expose] public section`. Header linter, `scripts/Audit.lean`, `scripts/Lint.lean` and
  `scripts/check_refs.py` all pass on the first file (`NLAlib/Matrix/Basic/Orthonormal.lean`).
- `lake-manifest.json` is generated and should be committed with the first commit.

## In NLAlibScaffold

Nothing. Every statement of the Matrix layer is proved (2026-10-14).
