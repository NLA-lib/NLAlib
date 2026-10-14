# Port status

Updated at every stopping point. Newest entry first within each section.

## Standing instructions

- 2026-10-14, maintainer: no approval stop for the Matrix layer. Each stage's design note is
  written, sent to a Fable review, amended, and implemented without waiting. Decisions that would
  have been approval questions are recorded in the note under "Open questions" with the choice
  taken, for review after the fact. When very unsure: commit a checkpoint, then continue.

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

## Current

**Probability round started, 2026-10-14.** The maintainer decided §2 of `docs/PORT_PROBABILITY.md`
(all ten as recommended; D4 revised: `RCLike` wherever the proof allows, Gaussian and Haar matrix
laws real for now with complex analogues in view). `CONTRIBUTING.md` §5.1 and §5.2 ("Numerical
bounds") and `Mathlib-deviations.md` entries 12 and 13 are updated to match. Design checkpoint
for the maintainer after P3. Now: P0.

**Waiting for the maintainer:** `docs/design/Probability-P0.md` §7 Q1, the scope for matrix
integrals (D10 chose `Matrix.Norms.Frobenius`, under which `Integrable` does not elaborate in the
pinned Mathlib; recommendation `Matrix.Norms.L2Operator` plus one scoped `NormedSpace ℝ`
instance). Only `Probability/MatrixIntegral.lean` waits; nothing before P5 needs it.

| Stage | File | Owner | State | Notes |
|---|---|---|---|---|
| P0 | design note `docs/design/Probability-P0.md` | orchestrator | written, Fable-reviewed | Q1 to the maintainer |
| P0 | `Probability/Law.lean`, `Tail.lean` | Opus agent | proved | `measureReal_abs_ge_le` needs no finiteness. Note for R1: `HasLaw.isProbabilityMeasure` does not find the `Measure.pi` instance at type `Measure (Matrix m n α)`; consider an instance for the nested product on matrices |
| P0 | `Probability/Isotropic.lean` | Opus agent | proved | `of_iIndepFun` needs no probability hypothesis (`iIndepFun` implies it) |
| P0 | checks on the proved part | orchestrator | done | `stage_check.sh`: 147 modules, 0 warnings, audit 3537 declarations 0 violations, lint 2714 clean, 34 keys; ledger +9 |
| P1 | design note `docs/design/Probability-P1.md` | orchestrator | written, Fable-reviewed | |
| P1 | `SubGaussian/Basic.lean`, `Moments.lean` | Opus agent | proved | `HasSubgaussianMGF.isFiniteMeasure` made public |
| P1 | `SubExponential/Basic.lean`, `Tail.lean` | Opus agent | proved | split at the skeleton (file budget); `measure_ge_le_of_le_mul` lost a redundant `0 ≤ t` |
| P1 | `SubGaussian/Square.lean` | Opus agent | proved | reached the literature's constants `32 c²`, `4 c`, now literals in the statement; stage report in the note |
| P2 | design note `docs/design/Probability-P2.md` | orchestrator | written, Fable-reviewed (§8 amendments) | |
| P2 | `Distributions/Rademacher.lean`, `Sampling.lean` | Opus agent | proved | `samplingMeasure_singleton` public |
| P2 | `Distributions/Gaussian.lean` | Opus agent | proved | |
| P0–P2 | checks | orchestrator | done | `stage_check.sh`: 155 modules, 0 warnings; audit 3697, 0 violations; lint 2818 clean; ledger +69 |
| P3 | design note `docs/design/Probability-P3.md` | orchestrator | written, Fable-reviewed (§8) | maintainer checkpoint after P3 |
| P3 | `SubGaussianVector/Basic.lean`, `Norm.lean` | Opus agent | proofs in progress | |
| P3 | `Distributions/ChiSquare.lean`, `QuadraticForm/Moments.lean` | Opus agent | proofs in progress | |
| P3 | `QuadraticForm/HansonWright.lean` | — | skeleton compiles | after the others; the long proof |
| P0 | `Probability/MatrixIntegral.lean` | — | waits on Q1 | |

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
