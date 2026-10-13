# Port status

Updated at every stopping point. Newest entry first within each section.

## Standing instructions

- 2026-10-14, maintainer: no approval stop for the Matrix layer. Each stage's design note is
  written, sent to a Fable review, amended, and implemented without waiting. Decisions that would
  have been approval questions are recorded in the note under "Open questions" with the choice
  taken, for review after the fact. When very unsure: commit a checkpoint, then continue.

## Current

| Stage | File | Owner | State | Notes |
|---|---|---|---|---|
| M0 | bootstrap | orchestrator | done | see "M0 findings" |
| M1 | all 15 files | Opus agents | **done** | `docs/design/Matrix-Foundations.md` with stage report; not maintainer-approved |
| M2 | all 8 files | Opus agents | **done** | `docs/design/Matrix-Norms.md` with stage report; not maintainer-approved |
| M3 | all 10 files | Opus agents | **done** | `docs/design/Matrix-Spectral.md` with stage report; not maintainer-approved |
| M3a | all 7 files | Opus agents | **done** | `docs/design/Matrix-Majorization.md` with stage report; not maintainer-approved |
| M3b | design note `docs/design/Matrix-InvariantNorms.md`, skeleton of 5 files under `Matrix/Norms/` | orchestrator | done, Fable-reviewed, not maintainer-approved | `SymmetricGauge` on `ℕ →₀ ℝ`, `Φ.matrixNorm`, `schattenNorm q` with `q : ℝ≥0∞` |
| M3b | `Norms/SymmetricGauge.lean` | Opus agent | proved | 564 lines: split the `ℓ^q` and Ky Fan gauges into their own file at wrap-up |
| M3b | `Norms/Nuclear.lean` | Opus agent | proved | 524 lines: split the Ky Fan section into `Norms/KyFanNorm.lean` at wrap-up; three private helpers to publish |
| M3b | `Schatten`, `SchattenHolder`, `UnitarilyInvariant` | Opus agents | in progress | |
| M5 | design note `docs/design/Matrix-Subspaces.md`, skeleton of 5 files under `Matrix/Subspaces/` | orchestrator | written, Fable-reviewed, review being folded in | |
| M6 | skeleton drafts `Perturbation/Inverse.lean`, `Sylvester.lean` | orchestrator | draft, no design note yet | |
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

Nothing yet.
