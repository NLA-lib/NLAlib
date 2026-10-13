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
| M1 | all 15 files | Opus agents | **done** | design note and stage report: `docs/design/Matrix-Foundations.md`; not maintainer-approved |
| M2 | design note `docs/design/Matrix-Norms.md` | orchestrator | done, Fable-reviewed, not maintainer-approved | drops `frobSq`; moves Schatten and UI norms to M3b |
| M2 | skeleton, 7 files under `Matrix/Norms/` | orchestrator | done, builds with `sorry` | |
| M2 | `Norms/Spectral.lean` | Opus agent | proved | follow-ups in "M2 notes" |
| M2 | `Norms/Frobenius.lean` | Opus agent | in progress | |
| M2 | `Norms/Compare.lean` | — | skeleton | after Frobenius |
| M2 | `Norms/Loewner.lean` | — | skeleton | after Compare |
| M2 | `Norms/Block.lean` | — | skeleton | after Compare |
| M2 | `Norms/Projector.lean` | — | skeleton | after Compare |
| M2 | `Norms/Net.lean` | — | skeleton | after Loewner |
| M3 | design note | orchestrator | being drafted | |

While a stage is being proved, `import NLAlib` contains `sorry` and `scripts/Audit.lean` fails.
That is the expected state between a stage's skeleton and its last proof.

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

## M2 notes

- From the Spectral report: add `specNorm_real_smul` (real scalar action) and the same for
  `frobNorm`; the private lemmas `norm_toLp_star` and `norm_toLp_comp_equiv` belong in
  `ForMathlib/Analysis/InnerProductSpace/PiL2.lean` as public lemmas; `specNorm_map_star` could
  be public. The docstring of `specNorm_le_of_forall_norm_star_dotProduct_mulVec_le` says "least
  constant" but the statement is only the sufficiency direction.

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
