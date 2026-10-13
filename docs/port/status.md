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
| M1 | design note `docs/design/Matrix-Foundations.md` | orchestrator | done, Fable-reviewed, not maintainer-approved | decisions in its §7 |
| M1 | skeleton, 13 files | orchestrator | done, builds with `sorry` | checkpoint commit |
| M1 | `ForMathlib/LinearAlgebra/Matrix/Rank.lean` | — | skeleton | |
| M1 | `ForMathlib/LinearAlgebra/Matrix/PosDef.lean` | — | skeleton | |
| M1 | `ForMathlib/LinearAlgebra/Matrix/Adjugate.lean` | — | skeleton | |
| M1 | `ForMathlib/LinearAlgebra/Matrix/SchurComplement.lean` | — | skeleton | |
| M1 | `ForMathlib/LinearAlgebra/Matrix/CauchyBinet.lean` | — | skeleton | |
| M1 | `Matrix/Basic/Orthonormal.lean` | — | skeleton | |
| M1 | `Matrix/Basic/QuadForm.lean` | — | skeleton | |
| M1 | `Matrix/Basic/Gram.lean` | — | skeleton | |
| M1 | `Matrix/Basic/Projector.lean` | — | skeleton | |
| M1 | `Matrix/Basic/SchurComplement.lean` | — | skeleton | |
| M1 | `Matrix/Basic/Selection.lean` | — | skeleton | |
| M1 | `Matrix/Basic/Dilation.lean` | — | skeleton | |
| M1 | `Matrix/Basic/PlaneRotation.lean` | — | skeleton | |

While a stage is being proved, `import NLAlib` contains `sorry` and `scripts/Audit.lean` fails.
That is the expected state between a stage's skeleton and its last proof.

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
