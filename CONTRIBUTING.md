# Contributing to NLAlib

NLAlib is a Lean 4 library, built on Mathlib, of the foundations of numerical linear algebra:
matrix analysis and perturbation theory, polynomial approximation, random matrices and
concentration, Krylov methods, sketching, least squares, low-rank approximation, trace
estimation, and lower bounds.

**The goal is to make proving new results easy.** The library exists so that someone analysing a
new algorithm can import a statement and apply it with `exact`, `rw` or `apply`. It is not a
transcription of the literature: a result is stated in the form most useful for building on it,
proved by whatever argument is cleanest, and cited where it (or the result it generalises) appears
in print. The statement is the product. A proof can be replaced; a statement nobody can apply is
wasted.

This file and the guides it links are the contract, for human contributors and for the AI agents
that do much of the work alike. Everything in them is enforced by CI, by review, or both.

## Setup

```
git clone https://github.com/NLA-lib/nlalib.git && cd nlalib
lake exe cache get                                  # Mathlib's .olean files; never build Mathlib
lake build NLAlib
```

The toolchain is pinned in `lean-toolchain` (Lean and Mathlib `v4.33.1`); `elan` installs it.
The checks also need Python 3.11 or later and, for the LaTeX check, Node 20 with
`npm install --no-save --no-package-lock katex@0.16.22`. Before opening a PR, run
`bash scripts/stage_check.sh` ([Pull requests and checks](#pull-requests-and-checks)).

## Ground rules

1. **Built for use, not transcription.** Choose the statement a downstream proof wants: the
   general form, the hypotheses it will actually have, the conclusion in the shape it will
   rewrite with. The printed version in a source is provenance, not a specification; deviating
   from it (generalising, changing the constant, restating as a tail instead of a sample size,
   splitting or merging) is normal and is recorded in the docstring.
2. **One interface per kind of hypothesis** ([statements](docs/contributing/statements.md) §3).
   Hypotheses are named predicates and structures shared across the library
   (`HasOrthonormalCols`, `IsSubspaceEmbedding`, an isotropy predicate, a spectral-gap predicate),
   never raw conditions re-spelled per theorem. If you write a raw condition a second time, it is
   an interface. If a theorem's hypotheses do not fit an existing interface, that is a design
   question ([design](docs/contributing/design.md)), not a reason to invent a local one.
3. **Mathlib first.** Before defining or proving anything, search Mathlib (`grep -rn` in
   `.lake/packages/mathlib/Mathlib`, `exact?`, `apply?`, `rw?`, Loogle). If Mathlib has the
   statement, use it. If Mathlib has the object (`Matrix.PosSemidef`, `IsHermitian.eigenvalues₀`,
   `LinearMap.singularValues`, `cfc`, `MatrixOrder`, `HasLaw`, `HasSubgaussianMGF`), build on it and
   never define a parallel one. If you must define your own, ship the bridge lemma to Mathlib's
   notion in the same file.
4. **One spelling per concept** ([vocabulary](docs/contributing/vocabulary.md)). A second
   spelling, a `Complex*` twin, an `ᵀ` copy of an `ᴴ` lemma, or a local re-definition is a defect,
   whatever its reason.
5. **General once, then corollaries.** Over `[RCLike 𝕜]` and arbitrary `[Fintype]` index types
   unless the mathematics needs ℝ or `Fin` ([statements](docs/contributing/statements.md) §1). The
   ℝ corollary, when useful, is one line.
6. **Every public declaration is documented and cited**
   ([docstrings](docs/contributing/docstrings.md)).
7. **No `sorry` on `main`.** A PR contains complete, checked work; how you stage unfinished
   work on your own branch is up to you. No `axiom`, no `native_decide`, no `admit`, no weakening
   a statement to make it provable ([proofs](docs/contributing/proofs.md) says what the audit
   allows).
8. **Files are topics, not proofs.** Up to about 1000 lines [F10] (Mathlib's linter limit of
   1500 is the hard ceiling), one mathematical topic, ordered
   definitions → basic API → main theorems → corollaries. No file named after a paper, a round of
   work, or a proof technique. No "toolkit", "bundle" or "part 2" files [F11].
9. **Design before code** ([design](docs/contributing/design.md)). New material of any size
   starts with a written design: the objects, the hypothesis interfaces, the statement shapes,
   and how later layers will consume them. Existing developments elsewhere are material to
   evaluate, not a template.
10. **A library, not a list of results.** A piece of work is finished when the next one is
    easier because of it, not only when its target theorems are proved. The mathematics is the
    hard part of a proof. Bookkeeping should not be: memory frames, index and layout arithmetic,
    unfolding an execution, re-deriving the same estimate. If you write the same non-mathematical
    argument a second time, or a proof is mostly such steps, a lemma, a rule, a tactic or an
    interface is missing. Add it, public and documented, in the file of its topic (rule 8: not a
    "toolkit" file), and use it. A design lists this shared machinery up front
    ([design](docs/contributing/design.md), item 7). Closing a run of targets by brute force and
    leaving the next contributor to repeat the effort is a defect, even when every proof checks.

## The guides

The rules are in topic guides under `docs/contributing/`, each short enough to read whole:

| Guide | What it covers |
|---|---|
| [layout](docs/contributing/layout.md) | folders and layers, imports, ForMathlib, the file template |
| [naming](docs/contributing/naming.md) | the name grammar, rules N1–N18, spellings, the names allowlist |
| [statements](docs/contributing/statements.md) | types, statement shape, numerical bounds, hypothesis interfaces |
| [vocabulary](docs/contributing/vocabulary.md) | one spelling per concept, with its Mathlib bridge |
| [programs](docs/contributing/programs.md) | fixed programs, operation models, total certificates and counted resources |
| [docstrings](docs/contributing/docstrings.md) | docstrings, citations, result ids, algorithm tags, LaTeX notation |
| [proofs](docs/contributing/proofs.md) | proof style and what each library may contain |
| [design](docs/contributing/design.md) | design notes for new material, Mathlib deviations |
| [checks](docs/contributing/checks.md) | the rules checker, the ratchet, allowlists, adding a rule, the other scripts |

**Rule ids.** A rule a script checks carries its id in brackets where it is stated, [F1], and the
check's messages cite the same id. The letter is the area: N names; F file template, P placement
and layers, S source and proof style, T types and statement shape, V vocabulary, B bounds,
D docstrings, M notation, C citations, R result ids, A algorithm tags, G design records,
E programs. The rule data is `docs/rules/rules.toml` ([checks](docs/contributing/checks.md) §1),
and `python3 scripts/check_rules.py --list` prints every id with its level. A rule with no id is
judged by review. Each topic folder has a generated `NLAlib/<Topic>/RULES.md`: its layer, the
rules its files keep, and its exemptions and allowlisted declarations, each with its reason.

## Pull requests and checks

**Pull requests.** One topic per branch and PR. A PR adds or changes one file's worth of
mathematics (a new topic file, or a coherent change to one), plus the consumers it breaks. It
contains complete, checked work: every statement proved, documented and cited, and the checks
below green.

**The one command before a PR.** From the repository root, with nothing else building:

```
bash scripts/stage_check.sh > /tmp/stage-check.log 2>&1; echo $?
```

It must exit 0. It writes its logs to `$TMPDIR/nlalib-stage-check` (default `/tmp`). With an
up-to-date build it takes roughly 10 to 20 minutes, most of it the kernel replay, the extraction
and the full build; after a Mathlib bump or a change low in the import graph, longer.
It runs, in order:

1. `lake build --wfail` of every NLAlib module (warnings are fatal, as in CI), then the axiom
   audit `scripts/Audit.lean` and the environment linters `scripts/Lint.lean` on those modules;
2. `lake build` of every library of `lakefile.toml`, `lake exe mk_all --lib NLAlib --check` (the
   root `NLAlib.lean` is current), and the freshness check `lake build --no-build --rehash`;
3. the kernel replay `scripts/Replay.lean` (every constant re-checked by Lean's kernel,
   [proofs](docs/contributing/proofs.md)) and its fixtures `scripts/replay_fixtures.sh`;
4. fixed-program checks `scripts/OpsPrograms.lean` (E2), canonical Ops certificates and
   kernel-checked structural/accounting fixtures ([programs](docs/contributing/programs.md));
5. `scripts/check_refs.py` (citations, result ids, `Asymptotic:` and `Algorithm:` tags),
   `scripts/gen_rules_md.py --check` (the generated rule files are current),
   `scripts/check_constants.py` (named-bound values, [statements](docs/contributing/statements.md)
   §2), and `scripts/check_latex.mjs` (docstring LaTeX renders with KaTeX; skipped with a message
   if KaTeX is not installed: `npm install --no-save --no-package-lock katex@0.16.22`);
6. the declaration extraction (`scripts/Explore.lean`) and `scripts/check_rules.py` on it: every
   rule with an id, the naming rules N1–N18 included, against the ratchet
   ([checks](docs/contributing/checks.md) §1);
7. the duplicate-statement report `scripts/Duplicates.lean`, which never fails the script.

`scripts/stage_check.sh EXCLUDE_REGEX` leaves out the modules matching the regex from steps 1
and 6, for files you are still editing. CI (`.github/workflows/ci.yml`) runs the same checks on
every push and PR, and in addition the unit tests of the checks
(`python3 -m unittest discover -s scripts -p 'test_*.py'` and
`node --test scripts/test_check_latex.mjs`, also on Windows) and `mk_all --check` for
`NLAlibTools`; run the unit tests too if you touched `scripts/`.

While working, the fast checks are `lake lean <file>` and
`python3 scripts/check_rules.py --files <the files you changed>`, which checks the source-text
rules (P1, P3, P11, P12, the docstring, citation and notation rules) in seconds without a
build. Check a file with `lake lean`, not `lake env lean`, which ignores the options in
`lakefile.toml`: `autoImplicit` is then on (a typo becomes a variable) and the Mathlib linters
are off.

**When a step fails.** A build or linter failure is fixed in the source; `--wfail` makes every
warning fatal. An Audit or Replay failure means an axiom, `sorry`, `unsafe` or `partial` constant
reached the library ([proofs](docs/contributing/proofs.md)). A `mk_all` failure: run
`lake exe mk_all --module --lib NLAlib`. A freshness failure: rebuild. A fixed-program check failure concerns computability, canonical
Ops coverage or an import of the retired execution core ([programs](docs/contributing/programs.md)).
A message of the
rules checker reads `<ID> <file>:<line> <declaration>: <what is wrong and the fix>`;
`python3 scripts/check_rules.py --list` prints every id.

**The pull request.** The description contains a read-back: for each headline theorem, what the
Lean statement says, written from the Lean alone (hypotheses, conclusion, degenerate cases). The
reviewer checks the read-back against the design note and the source, the names against
[naming](docs/contributing/naming.md), the hypotheses against
[statements](docs/contributing/statements.md) §3, the vocabulary against
[vocabulary](docs/contributing/vocabulary.md). A green CI plus one approving review merges; a
change to a vocabulary row or a hypothesis interface needs two. Changes to the checks, the rule
data, the allowlists, the ratchet baseline, CI and structural certification checks need a maintainer's
review (`.github/CODEOWNERS`).

Branches are named by kind: `feat/`, `fix/`, `design/`, `cleanup/`, `docs/`. A commit message
starts with the file or topic it changes and says what changed (`Krylov/CG: …`).

Mathlib bumps are their own PRs and are tagged. Releases are tagged with the Lean version they
build against (`v4.33.1-nlalib.1`).

## AI agents

The rules apply to agents unchanged. `AGENTS.md` adds the few that are specific to agents (what
they may not edit, push or register). A brief to an agent that writes or reviews library code
includes `docs/rules/DIGEST.md` whole and the `NLAlib/<Topic>/RULES.md` of each topic it
touches, so that the rules are in its context.
