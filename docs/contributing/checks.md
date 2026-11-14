# The checks

Part of the [contributor guide](../../CONTRIBUTING.md).

## 1. The rules checker

The rule data is in `docs/rules/rules.toml`, one entry per id: area, severity, what the check
needs, scope (the whole library or topic directories), the rule in one line, the fix and the
guide section that states it. It is the single source: `scripts/check_rules.py` and `scripts/check_names.py`
take severity, messages and scope from it, and `scripts/gen_rules_md.py` generates from it
`NLAlib/<Topic>/RULES.md`, the rules of one topic with its own first, and
`docs/rules/DIGEST.md`, every error rule in one line. CI and `scripts/stage_check.sh` fail when a
generated file is stale (`--check`); a test checks that every id the guides state is in `rules.toml`
and the reverse.

`python3 scripts/check_rules.py [DATA.json]` checks every rule with an id, the naming rules
included, on the extraction that `scripts/explore_data.sh` writes from the built library (about
a minute after `lake build NLAlib`), and prints each violation as `<ID> <file>:<line>
<declaration>: <what is wrong and the fix>`. Without the extraction it checks the source-text
rules only (`--files <files>`). `scripts/check_names.py` is the naming part ([naming](naming.md)), with
`scripts/names_allow.toml` as its allowlist ([naming](naming.md) §5).

- **Errors and warnings.** An error fails CI. A warning is a heuristic too noisy to fail on (its
  message says so); `--warnings` prints them, and reviewers read them as a review list.
- **The ratchet.** Debt that existed when a rule became checked is in
  `scripts/rules_baseline.json`, a count per rule and file. A count may only fall: CI fails when it
  rises, and on any violation of a rule with no baseline entry. When a count falls the check says
  so; lower it in the same commit with `--update-baseline`, which refuses to raise a count unless
  `--force` is given. `--force` is for maintainers: a PR that raises a count says so and needs
  their approval. The baseline file itself lists what is left, by rule and file.
- **The allowlist** `scripts/rules_allow.toml` holds false positives: the rule, the declaration
  (or the file), and a reason. It is never the fix for a real violation, and a stale entry fails.
  An entry is proposed in the PR and approved by a maintainer.

## 2. Adding or changing a rule

A rule that arrives as text alone drifts; every rule that shipped with a check and a sweep has
held. So a PR that adds or changes a rule:

1. ships with its entry in `docs/rules/rules.toml` (then `python3 scripts/gen_rules_md.py`) and
   its check in `scripts/check_rules.py` (or `check_names.py`), with a fixture in
   `scripts/test_check_rules.py` that breaks it and one that keeps it, **and** with a sweep of the
   library in the same PR or the remaining count in the baseline; or it says in its text that it is
   judged by review only;
2. is checked for conflicts with the other documents that state rules: the contributing guides, `AGENTS.md`,
   `docs/design/Mathlib-deviations.md` and the headers of `docs/references.bib` and
   `docs/constants.toml` (grep the rule's key terms); a conflict is fixed in the same PR, so that
   an author cannot follow one text and break another;
3. gives the rule an id in the area's letter series, cites it in brackets where the rule is
   stated, and uses the same id in the check's messages. Ids are never reused.

## 3. The other scripts

`scripts/check_constants.py` checks the named-bound values of [statements](statements.md) §2 rule 2 and, with
`--update NAME`, rewrites them after a change to a bound. `scripts/check_refs.py` checks
citations and result ids ([docstrings](docstrings.md)), the `Asymptotic:` tags of [statements](statements.md) §2 rule 3 and the `Algorithm:` tags of
[docstrings](docstrings.md) item 4b, and counts the algorithm ids in use.

`scripts/Duplicates.lean` is a report, not a gate: it lists library theorems (private ones
included) whose statements coincide with another library or Mathlib theorem up to universe
levels, binder names, metadata and eta, confirmed by reducible `isDefEq`. A private lemma that
duplicates a public one is deleted in favour of the public one.

`scripts/Reuse.lean` lists, for each declaration named in `scripts/reuse_targets.txt` (or every
public theorem of a `module M` line), the NLAlib and Mathlib constants its proof uses directly,
grouped by module. Run it on a PR's headline theorems to check that they are proved from the
library's API for their topic rather than re-derived.

`scripts/OpsPrograms.lean` checks computability of fixed Ops programs and inventories canonical
algorithm certificates. It rejects imports of the retired execution core. Structural rejection
and accounting regressions are kernel-checked modules in `NLAlib/Ops/Examples/Certification.lean`
and `NLAlib/Ops/Tools/ProgramFixtures.lean`; the whole-library audit and replay cover them.
The former E3–E6 and E8–E9 registry/syntax rules are retired, and their identifiers are not reused.

## CI build reuse

CI reuses compiled modules through immutable Actions artifacts, selected by
`scripts/ci_build_cache.py`. Only a completed, successful push CI run on this repository's
`main` can supply an artifact; PR and feature-branch runs cannot publish reusable builds.
The cache identity includes the runner OS and architecture, Lean toolchain, dependency
manifest and Lake configuration. Restore verifies the producing run, attempt and source
revision, the compressed archive's SHA-256, and its extraction paths before installing it.
The producing checkout must be clean and match its CI revision.

Lake then runs with `--rehash`: unchanged modules are reused, while edited modules and their
dependents rebuild. All axiom audits, environment linters, certificate checks, freshness
checks and full kernel replay still run. General branch-scoped `.lake` caching remains off:
Lake traces alone cannot bind arbitrary restored output bytes to the current source.
Here that binding comes from the authenticated successful-main producer and the verified
immutable artifact, including when a later run reuses a build that producer had itself reused.

Builds are saved after every Linux CI check passes, retained for one day, and consumed only
after the entire producing CI run succeeds. Missing, expired or unavailable artifacts fall
back to a normal build; malformed artifacts fail verification. The first successful main run
seeds the cache. Explorer publication reuses the artifact for its exact approved source
revision, then rebuilds with rehashing and checks freshness before extraction. Its existing
current-main and successful-CI publication gates remain mandatory.

## Environment-linter compatibility

`scripts/Lint.lean` runs the complete standard environment-linter set on imported NLAlib
modules. Its `simpNF` adapter recognizes a narrow compiler artifact: a constructor's generated
`injEq` theorem whose two equality propositions have definitionally equal operands. This occurs
when an operation constructor wraps a singleton tag. Recognition uses constructor metadata and
reduction, without a declaration allowlist or changes to the library's simp attributes.
Ordinary constructor injectivity facts and every user-authored theorem retain the upstream
`simpNF` check. The script runs regressions on each invocation: generated singleton facts pass,
ordinary generated injectivity facts remain checked, an authored theorem with the same redundant
statement is rejected, and a duplicate user simp theorem is rejected. The checker support and
fixtures are separate from the imported library declarations being audited.

The source and extraction scans distinguish structural errors from review clues. Missing
subject vocabulary [P9], printer-hidden proof terms [T9], and underscore hypothesis names [T13]
remain visible as warnings: none alone establishes misplaced mathematics, hidden assumptions,
or an unused hypothesis. Review the declaration and its API before changing it. Reliable checks
such as import-layer restrictions and executable-program certification remain errors; review
warnings are not exemptions from those checks.
