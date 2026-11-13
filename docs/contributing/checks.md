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

The extractor's `signature` is a compact elaborated presentation, not a lossless serialization of
Lean expressions. Local delaborators preserve explicit sigma-algebras in `Measurable`,
`StronglyMeasurable`, `AEMeasurable` and `AEStronglyMeasurable`, including non-ambient filtrations.
Raw JSON consumers should also use `statement` (source syntax in its module context); other
implicit arguments can still be hidden by pretty printing. `test_explore_signatures.py` checks
all four predicates against the default printer. With `EXPLORE_SIGNATURE_DATA` pointing to a
fresh extraction, it also checks the seven declarations identified in the 2026-11 audit.

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
