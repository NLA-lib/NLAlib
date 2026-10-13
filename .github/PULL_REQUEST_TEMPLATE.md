## What this adds

<!-- One topic per PR. Name the file(s) and the headline statements. -->

## Read-back

<!-- For each headline theorem: what the Lean statement says, written from the Lean alone
     (hypotheses, conclusion, degenerate cases). A reviewer checks this against the source. -->

## Checklist

- [ ] `LEAN_NUM_THREADS=4 lake build NLAlib NLAlibScaffold` passes with no new warnings
- [ ] `lake env lean scripts/Audit.lean` reports 0 violations
- [ ] `lake env lean scripts/Lint.lean` is clean for the touched files
- [ ] `python3 scripts/check_refs.py` passes; new sources are in `docs/references.bib`
- [ ] `lake exe mk_all --lib NLAlib --check` passes
- [ ] Every public declaration has a docstring with source and label; no theorem is named after a source
- [ ] Ported material: `docs/port/ledger.json` updated with old name → new name
