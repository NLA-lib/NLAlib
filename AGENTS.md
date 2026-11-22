# Agents working in this repository

`CONTRIBUTING.md` and the guides it links in `docs/contributing/` are the contract, for agents
as for people: read `CONTRIBUTING.md` and the guides your task touches before writing library
code, and read `docs/rules/DIGEST.md` and the `NLAlib/<Topic>/RULES.md` of each topic you touch.
For a program (anything under `NLAlib/Ops` or a file that states a routine, a certificate or a
randomized claim), read `docs/contributing/routines.md` first: it shows where each statement
lives and carries one example from the tree to the certificate report. The rules below are the
ones specific to agents.

1. **Do not change the checks.** Never edit `scripts/stage_check.sh`, the check scripts
   (`scripts/check_*.py`, `scripts/check_latex.mjs`, `scripts/*.lean`, their tests and fixtures),
   `docs/rules/rules.toml`, the allowlists `scripts/rules_allow.toml` and
   `scripts/names_allow.toml`, the ratchet `scripts/rules_baseline.json`, `.github/` (CI,
   CODEOWNERS, the PR template) or the build pins (`lakefile.toml`, `lake-manifest.json`,
   `lean-toolchain`), unless that edit is the task you were given. If a check seems wrong, or a
   false positive needs an allowlist entry, say so in your report; do not work around it.
2. **Preserve certificate scope.** Do not weaken a declared problem, operation contract or
   specification to prove a program certificate. Explain any required interface change and
   obtain maintainer review (docs/contributing/programs.md). The retired target registry is
   not used by Ops certificates.
3. **Do not commit or push unless asked to.** Keep pushes on the authorized branch.
4. **Run the checks before you report.** `lake lean <file>` (or `lake build <Module.Name>`
   when another file must import it) and
   `python3 scripts/check_rules.py --files <files>` while working; `bash scripts/stage_check.sh`
   (exit 0) before you call the work finished (CONTRIBUTING, "Pull requests and checks"). It
   includes the unit tests of the check scripts, as CI does. Run one build at a time: never
   start a build or the stage check while another is running in the checkout.
5. **Stay in scope.** Search Mathlib, then `NLAlib/`, before proving anything. Do not weaken a
   statement to make it provable, and do not add theorems, interfaces or vocabulary rows beyond your
   task; note what you saw in your report instead.
