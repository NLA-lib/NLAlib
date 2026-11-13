#!/usr/bin/env bash
# Stage checks on the fully proved part of the library (CONTRIBUTING, "Pull requests and checks"), usable while later
# skeletons still contain `sorry`.
#
# Usage: scripts/stage_check.sh [EXCLUDE_REGEX]
# Builds every module that `scripts/proved_modules.py` lists (minus those matching EXCLUDE_REGEX,
# for files an agent is editing) with warnings fatal (`--wfail`, as in CI), then runs the axiom
# audit and the environment linters on exactly those modules, `mk_all --check` on NLAlib (no
# module unreachable from NLAlib.lean, hence unaudited), the kernel replay (scripts/Replay.lean:
# every constant of the .olean files of every lean_lib re-checked by Lean's kernel, with the roots
# and strictness of CI, after `lake build NLAlib NLAlibTools` and the freshness
# check `lake build --no-build --rehash` of the same targets) and its fixtures
# (scripts/replay_fixtures.sh), the program checks
# (scripts/OpsPrograms.lean, E2 and fixed Ops certificate coverage), the reference check, the named-bound
# value check (scripts/check_constants.py, on the whole library), the freshness of the generated
# rule files (scripts/gen_rules_md.py --check), the rules check
# (scripts/check_rules.py, by rule id, the naming rules N1–N18 included, on an extraction of those
# modules) and the duplicate-statement report (which never fails the script). Logs go to $TMPDIR
# (default /tmp). Run from the repository root; never while another build is running.
set -euo pipefail
tmp="${TMPDIR:-/tmp}/nlalib-stage-check"
mkdir -p "$tmp"
python3 scripts/proved_modules.py | grep -v '^NLAlib$' | grep -Ev "${1:-^$}" > "$tmp/modules.txt"
sed 's/^/import /' "$tmp/modules.txt" > "$tmp/imports.txt"
echo "$(wc -l < "$tmp/modules.txt") proved modules;" \
  "$(python3 scripts/proved_modules.py bad | grep -c . || true) not yet"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake build --wfail $(tr '\n' ' ' < "$tmp/modules.txt") \
  > "$tmp/build.log" 2>&1 || { tail -30 "$tmp/build.log"; exit 1; }
echo "build: $(tail -1 "$tmp/build.log"); warnings: $(grep -c 'warning' "$tmp/build.log" || true)"
for check in Audit Lint; do
  { cat "$tmp/imports.txt"; sed '1d' "scripts/$check.lean"; } > "$tmp/$check.lean"
  if ! LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/$check.lean" > "$tmp/$check.log" 2>&1; then
    cat "$tmp/$check.log"
    exit 1
  fi
  tail -4 "$tmp/$check.log"
done
libs="NLAlib NLAlibTools"
LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" lake build $libs > "$tmp/build-all.log" 2>&1 || \
  { tail -30 "$tmp/build-all.log"; exit 1; }
lake exe mk_all --lib NLAlib --check > "$tmp/mk_all.log" 2>&1 || { cat "$tmp/mk_all.log"; exit 1; }
echo "mk_all --lib NLAlib --check: $(tail -1 "$tmp/mk_all.log")"
# freshness: the .olean files the replay reads are those of the current sources (every hash
# recomputed, none read from Lake's .hash files)
lake build --no-build --rehash $libs > "$tmp/fresh.log" 2>&1 || \
  { tail -30 "$tmp/fresh.log"; echo "stale .olean files: the replay would check old builds"; exit 1; }
echo "freshness: $(tail -1 "$tmp/fresh.log")"
# the same roots (every lean_lib) and strictness (NLAlib and what it imports) as CI
LEAN_NUM_THREADS=1 lake env lean -M 8000 scripts/Replay.lean > "$tmp/replay.log" 2>&1 || \
  { cat "$tmp/replay.log"; exit 1; }
echo "$(sed -n '/^replay:/,$p' "$tmp/replay.log" | tr -s ' \n' ' ')"
bash scripts/replay_fixtures.sh > "$tmp/replay-fixtures.log" 2>&1 || \
  { cat "$tmp/replay-fixtures.log"; exit 1; }
echo "replay fixtures: $(grep -c ': ok' "$tmp/replay-fixtures.log") verdicts as expected"
LEAN_NUM_THREADS=1 lake env lean -M 8000 scripts/OpsPrograms.lean > "$tmp/programs.log" 2>&1 || \
  { cat "$tmp/programs.log"; exit 1; }
grep '^ops programs:' "$tmp/programs.log"
python3 scripts/check_refs.py | tail -1
python3 scripts/gen_rules_md.py --check
python3 scripts/check_constants.py > "$tmp/constants.log" || { cat "$tmp/constants.log"; exit 1; }
tail -1 "$tmp/constants.log"
if node --input-type=module -e "await import('katex')" 2>/dev/null; then
  node scripts/check_latex.mjs > "$tmp/latex.log" 2>&1 || { cat "$tmp/latex.log"; exit 1; }
  tail -1 "$tmp/latex.log"
else
  echo "check_latex: skipped, KaTeX not found (npm install --no-save --no-package-lock katex@0.16.22)"
fi
{ cat "$tmp/imports.txt"; sed '1d' scripts/Explore.lean; } > "$tmp/Explore.lean"
EXPLORE_OUT="$tmp/explore-data.json" LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/Explore.lean" \
  > "$tmp/explore.log" 2>&1 || { tail -20 "$tmp/explore.log"; exit 1; }
python3 scripts/check_rules.py "$tmp/explore-data.json" --partial > "$tmp/rules.log" || \
  { cat "$tmp/rules.log"; exit 1; }
grep -v '^check_rules:' "$tmp/rules.log" || true
tail -1 "$tmp/rules.log"
{ cat "$tmp/imports.txt"; sed '1d' scripts/Duplicates.lean; } > "$tmp/Duplicates.lean"
LEAN_NUM_THREADS=1 lake env lean -M 8000 "$tmp/Duplicates.lean" > "$tmp/duplicates.log" 2>&1 || true
cat "$tmp/duplicates.log"
