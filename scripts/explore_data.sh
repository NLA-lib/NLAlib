#!/usr/bin/env bash
# Data for the explore website (nla-lib.org/explore): runs scripts/Explore.lean, then stamps the
# git commit and its date into the JSON.
#
# Usage: scripts/explore_data.sh [OUT]   (default explore-data.json; run from the repository root
# after `lake build NLAlib`). Never while another build is running (CONTRIBUTING §10).
set -euo pipefail
out="${1:-explore-data.json}"
EXPLORE_OUT="$out" LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}" \
  lake env lean -M 8000 scripts/Explore.lean
python3 - "$out" "$(git rev-parse HEAD)" "$(git show -s --format=%cI HEAD)" <<'EOF'
import json, sys
path, sha, date = sys.argv[1:]
with open(path) as f:
    data = json.load(f)
data["commit"], data["date"] = sha, date
with open(path, "w") as f:
    json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
    f.write("\n")
print(f"{path}: {len(data['modules'])} modules, {len(data['decls'])} declarations, {sha[:10]}")
EOF
