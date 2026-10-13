#!/usr/bin/env python3
"""List prototype declarations with no ledger entry.

Usage: python3 scripts/ledger_missing.py [MODULE_PREFIX ...]
Reads ~/Documents/prove2me/lean/atlas/declarations.json and docs/port/ledger.json and prints, per
prototype module whose name starts with one of the prefixes (default `NLAlib.Matrix.`), the
declarations that the ledger does not account for.
"""
import json
import sys
from collections import defaultdict
from pathlib import Path

root = Path(__file__).resolve().parent.parent
ledger = json.loads((root / "docs" / "port" / "ledger.json").read_text())
atlas = json.loads((Path.home() / "Documents/prove2me/lean/atlas/declarations.json").read_text())
prefixes = sys.argv[1:] or ["NLAlib.Matrix."]
missing = defaultdict(list)
total = 0
for d in atlas:
    if any(d["module"].startswith(p) for p in prefixes):
        total += 1
        if d["name"] not in ledger:
            missing[d["module"]].append(d["name"])
count = sum(len(v) for v in missing.values())
for mod in sorted(missing):
    print(f"{mod} ({len(missing[mod])})")
    for name in missing[mod]:
        print(f"  {name}")
print(f"{count} of {total} declarations unaccounted for")
