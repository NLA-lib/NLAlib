#!/usr/bin/env python3
"""List dropped prototype declarations that prototype code outside a layer still uses.

Usage: python3 scripts/downstream_nulls.py [LAYER_DIR ...]      (default: Matrix ForMathlib)
For every ledger entry with no new counterpart, searches the prototype sources outside the given
top-level directories of ~/Documents/prove2me/lean/NLAlib for the declaration's last name
component and prints the entries that occur, with the number of uses, the files using it most and
the ledger's reason. The match is textual, so some hits are coincidences; the list is where to
look for lemmas a layer dropped that the layers above it will ask for.
"""
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

root = Path(__file__).resolve().parent.parent
proto = Path.home() / "Documents/prove2me/lean/NLAlib"
ledger = json.loads((root / "docs" / "port" / "ledger.json").read_text())
skip = set(sys.argv[1:] or ["Matrix", "ForMathlib"])
uses = defaultdict(Counter)
for f in proto.rglob("*.lean"):
    rel = f.relative_to(proto)
    if rel.parts[0] in skip or len(rel.parts) == 1:
        continue
    for word in re.findall(r"[A-Za-z_][A-Za-z0-9_'₀-₉.]*", f.read_text()):
        for part in word.split("."):
            uses[part][str(rel)] += 1
count = 0
for old, entry in sorted(ledger.items()):
    if entry.get("new"):
        continue
    short = old.split(".")[-1]
    if short in uses:
        u = uses[short]
        sites = ", ".join(f"{p} ({c})" for p, c in u.most_common(4))
        print(f"{old}\t{sum(u.values())} uses in {len(u)} files: {sites}\t"
              f"ledger note: {entry.get('note')}")
        count += 1
print(f"{count} entries", file=sys.stderr)
