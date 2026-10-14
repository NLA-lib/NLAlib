#!/usr/bin/env python3
"""Add entries to docs/port/ledger.json.

Usage: python3 scripts/ledger_add.py STAGE < entries.txt
Each input line is `old -> new` or `old -> null (reason)`. `old` is the prototype's full name as
in atlas/declarations.json (with its `NLAlib.` prefix: `scripts/ledger_missing.py` looks keys up
that way); `new` is the full new name.
"""
import json
import re
import sys
from pathlib import Path

path = Path(__file__).resolve().parent.parent / "docs" / "port" / "ledger.json"
ledger = json.loads(path.read_text())
stage = sys.argv[1]
n = 0
for line in sys.stdin:
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    m = re.match(r"^(\S+)\s*(?:->|→)\s*(\S+)\s*(?:\((.*)\))?\s*$", line)
    if not m:
        sys.exit(f"cannot parse: {line}")
    old, new, note = m.group(1), m.group(2), m.group(3)
    entry = {"new": None if new == "null" else new, "stage": stage}
    if note:
        entry["note"] = note
    ledger[old] = entry
    n += 1
path.write_text(json.dumps(ledger, indent=1, ensure_ascii=False, sort_keys=True) + "\n")
print(f"{n} entries added; {len(ledger)} total")
