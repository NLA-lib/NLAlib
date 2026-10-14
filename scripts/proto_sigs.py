#!/usr/bin/env python3
"""Print the signatures of prototype declarations, one line each, grouped by module.

Usage: python3 scripts/proto_sigs.py MODULE_PREFIX [MODULE_PREFIX ...]
Reads ~/Documents/prove2me/lean/atlas/declarations.json and docs/port/ledger.json. A line starts
with `!SORRY` if the prototype declaration is unproved and with `L` if the ledger already accounts
for it, then `DEF` or `thm`, then the signature with universe and instance noise removed. This is
the reading list for a stage's design note.
"""
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

root = Path(__file__).resolve().parent.parent
atlas = json.loads((Path.home() / "Documents/prove2me/lean/atlas/declarations.json").read_text())
ledger = json.loads((root / "docs" / "port" / "ledger.json").read_text())
prefixes = sys.argv[1:]
if not prefixes:
    sys.exit(__doc__)
by_module = defaultdict(list)
for d in atlas:
    if any(d.get("module", "").startswith(p) for p in prefixes):
        by_module[d["module"]].append(d)
for module in sorted(by_module):
    decls = by_module[module]
    print(f"===== {module} ({len(decls)})")
    for d in sorted(decls, key=lambda d: d["line"]):
        sig = " ".join(d["signature"].split())
        sig = re.sub(r"\.\{[^}]*\}", "", sig)
        sig = re.sub(r"\[(Fintype|DecidableEq) [^\]]*\] ", "", sig)
        sig = re.sub(r"\{[a-zικ] : Type u_\d\} ", "", sig)
        sig = sig.replace("NLAlib.", "")
        kind = "DEF" if d["kind"] in ("def", "structure", "abbrev", "instance", "inductive",
                                      "class") else "thm"
        flags = ("!SORRY " if d.get("sorry") else "") + ("L " if d["name"] in ledger else "")
        print(f"{flags}{kind} {sig}")
