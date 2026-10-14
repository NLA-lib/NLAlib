#!/usr/bin/env python3
"""Check that every new name in docs/port/ledger.json is declared in the library.

Usage: python3 scripts/ledger_check.py
Declarations and structure fields are found textually (namespace tracking, `_root_.` prefixes), so
generated names (`Foo.mk`, `Foo.rec`) are reported as missing although they exist; anything else
reported is a ledger entry pointing at a renamed or deleted declaration. Exit status 1 if any
target is missing.
"""
import json
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
decl = re.compile(
    r"\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|public)\s+)*"
    r"(?:theorem|lemma|def|structure|abbrev|instance|class|inductive|alias)\s+([^\s:({\[]+)")
names = set()
for lib in ("NLAlib", "NLAlibScaffold"):
    for f in (root / lib).rglob("*.lean"):
        namespaces = []
        structure = None
        for line in f.read_text().splitlines():
            m = re.match(r"\s*namespace\s+(\S+)", line)
            if m:
                namespaces.append(m.group(1))
                continue
            m = re.match(r"\s*end\s+(\S+)\s*$", line)
            if m and namespaces and namespaces[-1] == m.group(1):
                namespaces.pop()
                continue
            m = decl.match(line)
            if m:
                n = m.group(1)
                full = n[7:] if n.startswith("_root_.") else ".".join(namespaces + [n])
                names.add(full)
                structure = full if re.search(r"\b(structure|class)\s", line) else None
                continue
            m = re.match(r"\s+([^\s:({\[]+)\s*:", line)
            if structure and m:
                names.add(f"{structure}.{m.group(1)}")
            elif line and not line[0].isspace():
                structure = None
ledger = json.loads((root / "docs" / "port" / "ledger.json").read_text())
missing = [(old, e["new"], e.get("stage")) for old, e in sorted(ledger.items())
           if e.get("new") and e["new"] not in names]
print(f"{len(names)} declarations found; {len(missing)} ledger targets missing")
for old, new, stage in missing:
    print(f"  [{stage}] {old} -> {new}")
sys.exit(1 if missing else 0)
