#!/usr/bin/env python3
"""Every `[Key]` or `[Key, label]` citation in a docstring names an entry of docs/references.bib,
and every `Result: id` line is a well-formed slug. Exit 1 on the first class of failure."""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
bib = (ROOT / "docs" / "references.bib").read_text()
keys = set(re.findall(r"^@\w+\{([^,\s]+),", bib, re.M))

cite = re.compile(r"\[([A-Z][A-Za-z]+\d{4}[a-z]?)(?:,[^\]]*)?\]")
result = re.compile(r"^\s*Result:\s*(.+?)\s*$", re.M)
slug = re.compile(r"^[a-z0-9]+(-[a-z0-9]+)*$")

bad = 0
for lib in ("NLAlib", "NLAlibScaffold"):
    for path in sorted((ROOT / lib).rglob("*.lean")):
        text = path.read_text()
        for m in cite.finditer(text):
            if m.group(1) not in keys:
                print(f"{path}: unknown reference key [{m.group(1)}]")
                bad += 1
        for m in result.finditer(text):
            for rid in m.group(1).split(","):
                if not slug.match(rid.strip()):
                    print(f"{path}: malformed result id {rid.strip()!r}")
                    bad += 1
print(f"{len(keys)} bibliography keys; {bad} problems")
sys.exit(1 if bad else 0)
