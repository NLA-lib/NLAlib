#!/usr/bin/env python3
"""Add ledger entries from the `Port of` lines of docstrings.

Usage: python3 scripts/ledger_from_ports.py STAGE FILE [FILE ...]
For every declaration in FILE whose docstring says "Port of `Old.name`" (several names allowed),
record `Old.name -> New.name` in docs/port/ledger.json, unless the old name already has an entry
or is not a prototype declaration. New names are resolved through `namespace` lines and the
`_root_.` prefix. Prints what was added and what was skipped.
"""
import json
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
ledger_path = root / "docs" / "port" / "ledger.json"
ledger = json.loads(ledger_path.read_text())
atlas = json.loads((Path.home() / "Documents/prove2me/lean/atlas/declarations.json").read_text())
proto = {d["name"] for d in atlas}
stage = sys.argv[1]
decl_re = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |nonrec )*"
    r"(theorem|lemma|def|structure|abbrev|instance|class|inductive)\s+(\S+)")
added = skipped = 0
for fname in sys.argv[2:]:
    text = Path(fname).read_text()
    ns = []
    doc = None
    i = 0
    lines = text.split("\n")
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            ns.append(m.group(1))
        m = re.match(r"^end\s+(\S+)", line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
        if line.startswith("/--"):
            j = i
            buf = []
            while j < len(lines):
                buf.append(lines[j])
                if "-/" in lines[j]:
                    break
                j += 1
            doc = "\n".join(buf)
            i = j + 1
            continue
        m = decl_re.match(line)
        if m and doc is not None:
            name = m.group(2)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join(ns + [name])
            olds = []
            for chunk in re.findall(r"Ports? of ((?:`[^`]+`(?:,| and|, and)?\s*)+)", doc):
                olds += re.findall(r"`([^`]+)`", chunk)
            for old in olds:
                cands = [old] if old in proto else []
                if not cands and ("NLAlib." + old) in proto:
                    cands = ["NLAlib." + old]
                for o in cands:
                    if o in ledger:
                        skipped += 1
                    else:
                        ledger[o] = {"new": full, "stage": stage}
                        added += 1
                        print(f"  {o} -> {full}")
                if not cands:
                    print(f"  ?? not a prototype declaration: {old} (at {full})")
            doc = None
        elif line.strip() and not line.startswith("@[") and not line.startswith("open ") \
                and not line.startswith("omit ") and not line.startswith("variable"):
            if not line.startswith(" "):
                doc = None if not line.startswith("/--") else doc
        i += 1
ledger_path.write_text(json.dumps(ledger, indent=1, ensure_ascii=False, sort_keys=True))
print(f"{added} added, {skipped} already present; {len(ledger)} total")
