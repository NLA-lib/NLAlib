#!/usr/bin/env python3
"""List the NLAlib modules that are fully proved, for checks on a library still under way.

Usage: python3 scripts/proved_modules.py [bad] [--imports]
A module is listed if neither it nor any NLAlib module it imports, directly or not, contains
`sorry` outside comments. With `bad`, the complement is listed. With `--imports`, each line is
printed as `import <module>`: prefix that list to `scripts/Audit.lean` or `scripts/Lint.lean`
minus their first line to audit or lint the proved part only, as `scripts/stage_check.sh` does.
"""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
mods = {}
for f in sorted((root / "NLAlib").rglob("*.lean")):
    name = ".".join(f.relative_to(root).with_suffix("").parts)
    text = f.read_text()
    imports = re.findall(r"^(?:public )?import (NLAlib\.\S+)", text, re.M)
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    code = re.sub(r"--.*", "", code)
    mods[name] = (imports, bool(re.search(r"\bsorry\b", code)))
bad = {m for m, (_, has_sorry) in mods.items() if has_sorry}
changed = True
while changed:
    changed = False
    for m, (imports, _) in mods.items():
        if m not in bad and any(i in bad for i in imports):
            bad.add(m)
            changed = True
args = sys.argv[1:]
chosen = sorted(bad) if "bad" in args else sorted(m for m in mods if m not in bad)
prefix = "import " if "--imports" in args else ""
print("\n".join(prefix + m for m in chosen))
