#!/usr/bin/env python3
"""Audit of the new core NLAlib/Ops (tooling plan §3).

1. Source scan of NLAlib/Ops/**/*.lean (comments and strings removed): `sorry`, `admit`,
   `native_decide`, `decide +native`, `set_option maxHeartbeats` / `maxRecDepth`
   / `synthInstance.maxHeartbeats`, `implemented_by`, `extern`, `unsafe`, `axiom`.
2. Environment scan (scripts/ops/Audit.lean with every NLAlib.Ops module imported): axioms of
   every constant only propext / Classical.choice / Quot.sound, no unsafe/partial, no
   implemented_by.
3. Per-file elaboration time (`lake env lean <file>`, one process at a time, gated); skip with
   --no-times.

Exit status: nonzero on any violation. Run from the repository root:
    python3 scripts/ops/audit.py [--no-times]
Lean runs through scripts/ops/lean_gated.sh (one Lean process, workers slice, 2 threads).
"""
import pathlib
import re
import subprocess
import sys
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parents[2]
OPS = ROOT / "NLAlib" / "Ops"
GATE = [str(ROOT / "scripts" / "ops" / "lean_gated.sh")]

FORBIDDEN = [
    (r"\bsorry\b", "sorry"), (r"\badmit\b", "admit"), (r"\bnative_decide\b", "native_decide"),
    (r"decide\s*\+native", "decide +native"),
    (r"set_option\s+(synthInstance\.)?maxHeartbeats", "raised maxHeartbeats"),
    (r"set_option\s+maxRecDepth", "raised maxRecDepth"),
    (r"\bimplemented_by\b", "implemented_by"), (r"@\[\s*extern", "extern"),
    (r"^[ \t]*(private\s+|protected\s+)?unsafe\b", "unsafe"), (r"^[ \t]*axiom\b", "axiom"),
]


def strip(src: str) -> str:
    """Remove nested block comments, line comments and string literals, keeping line breaks."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            out.append(" ")
            i = n if j < 0 else j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('"' + "\n" * src.count("\n", i, j) + '"')
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def modules():
    return sorted(OPS.rglob("*.lean"))


def modname(p: pathlib.Path) -> str:
    return ".".join(p.relative_to(ROOT).with_suffix("").parts)


def source_scan():
    bad = []
    for p in modules():
        source = strip(p.read_text())
        findings = sorted((m.start(), what) for pat, what in FORBIDDEN
                          for m in re.finditer(pat, source, re.MULTILINE))
        for offset, what in findings:
            line = source.count("\n", 0, offset) + 1
            bad.append(f"{p.relative_to(ROOT)}:{line}: {what}")
    return bad


def env_scan():
    mods = [modname(p) for p in modules()]
    build = subprocess.run(GATE + ["lake", "build", "--wfail"] + mods, cwd=ROOT, capture_output=True,
                           text=True)
    if build.returncode != 0:
        return False, build.stdout[-3000:] + build.stderr[-3000:]
    body = (ROOT / "scripts" / "ops" / "Audit.lean").read_text()
    with tempfile.TemporaryDirectory(prefix="nlalib-ops-audit-") as temp_dir:
        probe = pathlib.Path(temp_dir) / "Audit.lean"
        probe.write_text("".join(f"import {m}\n" for m in mods) + "\n" + body)
        result = subprocess.run(GATE + ["lake", "env", "lean", str(probe)], cwd=ROOT,
                                capture_output=True, text=True)
    return result.returncode == 0, (result.stdout + result.stderr).strip()


def times():
    rows = []
    for p in modules():
        t = time.monotonic()
        r = subprocess.run(GATE + ["lake", "env", "lean", str(p.relative_to(ROOT))], cwd=ROOT,
                           capture_output=True, text=True)
        rows.append((p.relative_to(OPS), time.monotonic() - t, r.returncode))
    return rows


def main():
    ok = True
    bad = source_scan()
    print(f"## Source scan: {len(modules())} files, {len(bad)} violations")
    for b in bad:
        print("  " + b)
    ok &= not bad
    env_ok, out = env_scan()
    print("## Environment scan")
    print("  " + "\n  ".join(out.splitlines()[-40:]))
    ok &= env_ok
    if "--no-times" not in sys.argv:
        rows = times()
        print("## Elaboration time (s), `lake env lean`, 2 threads")
        print("| file | s | exit |\n|---|---|---|")
        for f, s, rc in rows:
            print(f"| {f} | {s:.1f} | {rc} |")
            ok &= rc == 0
        print(f"| total | {sum(r[1] for r in rows):.1f} | |")
    print("AUDIT", "PASSED" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
