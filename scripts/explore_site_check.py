#!/usr/bin/env python3
"""Build the website's explorer against this checkout's declaration data.

nla-lib.org/explore is built in the repository NLA-lib/NLA-lib.github.io from the data that
`scripts/explore_data.sh` extracts here and from that repository's own metadata
(`explore/results.toml`, `explore/content/**/*.md`), which names declarations of this library.
A rename or removal here can therefore break the website's build. This script runs that build
as the website's `deploy.yml` does and reports whether it passes, and which names of the
website's metadata are not declarations of the data.

Usage (from the repository root, after `bash scripts/explore_data.sh explore-data.json`):

    python3 scripts/explore_site_check.py --data explore-data.json

Options: `--src DIR` (this checkout, default `.`), `--site DIR` (a local copy of the website
repository instead of fetching its `main`; also the environment variable `EXPLORE_SITE_DIR`),
`--site-ref REF` (default `main`), `--no-install` (use the installed PyYAML and markdown-it-py
instead of installing the website's pinned requirements into a temporary directory).

It exits 1 when the website's build fails, 2 when the check itself could not run (no network,
no pip), and 0 otherwise; names that are not declarations
but do not fail the build are listed as a warning. The fetched website code is run with a
minimal environment: no variable of the caller (no token) reaches it.
"""
import argparse
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

SITE_REPOSITORY = "NLA-lib/NLA-lib.github.io"
NAME = re.compile(r"NLAlib(?:\.[A-Za-z_][A-Za-z0-9_'!?₀-₉]*)+")
MODULE_MAP = "2026-11-ops-modules.json"


def rename_targets(maps):
    """`old -> new` of the rename maps (`[{"renames": [{"old", "new"}]}]`, in date order)."""
    step = {}
    for raw in maps:
        for entry in raw.get("renames", []):
            step[entry["old"]] = entry["new"]
    return step


def follow(name, step, names):
    """The declaration `name` is redirected to, through later renames, or `None`."""
    seen = set()
    while name in step and name not in seen:
        seen.add(name)
        name = step[name]
        if name in names:
            return name
    return None


def strip_comments(path, text):
    """TOML comment lines carry examples (`NLAlib.some_explicit_theorem`), not references."""
    if not path.endswith(".toml"):
        return text
    return "\n".join(line for line in text.splitlines() if not line.lstrip().startswith("#"))


def stale_references(texts, names, modules, step):
    """Names in the website's metadata that are not in the data.

    `texts` maps a file path to its text, `names` and `modules` are the declaration and module
    names of the data, `step` the rename table. A name that is a declaration, a module, or a
    prefix of one (a namespace or a directory of modules) is not stale. Returns
    `[(name, [files], target or None)]`, sorted.
    """
    known = set(names) | set(modules)
    prefixes = set()
    for full in known:
        parts = full.split(".")
        for i in range(1, len(parts)):
            prefixes.add(".".join(parts[:i]))
    found = {}
    for path, text in texts.items():
        for match in NAME.findall(strip_comments(path, text)):
            name = match.rstrip(".")
            if name in known or name in prefixes:
                continue
            found.setdefault(name, set()).add(path)
    return [(name, sorted(files), follow(name, step, names))
            for name, files in sorted(found.items())]


def metadata_texts(site):
    """The files of the website that name declarations: results.toml and the content pages."""
    explore = Path(site) / "explore"
    files = [explore / "results.toml"] + sorted((explore / "content").rglob("*.md"))
    return {str(f.relative_to(site)): f.read_text(encoding="utf-8", errors="replace")
            for f in files if f.is_file()}


def fetch_site(ref, target):
    """Download and unpack the website repository at `ref` into `target` (no token)."""
    url = f"https://codeload.github.com/{SITE_REPOSITORY}/tar.gz/{ref}"
    request = urllib.request.Request(url, headers={"User-Agent": "nlalib-explore-site-check"})
    with urllib.request.urlopen(request, timeout=120) as response:
        blob = response.read()
    root = Path(target).resolve()
    with tarfile.open(fileobj=io.BytesIO(blob), mode="r:gz") as archive:
        for member in archive.getmembers():
            parts = Path(member.name).parts[1:]
            if not parts or not (member.isfile() or member.isdir()):
                continue  # no links or devices from a downloaded archive
            destination = (root / Path(*parts)).resolve()
            if root != destination and root not in destination.parents:
                raise ValueError(f"unsafe path in the website archive: {member.name}")
            if member.isdir():
                destination.mkdir(parents=True, exist_ok=True)
            else:
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(archive.extractfile(member).read())


def clean_environment(home, extra_path=None):
    """The environment of the website's code: nothing of the caller's but PATH."""
    env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "HOME": str(home),
           "LANG": "C.UTF-8", "PYTHONUTF8": "1", "PYTHONDONTWRITEBYTECODE": "1"}
    if extra_path:
        env["PYTHONPATH"] = str(extra_path)
    return env


def run_build(site, data, src, work, install):
    """Run the website's explorer build as its deploy workflow does. Returns (ok, output)."""
    explore = Path(site) / "explore"
    deps = None
    if install:
        deps = Path(work) / "deps"
        installed = subprocess.run(
            [sys.executable, "-m", "pip", "install", "--quiet", "--target", str(deps),
             "-r", str(explore / "requirements.txt")], env=clean_environment(work))
        if installed.returncode != 0:
            sys.exit("explore_site_check: could not install the website's requirements "
                     "(explore/requirements.txt); with PyYAML and markdown-it-py installed, "
                     "pass --no-install")
    renames = Path(src) / "docs" / "renames"
    command = [sys.executable, "build.py", "--data", str(Path(data).resolve()),
               "--bib", str((Path(src) / "docs" / "references.bib").resolve()),
               "--src", str(Path(src).resolve()), "--out", str(Path(work) / "out")]
    if renames.is_dir():
        command += ["--renames", str(renames.resolve())]
        if (renames / MODULE_MAP).is_file():
            command += ["--module-map", str((renames / MODULE_MAP).resolve())]
    result = subprocess.run(command, cwd=explore, env=clean_environment(work, deps),
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    return result.returncode == 0, result.stdout


def report(ok, output, stale, site_label):
    """The verdict as Markdown (also the job summary)."""
    lines = [f"## Explorer build against the website's metadata ({site_label})", ""]
    last = [line for line in output.strip().splitlines() if line.strip()]
    if ok:
        lines.append("The website's explorer **builds** with this checkout's data.")
    else:
        lines += ["The website's explorer **does not build** with this checkout's data. "
                  "First error:", "", "```", last[-1] if last else "(no output)", "```", "",
                  "This check is advisory: the website's metadata can only follow a library "
                  "change. Prepare the matching change to NLA-lib/NLA-lib.github.io, merge the "
                  "library change first, then the website's "
                  "(docs/contributing/checks.md, \"The explorer build\")."]
    lines.append("")
    if stale:
        lines += [f"{len(stale)} name(s) in the website's metadata are not declarations of "
                  "this data:", "", "| Name | In | Rename map target |", "|---|---|---|"]
        for name, files, target in stale:
            shown = ", ".join(f.replace("explore/", "", 1) for f in files[:3])
            if len(files) > 3:
                shown += f", and {len(files) - 3} more"
            lines.append(f"| `{name}` | {shown} | {'`' + target + '`' if target else 'none'} |")
    else:
        lines.append("Every name in the website's metadata is a declaration of this data.")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--data", required=True, type=Path)
    parser.add_argument("--src", default=Path("."), type=Path)
    parser.add_argument("--site", type=Path, default=os.environ.get("EXPLORE_SITE_DIR") or None)
    parser.add_argument("--site-ref", default="main")
    parser.add_argument("--no-install", action="store_true")
    args = parser.parse_args()

    data = json.loads(args.data.read_text(encoding="utf-8"))
    names = {d["name"] for d in data["decls"]}
    modules = {m["name"] for m in data["modules"]}
    renames = args.src / "docs" / "renames"
    maps = [json.loads(p.read_text(encoding="utf-8")) for p in sorted(renames.glob("*.json"))] \
        if renames.is_dir() else []
    with tempfile.TemporaryDirectory(prefix="explore-site-check-") as work:
        if args.site:
            site, label = Path(args.site), f"local copy {args.site}"
        else:
            site, label = Path(work) / "site", f"{SITE_REPOSITORY}@{args.site_ref}"
            try:
                fetch_site(args.site_ref, site)
            except (OSError, ValueError, tarfile.TarError) as error:
                print(f"explore_site_check: could not fetch {label}: {error}")
                sys.exit(2)
        stale = stale_references(metadata_texts(site), names, modules, rename_targets(maps))
        ok, output = run_build(site, args.data, args.src, work, not args.no_install)
    text = report(ok, output, stale, label)
    print(text)
    if not ok:
        print("---- output of the website's build ----")
        print(output[-4000:])
    if not ok and os.environ.get("GITHUB_ACTIONS"):
        lines = [line for line in output.strip().splitlines() if line.strip()]
        print("::error title=The website's explorer does not build with this data::"
              + (lines[-1] if lines else "no output"))
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as handle:
            handle.write(text)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
