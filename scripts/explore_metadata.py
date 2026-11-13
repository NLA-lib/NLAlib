#!/usr/bin/env python3
"""Add presentation roles and source fingerprints to freshly extracted explorer data.

Run through explore_data.sh after building NLAlib. Hashes let the explorer safely use a
source checkout or a release archive, including a local preview of uncommitted doc edits.
Named bounds are supporting API by default; their constants.toml entry may explicitly set
explorer_role = "concept" when the definition itself is a headline mathematical concept.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tomllib


def enrich(data, root):
    root = Path(root).resolve()
    registry = tomllib.loads((root / "docs/constants.toml").read_text())
    roles = {}
    for entry in registry.get("constant", []):
        role = entry.get("explorer_role", "support")
        if role not in {"support", "concept"}:
            raise ValueError(f"invalid explorer_role for {entry['name']}: {role!r}")
        roles[entry["name"]] = role
    names = {d["name"] for d in data["decls"]}
    missing = roles.keys() - names
    if missing:
        raise ValueError(f"registered bounds missing from extraction: {sorted(missing)}")
    for decl in data["decls"]:
        if decl["name"] in roles:
            decl["explorerRole"] = roles[decl["name"]]
    hashes = {}
    for module in data["modules"]:
        relative = Path(module["path"])
        source = (root / relative).resolve()
        if relative.is_absolute() or ".." in relative.parts or not source.is_relative_to(root):
            raise ValueError(f"unsafe module path: {relative}")
        hashes[relative.as_posix()] = hashlib.sha256(source.read_bytes()).hexdigest()
    data["sourceHashes"] = hashes
    return data


def add_provenance(data, root, artifact=None):
    """Attribute clean snapshots to a commit and dirty previews only to their base."""
    def git(*argv):
        return subprocess.check_output(["git", "-C", str(root), *argv], text=True).strip()
    head = git("rev-parse", "HEAD")
    status_args = ["status", "--porcelain", "--untracked-files=normal"]
    if artifact is not None:
        artifact = Path(artifact).resolve()
        if artifact.is_relative_to(Path(root).resolve()):
            # Extraction creates this output before metadata is stamped. Its own untracked
            # file cannot make an otherwise clean publication snapshot into a dirty preview.
            relative = artifact.relative_to(Path(root).resolve()).as_posix()
            status_args += ["--", ".", f":(exclude,literal){relative}"]
    dirty = bool(git(*status_args))
    data["dirty"] = dirty
    if dirty:
        data["base_commit"] = head
        data["commit"] = None
        data["date"] = None
    else:
        data.pop("base_commit", None)
        data["commit"] = head
        data["date"] = git("show", "-s", "--format=%cI", "HEAD")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("data", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    data = add_provenance(enrich(json.loads(args.data.read_text()), root), root, args.data)
    args.data.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n")
    snapshot = (f"working-tree preview (base {data['base_commit'][:10]})" if data["dirty"]
                else data["commit"][:10])
    print(f"{args.data}: {len(data['modules'])} modules, {len(data['decls'])} declarations, "
          f"{snapshot}")


if __name__ == "__main__":
    main()
