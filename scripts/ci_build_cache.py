#!/usr/bin/env python3
"""Reuse immutable build artifacts from successful main-push CI, never PR caches.

The GitHub run is the provenance boundary; the archive digest detects corruption.
Lake must subsequently build with --rehash, and all audits still run.
"""
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile

from explore_publish import github_api

PINS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml")


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def cache_key(root, runner_os, arch):
    pins = {name: digest(root / name) for name in PINS}
    key = hashlib.sha256(json.dumps(pins, sort_keys=True).encode()).hexdigest()
    return f"nlalib-build-v1-{runner_os}-{arch}-{key}"


@contextmanager
def read_archive(archive):
    """Read a zstd tar stream without depending on a platform's tar executable."""
    process = subprocess.Popen(["zstd", "-dc", str(archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=process.stdout, mode="r|") as stream:
            yield stream
        if process.wait() != 0:
            raise ValueError("cache archive decompression failed")
    finally:
        process.stdout.close()
        if process.poll() is None:
            process.terminate()
        process.wait()


def select_cache(repository, key, read_api, sha=None):
    """Only completed successful push runs of this repository's main may supply builds."""
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[\w.-]+", repository):
        raise ValueError("invalid repository")
    endpoint = f"repos/{repository}/actions/workflows/ci.yml/runs?branch=main&event=push&per_page=20"
    if sha:
        if not re.fullmatch(r"[0-9a-f]{40}", sha):
            raise ValueError("invalid source SHA")
        endpoint += f"&head_sha={sha}"
    for run in read_api(endpoint)["workflow_runs"]:
        if (run.get("path") != ".github/workflows/ci.yml" or run.get("event") != "push"
                or run.get("head_branch") != "main" or run.get("status") != "completed"
                or run.get("conclusion") != "success"
                or run.get("head_repository", {}).get("full_name") != repository
                or not re.fullmatch(r"[0-9a-f]{40}", run.get("head_sha", ""))
                or (sha and run["head_sha"] != sha)):
            continue
        attempt = run.get("run_attempt", 1)
        name = f"{key}-attempt-{attempt}"
        artifacts = read_api(f"repos/{repository}/actions/runs/{run['id']}/artifacts?per_page=100")
        for artifact in artifacts["artifacts"]:
            if artifact.get("name") == name and not artifact.get("expired", True):
                return {"run_id": run["id"], "run_attempt": attempt,
                        "sha": run["head_sha"], "name": name}
    return None


def pack(root, out, key, sha, run_id, attempt):
    build = root / ".lake/build"
    if not build.is_dir() or build.is_symlink():
        raise ValueError("missing build directory")
    for path in build.rglob("*"):
        if path.is_symlink():
            raise ValueError(f"build cache cannot contain symlinks: {path}")
    out.mkdir(parents=True, exist_ok=True)
    archive = out / "build.tar.zst"
    process = subprocess.Popen(["zstd", "-q", "-f", "-T2", "-3", "-o", str(archive)],
                               stdin=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=process.stdin, mode="w|", dereference=True) as stream:
            stream.add(build, arcname=".lake/build")
        process.stdin.close()
        if process.wait() != 0:
            raise ValueError("cache archive compression failed")
    finally:
        if not process.stdin.closed:
            process.stdin.close()
        if process.poll() is None:
            process.terminate()
        process.wait()
    (out / "manifest.json").write_text(json.dumps({
        "key": key, "sha": sha, "run_id": run_id, "run_attempt": attempt,
        "archive_sha256": digest(archive),
    }, sort_keys=True) + "\n", encoding="utf-8")


def restore(root, source, key, sha, run_id, attempt):
    manifest = json.loads((source / "manifest.json").read_text(encoding="utf-8"))
    expected = {"key": key, "sha": sha, "run_id": run_id, "run_attempt": attempt}
    if any(manifest.get(k) != v for k, v in expected.items()):
        raise ValueError("cache provenance or toolchain/configuration does not match")
    archive = source / "build.tar.zst"
    if digest(archive) != manifest.get("archive_sha256"):
        raise ValueError("cache archive digest mismatch")
    if ((root / ".lake").is_symlink() or (root / ".lake/build").exists()
            or (root / ".lake/build").is_symlink()):
        raise ValueError("restore requires an empty build destination")
    # Validate every member before extracting anything into the workspace.
    with read_archive(archive) as stream:
        for member in stream:
            path = PurePosixPath(member.name)
            if (path.is_absolute() or ".." in path.parts or path.parts[:2] != (".lake", "build")
                    or not (member.isfile() or member.isdir()) or "\\" in member.name
                    or any(":" in part for part in path.parts)):
                raise ValueError(f"unsafe cache member: {member.name}")
    with read_archive(archive) as stream:
        stream.extractall(root, filter="data")


def output(values):
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as stream:
        for name, value in values.items():
            stream.write(f"{name}={value}\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("select", "pack", "restore"))
    parser.add_argument("--directory", type=Path)
    args = parser.parse_args()
    root = Path.cwd()
    key = cache_key(root, os.environ["RUNNER_OS"], os.environ["RUNNER_ARCH"])
    if args.command == "select":
        output({"save_name": f"{key}-attempt-{os.environ['GITHUB_RUN_ATTEMPT']}"})
        try:
            found = select_cache(os.environ["GITHUB_REPOSITORY"], key, github_api,
                                 os.environ.get("SOURCE_SHA"))
        except subprocess.CalledProcessError:
            print("Build cache lookup unavailable; building from source.")
            return
        if found:
            output(found)
            print(f"Compatible build from successful main CI run {found['run_id']} ({found['sha']}).")
        else:
            print("No compatible successful-main build artifact; building from source.")
    elif args.command == "pack":
        if (os.environ["GITHUB_EVENT_NAME"] != "push" or os.environ["GITHUB_REF"] != "refs/heads/main"):
            raise ValueError("only main-push CI may publish build caches")
        if subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"]):
            raise ValueError("cannot cache outputs from a modified checkout")
        if subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() != os.environ["GITHUB_SHA"]:
            raise ValueError("checkout does not match the CI source revision")
        pack(root, args.directory.resolve(), key, os.environ["GITHUB_SHA"],
             int(os.environ["GITHUB_RUN_ID"]), int(os.environ["GITHUB_RUN_ATTEMPT"]))
    else:
        restore(root, args.directory.resolve(), key, os.environ["CACHE_SHA"],
                int(os.environ["CACHE_RUN_ID"]), int(os.environ["CACHE_RUN_ATTEMPT"]))
        print("Verified build artifact restored; Lake will rehash inputs and rebuild changes.")


if __name__ == "__main__":
    main()
