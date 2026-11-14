"""Build reuse must preserve provenance, compatibility, and workspace boundaries."""
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest

from ci_build_cache import PINS, cache_key, digest, pack, restore, select_cache


class SelectionTests(unittest.TestCase):
    def setUp(self):
        self.repo = "NLA-lib/NLAlib"
        self.sha = "a" * 40
        self.run = {"id": 42, "run_attempt": 1, "path": ".github/workflows/ci.yml",
                    "event": "push", "head_branch": "main", "head_sha": self.sha,
                    "status": "completed", "conclusion": "success",
                    "head_repository": {"full_name": self.repo}}
        self.runs = [self.run]
        self.artifacts = [{"name": "compatible-attempt-1", "expired": False}]
        self.requests = []

    def api(self, endpoint):
        self.requests.append(endpoint)
        if "/artifacts?" in endpoint:
            return {"artifacts": self.artifacts}
        return {"workflow_runs": self.runs}

    def select(self, sha=None):
        return select_cache(self.repo, "compatible", self.api, sha)

    def test_successful_main_build_is_selected(self):
        self.assertEqual(self.select(), {"run_id": 42, "run_attempt": 1,
                                        "sha": self.sha, "name": "compatible-attempt-1"})

    def test_untrusted_or_unsuccessful_runs_cannot_supply_cache(self):
        for key, value in (("event", "pull_request"), ("head_branch", "feature"),
                           ("head_repository", {"full_name": "fork/NLAlib"}),
                           ("path", ".github/workflows/other.yml"),
                           ("status", "in_progress"), ("conclusion", "failure"),
                           ("head_sha", "invalid")):
            self.runs = [dict(self.run, **{key: value})]
            self.requests = []
            with self.subTest(key=key):
                self.assertIsNone(self.select())
                self.assertFalse(any("/artifacts?" in x for x in self.requests))

    def test_expired_incompatible_and_missing_artifacts_are_cache_misses(self):
        for artifacts in ([], [{"name": "incompatible-attempt-1", "expired": False}],
                          [{"name": "compatible-attempt-1", "expired": True}]):
            self.artifacts = artifacts
            with self.subTest(artifacts=artifacts):
                self.assertIsNone(self.select())

    def test_publication_uses_only_the_checked_source_revision(self):
        self.assertIsNotNone(self.select(self.sha))
        self.assertIn("head_sha=" + self.sha, self.requests[0])
        self.assertIsNone(self.select("b" * 40))

    def test_old_artifact_from_previous_attempt_is_not_used(self):
        self.runs = [dict(self.run, run_attempt=2)]
        self.assertIsNone(self.select())

    def test_lookup_falls_back_to_an_older_successful_main_run(self):
        self.runs = [dict(self.run, id=43, conclusion="failure"), self.run]
        self.assertEqual(self.select()["run_id"], 42)

    def test_unsafe_repository_or_sha_is_rejected(self):
        with self.assertRaises(ValueError):
            select_cache("../other", "compatible", self.api)
        with self.assertRaises(ValueError):
            self.select("invalid")


class CompatibilityTests(unittest.TestCase):
    def test_pins_platform_and_configuration_invalidate_builds(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in PINS:
                (root / name).write_text(name)
            original = cache_key(root, "Linux", "X64")
            for name in PINS:
                (root / name).write_text("changed")
                self.assertNotEqual(original, cache_key(root, "Linux", "X64"))
                (root / name).write_text(name)
            self.assertNotEqual(original, cache_key(root, "Windows", "X64"))
            self.assertNotEqual(original, cache_key(root, "Linux", "ARM64"))
            # Lean edits deliberately reuse the baseline: Lake invalidates their dependents.
            (root / "Module.lean").write_text("changed source")
            self.assertEqual(original, cache_key(root, "Linux", "X64"))


@unittest.skipUnless(shutil.which("zstd") and shutil.which("tar"), "requires tar and zstd")
class ArchiveTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.build = self.source / ".lake/build/lib/lean"
        self.build.mkdir(parents=True)
        (self.build / "Module.olean").write_bytes(b"checked build")
        self.cache = self.root / "cache"
        pack(self.source, self.cache, "compatible", "a" * 40, 42, 1)
        self.dest = self.root / "dest"
        self.dest.mkdir()

    def restore(self, **kwargs):
        params = dict(key="compatible", sha="a" * 40, run_id=42, attempt=1)
        params.update(kwargs)
        restore(self.dest, self.cache, **params)

    def test_round_trip_preserves_build_outputs(self):
        self.restore()
        self.assertEqual((self.dest / ".lake/build/lib/lean/Module.olean").read_bytes(), b"checked build")

    def test_changed_bytes_are_rejected_before_any_workspace_write(self):
        with (self.cache / "build.tar.zst").open("ab") as stream:
            stream.write(b"tampered")
        with self.assertRaisesRegex(ValueError, "digest mismatch"):
            self.restore()
        self.assertFalse((self.dest / ".lake").exists())

    def test_different_source_run_attempt_or_pins_are_rejected(self):
        for values in ({"sha": "b" * 40}, {"key": "other"}, {"run_id": 43}, {"attempt": 2}):
            with self.subTest(values=values), self.assertRaisesRegex(ValueError, "provenance"):
                self.restore(**values)

    def test_existing_build_is_never_overwritten(self):
        (self.dest / ".lake/build").mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, "empty build destination"):
            self.restore()

    def test_symlink_in_pack_source_is_rejected(self):
        (self.build / "bad").symlink_to(self.root / "outside")
        with self.assertRaisesRegex(ValueError, "symlinks"):
            pack(self.source, self.cache, "compatible", "a" * 40, 42, 1)

    def test_unsafe_archive_members_cannot_escape_or_replace_sources(self):
        for name, kind in (("../escape", tarfile.REGTYPE), ("NLAlib.lean", tarfile.REGTYPE),
                           (".lake/build/../../escape", tarfile.REGTYPE),
                           (".lake/build/link", tarfile.SYMTYPE),
                           (".lake/build/link", tarfile.LNKTYPE)):
            tar_path = self.root / "bad.tar"
            with tarfile.open(tar_path, "w") as stream:
                member = tarfile.TarInfo(name)
                member.type = kind
                member.linkname = "../../../outside"
                stream.addfile(member, io.BytesIO())
            archive = self.cache / "build.tar.zst"
            subprocess.run(["zstd", "-q", "-f", str(tar_path), "-o", str(archive)], check=True)
            manifest_path = self.cache / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["archive_sha256"] = digest(archive)
            manifest_path.write_text(json.dumps(manifest))
            with self.subTest(name=name, kind=kind), self.assertRaisesRegex(ValueError, "unsafe cache member"):
                self.restore()
            self.assertFalse((self.dest / ".lake").exists())


if __name__ == "__main__":
    unittest.main()
