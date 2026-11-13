"""Regression checks for the explorer's extraction metadata."""
import copy
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from explore_metadata import add_provenance, enrich


class MetadataTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "docs").mkdir()
        (self.root / "NLAlib").mkdir()
        (self.root / "NLAlib/Example.lean").write_bytes(b"-- a source file\n")
        self.registry = self.root / "docs/constants.toml"
        self.registry.write_text('[[constant]]\nname = "NLAlib.bound"\n')
        self.data = {"modules": [{"path": "NLAlib/Example.lean"}],
                     "decls": [{"name": "NLAlib.bound"}, {"name": "NLAlib.concept"}]}

    def test_support_role_preserves_declarations_and_hashes_source(self):
        original = copy.deepcopy(self.data)
        result = enrich(self.data, self.root)
        self.assertEqual(result["decls"][0]["explorerRole"], "support")
        self.assertNotIn("explorerRole", result["decls"][1])
        self.assertEqual([d["name"] for d in result["decls"]],
                         [d["name"] for d in original["decls"]])
        self.assertEqual(result["sourceHashes"]["NLAlib/Example.lean"],
                         hashlib.sha256(b"-- a source file\n").hexdigest())

    def test_explicit_concept_override(self):
        with self.registry.open("a") as out:
            out.write('explorer_role = "concept"\n')
        self.assertEqual(enrich(self.data, self.root)["decls"][0]["explorerRole"], "concept")

    def test_invalid_role_and_missing_bound_fail(self):
        with self.registry.open("a") as out:
            out.write('explorer_role = "hidden"\n')
        with self.assertRaisesRegex(ValueError, "invalid explorer_role"):
            enrich(self.data, self.root)
        self.registry.write_text('[[constant]]\nname = "NLAlib.missing"\n')
        with self.assertRaisesRegex(ValueError, "missing from extraction"):
            enrich(self.data, self.root)

    def test_unsafe_path_fails(self):
        for path in ("../outside.lean", "/tmp/outside.lean"):
            with self.subTest(path=path):
                self.data["modules"][0]["path"] = path
                with self.assertRaisesRegex(ValueError, "unsafe module path"):
                    enrich(self.data, self.root)

    def test_dirty_preview_cannot_claim_the_base_commit_or_date(self):
        data = {"commit": "stale", "date": "stale", "sourceHashes": {"source": "hash"}}
        for status in (" M NLAlib/Example.lean", "?? NLAlib/New.lean", " D NLAlib/Old.lean"):
            with self.subTest(status=status), patch("explore_metadata.subprocess.check_output",
                                                   side_effect=["a" * 40, status]):
                result = add_provenance(copy.deepcopy(data), self.root)
                self.assertTrue(result["dirty"])
                self.assertEqual(result["base_commit"], "a" * 40)
                self.assertIsNone(result["commit"])
                self.assertIsNone(result["date"])
                self.assertEqual(result["sourceHashes"], {"source": "hash"})

    def test_clean_snapshot_uses_the_actual_commit_and_clears_preview_base(self):
        with patch("explore_metadata.subprocess.check_output",
                   side_effect=["b" * 40, "", "2026-11-13T00:00:00Z"]):
            result = add_provenance({"base_commit": "stale"}, self.root)
        self.assertFalse(result["dirty"])
        self.assertEqual(result["commit"], "b" * 40)
        self.assertEqual(result["date"], "2026-11-13T00:00:00Z")
        self.assertNotIn("base_commit", result)

    def test_generated_artifact_is_excluded_without_excluding_other_changes(self):
        with patch("explore_metadata.subprocess.check_output",
                   side_effect=["c" * 40, "?? NLAlib/New.lean"]) as git:
            result = add_provenance({}, self.root, self.root / "explore-data.json")
        self.assertTrue(result["dirty"])
        self.assertEqual(git.call_args_list[1].args[0][-3:],
                         ["--", ".", ":(exclude,literal)explore-data.json"])


if __name__ == "__main__":
    unittest.main()
