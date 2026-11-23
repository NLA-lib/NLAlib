"""The scan of the website's metadata lists exactly the names that are not in the data."""
import unittest

from explore_site_check import (clean_environment, follow, rename_targets, report,
                                stale_references)


class StaleReferenceTests(unittest.TestCase):
    names = {"NLAlib.MGS.factorProgram", "NLAlib.Ops.Inputs.problem", "NLAlib.weyl"}
    modules = {"NLAlib.Matrix.Norms.Basic", "NLAlib.Ops.RoutineProblem"}
    step = rename_targets([
        {"renames": [{"old": "NLAlib.MGS.program", "new": "NLAlib.MGS.factorProg"}]},
        {"renames": [{"old": "NLAlib.MGS.factorProg", "new": "NLAlib.MGS.factorProgram"},
                     {"old": "NLAlib.gone", "new": "NLAlib.alsoGone"}]}])

    def scan(self, texts):
        return stale_references(texts, self.names, self.modules, self.step)

    def test_declarations_modules_and_prefixes_are_not_stale(self):
        text = ("`NLAlib.weyl`, `NLAlib.Matrix.Norms.Basic`, the directory NLAlib.Matrix.Norms, "
                "the namespace NLAlib.Ops.Inputs, and NLAlib.MGS.factorProgram.")
        self.assertEqual(self.scan({"explore/content/a.md": text}), [])

    def test_stale_names_carry_their_files_and_rename_target(self):
        found = self.scan({"explore/results.toml": 'primary = "NLAlib.MGS.program"',
                           "explore/content/a.md": "NLAlib.MGS.program and `NLAlib.gone`",
                           "explore/content/b.md": "NLAlib.neverExisted"})
        self.assertEqual(found, [
            ("NLAlib.MGS.program", ["explore/content/a.md", "explore/results.toml"],
             "NLAlib.MGS.factorProgram"),
            ("NLAlib.gone", ["explore/content/a.md"], None),
            ("NLAlib.neverExisted", ["explore/content/b.md"], None)])

    def test_toml_comments_are_examples(self):
        text = '#   primary = "NLAlib.some_explicit_theorem"\n[weyl]\nprimary = "NLAlib.weyl"\n'
        self.assertEqual(self.scan({"explore/results.toml": text}), [])
        self.assertEqual(len(self.scan({"explore/content/a.md": text})), 1)

    def test_rename_chains_stop_at_a_declaration_and_at_cycles(self):
        self.assertEqual(follow("NLAlib.MGS.program", self.step, self.names),
                         "NLAlib.MGS.factorProgram")
        self.assertIsNone(follow("NLAlib.gone", self.step, self.names))
        cycle = {"A": "B", "B": "A"}
        self.assertIsNone(follow("A", cycle, set()))

    def test_report_states_the_verdict_and_the_procedure(self):
        failing = report(False, "Traceback\nValueError: primary declaration X is absent\n",
                         [("NLAlib.gone", ["explore/content/a.md"], None)], "site@main")
        self.assertIn("does not build", failing)
        self.assertIn("ValueError: primary declaration X is absent", failing)
        self.assertIn("merge the library change first", failing)
        self.assertIn("| `NLAlib.gone` | content/a.md | none |", failing)
        passing = report(True, "", [], "site@main")
        self.assertIn("**builds**", passing)
        self.assertIn("Every name", passing)

    def test_the_website_code_sees_no_caller_variable(self):
        env = clean_environment("/tmp/home", "/tmp/deps")
        self.assertEqual(set(env), {"PATH", "HOME", "LANG", "PYTHONUTF8",
                                    "PYTHONDONTWRITEBYTECODE", "PYTHONPATH"})


if __name__ == "__main__":
    unittest.main()
