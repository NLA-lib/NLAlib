import pathlib
import re
import tempfile
import unittest
from unittest.mock import patch

from scripts.ops import audit


class AuditSourceTests(unittest.TestCase):
    def test_token_boundaries_and_lines(self):
        source = '''/- ignored sorry /- nested axiom -/ -/
"ignored
multiline native_decide"
example : True := by sorry/--/trivial
set_option/- split -/
  maxHeartbeats 800000 in
example : True := by
  decide
    +native
'''
        with tempfile.TemporaryDirectory() as temp_dir:
            root = pathlib.Path(temp_dir)
            ops = root / "NLAlib" / "Ops"
            fixture = pathlib.Path("NLAlib", "Ops", "Fixture.lean")
            ops.mkdir(parents=True)
            (root / fixture).write_text(source)
            with patch.object(audit, "ROOT", root), patch.object(audit, "OPS", ops):
                self.assertEqual(audit.source_scan(), [
                    f"{fixture}:4: sorry",
                    f"{fixture}:5: raised maxHeartbeats",
                    f"{fixture}:8: decide +native",
                ])

    def test_lint_all_imports_every_scanned_module(self):
        modules = {audit.modname(path): path for path in audit.modules()}
        expected = {
            name for name in modules
            if len(name.split(".")) > 3
            and not name.startswith(("NLAlib.Ops.Logic.", "NLAlib.Ops.Tools."))
        }
        pending = ["NLAlib.Ops.Tools.LintAll"]
        reached = set()
        while pending:
            name = pending.pop()
            if name in reached:
                continue
            reached.add(name)
            source = audit.strip(modules[name].read_text(encoding="utf-8"))
            imports = re.findall(r"^ *(?:public |meta )*import +(NLAlib\.Ops\.[\w.]+)",
                                 source, re.MULTILINE)
            pending.extend(name for name in imports if name in modules)
        self.assertEqual(expected - reached, set())
