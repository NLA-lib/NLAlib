import pathlib
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
            ops.mkdir(parents=True)
            (ops / "Fixture.lean").write_text(source)
            with patch.object(audit, "ROOT", root), patch.object(audit, "OPS", ops):
                self.assertEqual(audit.source_scan(), [
                    "NLAlib/Ops/Fixture.lean:4: sorry",
                    "NLAlib/Ops/Fixture.lean:5: raised maxHeartbeats",
                    "NLAlib/Ops/Fixture.lean:8: decide +native",
                ])
