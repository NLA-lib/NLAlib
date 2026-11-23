import pathlib
import unittest

from scripts import worked_instances

ROOT = pathlib.Path(__file__).resolve().parents[1]
DIR = ROOT / "NLAlib" / "Ops" / "Examples" / "WorkedInstances"


def source(name):
    return (DIR / f"{name}.lean").read_text(encoding="utf-8")


class WorkedInstanceTests(unittest.TestCase):
    """The literals of the Lean theorems are the values computed outside the library."""

    def test_vector_sum(self):
        v = worked_instances.vector_sum()
        lean = source("VectorSum")
        self.assertIn(f"st.mem.store.readBlock 2 0 3 = some {v['output']}", lean)
        self.assertIn(f"Count.original st.cost = {v['add']} • Count.one ScalarOp.add []", lean)

    def test_strided_scaling(self):
        v = worked_instances.strided_scaling()
        lean = source("Strided")
        cells = ", ".join(f"some {w}" for w in v["buffer"].strip("[]").split(", "))
        self.assertIn(f"st.mem = ⟨[[some 5], [{cells}]], 0⟩", lean)
        self.assertIn(f"Count.original st.cost = {v['mul']} • Count.one ScalarOp.mul []", lean)

    def test_dense_matvec(self):
        v = worked_instances.dense_matvec()
        lean = source("Matvec")
        self.assertIn(f".encode amat = {v['storage']}", lean)
        self.assertIn(f"st.mem.store.readBlock 2 0 2 = some {v['output']}", lean)
        self.assertEqual(v["mul"], v["lit"] * 3)
        self.assertEqual(v["add"], v["lit"] * 3)
        self.assertIn(
            f"Count.original st.cost = {v['lit']} • (Count.one (ScalarOp.lit 0) [] +\n"
            "        3 • (Count.one ScalarOp.mul [] + Count.one ScalarOp.add []))", lean)
        self.assertIn(f"st.peak = {v['scratch_cells']}", lean)

    def test_integrator(self):
        v = worked_instances.integrator()
        lean = source("Integrator")
        self.assertIn(f"st.mem.store.readBlock 1 0 2 = some {v['output']}", lean)
        self.assertEqual(v["matvec"], v["axpy"])
        self.assertIn(
            f"{v['matvec']} • (Count.one MyOperation.matvec [2, 2] + "
            "Count.one MyOperation.axpy [2])", lean)
        self.assertIn(f"st.peak = {v['scratch_cells']}", lean)

    def test_early_exit(self):
        lean = source("EarlyExit")
        for start, total in ((2, 37), (7, 81)):
            v = worked_instances.countdown(start)
            self.assertIn(f"st.mem = {v['cells']}", lean)
            self.assertIn(
                f"tallies st.cost = ({v['dec']}, {v['inc']}, {v['tests']}, {v['operand']}, "
                f"{total})", lean)


if __name__ == "__main__":
    unittest.main()
