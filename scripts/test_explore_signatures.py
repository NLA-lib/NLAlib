"""The extractor must retain scoped sigma-algebras in its compact signatures."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = r'''
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
open Lean Elab Command Meta MeasureTheory
-- DELABORATORS
section
variable {Ω : Type} (m mΩ : MeasurableSpace Ω) (f : Ω → ℝ)
  (μ : @Measure Ω mΩ) (μm : @Measure Ω m)
theorem scopedStrong (h : StronglyMeasurable[m] f) : StronglyMeasurable[m] f := h
theorem scopedMeasurable (h : Measurable[m] f) : Measurable[m] f := h
theorem scopedAE (h : AEMeasurable[m] f μm) : AEMeasurable[m] f μm := h
theorem scopedAEStrong (h : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m] f μ := h
run_cmd do
  for n in [`scopedStrong, `scopedMeasurable, `scopedAE, `scopedAEStrong] do
    let sig ← liftTermElabM do pure ((← PrettyPrinter.ppSignature n).fmt.pretty 100)
    logInfo sig
end
'''


class ExploreSignatureTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('lake'), 'Lean toolchain not installed')
    def test_compact_signature_scopes_for_all_four_predicates(self):
        source = (ROOT / 'scripts/Explore.lean').read_text(encoding='utf-8')
        # Exercise the actual producer presentation rules without loading/rebuilding NLAlib.
        helpers = source.split('/-! Keep the sigma-algebra', 1)[1].split(
            '/-- Name components Lean generates', 1)[0]
        helpers = '/-! Keep the sigma-algebra' + helpers
        with tempfile.TemporaryDirectory() as tmp:
            fixture = Path(tmp) / 'ScopedSignatures.lean'
            outputs = []
            for rules in ('', helpers):
                fixture.write_text(FIXTURES.replace('-- DELABORATORS', rules), encoding='utf-8')
                out = subprocess.run(['lake', 'env', 'lean', '-DautoImplicit=false', str(fixture)],
                                     cwd=ROOT, capture_output=True, text=True, encoding='utf-8',
                                     timeout=180)
                self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
                outputs.append(out.stdout)
        for notation in ('StronglyMeasurable[m]', 'Measurable[m,',
                         'AEMeasurable[m]', 'AEStronglyMeasurable[m]'):
            self.assertNotIn(notation, outputs[0])  # Reproduce the old default omission.
            self.assertIn(notation, outputs[1])
        self.assertNotIn('@MeasureTheory.StronglyMeasurable', outputs[1])

    @unittest.skipUnless(os.environ.get('EXPLORE_SIGNATURE_DATA'),
                         'Set EXPLORE_SIGNATURE_DATA to test a fresh full extraction')
    def test_seven_audited_signatures_in_fresh_json(self):
        data = json.loads(Path(os.environ['EXPLORE_SIGNATURE_DATA']).read_text(encoding='utf-8'))
        decls = {d['name']: d for d in data['decls']}
        expected = {
            'NLAlib.measurable_tapeSigma_apply': 'Measurable[tapeSigmaQ,',
            'NLAlib.condExp_re_trace_exp_add_le': 'StronglyMeasurable[m]',
            'NLAlib.HasCondMatrixMGFBound.supermartingale_re_trace_exp': 'StronglyMeasurable[ℱ(j+1)]',
            'NLAlib.HasCondMatrixMGFBound.measureReal_exists_eigenvalue_zero_sum_ge_le':
                'StronglyMeasurable[ℱ(j+1)]',
            'NLAlib.measureReal_exists_eigenvalue_zero_sum_ge_le_freedman':
                'StronglyMeasurable[ℱ(j+1)]',
            'NLAlib.measureReal_exists_eigenvalue_zero_sum_ge_le_freedman_of_ae_le':
                'StronglyMeasurable[ℱ(j+1)]',
            'NLAlib.measureReal_exists_specNorm_sum_ge_le_freedman': 'StronglyMeasurable[ℱ(j+1)]',
        }
        for name, notation in expected.items():
            with self.subTest(name=name):
                # The bundled filtration can print with an explicit coercion to a function.
                signature = ''.join(decls[name]['signature'].split()).replace('[↑ℱ(', '[ℱ(')
                self.assertIn(notation, signature)
                self.assertTrue(decls[name]['statement'])


if __name__ == '__main__':
    unittest.main()
