#!/usr/bin/env python3
"""Regressions for scripts/check_names.py (docs/contributing/naming.md): one passing and one failing name per
checked rule, on hand-written declarations in the extraction format."""
import json
import tempfile
import unittest
from pathlib import Path

from check_names import SEVERITY, check, derived_asymptotic, main, record


def thm(name, sig, doc='', module='NLAlib.Probability.Tail'):
    return {'name': name, 'kind': 'theorem', 'module': module, 'signature': f'{name} {sig}', 'doc': doc}


def defn(name, sig, module='NLAlib.Matrix.Norms.Spectral'):
    return {'name': name, 'kind': 'def', 'module': module, 'signature': f'{name} {sig}', 'doc': ''}


# library definitions the checks look up (function tokens, power arguments)
LIB = [defn('NLAlib.singularValues', '(A : Matrix m n 𝕜) : ℕ → ℝ'),
       defn('NLAlib.frobNorm', '(A : Matrix m n 𝕜) : ℝ'),
       defn('NLAlib.hutchpp', '(A : Matrix n n 𝕜) (S : Matrix n s 𝕜) (G : Matrix n t 𝕜) : 𝕜'),
       defn('NLAlib.rsvd', '(A : Matrix m n 𝕜) (X : Matrix n l 𝕜) : Matrix m n 𝕜')]


def rules(*decls, registered=()):
    return {(r, n) for r, n, _ in check(list(LIB) + list(decls), registered)}


class GenericFunctionNotationTests(unittest.TestCase):
    def test_zero_function_does_not_hide_zero_numeral(self):
        zero = defn('NLAlib.Computation.StaticCost.zero', ': StaticCost P i')
        for sig in [': f x = 0', '(h : x = 0) : f x = 0']:
            d = thm('NLAlib.f_eq_zero', sig)
            self.assertNotIn(('N4', d['name']), rules(zero, d))
        for sig in [': f x = 1', ': f x = 10', ': f x = x0']:
            d = thm('NLAlib.f_eq_zero', sig)
            self.assertIn(('N4', d['name']), rules(zero, d))
        d = thm('NLAlib.f_eq_of_zero', '(h : x = 0) : f x = y')
        self.assertNotIn(('N4', d['name']), rules(zero, d))

    def test_branch_function_accepts_conditional_notation(self):
        branch = defn('NLAlib.Computation.StaticCost.branch', ': StaticCost P i')
        good = thm('NLAlib.exec_branch_eq', ': exec I (ifThenElse p c x y t e).run st = z')
        bad = thm('NLAlib.exec_branch_eq', ': exec I t st = z')
        self.assertNotIn(('N4', good['name']), rules(branch, good))
        self.assertIn(('N4', bad['name']), rules(branch, bad))

    def test_zero_numeral_after_power_is_not_a_function_argument(self):
        zero = defn('NLAlib.Computation.StaticCost.zero', ': StaticCost P i')
        good = thm('NLAlib.eval_comp_X_sq_zero', ': (p.comp (X ^ 2)).eval 0 = 1')
        bad = thm('NLAlib.sq_zero', ': zero x ^ 2 = y')
        self.assertNotIn(('N6', good['name']), rules(zero, good))
        self.assertIn(('N6', bad['name']), rules(zero, bad))


class TailTests(unittest.TestCase):
    def test_prefix_follows_statement(self):
        sig = '(h : HasFoo X μ) : μ.real {ω | b < frobNorm (X ω)} ≤ δ'
        self.assertIn(('N14', 'NLAlib.HasFoo.measure_frobNorm_gt_le'),
                      rules(thm('NLAlib.HasFoo.measure_frobNorm_gt_le', sig)))
        self.assertFalse(rules(thm('NLAlib.HasFoo.measureReal_frobNorm_gt_le', sig)))

    def test_scalar_event_is_positive(self):
        bad = thm('NLAlib.measureReal_not_frobNorm_le_le', ': μ.real {ω | ¬frobNorm (X ω) ≤ b} ≤ δ')
        self.assertIn(('N15', bad['name']), rules(bad))
        loewner = thm('NLAlib.measureReal_not_smul_one_le_conjTranspose_mul_self_le',
                      ': μ.real {ω | ¬a • 1 ≤ (X ω)ᴴ * X ω} ≤ δ')
        self.assertFalse({r for r in rules(loewner) if r[0] == 'N15'})

    def test_subject_first_and_two_relations(self):
        sig = ': μ.real {ω | c * b ≤ frobNorm (X ω)} ≤ δ'
        self.assertIn(('N15', 'NLAlib.measureReal_mul_le_frobNorm_le'),
                      rules(thm('NLAlib.measureReal_mul_le_frobNorm_le', sig)))
        self.assertIn(('N15', 'NLAlib.measureReal_frobNorm_le'),
                      rules(thm('NLAlib.measureReal_frobNorm_le', sig)))
        self.assertFalse(rules(thm('NLAlib.measureReal_frobNorm_ge_le', sig)))

    def test_variable_subject_has_no_token(self):
        sig = ': μ.real {ω | ∫ (ω\' : Ω), f (X ω\') ∂μ + t ≤ f (X ω)} ≤ δ'
        self.assertFalse(rules(thm('NLAlib.measureReal_ge_integral_add_le', sig)))


class ShapeTests(unittest.TestCase):
    def test_power_after_argument(self):
        sig = '(A : Matrix m n 𝕜) (k : ℕ) : singularValues A k ^ 2 = eigenvalue (Aᴴ * A) k'
        self.assertIn(('N6', 'NLAlib.sq_singularValues'), rules(thm('NLAlib.sq_singularValues', sig)))
        self.assertFalse({r for r in rules(thm('NLAlib.singularValues_sq', sig)) if r[0] == 'N6'})

    def test_error_is_exact_minus_computed(self):
        bad = thm('NLAlib.hutchpp_sub_trace', ': hutchpp A S G - A.trace = 0')
        good = thm('NLAlib.trace_sub_hutchpp', ': A.trace - hutchpp A S G = 0')
        self.assertIn(('N10', bad['name']), rules(bad))
        self.assertFalse({r for r in rules(good) if r[0] == 'N10'})
        krylov = thm('NLAlib.cgIterate_sub_mem_krylovSpace', ': cgIterate A b x q - x ∈ krylovSpace A b q')
        self.assertFalse({r for r in rules(krylov) if r[0] == 'N10'})

    def test_relation_before_hypotheses(self):
        sig = '(h : HasLaw ε (rademacherVector n) ν) : Var[fun ω ↦ quadForm A (ε ω); ν] ≤ v'
        self.assertIn(('N3', 'NLAlib.variance_quadForm_of_hasLaw_rademacherVector_le'),
                      rules(thm('NLAlib.variance_quadForm_of_hasLaw_rademacherVector_le', sig)))
        self.assertFalse(rules(thm('NLAlib.variance_quadForm_le_of_hasLaw_rademacherVector', sig)))

    def test_head_first(self):
        sig = ': (Polynomial.X - Polynomial.C μ) * A.charpoly = B.charpoly'
        self.assertIn(('N2', 'NLAlib.charpoly_mul_eq'), rules(thm('NLAlib.charpoly_mul_eq', sig)))
        self.assertFalse(rules(thm('NLAlib.X_sub_C_mul_charpoly_eq', sig)))

    def test_synonyms(self):
        sig = ': f (intrinsicDimension A) ≤ 1'
        self.assertIn(('N5', 'NLAlib.foo_intrinsicDim_le'), rules(thm('NLAlib.foo_intrinsicDim_le', sig)))
        sig = ': (rangeProjector A).mulVecLin.range = A.mulVecLin.range'
        self.assertIn(('N5', 'NLAlib.range_mulVecLin_rangeProjector'),
                      rules(thm('NLAlib.range_mulVecLin_rangeProjector', sig)))

    def test_case(self):
        self.assertIn(('N1', 'NLAlib.foo_bar'), rules(defn('NLAlib.foo_bar', '(A : Matrix m n 𝕜) : ℝ')))

    def test_law_suffix(self):
        sig = '(hX : HasLaw X (gaussianMatrix n l) μ) : ∫ (ω : Ω), frobNorm (X ω) ^ 2 ∂μ = c'
        self.assertIn(('N9', 'NLAlib.integral_frobNorm_sq'), rules(thm('NLAlib.integral_frobNorm_sq', sig)))
        self.assertFalse(rules(thm('NLAlib.integral_frobNorm_sq_of_hasLaw_gaussianMatrix', sig)))

    def test_mean_square_has_sq(self):
        sig = '(hX : HasLaw X (gaussianMatrix n l) μ) : ∫ (ω : Ω), frobNorm (X ω) ^ 2 ∂μ ≤ c'
        self.assertIn(('N13', 'NLAlib.integral_frobNorm_le_of_hasLaw_gaussianMatrix'),
                      rules(thm('NLAlib.integral_frobNorm_le_of_hasLaw_gaussianMatrix', sig)))

    def test_bound_suffixes(self):
        size = defn('NLAlib.countSketchRows', '(d : ℕ) (ε δ : ℝ) : ℝ', module='NLAlib.Sketching.Sparse.X')
        self.assertIn(('N16', size['name']), rules(size, registered={size['name']}))
        dim = defn('NLAlib.countSketchEmbeddingDim', '(d : ℕ) (ε δ : ℝ) : ℝ', module='NLAlib.Sketching.X')
        self.assertFalse(rules(dim, registered={dim['name']}))


class AsymptoticTests(unittest.TestCase):
    def test_derivation(self):
        tgt = record(thm('NLAlib.integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix',
                         ': ∫ (ω : Ω), specNorm (A - rbki A (X ω)) ^ 2 ∂μ ≤ c'))
        self.assertEqual(derived_asymptotic(tgt),
                         'exists_forall_integral_specNorm_sub_rbki_sq_le_of_singularGapRatio_pos_of_hasLaw_gaussianMatrix')
        tgt = record(thm('NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le',
                         ': IsObliviousSubspaceEmbedding S d ε δ μ'))
        self.assertEqual(derived_asymptotic(tgt),
                         'exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_countSketch')


class IndexHeadTests(unittest.TestCase):
    def test_getelem_head(self):
        from leanexpr import head_candidates
        self.assertIn('getElem?', head_candidates('s.shape[b]?'))
        self.assertIn('getElem', head_candidates('x[i]'))
        self.assertIn('getElem', head_candidates('x[i]!'))
        self.assertNotIn('getElem', head_candidates('x.shape'))


class NamingBoundaryTests(unittest.TestCase):
    def test_generated_parser_names_are_not_data_api_names(self):
        for name in ['Parser.Attr.storeNF_proc', 'NLAlib.Ops.«opsIdx_+_»',
                     'NLAlib.Ops.tacticLoop_inv___With___']:
            for ty in ['ParserDescr', 'TrailingParserDescr', 'Lean.ParserDescr']:
                d = defn(name, ': ' + ty)
                self.assertNotIn(('N1', name), rules(d))
        ordinary = defn('NLAlib.bad_data_name', ': List ℕ')
        self.assertIn(('N1', ordinary['name']), rules(ordinary))

    def test_type_universe_expressions_and_predicate_components(self):
        for sig in [': Type (max u v)', ': Sort (u + 1)', ': ℕ → Type u']:
            d = defn('NLAlib.Family', sig)
            self.assertNotIn(('N1', d['name']), rules(d))
        for name in ['NLAlib.Model.admissible', 'NLAlib.Model.contracts', 'NLAlib.Model.Safe']:
            d = defn(name, '(x : ℕ) : Prop')
            self.assertNotIn(('N1', d['name']), rules(d))
        d = defn('NLAlib.WrongData', ': ℕ')
        self.assertIn(('N1', d['name']), rules(d))
        d = thm('NLAlib.WrongTheorem', ': x = x')
        self.assertIn(('N1', d['name']), rules(d))

    def test_subject_rules_respect_declared_module_scope(self):
        name = 'NLAlib.levelSampleSize'
        inside = defn(name, ': ℕ', module='NLAlib.Sketching.Gaussian')
        outside = defn(name, ': ℕ', module='NLAlib.Eigensolvers.SpectralBisection.Samples')
        sibling = defn(name, ': ℕ', module='NLAlib.SketchingExtra.Example')
        self.assertIn(('N16', name), rules(inside, registered={name}))
        self.assertNotIn(('N16', name), rules(outside, sibling, registered={name}))

    def test_semantic_findings_are_visible_review_warnings(self):
        cases = [
            ('N2', thm('NLAlib.charpoly_mul_eq',
                        ': (Polynomial.X - Polynomial.C μ) * A.charpoly = B.charpoly')),
            ('N3', thm('NLAlib.bound_of_condition_le', '(h : P) : f x ≤ c')),
            ('N4', thm('NLAlib.frobNorm_eq', ': f x = y')),
            ('N6', thm('NLAlib.sq_singularValues', ': singularValues A k ^ 2 = v')),
        ]
        for rid, decl in cases:
            with self.subTest(rule=rid):
                self.assertIn((rid, decl['name']), rules(decl))
                self.assertEqual(SEVERITY[rid], 'warning')
                with tempfile.TemporaryDirectory() as tmp:
                    data, allow = Path(tmp) / 'data.json', Path(tmp) / 'allow.toml'
                    data.write_text(json.dumps({'decls': LIB + [decl]}))
                    allow.write_text('')
                    self.assertEqual(main([str(data), '--allow', str(allow), '--only', rid]), 0)
        self.assertEqual(SEVERITY['N1'], 'error')
        self.assertEqual(SEVERITY['N5'], 'error')


class AllowlistTests(unittest.TestCase):
    def run_main(self, decls, allow):
        with tempfile.TemporaryDirectory() as d:
            data, al = Path(d) / 'data.json', Path(d) / 'allow.toml'
            data.write_text(json.dumps({'decls': LIB + decls}))
            al.write_text(allow)
            return main([str(data), '--allow', str(al)])

    def test_allowed_and_stale(self):
        bad = thm('NLAlib.foo_intrinsicDim_le', ': f (intrinsicDimension A) ≤ 1')
        entry = ('[[allow]]\nname = "NLAlib.foo_intrinsicDim_le"\nrule = "N5"\n'
                 'reason = "synthetic allowlist fixture"\n')
        self.assertEqual(self.run_main([bad], ''), 1)
        self.assertEqual(self.run_main([bad], entry), 0)
        self.assertEqual(self.run_main([], entry), 1)  # stale: the declaration is gone


if __name__ == '__main__':
    unittest.main()
