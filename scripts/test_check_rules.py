#!/usr/bin/env python3
"""Regressions for scripts/check_rules.py: for every rule id, a fixture that breaks the rule and a
fixture that keeps it, on a throw-away repository (source rules) or on hand-written declarations
in the extraction format (extraction rules). A rule added without a fixture fails
`test_every_rule_has_a_fixture`."""
import json
import tempfile
import unittest
from pathlib import Path

import check_rules
from check_rules import RULES, Ctx, run

HDR = """/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Real.Basic

"""
MODDOC = """/-!
# Title

Text.

## Main results

* `NLAlib.foo`
-/

"""
OPEN = "@[expose] public section\n\nnamespace NLAlib\n\n"
CLOSE = "\n\nend NLAlib\n"
FOO = "/-- A docstring. -/\ntheorem foo : True := trivial"


def lean(body=FOO, moddoc=MODDOC, header=HDR, open_=OPEN, close=CLOSE):
    return header + moddoc + open_ + body + close


BIB = """% header
@book{Abc2000,
  title = {A}, year = {2000}, doi = {10.1/a}
}

@book{Def2001,
  title = {B}, year = {2001}, doi = {10.1/b}
}
"""
CONTRIB = """# Contributing

The bridge `foo_bar_baz` exists.
"""
NAMING = """# Names

`made_up_example_name` is a pattern here.
"""
VOCABULARY = """# Vocabulary

| short algorithm names in `\\mathsf` | `\\mathsf{gn}` for `generalizedNystrom` | — |
"""
DEVIATIONS = """# Deviations

## 1. Good

- **Mathlib.** a
- **NLAlib.** b
- **Bridge.** c
- **Why.** d
- **Cost.** e
- **Status.** f
"""
CONSTANTS = """[[constant]]
name = "NLAlib.fooConstant"
kind = "constant"
file = "NLAlib/Matrix/A.lean"
args = []
latex = '1'
lean_body = 'fooConstant : ℝ := 1'
body_hash = "0"
"""
CITED = ("/-- **Foo.** A result. [Abc2000, Theorem 1]; [Def2001, layout §1].\nResult: foo-result -/\n"
         "theorem foo : True := trivial")


def make_root(tmp, files=None, docs=None):
    root = Path(tmp)
    base = {'NLAlib/Matrix/A.lean': lean(CITED), 'docs/references.bib': BIB,
            'CONTRIBUTING.md': CONTRIB, 'docs/contributing/naming.md': NAMING,
            'docs/contributing/vocabulary.md': VOCABULARY, 'docs/design/Mathlib-deviations.md': DEVIATIONS,
            'docs/constants.toml': CONSTANTS}
    base.update(docs or {})
    base.update(files or {})
    for p, t in base.items():
        if t is None:
            continue
        f = root / p
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(t)
    (root / 'NLAlibScaffold').mkdir(exist_ok=True)
    ml = root / 'mathlib'
    for p, t in {'Data/Real/Basic.lean': 'theorem foo_bar_baz : True := trivial\n',
                 'Analysis/Calculus/Deriv/Basic.lean': ''}.items():
        (ml / p).parent.mkdir(parents=True, exist_ok=True)
        (ml / p).write_text(t)
    return root, ml


def decl(name, sig, kind='theorem', doc='A docstring.', module='NLAlib.Matrix.A', deps=(), line=10):
    return {'name': name, 'kind': kind, 'module': module, 'signature': f'{name} {sig}', 'doc': doc,
            'typeDeps': list(deps), 'line': str(line)}


def data(*decls):
    mods = sorted({d['module'] for d in decls} | {'NLAlib.Matrix.A'})
    return {'decls': list(decls), 'modules': [{'name': m, 'path': m.replace('.', '/') + '.lean'}
                                              for m in mods]}


ALG = decl('NLAlib.rsvd', '(A : Matrix m n 𝕜) (X : Matrix n l 𝕜) : Matrix m n 𝕜', kind='def',
           doc='$\\mathsf{rsvd}(\\mathbf{A}, \\mathbf{X}) := \\mathbf{P}\\mathbf{A}$.')

# rule id -> (bad, good). A source fixture is {path: text} (or a body string for NLAlib/Matrix/A.lean);
# an extraction fixture is a list of declarations.
S = 'src'
FIX = {
    'F1': ({'NLAlib/Matrix/A.lean': lean(header=HDR.replace('Authors: NLAlib contributors', 'Authors:'))},
           {}),
    'F2': ({'NLAlib/Matrix/A.lean': lean(open_='namespace NLAlib\n\n')}, {}),
    'F3': ({'NLAlib/Matrix/A.lean': lean(header=HDR + 'import Mathlib\n\n')}, {}),
    'F4': ({'NLAlib/Matrix/A.lean': lean(open_='@[expose] public section\n\nnamespace Foo\n\n',
                                         close='\n\nend Foo\n')}, {}),
    'F5': ('set_option maxHeartbeats 400000\n\n' + CITED, '-- heavy\nset_option maxHeartbeats 400000 in\n' + CITED),
    'F6': ('set_option maxHeartbeats 400000 in\n' + CITED, '-- heavy\nset_option maxHeartbeats 400000 in\n' + CITED),
    'F7': ('open Classical\n\n' + CITED, 'open Classical in\n' + CITED),
    'F8': ('noncomputable section\n\n' + CITED, CITED),
    'F9': ('attribute [instance] foo\n\n' + CITED, 'attribute [local instance] foo in\n' + CITED),
    'F10': (CITED + '\n' * 1001, CITED),
    'F11': ({'NLAlib/Matrix/A.lean': None, 'NLAlib/Matrix/AToolkit.lean': lean(CITED)}, {}),
    'P1': ({'NLAlib/Matrix/A.lean': lean(header=HDR + 'public import NLAlib.Sketching.B\n\n')}, {}),
    'P2': ({'NLAlib/Matrix/B.lean': lean('')}, {}),
    'P3': ({'NLAlib/Matrix/A.lean': lean(header=HDR + 'public import NLAlibScaffold.Matrix.B\n\n')}, {}),
    'P12': ({'NLAlib/Matrix/A.lean': lean(header=HDR + 'public import NLAlibTools.Float\n\n')}, {}),
    'P4': ([decl('Real.foo', ': specNorm 0 = 0', module='NLAlib.ForMathlib.Data.Real.Basic',
                 deps=['NLAlib.specNorm'])],
           [decl('Real.foo', ': (0 : ℝ) = 0', module='NLAlib.ForMathlib.Data.Real.Basic')]),
    'P5': ({'NLAlib/ForMathlib/Data/Real/Basic.lean': lean(moddoc=MODDOC.replace('Text.', 'Upstream candidates.'))},
           {'NLAlib/ForMathlib/Data/Real/Basic.lean': lean(moddoc=MODDOC.replace('Text.', 'Upstream candidates.'),
                                                           open_='@[expose] public section\n\nnamespace Real\n\n',
                                                           close='\n\nend Real\n')}),
    'P6': ({'NLAlib/ForMathlib/Data/Real/Basic.lean': lean(open_='@[expose] public section\n\n', close='\n')},
           {'NLAlib/ForMathlib/Data/Real/Basic.lean': lean(moddoc=MODDOC.replace('Text.', 'Upstream candidates.'),
                                                           open_='@[expose] public section\n\n', close='\n')}),
    'P7': ({'NLAlib/ForMathlib/Data/Real/Other.lean': lean(moddoc=MODDOC.replace('Text.', 'Upstream.'),
                                                         open_='@[expose] public section\n\n', close='\n')},
           {'NLAlib/ForMathlib/Data/Real/Basic.lean': lean(moddoc=MODDOC.replace('Text.', 'Upstream.'),
                                                           open_='@[expose] public section\n\n', close='\n')}),
    'P8': ('/-- Doc. -/\ntheorem _root_.Foo.bar : True := trivial',
           '/-- Doc. -/\ntheorem _root_.Matrix.IsHermitian.bar : True := trivial'),
    'P9': ([decl('NLAlib.one_le_two', ': (1 : ℝ) ≤ 2')],
           [decl('NLAlib.specNorm_nonneg', '(A : Matrix m n 𝕜) : 0 ≤ specNorm A', deps=['NLAlib.specNorm']),
            dict(decl('NLAlib.convex_setOf_posDef', ': Convex ℝ {A | A.PosDef}'),
                 statement='theorem convex_setOf_posDef : Convex ℝ {A : Matrix n n 𝕜 | A.PosDef}'),
            decl('NLAlib.cfc_diagonal', '(f : ℝ → ℝ) (d : n → ℝ) : cfc f (diagonal d) = diagonal (f ∘ d)')]),
    'P11': ({'NLAlib/Polynomial/A.lean': lean(header=HDR + 'public import NLAlib.Matrix.A\n\n')},
            {'NLAlib/Polynomial/A.lean': lean(header=HDR + 'public import NLAlib.ForMathlib.Data.Real.Basic\n'
                                              'public import NLAlib.Polynomial.B\n'
                                              'import all Mathlib.Data.Real.Basic\n\n')}),
    'P10': ([decl('NLAlib.specNorm', '(A : Matrix m n 𝕜) : ℝ', kind='def'),
             decl('NLAlib.foo', '(A : Matrix m n 𝕜) : 0 ≤ specNorm A', module='NLAlib.LowRank.B',
                  deps=['NLAlib.specNorm'])],
            [decl('NLAlib.specNorm', '(A : Matrix m n 𝕜) : ℝ', kind='def'),
             decl('NLAlib.foo', '(A : Matrix m n 𝕜) : 0 ≤ specNorm A', deps=['NLAlib.specNorm'])]),
    'S1': (CITED.replace('trivial', 'by simp_all'), CITED),
    'S2': (CITED.replace('trivial', 'by exact?'), CITED),
    'S3': (CITED.replace('trivial', 'by decide'), CITED),
    'S4': (CITED.replace('trivial', 'by\n' + '  skip\n' * 81 + '  trivial'), CITED),
    'S5': ({'NLAlib/Matrix/A.lean': lean(CITED + '\n\nprivate theorem helper : True := trivial'),
            'NLAlib/Matrix/B.lean': lean(FOO.replace('foo', 'baz') + '\n\nprivate theorem helper : True := trivial')},
           {'NLAlib/Matrix/A.lean': lean(CITED + '\n\nprivate theorem helper : True := trivial')}),
    'S6': ([decl('Matrix.instFoo', ': Foo (Matrix m n ℝ)', kind='instance')],
           [decl('NLAlib.instFoo', ': Foo (specNorm A)', kind='instance', deps=['NLAlib.specNorm'])]),
    'S7': (CITED.replace('A result.', 'A result ' + 'x ' * 50 + '.'),
           CITED.replace('[Def2001, layout §1].', '[Def2001, layout §1],\n`' + 'x' * 110 + '`.')),
    'S9': ('/-- Doc. -/\nunsafe def anything.{u} (α : Sort u) : α := anything α\n\n'
           '-- why\nset_option debug.skipKernelTC true in\n/-- Doc. -/\ntheorem t : False := anything _',
           {'NLAlib/Matrix/A.lean': lean('/-- A partial isometry; `unsafe`, `partial` in prose. -/\n'
                                         'theorem partialSum_unsafe : True := trivial'),
            'lakefile.toml': '# no debug. options here\n[leanOptions]\nautoImplicit = false\n'}),
    'S8': ('-- why\nset_option linter.style.longLine false in\n' + CITED,
           '-- why\nset_option linter.style.longLine false in\n' + CITED.replace('A result.', '`' + 'x' * 110 + '`.')),
    'T1': ([decl('NLAlib.t', '(x : n → ℝ) : √(x ⬝ᵥ x) = 0')], [decl('NLAlib.t', '(x : n → ℝ) : ‖x‖ = 0')]),
    'T2': ([decl('NLAlib.t', '(x : ℝ) : P x.toNNReal')], [decl('NLAlib.t', '(x : ℝ) : P ‖x‖₊')]),
    'T3': ('open scoped Matrix.Norms.Frobenius\n\n' + CITED, 'open scoped Matrix.Norms.Frobenius in\n' + CITED),
    'T4': ([decl('NLAlib.t', '(A : Matrix m n ℝ) : ‖A‖ = 0')],
           [decl('NLAlib.t', '(A : Matrix m n ℝ) : specNorm A = 0')]),
    'T5': ([decl('NLAlib.t', '(A : Matrix m n ℝ) : Aᵀ = 0')], [decl('NLAlib.t', '(A : Matrix m n ℝ) : Aᴴ = 0')]),
    'T6': ([decl('NLAlib.t', '(A : Matrix (Fin k) n ℝ) : A = 0')], [decl('NLAlib.t', '(A : Matrix m n 𝕜) : A = 0')]),
    'T7': ([decl('NLAlib.t', '(A : Matrix m n ℝ) : A = 0')], [decl('NLAlib.t', '[RCLike 𝕜] (A : Matrix m n 𝕜) : A = 0')]),
    'T8': ([decl('NLAlib.t', ': ∀ i, P (hA.eigenvectorBasis i)')], [decl('NLAlib.t', ': ∀ u, P u')]),
    'T9': ([decl('NLAlib.t', ': f ⟨k, ⋯⟩ = 0')], [decl('NLAlib.t', '(hk : k < n) : f ⟨k, hk⟩ = 0')]),
    'T10': ([decl('NLAlib.t', ': ∀ θ : ℕ, θ • Y = 0')], [decl('NLAlib.t', ': ∀ θ : ℝ, θ • Y = 0')]),
    'T11': ([decl('NLAlib.t', ': 0 ≤ x ∧ x ≤ 1')], [decl('NLAlib.t', ': 0 ≤ x'), decl('NLAlib.t2', ': P (fun k ↦ if a ∧ b then x else y)'),
            decl('NLAlib.t3', ': P fun k ↦ if a ∧ b then x else y')]),
    'T12': ([decl('NLAlib.t', ': ∃ k, 0 < eigenvalue A k')], [decl('NLAlib.t', ': ∃ k < n, 0 < eigenvalue A k')]),
    'T13': ([decl('NLAlib.t', '(_hQ : P Q) : Q = Q')], [decl('NLAlib.t', '(hQ : P Q) : Q = Q')]),
    'T14': ([decl('NLAlib.t', ': μ {ω | b < X ω} ≤ δ')], [decl('NLAlib.t', ': μ.real {ω | b < X ω} ≤ δ')]),
    'T15': ('/-- **First moment.** By Jensen from the squared form `NLAlib.foo_sq`.\nResult: r-id -/\n'
            'theorem bar : True := trivial',
            '/-- **Second moment.** [Abc2000, Theorem 1] prints the first-moment form, which follows by '
            'Jensen\'s inequality (`ProbabilityTheory.integral_le_sqrt_integral_sq`).\nResult: r-id -/\n'
            'theorem bar : True := trivial'),
    'V1': ([decl('NLAlib.t', '(hQ : Qᴴ * Q = 1) : P Q')], [decl('NLAlib.t', '(h : Aᴴ * A + Bᴴ * B = 1) : P A')]),
    'V2': ([decl('NLAlib.t', ': f k = Fintype.card n - k')], [decl('NLAlib.t', '(hd : k + d = Fintype.card n) : f d = 0')]),
    'V3': ([decl('NLAlib.t', ': singularValues A j / singularValues A i ≤ 1')],
           [decl('NLAlib.t', ': singularGapRatio A i j ≤ 1')]),
    'V4': ([decl('NLAlib.t', ': frobNorm A * frobNorm A = 0')], [decl('NLAlib.t', ': frobNorm A ^ 2 = 0')]),
    'V5': ('/-- Doc. -/\ndef matrixExp : ℝ := 0', '/-- Doc. -/\ndef specNorm : ℝ := 0'),
    'V6': ({'docs/contributing/vocabulary.md': VOCABULARY + '\nAnd `missing_lemma_here`.\n'}, {}),
    'V7': ([decl('NLAlib.newThing', ': ℝ', kind='def')], [decl('NLAlib.generalizedNystrom', ': ℝ', kind='def')]),
    'B1': ('/-- Doc. -/\ndef barConstant : ℝ := 1', '/-- Doc. -/\ndef fooConstant : ℝ := 1'),
    'B2': ([decl('NLAlib.t', ': ∃ C : ℝ, 0 < C')], [decl('NLAlib.exists_forall_t', ': ∃ C : ℝ, 0 < C')]),
    'B3': ('/-- An asymptotic form.\nAsymptotic: NLAlib.foo -/\ntheorem exists_forall_foo : True := trivial',
           '/-- $O(k)$ suffices.\nAsymptotic: NLAlib.foo -/\ntheorem exists_forall_foo : True := trivial'),
    'B4': ([decl('NLAlib.exists_forall_t', '{m : Type u_1} : ∃ C : ℝ, 0 < C', doc='$O(1)$ suffices.\nAsymptotic: NLAlib.t')],
           [decl('NLAlib.exists_forall_t', ': ∃ C : ℝ, ∀ {m : Type}, 0 < C', doc='$O(1)$ suffices.\nAsymptotic: NLAlib.t')]),
    'B5': ([decl('NLAlib.t', '(hε : 0 < ε) (hk : f ε ≤ Fintype.card k) : P', module='NLAlib.Sketching.B', doc='X.\nResult: r-id')],
           [decl('NLAlib.t', '(hε : 0 < ε) (hk : f ε ≤ Fintype.card k) : P', module='NLAlib.Sketching.B',
                 doc='X. Asymptotic form: `NLAlib.exists_forall_t`.\nResult: r-id')]),
    'D1': (CITED.replace('**Foo.** ', ''), CITED),
    'D2': (CITED.replace('A result.', 'Under the hypotheses of `NLAlib.bar`, it holds.'), CITED),
    'D3': ([decl('NLAlib.t', ': x ≤ 1 / k', doc='$x \\le 1/k$.\nResult: r-id')],
           [decl('NLAlib.t', ': x ≤ 1 / k', doc='$$x \\le \\frac{1}{k}\\,.$$\nResult: r-id')]),
    'D4': (CITED.replace('A result.', 'A result $x \\le \\frac{1}{2}$.'),
           CITED.replace('A result.', 'A result $$x \\le \\frac{1}{2}\\,.$$')),
    'D5': (CITED.replace('A result.', 'A result $$x \\le 1$$.'), CITED.replace('A result.', 'A result $$x \\le 1\\,.$$')),
    'D6': (CITED.replace('A result.', 'A result $specNorm(x)$.'), CITED.replace('A result.', 'A result `specNorm`.')),
    'D7': (CITED.replace('A result.', 'A result `‖A‖₂ ≤ 1`.'), CITED.replace('A result.', 'A result $\\|A\\|_2 \\le 1$.')),
    'D8': (CITED.replace('A result.', 'A result.\nProof: by induction.'), CITED),
    'D9': ({'NLAlib/Matrix/A.lean': lean(CITED, moddoc='')}, {}),
    'D12': ([decl('NLAlib.t', '(hind : iIndepFun X μ) : P', doc='For summands $\\mathbf{X}_k$, $P$.')],
            [decl('NLAlib.t', '(hind : iIndepFun X μ) : P', doc='For independent summands, $P$.'),
             decl('NLAlib.u', '(hX : HasLaw X ν μ) : P', doc='**Gaussian tail**: for a standard Gaussian '
                  '$\\mathbf{X}$, $P$.\nResult: r-id')]),
    'D13': ([decl('NLAlib.t', '[Nonempty n] : P', doc='**Tail**: $P$.\nResult: r-id')],
            [decl('NLAlib.t', '[Nonempty n] : P', doc='**Tail**: for $n$ nonempty, $P$.\nResult: r-id')]),
    'D10': ({'NLAlib/Matrix/A.lean': lean(CITED, moddoc=MODDOC.replace('## Main results', 'More'))}, {}),
    'D11': ({'NLAlib/Matrix/A.lean': lean(CITED, moddoc=MODDOC.replace('`NLAlib.foo`', '`NLAlib.gone`'))}, {}),
    'M1': (CITED.replace('A result.', 'A result $\\mathbb{P}\\bigl\\{E\\bigr\\} \\le \\mathbb{P}(E)$.'),
           CITED.replace('A result.', 'A result $\\mathbb{P}[E] \\le 1$.')),
    'M2': ([ALG, decl('NLAlib.t', '(A : Matrix m n 𝕜) : frobNorm (A - rsvd A X) ≤ 1', deps=['NLAlib.rsvd'],
                      doc='$\\|\\mathbf{A} - \\mathbf{P}\\mathbf{A}\\| \\le 1$.\nResult: r-id')],
           [ALG, decl('NLAlib.t', '(A : Matrix m n 𝕜) : frobNorm (A - rsvd A X) ≤ 1', deps=['NLAlib.rsvd'],
                      doc='$\\|\\mathbf{A} - \\mathsf{rsvd}(\\mathbf{A}, \\mathbf{X})\\| \\le 1$.\nResult: r-id')]),
    'M3': ([ALG, decl('NLAlib.t', '(A : Matrix m n 𝕜) : frobNorm (A - rsvd A X) ≤ 1', deps=['NLAlib.rsvd'],
                      doc='$\\|\\mathbf{A} - \\mathbf{P}\\mathbf{A}\\| \\le 1$.')],
           [ALG, decl('NLAlib.t', '(A : Matrix m n 𝕜) : frobNorm (A - rsvd A X) ≤ 1', deps=['NLAlib.rsvd'],
                      doc='$\\mathsf{rsvd}(\\mathbf{A}, \\mathbf{X})$.')]),
    'M4': (CITED.replace('A result.', 'A result $\\mathsf{rangeFinder}(\\mathbf{A})$.'),
           CITED.replace('A result.', 'A result $\\mathsf{gn}(\\mathbf{A}) = \\mathsf{foo}(\\mathbf{A})$.')),
    'M5': ([decl('NLAlib.alg', '(A : Matrix m n 𝕜) : Matrix m n 𝕜', kind='def', module='NLAlib.LowRank.B', doc='An algorithm.'),
            decl('NLAlib.t1', ': P', deps=['NLAlib.alg'], doc='X.\nResult: a-id'),
            decl('NLAlib.t2', ': P', deps=['NLAlib.alg'], doc='X.\nResult: b-id')],
           [decl('NLAlib.alg', '(A : Matrix m n 𝕜) : Matrix m n 𝕜', kind='def', module='NLAlib.LowRank.B',
                 doc='$\\mathsf{alg}(\\mathbf{A}) := \\mathbf{A}$.'),
            decl('NLAlib.t1', ': P', deps=['NLAlib.alg'], doc='X.\nResult: a-id'),
            decl('NLAlib.t2', ': P', deps=['NLAlib.alg'], doc='X.\nResult: b-id')]),
    'M6': (CITED.replace('A result.', 'A result $\\|\\mathbf{A}\\|_F$.'),
           CITED.replace('A result.', 'A result $\\|\\mathbf{A}\\|_{\\mathsf{F}}$.')),
    'M7': (CITED.replace('A result.', 'A result $\\mathbf{A}^*$.'),
           CITED.replace('A result.', 'A result $\\mathbf{A}^{\\mathsf{H}}$, $\\|\\mathbf{A}\\|_*$.')),
    'M8': (CITED.replace('A result.', 'A result $\\epsilon$.'), CITED.replace('A result.', 'A result $\\varepsilon$.')),
    'M9': (CITED.replace('A result.', 'A result $\\mathrm{tr}(\\mathbf{A})$.'),
           CITED.replace('A result.', 'A result $\\operatorname{tr}(\\mathbf{A})$.')),
    'M10': (CITED.replace('A result.', 'A result $E[X]$.'), CITED.replace('A result.', 'A result $\\mathbb{E}[X]$.')),
    'M11': (CITED.replace('A result.', 'A result $\\boldsymbol{\\Omega}$.'),
            CITED.replace('A result.', 'A result $\\mathbf{\\Omega}$.')),
    'M12': (CITED.replace('A result.', 'A result $\\R$.'), CITED.replace('A result.', 'A result $\\mathbb{R}$.')),
    'M13': (CITED.replace('A result.', 'A result $\\mathbb{K}$.'), CITED.replace('A result.', 'A result $\\Bbbk$.')),
    'M14': (CITED.replace('A result.', 'A result $\\lfloor \\mathbf{A} \\rfloor_k$.'),
            CITED.replace('A result.', 'A result $\\llbracket \\mathbf{A} \\rrbracket_k$.')),
    'M15': (CITED.replace('A result.', 'A result $\\|\\mathbf{A}\\|$.'), CITED.replace('A result.', 'A result $\\|\\mathbf{A}\\|_2$.')),
    'M16': (CITED.replace('A result.', 'A result $|n|$.'), CITED.replace('A result.', 'A result $\\lvert n \\rvert$.')),
    'M17': (CITED.replace('A result.', 'A result $\\mathbf{A} \\succcurlyeq 0$.'),
            CITED.replace('A result.', 'A result $\\mathbf{0} \\preceq \\mathbf{A}$.')),
    'M18': ([decl('NLAlib.t', '(A : Matrix m n ℝ) : A = A', doc='$A = A$.')],
            [decl('NLAlib.t', '(A : Matrix m n ℝ) : A = A', doc='$\\mathbf{A} = \\mathbf{A}$.')]),
    'C1': (CITED.replace(' [Abc2000, Theorem 1]; [Def2001, layout §1].', ''),
           CITED.replace(' [Abc2000, Theorem 1]; [Def2001, layout §1].', ' No printed source.')),
    'C2': (CITED.replace('Theorem 1', '').replace(', ]', ']'), CITED),
    'C3': (CITED.replace('Theorem 1', 'Theorem 1, $k = 2$'), CITED),
    'C4': (CITED.replace('[Def2001, layout §1]', '[Smith et al. 2001]'), CITED),
    'C5': ({'docs/references.bib': BIB + '\n@book{abc_2002,\n  title = {C}\n}\n'}, {}),
    'C6': ({'docs/references.bib': BIB.replace('10.1/b', '10.1/a')}, {}),
    'C7': ({'docs/references.bib': BIB.replace('Abc2000', 'Xyz2000')}, {}),
    'C8': ({'docs/references.bib': BIB + '\n@book{Ghi2002,\n  title = {C}\n}\n'}, {}),
    'C9': (CITED.replace(' [Abc2000, Theorem 1]; [Def2001, layout §1].', '').replace('\nResult: foo-result', ''), CITED),
    'A1': ('/-- **A def.**\nAlgorithm: Bad_Id -/\ndef bar : ℝ := 0',
           '/-- **A def.**\nAlgorithm: some-algo (specification) -/\ndef bar : ℝ := 0'),
    'A2': ('/-- A docstring.\nAlgorithm: some-algo -/\ntheorem foo : True := trivial',
           '/-- **A def.**\nAlgorithm: some-algo -/\nstructure Bar where\n  x : ℕ'),
    'A3': ('/-- **A def.**\nAlgorithm: some-algo\nAlgorithm: other-algo -/\ndef bar : ℝ := 0',
           '/-- **A def.**\nAlgorithm: some-algo -/\ndef bar : ℝ := 0'),
    'R1': ('/-- **A def.** [Abc2000, Definition 1].\nResult: a-def -/\ndef bar : ℝ := 0',
           '/-- **Invariant.** [Abc2000, Theorem 1].\nResult: a-inv -/\ninstance isFoo_bar : IsFoo bar := ⟨⟩'),
    'R2': (CITED + '\n\n' + CITED.replace('foo', 'baz').replace('baz-result', 'foo-resukt'),
           CITED + '\n\n' + CITED.replace('foo', 'baz').replace('baz-result', 'bar-result')),
    'R3': (None, None),  # needs the explorer's data files; covered by test_orphans
    'G1': ({'docs/design/Mathlib-deviations.md': DEVIATIONS + '\n## 2. Bad\n\n- **Mathlib.** a\n'}, {}),
    'E5': ({'NLAlib/Computation/A.lean': lean(header=HDR + 'public import NLAlib.Matrix.A\n\n')},
           {'NLAlib/Computation/A.lean': lean(header=HDR + 'public import NLAlib.ForMathlib.Data.Nat.Init\n'
                                              'public import NLAlib.Computation.Exec\n\n')}),
    'E6': ('/-- Doc. -/\nnoncomputable def mySem : ScalarSem P ℝ := exactSem',
           {'NLAlib/Computation/A.lean': lean('/-- Doc. -/\nnoncomputable def mySem : ScalarSem P ℝ := '
                                              'exactSem\n\n/-- Doc. -/\ntheorem t (I : Interp P ι K C) : True := trivial'),
            'NLAlib/Matrix/A.lean': lean('/-- Doc. -/\ntheorem t (I : Interp P ι K C) : I = I := rfl')}),
    'E8': ('/-- Doc. -/\ndef k : Builder P ι VB VI Unit :=\n  named "k" [] (pure ())',
           {'NLAlib/Computation/BLAS.lean': lean('/-- Doc. -/\ndef k : Builder P ι VB VI Unit :=\n'
                                                 '  named "k" [] (pure ())'),
            'NLAlib/Matrix/A.lean': lean('/-- The `named` kernels. -/\ndef k : ℕ := 0\n\n'
                                         '/-- A compile equation. -/\ntheorem t : Stmt.named "k" [] .skip = '
                                         'Stmt.named "k" [] .skip :=\n  rfl')}),
}


def violations(rid, fixture):
    """Number of violations of rule `rid` on a fixture."""
    with tempfile.TemporaryDirectory() as tmp:
        if RULES[rid]['tier'] == 'x':
            root, ml = make_root(tmp)
            c = Ctx(root, data(*fixture), None, ml)
        else:
            files = fixture if isinstance(fixture, dict) else {'NLAlib/Matrix/A.lean': lean(fixture)}
            root, ml = make_root(tmp, files)
            c = Ctx(root, None, None, ml)
        return [v for v in RULES[rid]['fn'](c) if v.rule == rid]


class RuleTests(unittest.TestCase):
    def test_every_rule_has_a_fixture(self):
        self.assertEqual(set(RULES) - set(FIX), set())

    def test_rules(self):
        for rid, (bad, good) in sorted(FIX.items()):
            if bad is None:
                continue
            with self.subTest(rule=rid):
                self.assertTrue(violations(rid, bad), f'{rid}: the bad fixture passes')
                self.assertEqual([v.text() for v in violations(rid, good)], [], f'{rid}: the good fixture fails')

    def test_v7_target_registry_records(self):
        # a registered target, a registered tree and its program, and a targets file's count
        # need no vocabulary row (programs)
        reg = ('[[tree]]\nname = "NLAlib.fooProg.compiled"\n\n'
               '[[target]]\nname = "NLAlib.MatrixFreeFoo"\n')
        ds = [decl('NLAlib.fooProg', ': ℕ', kind='def'), decl('NLAlib.MatrixFreeFoo', ': Prop', kind='def'),
              decl('NLAlib.fooCount', ': ℕ', kind='def', module='NLAlib.Matrix.FooTargets')]
        def v7(registry):
            with tempfile.TemporaryDirectory() as tmp:
                root, ml = make_root(tmp, docs={'docs/targets.toml': registry})
                return [v.text() for v in RULES['V7']['fn'](Ctx(root, data(*ds), None, ml))]
        self.assertEqual(v7(reg), [])
        self.assertEqual(len(v7(None)), 2)  # the count is recorded by its file, not the registry

    def test_layer_table_matches_contributing(self):
        # the layout guide's folder block and docs/rules/layers.toml give each top-level folder one
        # layer, and every top-level folder of NLAlib/ has one
        folders = {d.name for d in (Path(__file__).resolve().parent.parent / 'NLAlib').iterdir() if d.is_dir()}
        self.assertEqual(folders, set(check_rules.LAYER))
        for e in check_rules.LAYERS.values():  # a narrowed import list names its rule and reason
            self.assertEqual('imports' in e, 'rule' in e and 'reason' in e)
            self.assertIn(e.get('rule', 'P1'), check_rules.SPECS)
        import re
        text = (Path(__file__).resolve().parent.parent / 'docs/contributing/layout.md').read_text()
        block = text[text.index('## 1. Folders and layers'):text.index('NLAlibTools/')]
        table, folder = {}, None
        for line in block.splitlines():
            m = re.match(r'  (\w+)/', line)
            folder = m.group(1) if m else folder
            n = re.search(r'\(layer ([−-]?[\d.]+)\)\s*$', line)
            if n and folder:
                table[folder] = float(n.group(1).replace('−', '-'))
        self.assertEqual(table, {k: float(v) for k, v in check_rules.LAYER.items()})

    def test_p1_half_layers_and_unknown_folders(self):
        imp = lambda me, th: {f'NLAlib/{me}/A.lean': lean(header=HDR + f'public import NLAlib.{th}.B\n\n')}
        self.assertTrue(violations('P1', imp('Krylov', 'Probability')))
        self.assertEqual(violations('P1', imp('Probability', 'Krylov')), [])
        self.assertTrue(violations('P1', imp('LowRank', 'Estimation')))
        self.assertEqual(violations('P1', imp('Estimation', 'LowRank')), [])
        self.assertEqual(violations('P1', imp('LowerBounds', 'Estimation')), [])
        self.assertTrue(violations('P1', imp('Estimation', 'LowerBounds')))
        self.assertTrue(violations('P1', imp('Solvers', 'Matrix')))

    def test_import_all_names_the_module(self):
        # `import all X` imports X with its private bodies, not a module named `all`
        import leansrc
        text = HDR + 'import all Mathlib.Data.Real.Sqrt\npublic meta import all NLAlib.Foo\n'
        self.assertEqual(leansrc.parse(text)['imports'],
                         [(8, True, 'Mathlib.Data.Real.Basic'), (10, False, 'Mathlib.Data.Real.Sqrt'),
                          (11, True, 'NLAlib.Foo')])

    def test_every_rule_is_cited_where_it_is_stated(self):
        # checks guide layout §1: each rule's prose cites its id, as its messages do; and every id the
        # guides state (in brackets, or a row of the naming tables) is in rules.toml
        import re
        text = '\n'.join(check_rules.guide_texts(Path(__file__).resolve().parent.parent).values())
        cited = {x.strip() for m in re.finditer(r'\[((?:[A-Z]\d+)(?:,\s*[A-Z]\d+)*)\]', text)
                 for x in m.group(1).split(',')} | set(re.findall(r'^\| ([A-Z]\d+) \|', text, re.M))
        self.assertEqual(set(check_rules.SPECS) - cited, set(), 'in rules.toml, not in CONTRIBUTING')
        self.assertEqual(cited - set(check_rules.SPECS), set(), 'in CONTRIBUTING, not in rules.toml')
        self.assertEqual(set(RULES) - set(check_rules.SPECS), set())

    def test_rules_toml_entries(self):
        for rid, sp in check_rules.SPECS.items():
            with self.subTest(rule=rid):
                self.assertEqual(set(sp) - {'id', 'area', 'severity', 'check', 'scope', 'exclude', 'home',
                                            'exempt', 'exempt_while', 'exempt_reason', 'section',
                                            'statement', 'fix'}, set())
                self.assertEqual('exempt' in sp, 'exempt_reason' in sp)
                self.assertIn(sp['severity'], ('error', 'warning', 'review'))
                self.assertIn(sp['check'], ('source', 'extraction', 'lean', 'none'))
                self.assertEqual(sp['check'] == 'none', sp['severity'] == 'review')
                self.assertTrue(sp['statement'] and sp['fix'] and '\n' not in sp['statement'])
                self.assertFalse(sp['statement'].endswith('.'))
                if sp['scope'] != 'library':
                    self.assertTrue(all(s.startswith('NLAlib/') for s in sp['scope']))

    def test_lean_rules_are_checked_by_programs(self):
        # rules with `check = "lean"` are checked by scripts/Programs.lean or scripts/Targets.lean,
        # whose messages cite them: an error rule by `logError`, a warning by `logWarning`
        here = Path(__file__).resolve().parent
        text = (here / 'Programs.lean').read_text() + (here / 'Targets.lean').read_text()
        for rid, sp in check_rules.SPECS.items():
            if sp['check'] == 'lean':
                with self.subTest(rule=rid):
                    self.assertIn(sp['severity'], ('error', 'warning'))
                    if sp['severity'] == 'warning':
                        self.assertIn(f'logWarning m!"{rid} ', text)
                    else:  # Targets.lean collects its messages as `s!"E3 …"`, then logs them
                        self.assertTrue(f'logError m!"{rid} ' in text or f's!"{rid} ' in text)
        self.assertNotIn('E1', check_rules.SPECS)  # retired, never reused

    def test_scope(self):
        # a rule scoped to the Matrix layer (T7) ignores the same declaration in LowRank
        bad = FIX['T7'][0][0]
        self.assertTrue(violations('T7', [bad]))
        self.assertEqual(violations('T7', [dict(bad, module='NLAlib.LowRank.B')]), [])

    def test_generated_rule_files_are_current(self):
        import gen_rules_md
        self.assertEqual(gen_rules_md.main(['--check']), 0)

    def test_message_shape(self):
        v = violations('S1', FIX['S1'][0])[0].text()
        self.assertRegex(v, r'^S1 NLAlib/Matrix/A\.lean:\d+ \S+: No `simp_all`')

    def test_unsafe_and_kernel_options(self):
        # S9 (final audit, 2026-10-24): each keyword and option that bypasses the kernel, in code
        for body in ['/-- Doc. -/\npartial def f (n : ℕ) : ℕ := f n',
                     '/-- Doc. -/\n@[implemented_by g] def f (n : ℕ) : ℕ := n',
                     '/-- Doc. -/\n@[extern "f"] def f (n : ℕ) : ℕ := n',
                     '/-- Doc. -/\ntheorem t : True := by\n  set_option debug.byAsSorry true in trivial',
                     '-- why\nset_option debug.skipKernelTC true in\n' + FOO,
                     '/-- Doc. -/\nunsafe inductive U : Type where\n  | mk : (U → U) → U',
                     'run_cmd do\n  match (← getEnv).addDeclCore 0 0 d none (doCheck := false) with\n  | _ => pure ()']:
            with self.subTest(body=body):
                self.assertTrue(violations('S9', body), body)
        for lake in ['[leanOptions]\ndebug.skipKernelTC = true\n',
                     '[[lean_lib]]\nname = "NLAlib"\nmoreLeanArgs = ["-DautoImplicit=false"]\n']:
            with self.subTest(lake=lake):
                self.assertTrue(violations('S9', {'lakefile.toml': lake}), lake)
        self.assertEqual(violations('S9', '/-- Doc. -/\ntheorem partialSum_le : True := trivial'), [])

    def test_package_libraries_not_imported(self):
        # P12 (final audits, 2026-10-24): neither tools nor scaffold, in a file or in the root,
        # nor a library that lakefile.toml adds; a Mathlib or NLAlib import passes
        for files in [{'NLAlib/Matrix/A.lean': lean(header=HDR + 'import NLAlibScaffold\n\n')},
                      {'NLAlib.lean': 'module\n\npublic import NLAlib.Matrix.A\npublic import NLAlibTools\n'},
                      {'lakefile.toml': '[[lean_lib]]\nname = "NLAlib"\n\n[[lean_lib]]\nname = "NLAlibExtra"\n',
                       'NLAlib/Matrix/A.lean': lean(header=HDR + 'public import NLAlibExtra.B\n\n')}]:
            with self.subTest(files=files):
                self.assertTrue(violations('P12', files), files)
        self.assertEqual(violations('P12', {
            'NLAlib.lean': 'module\n\npublic import NLAlib.Matrix.A\n',
            'NLAlib/Matrix/A.lean': lean(header=HDR + 'public import NLAlib.Matrix.B\nimport NLAlibToolsLike\n\n')}), [])

    def test_long_line_exemption(self):
        self.assertTrue(check_rules.long_line_exempt('  `' + 'x' * 120 + '`.'))
        self.assertTrue(check_rules.long_line_exempt('* `' + 'x' * 120 + '`:'))
        self.assertTrue(check_rules.long_line_exempt('see https://example.org/' + 'x' * 100))
        self.assertTrue(check_rules.long_line_exempt('    ' + 'x' * 120 + ' :'))
        self.assertFalse(check_rules.long_line_exempt('theorem ' + 'x' * 120))
        self.assertFalse(check_rules.long_line_exempt('  have h := ' + 'x' * 120))

    def test_name_on_its_own_line(self):
        # `theorem` alone, the long name in column 0 on the next line: one declaration, whose
        # exemption is needed (S8) and whose name line is one identifier (S7)
        body = ('-- why\nset_option linter.style.longLine false in\n/-- Doc. -/\ntheorem\n'
                + 'x' * 110 + ' :\n    True := trivial')
        self.assertEqual(violations('S8', body), [])
        self.assertEqual(violations('S7', body), [])

    def test_deferral_phrasings(self):
        # D2 misses found in stage 2: each phrasing defers the setting to another statement
        for phrase in ('for summands $\\mathbf{X}_k$ as in the\ntail', 'as in the general form',
                       'on the same instance the ratio is', 'if moreover $g \\ge 0$'):
            with self.subTest(phrase=phrase):
                self.assertTrue(violations('D2', CITED.replace('A result.', f'A result {phrase}.')))
        for phrase in ('as in the source', 'with the same constants', 'as in `NLAlib.bar`'):
            with self.subTest(phrase=phrase):
                self.assertEqual(violations('D2', CITED.replace('A result.', f'A result {phrase}.')), [])

    def test_proof_sentence_mid_line(self):
        for doc in ('A result. Proof: by induction.', '**Foo.** Proof: by induction.',
                    'A result (there scalar). Proof:\n$x = y$.'):
            with self.subTest(doc=doc):
                self.assertTrue(violations('D8', CITED.replace('**Foo.** A result.', doc)))
        self.assertEqual(violations('D8', CITED.replace('A result.', 'A result; the proof is new.')), [])

    def test_absolute_values(self):
        # M16: an absolute value is `\lvert x \rvert` like a cardinality; `\|` norms and a bar in a
        # subscript are not flagged
        self.assertTrue(violations('M16', CITED.replace('A result.', 'A result $|p(x)| \\le 1$.')))
        self.assertTrue(violations('M16', CITED.replace('A result.', 'A result $\\left|p\\right|$.')))
        for ok in ('$\\lvert p \\rvert \\le 1$', '$\\|\\mathbf{A}\\|_2$', '$q_{t|u}$',
                   '$\\mathbb{E}[X \\bigm| m]$'):
            with self.subTest(ok=ok):
                self.assertEqual(violations('M16', CITED.replace('A result.', f'A result {ok}.')), [])

    def test_polynomial_exemption_needs_p11(self):
        # P9 exempts the Polynomial layer only while P11 holds (maintainer decision 2026-10-20)
        fact = decl('NLAlib.one_le_two', ': (1 : ℝ) ≤ 2', module='NLAlib.Polynomial.A')
        clean = {'NLAlib/Polynomial/A.lean': lean(CITED)}
        broken = {'NLAlib/Polynomial/A.lean': lean(CITED, header=HDR + 'public import NLAlib.Matrix.A\n\n')}
        for files, n in ((clean, 0), (broken, 1)):
            with tempfile.TemporaryDirectory() as tmp:
                root, ml = make_root(tmp, files)
                c = Ctx(root, data(fact), None, ml)
                self.assertEqual(len(RULES['P9']['fn'](c)), n)

    def test_orphans(self):
        with tempfile.TemporaryDirectory() as tmp:
            root, ml = make_root(tmp)
            ex = root / 'explore'
            ex.mkdir()
            (ex / 'collections.toml').write_text('results = ["foo-result", "gone-result"]\n')
            c = Ctx(root, None, ex, ml)
            self.assertEqual([v.decl for v in RULES['R3']['fn'](c)], ['gone-result'])
            (ex / 'algorithms.toml').write_text('[cg]\nresults = ["foo-result"]\nnot_results = ["gone-cg"]\n'
                                                'definitions = ["NLAlib.foo", "NLAlib.gone"]\n')
            self.assertEqual(sorted(v.decl for v in RULES['R3']['fn'](c)),
                             ['NLAlib.gone', 'gone-cg', 'gone-result'])


class RatchetTests(unittest.TestCase):
    def run_main(self, root, *args):
        import contextlib
        import io
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = run(['--root', str(root), '--mathlib', str(root / 'mathlib'), '--no-names',
                        '--baseline', str(root / 'baseline.json'), '--allow', str(root / 'allow.toml'),
                        *args])
        return code, out.getvalue()

    def test_baseline_ratchet(self):
        bad = CITED.replace('trivial', 'by simp_all')
        with tempfile.TemporaryDirectory() as tmp:
            root, _ = make_root(tmp, {'NLAlib/Matrix/A.lean': lean(bad)})
            code, out = self.run_main(root)
            self.assertEqual(code, 1)
            self.assertIn('S1 NLAlib/Matrix/A.lean', out)
            # the extraction rules have counts: a baseline needs DATA.json
            code, out = self.run_main(root, '--update-baseline')
            self.assertEqual(code, 1)
            (root / 'd.json').write_text(json.dumps(data()))
            code, out = self.run_main(root, str(root / 'd.json'), '--update-baseline')
            self.assertEqual(code, 1)  # creating an entry is a rise
            code, out = self.run_main(root, str(root / 'd.json'), '--update-baseline', '--force')
            self.assertEqual(code, 0, out)
            self.assertEqual(json.loads((root / 'baseline.json').read_text())['rules']['S1'],
                             {'NLAlib/Matrix/A.lean': 1})
            code, out = self.run_main(root)
            self.assertEqual(code, 0, out)
            # a second violation in the same file fails, and the update refuses to raise the count
            (root / 'NLAlib/Matrix/A.lean').write_text(lean(bad + '\n\n' + bad.replace('foo', 'baz')
                                                            .replace('foo-result', 'baz-result')))
            code, out = self.run_main(root)
            self.assertEqual(code, 1)
            self.assertIn('baseline 1', out)
            code, out = self.run_main(root, str(root / 'd.json'), '--update-baseline')
            self.assertEqual(code, 1)
            self.assertIn('would rise', out)
            # fixing it reminds to lower the baseline
            (root / 'NLAlib/Matrix/A.lean').write_text(lean(CITED))
            code, out = self.run_main(root)
            self.assertEqual(code, 0)
            self.assertIn('Counts below the baseline', out)

    def test_allowlist_needs_reason_and_goes_stale(self):
        with tempfile.TemporaryDirectory() as tmp:
            root, _ = make_root(tmp)
            (root / 'allow.toml').write_text('[[allow]]\nrule = "S1"\npath = "x"\n')
            with self.assertRaises(SystemExit):
                self.run_main(root)
            (root / 'allow.toml').write_text('[[allow]]\nrule = "D1"\ndecl = "NLAlib.foo"\nreason = "r"\n')
            code, out = self.run_main(root)
            self.assertEqual(code, 1)
            self.assertIn('stale allowlist entry', out)


if __name__ == '__main__':
    unittest.main()
