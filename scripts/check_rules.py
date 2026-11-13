#!/usr/bin/env python3
"""Check the library against the contribution rules of CONTRIBUTING.md, by rule id.

    python3 scripts/check_rules.py [DATA.json] [--files F ...] [--only ID,...] [--warnings]
                                   [--all] [--partial] [--no-names] [--list]
    python3 scripts/check_rules.py [DATA.json] --update-baseline [--force]

Every rule has a stable id: a letter for its area and a number, as the naming rules N1–N18
(`scripts/check_names.py`). Areas, with the guide of docs/contributing that states them: F file
template (layout), P placement and layers (layout, design), S source and proof style (proofs),
T types and statement shape (statements), V vocabulary (vocabulary), B bounds and asymptotic
forms (statements), D docstrings, M mathematical notation, C citations, R `Result:` ids and
A algorithm tags (docstrings), G design records (design), E programs (programs; E2–E4 and E9 are
checked on the built library by `scripts/Programs.lean` and `scripts/Targets.lean`,
`check = "lean"` in rules.toml). The rule data, severity, statement, fix, scope and section, is in
`docs/rules/rules.toml`, the single source this script, `check_names.py` and
`scripts/gen_rules_md.py` read; this file holds the checks. `--list` prints every rule.

Two tiers. The source tier reads the Lean sources and documents and needs no build. The
extraction tier reads DATA.json, the output of `scripts/explore_data.sh` after `lake build NLAlib`
(the same file `check_names.py` reads); without it those rules are skipped and the naming rules
are not run. With it, the naming rules N1–N18 are run too (through `check_names.check`, with its
allowlist), so one command reports everything.

Each violation prints as one line, `<ID> <file>:<line> <decl>: <message and fix>`.

Levels. An *error* fails the check. Existing debt is ratcheted:
`scripts/rules_baseline.json` holds, per error rule and file, the number of violations that
existed when the rule became checked, and only violations above that count fail (all of a file's
violations of the rule are then printed). A rule with no baseline entry is clean, so every
violation of it fails. When a count falls below its baseline the check says so; lower it with
`--update-baseline`, which refuses to raise a count unless `--force` is given (a rise needs the
maintainer, not a flag). A *warning* is a heuristic too noisy to fail on (the message says so);
warnings are counted, and printed with `--warnings` or `--files`.

A false positive goes in `scripts/rules_allow.toml`, with the rule, the declaration (or the path,
for a file-level rule) and a reason; an entry is never the fix for a real violation, and a stale
entry fails the check.

`--files F ...` restricts the report and the ratchet to those files (an agent checking its own
work). `--partial` says DATA.json covers part of the library (`scripts/stage_check.sh`): the
extraction rules then judge only the files it covers.
"""
import argparse
import collections
import json
import re
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import leansrc  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / 'scripts' / 'rules_baseline.json'
ALLOW = ROOT / 'scripts' / 'rules_allow.toml'
LIBS = ('NLAlib', 'NLAlibScaffold')
BIB = 'docs/references.bib'
DEVIATIONS = 'docs/design/Mathlib-deviations.md'
GUIDES = 'docs/contributing'  # the topic guides; CONTRIBUTING.md is their hub

LAYERS_TOML = ROOT / 'docs' / 'rules' / 'layers.toml'


def load_layers(path=LAYERS_TOML):
    """{folder: entry of layers.toml}: each top-level folder's layer and, optionally, the only
    folders it may import (docs/contributing/layout.md §1). A folder missing here is a P1 error."""
    return {e['folder']: e for e in tomllib.loads(path.read_text())['layer']}


LAYERS = load_layers()
LAYER = {f: e['layer'] for f, e in LAYERS.items()}

# ------------------------------------------------------------------ the rule registry
# The rule data (severity, statement, fix, scope, section) is in docs/rules/rules.toml, the single
# source; this file holds the checks, registered by id with `@rule`.
RULES_TOML = ROOT / 'docs' / 'rules' / 'rules.toml'


def load_specs(path=RULES_TOML):
    """{id: entry of rules.toml}, in file order."""
    return {r['id']: r for r in tomllib.loads(path.read_text())['rule']}


SPECS = load_specs()
RULES = {}


def in_scope_path(spec, path):
    """Does the rule apply to `path`? `NLAlib/<Topic>` scopes cover `NLAlibScaffold/<Topic>` too;
    a path outside the library (a document) is in every library-wide rule's scope."""
    def under(prefixes):
        return any(path == q or path.startswith(q + '/') or
                   path.startswith(q.replace('NLAlib/', 'NLAlibScaffold/', 1) + '/') for q in prefixes)
    if spec['scope'] != 'library' and not under(spec['scope']):
        return False
    return not under(spec.get('exclude', []))


def rule(rid):
    """Register the check of rule `rid` (its data is the rules.toml entry); the check's
    violations outside the rule's scope are dropped."""
    spec = SPECS.get(rid)
    if spec is None or spec['check'] not in ('source', 'extraction'):
        raise SystemExit(f'check_rules: rule {rid} has no checked entry in {RULES_TOML}')

    def deco(fn):
        def scoped(c):
            vs = [v for v in fn(c) if in_scope_path(spec, v.path)]
            if spec.get('exempt') and not RULES[spec['exempt_while']]['fn'](c):
                vs = [v for v in vs if not in_scope_path({'scope': spec['exempt']}, v.path)]
            return vs
        RULES[rid] = dict(level=spec['severity'], tier='src' if spec['check'] == 'source' else 'x',
                          ref=spec['section'], text=spec['statement'], fix=spec['fix'], fn=scoped,
                          spec=spec)
        return fn
    return deco


class V:
    """A violation."""
    __slots__ = ('rule', 'path', 'line', 'decl', 'detail')

    def __init__(self, rid, path, line, decl, detail=''):
        self.rule, self.path, self.line, self.decl, self.detail = rid, path, line, decl, detail

    def text(self):
        r = RULES[self.rule] if self.rule in RULES else None
        msg = r['text'] if r else self.detail
        if r and self.detail:
            msg += ' (' + ' '.join(str(self.detail).split()) + ')'
        if r and r['fix']:
            msg += '. ' + r['fix'] + '.'
        return f'{self.rule} {self.path}:{self.line} {self.decl}: {msg}'


def topic_of_path(p):
    parts = Path(p).parts
    return parts[1] if len(parts) > 2 and parts[0] in LIBS else '(root)'


def topic_of_module(m):
    parts = m.split('.')
    return parts[1] if len(parts) > 2 else '(root)'


def has_result(doc):
    return bool(doc and re.search(r'^\s*Result:', doc, re.M))


CITE = re.compile(r'\[([A-Z][A-Za-z]+\d{4}[a-z]?)(?:,[^\]]*)?\]')
BARE_CITE = re.compile(r'\[([A-Z][A-Za-z]+\d{4}[a-z]?)\]')
NO_SOURCE = re.compile(r'(no|without a|without) (literature )?source|not in the literature|'
                       r'new here|proved here|no printed|not printed|folklore|standard\b', re.I)


def split_sig(sig):
    """(binders, conclusion) of a pretty-printed signature `Name.{u} binders :\\n  concl`."""
    m = re.match(r'[^\s{]+(?:\.\{[^}]*\})?', sig)
    i = m.end() if m else 0
    depth = 0
    while i < len(sig):
        ch = sig[i]
        if ch in '([{⦃⟨':
            depth += 1
        elif ch in ')]}⦄⟩':
            depth -= 1
        elif ch == ':' and depth == 0 and sig[i:i + 2] != ':=':
            return sig[:i], sig[i + 1:]
        i += 1
    return sig, ''


# ------------------------------------------------------------------ context
class Ctx:
    def __init__(self, root, data=None, explore_repo=None, mathlib=None):
        self.root = root
        self.files = {}
        for lib in LIBS:
            for f in sorted((root / lib).rglob('*.lean')):
                rel = f.relative_to(root).as_posix()
                text = f.read_text()
                self.files[rel] = (text, leansrc.parse(text))
        self.lib_files = {p: v for p, v in self.files.items() if p.startswith('NLAlib/')}
        self.bib = (root / BIB).read_text()
        self.guides = guide_texts(root)
        self.contrib = '\n'.join(self.guides.values())
        self.deviations = (root / DEVIATIONS).read_text()
        self.registry = tomllib.loads((root / 'docs/constants.toml').read_text())['constant']
        self.reg_names = {c['name'] for c in self.registry}
        self.target_names = target_registry_names(root)
        self.explore_repo = explore_repo
        self.mathlib = mathlib
        self._mlnames = None
        # source declarations: (path, decl dict)
        self.src_decls = [(p, d) for p, (t, x) in self.lib_files.items() for d in x['decls']]
        self.src_short = {d['full'].split('.')[-1] for p, d in self.src_decls if d['full']}
        # every docstring of the library: (path, line, owner, text, kind)
        self.alldocs = []
        for rel, (text, x) in self.lib_files.items():
            for ln, block in x['moddocs']:
                self.alldocs.append((rel, ln, '(module doc)', block, 'module'))
            for d in x['decls']:
                if d['doc']:
                    self.alldocs.append((rel, d['doc_line'], d['full'] or '(anonymous)', d['doc'],
                                         'decl'))
        self.short_mathsf = short_mathsf_names(self.contrib)
        # extraction
        self.E = data
        self.decls = data['decls'] if data else []
        for d in self.decls:
            d['line'] = int(d.get('line') or 0)
        self.by_name = {d['name']: d for d in self.decls}
        self.mod_path = {m['name']: m['path'] for m in data['modules']} if data else {}
        self.x_paths = set(self.mod_path.values())

    def path_of(self, d):
        return self.mod_path.get(d['module'], d['module'].replace('.', '/') + '.lean')

    def topic(self, d):
        return topic_of_module(d['module'])

    def code(self, p):
        return leansrc.strip_comments(self.files[p][0]).split('\n')


def guide_texts(root):
    """{path: text} of the contributor guide: `CONTRIBUTING.md` and `docs/contributing/*.md`."""
    paths = [root / 'CONTRIBUTING.md'] + sorted((root / GUIDES).glob('*.md'))
    return {p.relative_to(root).as_posix(): p.read_text() for p in paths if p.exists()}


def target_registry_names(root):
    """The definitions `docs/targets.toml` records (programs): its targets and trees, and the program
    each tree compiles (`cgProg` for `cgProg.compiled`)."""
    path = root / 'docs/targets.toml'
    if not path.exists():
        return set()
    reg = tomllib.loads(path.read_text())
    names = {e['name'] for e in reg.get('target', []) + reg.get('tree', [])}
    return names | {n.rsplit('.', 1)[0] for e in reg.get('tree', []) for n in [e['name']]}


def short_mathsf_names(contrib):
    """Registered short `\\mathsf` names (the vocabulary row "short algorithm names"):
    {short: Lean name}. The row lists pairs `` `\\mathsf{gn}` for `generalizedNystrom` ``."""
    out = {}
    for row in contrib.split('\n'):
        if row.startswith('| short algorithm names'):
            for m in re.finditer(r'`\\mathsf\{([^{}]+)\}` for `([^`]+)`', row):
                out[m.group(1)] = m.group(2)
    return out


def public_src(c):
    return [(p, d) for p, d in c.src_decls if not d['private'] and d['full']]


# ================================================================== F: file template (layout §2)
HEADER = re.compile(r'^/-\nCopyright \(c\) \d{4} [^\n]+\. All rights reserved\.\n'
                    r'Released under Apache 2\.0 license as described in the file LICENSE\.\n'
                    r'Authors: \S[^\n]*\n-/$')


@rule('F1')
def f_header(c):
    return [V('F1', p, 1, '(file)') for p, (t, x) in c.files.items()
            if not (x['header'] and HEADER.match(x['header']))]


@rule('F2')
def f_order(c):
    out = []
    for p, (t, x) in c.files.items():
        last_imp = max([ln for ln, _, _ in x['imports']] or [0])
        first_doc = min([ln for ln, _ in x['moddocs']] or [10 ** 9])
        expose = [ln for ln, l in x['commands'] if l.startswith('@[expose] public section')]
        problems = []
        if not x['has_module']:
            problems.append('no `module`')
        if first_doc < last_imp:
            problems.append('module docstring before an import')
        if not expose:
            problems.append('no `@[expose] public section`')
        elif expose[0] < first_doc < 10 ** 9:
            problems.append('`public section` before the module docstring')
        if problems:
            out.append(V('F2', p, 1, '(file)', '; '.join(problems)))
    return out


@rule('F3')
def f_import_mathlib(c):
    return [V('F3', p, ln, '(file)', mod) for p, (t, x) in c.files.items()
            for ln, pub, mod in x['imports'] if mod in ('Mathlib', 'Mathlib.Tactic')]


@rule('F4')
def f_namespace(c):
    return [V('F4', p, 1, '(file)') for p, (t, x) in c.files.items()
            if topic_of_path(p) != 'ForMathlib' and x['decls']
            and not re.search(r'^namespace NLAlib\b', t, re.M)]


@rule('F5')
def f_setoption(c):
    return [V('F5', p, ln, '(file)', l.strip()) for p, (t, x) in c.files.items()
            for ln, l in x['commands']
            if l.startswith('set_option') and not re.search(r'\bin\s*$', l)]


@rule('F6')
def f_heartbeat_comment(c):
    out = []
    for p, (t, x) in c.files.items():
        L = x['lines']
        for ln, l in x['commands']:
            if l.startswith('set_option maxHeartbeats'):
                near = ' '.join(L[max(0, ln - 4):ln - 1])
                if '--' not in near and '-/' not in near:
                    out.append(V('F6', p, ln, '(file)', l.strip()))
    return out


@rule('F7')
def f_classical(c):
    return [V('F7', p, ln, '(file)', l.strip()) for p, (t, x) in c.files.items()
            for ln, l in x['commands']
            if re.match(r'open\b.*\bClassical\b', l) and not re.search(r'\bin\s*$', l)]


@rule('F8')
def f_noncomputable(c):
    return [V('F8', p, ln, '(file)') for p, (t, x) in c.files.items() for ln, l in x['commands']
            if l.startswith('noncomputable section')]


@rule('F9')
def f_attr_instance(c):
    return [V('F9', p, ln, '(file)', l.strip()) for p, (t, x) in c.files.items()
            for ln, l in x['commands']
            if re.match(r'attribute \[instance', l) and not re.search(r'\bin\s*$', l)]


@rule('F10')
def f_length(c):
    return [V('F10', p, 1, '(file)', f"{len(x['lines'])} lines") for p, (t, x) in c.files.items()
            if len(x['lines']) > 1000]


BAD_FILE_WORDS = re.compile(r'(Part\d|Toolkit|Bundle|Aux|Misc|Helpers?|Lemmas|Extra)')


@rule('F11')
def f_name(c):
    return [V('F11', p, 1, '(file)', Path(p).stem) for p in c.files
            if BAD_FILE_WORDS.search(Path(p).stem)]


# ================================================================== P: placement and layers
@rule('P1')
def p_layer(c):
    out = []
    for p, (t, x) in c.lib_files.items():
        me = topic_of_path(p)
        for ln, pub, mod in x['imports']:
            if not mod.startswith('NLAlib.'):
                continue
            th = topic_of_module(mod)
            if me == '(root)' or th == '(root)':
                continue
            if me not in LAYER or th not in LAYER:
                unknown = me if me not in LAYER else th
                out.append(V('P1', p, ln, '(file)', f'{unknown} has no layer in docs/rules/layers.toml'))
                continue
            if LAYER[th] > LAYER[me]:
                out.append(V('P1', p, ln, '(file)', f'{me} imports {mod}'))
    return out + restricted_imports(c, 'P1')


def restricted_imports(c, rid):
    """Imports outside Mathlib and the folders a layers.toml entry checked as `rid` allows."""
    out = []
    for p, (t, x) in c.lib_files.items():
        me = topic_of_path(p)
        e = LAYERS.get(me, {})
        if e.get('rule') != rid:
            continue
        ok = tuple(f'NLAlib.{f}.' for f in [me] + e['imports'])
        for ln, pub, mod in x['imports']:
            if mod == 'Mathlib' or mod.startswith(('Mathlib.',) + ok):
                continue
            if rid == 'P1' and not mod.startswith('NLAlib.'):
                continue  # P1 is about the layers of NLAlib
            out.append(V(rid, p, ln, '(file)', f'{me} imports {mod}' if rid == 'P1' else mod))
    return out


@rule('P2')
def p_aggregator(c):
    return [V('P2', p, 1, '(file)') for p, (t, x) in c.lib_files.items() if not x['decls']]


@rule('P3')
def p_scaffold(c):
    return [V('P3', p, ln, '(file)', mod) for p, (t, x) in c.lib_files.items()
            for ln, pub, mod in x['imports'] if mod.startswith('NLAlibScaffold')]


def nl_deps(d):
    return [t for t in d.get('typeDeps') or [] if t.startswith('NLAlib.')]


@rule('P4')
def p_fm_vocab(c):
    return [V('P4', c.path_of(d), d['line'], d['name'], ', '.join(nl_deps(d))[:120])
            for d in c.decls if c.topic(d) == 'ForMathlib' and nl_deps(d)]


@rule('P5')
def p_fm_namespace(c):
    return [V('P5', p, d['line'], d['full']) for p, d in public_src(c)
            if topic_of_path(p) == 'ForMathlib' and d['full'].startswith('NLAlib.')]


@rule('P6')
def p_fm_moddoc(c):
    out = []
    for p, (t, x) in c.lib_files.items():
        if topic_of_path(p) == 'ForMathlib':
            doc = x['moddocs'][0][1] if x['moddocs'] else ''
            if not re.search(r'upstream|Mathlib candidate|for Mathlib', doc, re.I):
                out.append(V('P6', p, 1, '(module doc)'))
    return out


@rule('P7')
def p_fm_path(c):
    if not c.mathlib or not c.mathlib.exists():
        return []
    out = []
    for p in c.lib_files:
        if topic_of_path(p) == 'ForMathlib':
            rel = Path(*Path(p).parts[2:])
            if not (c.mathlib / rel).is_file():
                out.append(V('P7', p, 1, '(file)',
                             'no pinned Mathlib/' + rel.as_posix() +
                             '; review the upstream destination for this module'))
    return out


NS_ROOT_OK = re.compile(r'^(NLAlib\.|Matrix\.(IsHermitian|PosSemidef|PosDef|IsDiag|IsSymm|'
                        r'BlockTriangular|IsUpperTriangular|IsLowerTriangular|IsHadamard)\.|'
                        r'IsStarProjection\.|IsStarNormal\.|IsIdempotentElem\.|'
                        r'ProbabilityTheory\.(HasSubgaussianMGF|IndepFun|iIndepFun|HasLaw)\.|'
                        r'MeasureTheory\.HasLaw\.|Mathlib\.Meta\.Positivity\.)')


@rule('P8')
def p_ns_root(c):
    return [V('P8', p, d['line'], d['full'], '.'.join(d['full'].split('.')[:-1]))
            for p, d in public_src(c)
            if topic_of_path(p) not in ('ForMathlib', '(root)') and d['kind'] != 'instance'
            and not NS_ROOT_OK.match(d['full'])]


# Matrix vocabulary in the source statement: the pretty-printed signature drops binder types
# (`{A | A.PosDef}`, `cfc f (diagonal d)`), so `Matrix` alone misses matrix statements.
MATRIX_VOCAB = re.compile(r'\bMatrix\b|\b(?:circulant|diagonal|vecMulVec|fromBlocks)\b|mulVec|\*ᵥ|ᴴ|'
                          r'\.(?:PosDef|PosSemidef|IsHermitian|charpoly|det|trace|rank)\b')


# Final audits, 2026-10-24: a forged lemma in `NLAlibScaffold`, reached by `NLAlib` through an
# `NLAlibTools` import, was trusted as base by the replay. The library imports no other library of
# the package (read from lakefile.toml; the two named ones always), in any file or the root.
PACKAGE_LIBS = ('NLAlibScaffold', 'NLAlibTools')


def other_package_libs(root):
    lake = root / 'lakefile.toml'
    names = set(PACKAGE_LIBS)
    if lake.exists():
        names |= {l['name'] for l in tomllib.loads(lake.read_text()).get('lean_lib', [])}
    return names - {'NLAlib'}


@rule('P12')
def p_package_libs(c):
    others = other_package_libs(c.root)
    files = dict(c.lib_files)
    top = c.root / 'NLAlib.lean'
    if top.exists():
        text = top.read_text()
        files['NLAlib.lean'] = (text, leansrc.parse(text))
    return [V('P12', p, ln, '(file)', mod) for p, (t, x) in files.items()
            for ln, pub, mod in x['imports'] if mod.split('.')[0] in others]


@rule('P11')
def p_poly_imports(c):
    return restricted_imports(c, 'P11')


@rule('P9')
def p_fm_candidate(c):
    # The Polynomial layer is exempt while P11 holds (rules.toml `exempt`; maintainer decision
    # 2026-10-20): its headline scalar results stay in NLAlib/Polynomial.
    return [V('P9', c.path_of(d), d['line'], d['name']) for d in c.decls
            if c.topic(d) not in ('ForMathlib', '(root)') and d['kind'] == 'theorem'
            and not nl_deps(d) and not d['name'].startswith('Mathlib.Meta')
            and not MATRIX_VOCAB.search(d['signature'] + '\n' + (d.get('statement') or ''))
            and not re.search(r'Measure|∫|HasLaw|IndepFun|∂|Integrable|Measurable|ℙ|condExp|μ',
                              d['signature'])]


@rule('P10')
def p_lower(c):
    def_topic = {d['name']: c.topic(d) for d in c.decls}
    A = algo_defs(c)
    out = []
    for d in c.decls:
        me = c.topic(d)
        if me not in LAYER or me == 'ForMathlib' or d['kind'] != 'theorem':
            continue
        tops = {def_topic.get(t) for t in nl_deps(d)} - {None, 'ForMathlib'}
        algos = [t for t in nl_deps(d) if t in A]
        random = re.search(r'Measure|∫|HasLaw|IndepFun|∂|μ|[Mm]easurable|[Ii]ntegrable', d['signature'])
        if tops and all(LAYER.get(t, 99) < LAYER[me] for t in tops) and not algos and \
                (len(tops) == 1 or not random) and not (random and me == 'Probability'):
            out.append(V('P10', c.path_of(d), d['line'], d['name'], 'uses ' + ', '.join(sorted(tops))))
    return out


# ================================================================== S: source and proof style
@rule('S1')
def s_simp_all(c):
    return [V('S1', p, i + 1, '(proof)', l.strip()[:60]) for p in c.files
            for i, l in enumerate(c.code(p)) if re.search(r'\bsimp_all\b', l)]


@rule('S2')
def s_search(c):
    return [V('S2', p, i + 1, '(proof)', l.strip()[:60]) for p in c.files
            for i, l in enumerate(c.code(p))
            if re.search(r'\b(exact|apply|rw|simp|aesop|hint)\?(?!\s*says)', l)]


@rule('S3')
def s_decide(c):
    return [V('S3', p, i + 1, '(proof)', l.strip()[:60]) for p in c.files
            for i, l in enumerate(c.code(p))
            if re.search(r'(?<![\w.])decide\b(?!\s*:=)', l) and 'native_decide' not in l
            and 'Decidable' not in l]


@rule('S4')
def s_long_proof(c):
    out = []
    for p, (t, x) in c.files.items():
        for d in x['decls']:
            if d['kind'] in ('theorem', 'lemma', 'def', 'instance', 'irreducible_def', 'abbrev'):
                n = d['end'] - d['stmt_end']
                if n > 80:
                    out.append(V('S4', p, d['line'], d['full'] or '(instance)', f'{n} lines'))
    return out


@rule('S5')
def s_private_dup(c):
    seen = collections.defaultdict(list)
    for p, (t, x) in c.lib_files.items():
        for d in x['decls']:
            if d['private'] and d['name']:
                seen[d['name']].append((p, d['line']))
    out = []
    for n, locs in seen.items():
        if len({p for p, _ in locs}) >= 2:
            for p, ln in locs:
                out.append(V('S5', p, ln, n, f'{len(locs)} files'))
    return out


@rule('S6')
def s_instance(c):
    out = []
    for d in c.decls:
        if d['kind'] != 'instance':
            continue
        _, concl = split_sig(d['signature'])
        if not nl_deps(d):
            out.append(V('S6', c.path_of(d), d['line'], d['name'], concl.strip()[:100]))
    return out


def long_line_exempt(line):
    """S7: a line over 100 characters is allowed only when a single
    identifier or a URL makes it long: the line, after its indentation, an optional list marker
    and trailing punctuation (`name :`, `name :=`), is one token, or it contains a URL."""
    if 'http://' in line or 'https://' in line:
        return True
    toks = line.split()
    if toks and toks[0] in ('*', '-', '+') or (toks and re.fullmatch(r'\d+\.', toks[0])):
        toks = toks[1:]
    while len(toks) > 1 and toks[-1] in (':', ':=', ',', '.', '|'):
        toks = toks[:-1]
    return len(toks) == 1


@rule('S7')
def s_long_line(c):
    return [V('S7', p, i + 1, '(line)', f'{len(l)} characters') for p, (t, x) in c.files.items()
            for i, l in enumerate(x['lines']) if len(l) > 100 and not long_line_exempt(l)]


@rule('S8')
def s_longline_option(c):
    out = []
    for p, (t, x) in c.files.items():
        L = x['lines']
        starts = sorted([d['doc_line'] or d['line'] for d in x['decls']])
        for ln, l in x['commands']:
            if not l.startswith('set_option linter.style.longLine false in'):
                continue
            d = next((d for d in x['decls'] if (d['doc_line'] or d['line']) > ln), None)
            if d is None:
                continue
            body = L[ln:d['end']]
            if not any(len(s) > 100 for s in body):
                out.append(V('S8', p, ln, d['full'] or '(declaration)'))
    return out


# Final audit, 2026-10-24: `unsafe def anything (α : Sort u) : α := anything α` and
# `set_option debug.skipKernelTC true in theorem t : T := anything _` elaborate with no warning and
# no axiom. The keywords and options that switch off or bypass the kernel, in code (comments and
# docstrings stripped); in lakefile.toml, the options and arguments passed to every file.
UNSAFE_RE = re.compile(r"(?<![\w.'])(?:unsafe|partial|implemented_by|extern)(?![\w'])|skipKernelTC|"
                       r"\bset_option\s+(?:debug\.|\S*(?:[Kk]ernel|trust))|"
                       # meta code adding a declaration without the kernel (replay audit)
                       r"\b(?:addDeclCore|addDeclWithoutChecking|doCheck)\b")
LAKE_UNSAFE_RE = re.compile(r'debug\.|[Kk]ernel|trust|^\s*(?:more|weak)LeanArgs\b')


@rule('S9')
def s_unsafe(c):
    out = [V('S9', p, i + 1, '(code)', l.strip()[:80]) for p in c.files
           for i, l in enumerate(c.code(p)) if UNSAFE_RE.search(l)]
    lake = c.root / 'lakefile.toml'
    if lake.exists():
        for i, l in enumerate(lake.read_text().split('\n'), 1):
            if LAKE_UNSAFE_RE.search(l.split('#')[0]):
                out.append(V('S9', 'lakefile.toml', i, '(option)', l.strip()[:80]))
    return out


# ================================================================== T: types and shapes
def public_thms(c):
    return [d for d in c.decls if d['kind'] == 'theorem']


@rule('T1')
def t_sqrt_dot(c):
    return [V('T1', c.path_of(d), d['line'], d['name']) for d in c.decls
            if re.search(r'(√|Real\.sqrt)\s*\(?[^)]*⬝ᵥ', d['signature'])]


@rule('T2')
def t_nnreal(c):
    return [V('T2', c.path_of(d), d['line'], d['name']) for d in c.decls
            if 'toNNReal' in d['signature'] and 'toNNReal' not in d['name']
            and not d['name'].endswith('_def') and d['kind'] == 'theorem']


@rule('T3')
def t_norm_scope(c):
    return [V('T3', p, ln, '(file)', l.strip()) for p, (t, x) in c.files.items()
            for ln, l in x['commands'] if re.match(r'open.*Matrix\.Norms\.(Frobenius|Elementwise)', l)
            and not re.search(r'\bin\s*$', l)]


def matrix_vars(sig):
    out = set()
    for m in re.finditer(r'[({]([^(){}:]+?) : (?:Ω → )?Matrix ', sig):
        out.update(m.group(1).split())
    return out


@rule('T4')
def t_matrix_norm(c):
    l2 = {p for p, (t, x) in c.lib_files.items()
          if re.search(r'^open scoped.*Matrix\.Norms\.L2Operator', t, re.M)}
    out = []
    for d in c.decls:
        p = c.path_of(d)
        if p in l2 or re.search(r'norm_eq|eq_norm|Norm', d['name'].split('.')[-1]):
            continue
        for v in matrix_vars(d['signature']):
            if re.search('‖' + re.escape(v) + '‖', d['signature']):
                out.append(V('T4', p, d['line'], d['name'], f'‖{v}‖'))
                break
    return out


@rule('T5')
def t_transpose(c):
    return [V('T5', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if 'ᵀ' in d['signature'] and 'transpose' not in d['name'].lower()]


@rule('T6')
def t_fin(c):
    return [V('T6', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if re.search(r'Matrix \(Fin ', d['signature'])
            and '/Factorizations/' not in c.path_of(d) and '/Structured/' not in c.path_of(d)]


@rule('T7')
def t_real(c):
    return [V('T7', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if re.search(r'Matrix \S+ \S+ ℝ', d['signature'])
            and 'RCLike' not in d['signature']]


@rule('T8')
def t_eigbasis(c):
    return [V('T8', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if 'eigenvectorBasis' in d['signature'] and 'eigenvectorBasis' not in d['name']]


@rule('T9')
def t_proof_term(c):
    return [V('T9', c.path_of(d), d['line'], d['name']) for d in c.decls
            if d['kind'] == 'theorem' and '⋯' in d['signature']]


@rule('T10')
def t_smul_nat(c):
    out = []
    for d in c.decls:
        s = d['signature']
        for m in re.finditer(r'∀ \(?([^(),:]+) : ℕ\)?', s):
            for v in m.group(1).split():
                if re.search(r'\b' + re.escape(v) + r' •', s[m.end():]):
                    out.append(V('T10', c.path_of(d), d['line'], d['name'], v))
    return out


def conclusion_top_and(concl):
    depth = 0
    s = concl.strip()
    if s.startswith(('∃', '∀', '¬')):
        return False
    for i, ch in enumerate(s):
        if depth == 0 and (s.startswith(('fun ', 'λ', '↦', ' if '), i)):
            return False
        if ch in '([{⦃⟨':
            depth += 1
        elif ch in ')]}⦄⟩':
            depth -= 1
        elif depth == 0 and ch in '→∃∀↔':
            return False
        elif depth == 0 and ch == '∧':
            return True
    return False


@rule('T11')
def t_conj(c):
    return [V('T11', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if conclusion_top_and(split_sig(d['signature'])[1])]


@rule('T12')
def t_padded(c):
    out = []
    for d in public_thms(c):
        s = d['signature']
        for m in re.finditer(r'∃ (?:\()?(\w+)(?: : ℕ)?\)?,', s):
            v = m.group(1)
            body = s[m.end():]
            if re.search(r'(eigenvalue|singularValues) \S+ ' + re.escape(v) + r'\b', body) and not \
                    re.search(re.escape(v) + r' (<|≤|\+ 1 =|∈)', body) and \
                    not re.search(r'∃ ' + re.escape(v) + r' < ', s):
                out.append(V('T12', c.path_of(d), d['line'], d['name'], v))
    return out


@rule('T13')
def t_unused_hyp(c):
    out = []
    for d in c.decls:
        m = re.search(r'[({]_h\w*', split_sig(d['signature'])[0])
        if m:
            out.append(V('T13', c.path_of(d), d['line'], d['name'], m.group(0)[1:]))
    return out


@rule('T14')
def t_tail_measure(c):
    return [V('T14', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if c.topic(d) != 'ForMathlib'
            and re.search(r'\bμ \{[^}]*\} ≤', split_sig(d['signature'])[1])]


JENSEN_FROM = re.compile(r"\b(?:by|via|from) Jensen\b|\bJensen(?:'s inequality)? (?:from|and|applied to)\b")
JENSEN_LEMMAS = {'integral_le_sqrt_integral_sq', 'map_integral_le', 'le_map_integral',
                 'le_map_integral_of_integral_mem', 'exp_integral_le_integral', 'le_integral_comp'}


@rule('T15')
def t_jensen_corollary(c):
    out = []
    for p, d in public_src(c):
        if d['kind'] not in ('theorem', 'lemma') or not d['doc']:
            continue
        flat = ' '.join(d['doc'].split())
        for sent in re.split(r'(?<=[.;])\s+', flat):
            if not JENSEN_FROM.search(sent):
                continue
            names = {n for n in re.findall(r"`([A-Za-z_][\w'.₀-₉]*)`", sent)
                     if ('_' in n or '.' in n) and n.split('.')[-1] not in JENSEN_LEMMAS
                     and n.split('.')[-1] != d['full'].split('.')[-1]}
            if names:
                out.append(V('T15', p, d['line'], d['full'], 'from ' + ', '.join(sorted(names))))
                break
    return out


# ================================================================== V: vocabulary (vocabulary)
@rule('V1')
def v_raw_ortho(c):
    return [V('V1', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if re.search(r"\([\w'₀-₉]+ : (\w+)ᴴ \* \1 = 1\)", split_sig(d['signature'])[0])
            and 'hasorthonormalcols' not in d['name'].lower()]


@rule('V2')
def v_trunc_sub(c):
    return [V('V2', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if re.search(r'(?<!\()Fintype\.card \w+ - ', d['signature'])]


@rule('V3')
def v_gap_ratio(c):
    return [V('V3', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if re.search(r'singularValues \S+ \S+ / singularValues', d['signature'])]


@rule('V4')
def v_frob_mul(c):
    return [V('V4', c.path_of(d), d['line'], d['name']) for d in c.decls
            if re.search(r'frobNorm (\S+) \* frobNorm \1(?!\S)', d['signature'])]


@rule('V5')
def v_forbidden(c):
    pat = re.compile(r'\b(matrixExp|matrixLog|traceExp|lambdaMax|conditionNumber)\b')
    return [V('V5', p, d['line'], d['full']) for p, d in public_src(c)
            if pat.search(d['full'].split('.')[-1]) and 'deprecated' not in d['attrs']]


KEYWORDS = {'native_decide', 'mk_all', 'set_option', 'snake_case', 'irreducible_def', 'previous_latex',
            'previous_display', 'lean_body', 'exists_forall_', 'explorer_role', 'simp_all',
            'with_reducible_and_instances', 'eigenvalues₀_congr', 'body_hash', 'x_k', 'x_0',
            'implemented_by', 'exempt_while', 'exempt_reason'}


def mathlib_names(c):
    if c._mlnames is None:
        names = set()
        if c.mathlib and c.mathlib.exists():
            rx = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|public)\s+)*'
                            r'(?:theorem|lemma|def|abbrev|structure|class|instance|irreducible_def|alias)\s+'
                            r'([^\s:({\[]+)', re.M)
            for f in c.mathlib.rglob('*.lean'):
                for m in rx.finditer(f.read_text(errors='ignore')):
                    names.add(m.group(1).split('.')[-1])
        c._mlnames = names
    return c._mlnames


@rule('V6')
def v_stale_names(c):
    if not c.mathlib or not c.mathlib.exists():
        return []
    ml = mathlib_names(c)
    local = set(c.src_short) | {d['name'].split('.')[-1] for p, (t, x) in c.files.items()
                                for d in x['decls'] if d['name']}
    out = []
    # the naming guide's examples are patterns, not declarations
    texts = [(p, t) for p, t in c.guides.items() if p != f'{GUIDES}/naming.md']
    for path, full in texts + [(DEVIATIONS, c.deviations)]:
        for row in full.split('\n'):
            for tok in re.findall(r'`([^`]+)`', row):
                if re.search(r'/|\.(py|lean|toml|md|json|mjs|sh|bib)\b', tok):
                    continue  # a path or a file name, not a declaration
                for name in re.findall(r"(?:^|[\s(])((?:[A-Za-z_][\w'.₀-₉]*\.)*[a-z][\w'₀-₉]*_[\w'₀-₉]+)",
                                       tok):
                    short = name.split('.')[-1]
                    if short not in local and short not in ml and name not in KEYWORDS:
                        ln = next((i + 1 for i, r in enumerate(full.split('\n')) if r == row), 0)
                        out.append(V('V6', path, ln, name))
    return out


@rule('V7')
def v_unrecorded(c):
    text = c.contrib + c.deviations
    out = []
    for d in c.decls:
        if d['kind'] in ('def', 'structure', 'class', 'abbrev') and c.topic(d) != 'ForMathlib' \
                and d['name'] not in c.reg_names and d['name'] not in c.target_names \
                and not c.path_of(d).endswith('Targets.lean') and d.get('explorerRole') != 'support':
            # a target, a registered tree and its program are recorded by docs/targets.toml, and so
            # is a definition of a targets file (a target's count)
            short = d['name'].split('.')[-1]
            if not re.search(r'\b' + re.escape(short) + r'\b', text):
                out.append(V('V7', c.path_of(d), d['line'], d['name']))
    return out


# ================================================================== B: bounds (statements §2)
BOUND_NAME = re.compile(r'(Constant|Bound|Tail|Dim|Factor|Size|Rows|Rate|Exponent|Threshold)$')


@rule('B1')
def b_unregistered(c):
    return [V('B1', p, d['line'], d['full']) for p, d in c.src_decls
            if d['kind'] in ('def', 'irreducible_def', 'abbrev') and d['name'] and not d['private']
            and BOUND_NAME.search(d['name']) and d['full'] not in c.reg_names]


@rule('B2')
def b_exists_c(c):
    rx = re.compile(r"∃ \(?(C|c|K|C₀|c₀|C'|c'|κ|L)\b[^,]*?:\s*ℝ")
    return [V('B2', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if rx.search(d['signature']) and 'exists_forall_' not in d['name']]


def asymptotic(doc):
    return bool(re.search(r'^\s*Asymptotic:', doc or '', re.M))


@rule('B3')
def b_asym_words(c):
    return [V('B3', p, d['line'], d['full']) for p, d in public_src(c)
            if asymptotic(d['doc']) and not (re.search(r'O\(', d['doc']) and 'suffice' in d['doc'])]


@rule('B4')
def b_asym_shape(c):
    out = []
    for d in c.decls:
        if not asymptotic(d.get('doc')):
            continue
        b, concl = split_sig(d['signature'])
        probs = []
        if not concl.strip().startswith('∃'):
            probs.append('conclusion does not start with ∃')
        if re.search(r'\{[^{}]*: Type', b) or '.{' in b.split()[0]:
            probs.append('types or universes bound before the constants')
        if re.search(r'Type u_|Type\*', concl):
            probs.append('index types not `Type`')
        if probs:
            out.append(V('B4', c.path_of(d), d['line'], d['name'], '; '.join(probs)))
    return out


@rule('B5')
def b_asym_missing(c):
    out = []
    for d in public_thms(c):
        if not has_result(d.get('doc')):
            continue
        if 'exists_forall_' in d['name'] or 'Asymptotic form:' in (d.get('doc') or ''):
            continue
        b, _ = split_sig(d['signature'])
        if re.search(r'ε', b) and re.search(r'≤ ↑?\(?Fintype\.card', b):
            out.append(V('B5', c.path_of(d), d['line'], d['name']))
    return out


# ================================================================== D: docstrings (docstrings)
@rule('D1')
def d_bold(c):
    return [V('D1', p, d['line'], d['full']) for p, d in public_src(c)
            if has_result(d['doc']) and '**' not in d['doc']]


SELF_STRONG = re.compile(r'(?:[Uu]nder|[Ww]ith)\s+the\s+(?:hypotheses|assumptions|notation|setting)\s+of\s+'
                         r'(?:`[^`]+`|the [a-z ]+?)(?!`?\s*:)(?=[ ,.;)(]|$)|\bas there\b|'
                         r'(?:frames|notation|hypotheses|quantities) as in `|\bas above\b|'
                         r'[Ss]ame (?:hypotheses|setting) as|'
                         # stage 3: "as in the tail", "as in the general form", "on the same
                         # instance", "if moreover …" point at another statement for the setting
                         r'\bas in the (?!source\b|literature\b|paper\b|prototype\b)[a-z]+\b|'
                         r'\b(?:on|for|in) the same (?:instance|example|setting|data)\b|'
                         r'\b(?:[Ii]f|[Ww]hen) moreover\b')


@rule('D2')
def d_self_contained(c):
    out = []
    for p, d in public_src(c):
        m = SELF_STRONG.search(' '.join((d['doc'] or '').split()))
        if m:
            out.append(V('D2', p, d['line'], d['full'], m.group(0)[:50]))
    return out


@rule('D3')
def d_no_display(c):
    return [V('D3', c.path_of(d), d['line'], d['name']) for d in public_thms(c)
            if has_result(d.get('doc')) and '$$' not in d['doc']
            and re.search(r' / |\^ \(?-', split_sig(d['signature'])[1])]


@rule('D4')
def d_frac_inline(c):
    return [V('D4', p, ln, who) for p, ln, who, doc, k in c.alldocs
            if any(not disp and '\\frac' in s for disp, s in leansrc.math_spans(doc))]


@rule('D5')
def d_punct(c):
    return [V('D5', p, ln, who) for p, ln, who, doc, k in c.alldocs
            if re.search(r'(?<!\\)\$\$[ \t]*[.,;:](?!\w)', re.sub(r'<!--.*?-->', '', doc))
            and re.search(r'[^$]\$\$[ \t]*[.,;:]', doc)]


@rule('D6')
def d_lean_in_math(c):
    out = []
    for p, ln, who, doc, k in c.alldocs:
        for disp, s in leansrc.math_spans(doc):
            t = re.sub(r'\\(mathsf|operatorname|mathrm|text|mathit|textsf)\{[^{}]*\}', ' ', s)
            m = re.search(r'\\(texttt|mathtt)|(?<![\\a-zA-Z])[a-z]+[A-Z][a-zA-Z]+', t)
            if m:
                out.append(V('D6', p, ln, who, m.group(0)))
                break
    return out


MATH_UNI = re.compile(r'‖[^‖]*‖[₂ₖ₁*F]|[σλ][₀-₉ᵢⱼₖ]|[σλ]_|≤|≥|√|∑')
LEAN_TOK = re.compile(r'[A-Za-z]\.[A-Za-z]|\bfun\b|:=|\bMatrix\b|Finset|toLp|μ\.real|∂|∀|∃|\b[a-z]+[A-Z]\w*')


@rule('D7')
def d_unicode(c):
    out = []
    for p, ln, who, doc, k in c.alldocs:
        for m in re.finditer(r'`([^`\n]+)`', doc):
            s = m.group(1)
            if MATH_UNI.search(s) and not LEAN_TOK.search(s) and len(s) > 1 and \
                    not re.search(r' : |⬝ᵥ|•|\bhA\b|\(\w+ \w+\)', s):
                out.append(V('D7', p, ln, who, s[:40]))
                break
    return out


@rule('D8')
def d_proof_line(c):
    # a `Proof:` line, or a sentence starting `Proof:` in mid-line (stage 3)
    return [V('D8', p, ln, who) for p, ln, who, doc, k in c.alldocs
            if re.search(r'^\s*Proof:|(?:[.;:)]|\*\*|\$\$)\s+Proof(?: sketch)?:', doc, re.M)]


@rule('D9')
def d_moddoc_missing(c):
    return [V('D9', p, 1, '(file)') for p, (t, x) in c.lib_files.items() if not x['moddocs']]


@rule('D10')
def d_moddoc_shape(c):
    out = []
    for p, (t, x) in c.lib_files.items():
        if not x['moddocs']:
            continue
        ln, block = x['moddocs'][0]
        probs = []
        if not block[3:].lstrip().startswith('# '):
            probs.append('first line not `# Title`')
        if not re.search(r'^## Main (results|statements|definitions|declarations)', block, re.M):
            probs.append('no `## Main results`')
        if probs:
            out.append(V('D10', p, ln, '(module doc)', '; '.join(probs)))
    return out


@rule('D11')
def d_moddoc_names(c):
    allnames = {d['full'] for p, (t, x) in c.files.items() for d in x['decls'] if d['full']}
    out = []
    for p, (t, x) in c.lib_files.items():
        for ln, block in x['moddocs']:
            for m in re.finditer(r'^\s*[*-] `([^`\s]+)`', block, re.M):
                n = m.group(1)
                if '.' in n and not ({n, 'NLAlib.' + n} & allnames) and \
                        not n.startswith(('NLAlib/', 'docs/', 'Mathlib.', 'NLAlib.ForMathlib.')) \
                        and not re.match(r'NLAlib\.[A-Z]\w*\.[A-Z]', n):
                    out.append(V('D11', p, ln, '(module doc)', n))
    return out


def headline(doc):
    """A headline theorem: a `Result:` id or a bold name first."""
    return has_result(doc) or bool(doc and doc.lstrip().startswith('**'))


LAW_WORDS = re.compile(r'law|distribut|gaussian|haar|uniform|rademacher|normal|\\sim\b|i\.i\.d|'
                       r'sampl|invariant|countsketch|srht|random sign', re.I)


@rule('D12')
def d_hyp_omitted(c):
    out = []
    for d in public_thms(c):
        doc = d.get('doc')
        if not doc:
            continue
        b, _ = split_sig(d['signature'])
        flat = ' '.join(doc.split())
        if re.search(r'\b(?:iIndepFun|IndepFun)\b', b) and not re.search(r'independ|i\.i\.d', flat, re.I):
            out.append(V('D12', c.path_of(d), d['line'], d['name'], 'independence'))
        elif headline(doc) and 'HasLaw ' in b and not LAW_WORDS.search(flat):
            out.append(V('D12', c.path_of(d), d['line'], d['name'], 'the law'))
    return out


@rule('D13')
def d_nonempty_omitted(c):
    out = []
    for d in public_thms(c):
        doc = d.get('doc')
        if not doc or not headline(doc):
            continue
        b, _ = split_sig(d['signature'])
        ts = re.findall(r'\[Nonempty (\w+)\]', b)
        if ts and not re.search(r'non-?empty|\\ne(?:q)? \\emptyset|\\ge(?:q)? 1\b|at least one',
                                ' '.join(doc.split()), re.I):
            out.append(V('D13', c.path_of(d), d['line'], d['name'], ', '.join(ts)))
    return out


# ================================================================== M: notation (docstrings item 5)
def math_rule(rid, pat):
    rx = re.compile(pat)

    def fn(c):
        out = []
        for p, ln, who, doc, k in c.alldocs:
            for disp, s in leansrc.math_spans(doc):
                m = rx.search(s)
                if m:
                    out.append(V(rid, p, ln, who, m.group(0)))
                    break
        return out
    rule(rid)(fn)


math_rule('M1', r'\\Pr\b|\\mathbb\{P\}\s*(_\{[^}]*\}|_\w)?\s*(\\left|\\[bB]igg?l)?(\(|\\\{)')


def algo_defs(c):
    """{definition: names its docstring writes in `\\mathsf`}: definitions whose own docstring
    writes them as `\\mathsf{name}` (the Lean name or its registered short name)."""
    out = {}
    rev = collections.defaultdict(set)
    for s, full in c.short_mathsf.items():
        rev[full.split('.')[-1]].add(s)
    for d in c.decls:
        if d['kind'] in ('def', 'abbrev', 'irreducible_def') and d.get('doc'):
            short = d['name'].split('.')[-1]
            names = {short} | rev[short]
            if any('\\mathsf{' + n + '}' in d['doc'] for n in names):
                out[d['name']] = names
    return out


def mathsf_missing(c, results_only):
    A = algo_defs(c)
    out = []
    for d in c.decls:
        if d['kind'] != 'theorem' or not d.get('doc'):
            continue
        if has_result(d['doc']) != results_only:
            continue
        used = [t for t in d.get('typeDeps') or [] if t in A]
        miss = [t.split('.')[-1] for t in used if not any('\\mathsf{' + n + '}' in d['doc'] for n in A[t])]
        concl = split_sig(d['signature'])[1]
        if miss and re.search(r'\b(' + '|'.join(map(re.escape, miss)) + r')\b', concl):
            out.append((d, miss))
    return out


@rule('M2')
def m_mathsf_result(c):
    return [V('M2', c.path_of(d), d['line'], d['name'], ', '.join(miss))
            for d, miss in mathsf_missing(c, True)]


@rule('M3')
def m_mathsf_other(c):
    return [V('M3', c.path_of(d), d['line'], d['name'], ', '.join(miss))
            for d, miss in mathsf_missing(c, False)]


MATHSF_STD = {'F', 'H', 'T', 'Haar', 'OSE', 'OSI', 'JL', 'PCP'}


@rule('M4')
def m_mathsf_unknown(c):
    known = MATHSF_STD | set(c.short_mathsf) | c.src_short
    out = []
    for p, ln, who, doc, k in c.alldocs:
        seen = set()
        for disp, s in leansrc.math_spans(doc):
            for m in re.finditer(r'\\mathsf\{([^{}]+)\}', s):
                n = m.group(1).strip()
                if n not in known and n not in seen and not re.fullmatch(r'[A-Z]{1,5}|[a-z]', n):
                    seen.add(n)
                    out.append(V('M4', p, ln, who, n))
    return out


@rule('M5')
def m_mathsf_def(c):
    A = algo_defs(c)
    used = collections.Counter(t for d in c.decls if has_result(d.get('doc')) for t in d.get('typeDeps') or [])
    out = []
    for d in c.decls:
        if d['kind'] in ('def', 'abbrev') and d['name'] not in A and used[d['name']] >= 2 and \
                re.search(r': Matrix|→ Matrix', ' :' + split_sig(d['signature'])[1]):
            out.append(V('M5', c.path_of(d), d['line'], d['name'], f'used by {used[d["name"]]} results'))
    return out


math_rule('M6', r'\|_\{?(F|\\mathrm\{F\}|\\text\{F\}|\\rm F|fro|\\mathrm\{fro\})\}?(?![a-zA-Z])')
math_rule('M7', r'\^\{?(T|H|\*|\\top|\\ast|\\mathrm\{[TH]\}|\\intercal|\\dagger|\\star)\}?(?![a-zA-Z])')
math_rule('M8', r'\\(epsilon|phi)(?![a-zA-Z])')
math_rule('M9', r'\\(mathrm|text)\{(tr|Tr|rank|diag|Var|Re|adj|det|card)\}|'
          r'\\operatorname\{(Tr|trace|Rank|Diag)\}')
math_rule('M10', r'\\(mathbf|mathrm|operatorname)\{E\}\s*(\[|\\left\[|\\bigl\[)|(?<![\w\\{])E\[')
math_rule('M11', r'\\(boldsymbol|bm)\{\\[A-Z]')
math_rule('M12', r'\\(R|N|Z|C|Q|RR|NN|ZZ|eps|Set|set|abs|norm|tr)\b(?![a-zA-Z{])')
math_rule('M13', r'\\mathbb\{[Kk]\}')
math_rule('M14', r'\[\\!\[|\\lfloor\s*\\mathbf')
math_rule('M15', r'\\\|\\mathbf\{[A-Z]\}\\\|(?!_)')
math_rule('M16', r'\\(#|operatorname\{card\}|mathrm\{card\})|\\left\||'
          r'(?<![\\\w{|])\|[^|{}\n]{1,40}?(?<!\\)\|')
math_rule('M17', r'\\(succcurlyeq|preccurlyeq)')


@rule('M18')
def m_bare_matrix(c):
    out = []
    for d in c.decls:
        vs = {v for v in matrix_vars(d['signature']) if len(v) == 1 and v.isupper()}
        if not vs or not d.get('doc'):
            continue
        for disp, s in leansrc.math_spans(d['doc']):
            t = re.sub(r'\\[a-zA-Z]+', ' ', s)
            hit = [v for v in vs if re.search(r'(?<![{\w])' + v + r'(?![\w}])', t)]
            if hit:
                out.append(V('M18', c.path_of(d), d['line'], d['name'], ', '.join(hit)))
                break
    return out


# ================================================================== C: citations (docstrings)
@rule('C1')
def c_result_cited(c):
    return [V('C1', p, d['line'], d['full']) for p, d in public_src(c)
            if has_result(d['doc']) and not CITE.search(d['doc']) and not NO_SOURCE.search(d['doc'])]


@rule('C2')
def c_bare_key(c):
    out = []
    for p, ln, who, doc, k in c.alldocs:
        if k == 'decl':
            for m in BARE_CITE.finditer(doc):
                out.append(V('C2', p, ln, who, m.group(0)))
    return out


@rule('C3')
def c_math_in_bracket(c):
    return [V('C3', p, ln, who, m.group(0)[:60]) for p, ln, who, doc, k in c.alldocs
            for m in re.finditer(r'\[[A-Z][A-Za-z]+\d{4}[a-z]?,[^\]]*\$[^\]]*\]', doc)]


@rule('C4')
def c_unparsed(c):
    out = []
    pat = re.compile(r'\[([^\]\[\n`$]*?\b(?:19|20)\d{2}[a-z]?\b[^\]\[\n`$]*)\]')
    for p, ln, who, doc, k in c.alldocs:
        for m in pat.finditer(doc):
            if not CITE.fullmatch(m.group(0)) and not re.fullmatch(r'[A-Z][A-Za-z]+\d{4}[a-z]?(,.*)?',
                                                                    m.group(1)):
                out.append(V('C4', p, ln, who, m.group(0)[:60]))
    return out


def bib_entries(c):
    return [(m.group(1), m.group(2), c.bib.count('\n', 0, m.start()) + 1) for m in
            re.finditer(r'^@\w+\{([^,\s]+),(.*?)^\}', c.bib, re.M | re.S)]


@rule('C5')
def c_bib_key(c):
    return [V('C5', BIB, ln, k) for k, body, ln in bib_entries(c)
            if not re.fullmatch(r'(?:[A-Z][a-z]+(?:[A-Z][a-z]+)*(?:Van|De|Von)?)+\d{4}[a-z]?', k)]


@rule('C6')
def c_bib_dup(c):
    out = []
    keys = collections.Counter(k for k, _, _ in bib_entries(c))
    out += [V('C6', BIB, 0, k, 'key twice') for k, n in keys.items() if n > 1]
    dois = collections.defaultdict(list)
    for k, body, ln in bib_entries(c):
        m = re.search(r'doi\s*=\s*\{([^}]+)\}', body)
        if m:
            dois[m.group(1).lower()].append(k)
    out += [V('C6', BIB, 0, '/'.join(v), f'DOI {d}') for d, v in dois.items() if len(v) > 1]
    return out


@rule('C7')
def c_bib_order(c):
    E = bib_entries(c)
    return [V('C7', BIB, ln, b, f'after {a}') for (a, _, _), (b, _, ln) in zip(E, E[1:])
            if b.lower() < a.lower()]


@rule('C8')
def c_bib_unused(c):
    alltext = '\n'.join(t for t, x in c.lib_files.values())
    return [V('C8', BIB, ln, k) for k, body, ln in bib_entries(c)
            if not re.search(r'\[' + re.escape(k) + r'[\],]', alltext)]


@rule('C9')
def c_headline(c):
    return [V('C9', p, d['line'], d['full']) for p, d in public_src(c)
            if d['kind'] in ('theorem', 'lemma') and d['doc'] and d['doc'][3:].lstrip().startswith('**')
            and not CITE.search(d['doc']) and not has_result(d['doc'])]


# ================================================================== R: result ids (docstrings)
def prop_instance(d):
    """An instance of a Prop-valued class (`isLeftUnitarilyInvariant_haarFrame`) states a result."""
    return d['kind'] == 'instance' and re.match(r'(is|has)[A-Z]', d['full'].split('.')[-1])


@rule('R1')
def r_on_def(c):
    return [V('R1', p, d['line'], d['full'], d['kind']) for p, d in public_src(c)
            if has_result(d['doc']) and d['kind'] not in ('theorem', 'lemma') and not prop_instance(d)]


def lev(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def result_ids(c):
    ids = collections.defaultdict(list)
    for p, d in public_src(c):
        for m in re.finditer(r'^\s*Result:\s*(.+?)\s*(?:-/)?\s*$', d['doc'] or '', re.M):
            for r in m.group(1).split(','):
                ids[r.strip()].append((p, d['line'], d['full']))
    return ids


VARIANTS = ({'ose', 'osi'}, {'pd', 'psd'}, {'lu', 'qr'}, {'rbki', 'rsi'}, {'nysbki', 'nyssi'})


@rule('R2')
def r_near_dup(c):
    ids = result_ids(c)
    keys = sorted(ids)
    out = []
    for i, a in enumerate(keys):
        for b in keys[i + 1:]:
            if abs(len(a) - len(b)) > 2 or min(len(a), len(b)) < 8:
                continue
            pa, pb = a.split('-'), b.split('-')
            diff = [(x, y) for x, y in zip(pa, pb) if x != y]
            variant = len(pa) == len(pb) and len(diff) == 1 and (
                diff[0][1] == 'p' + diff[0][0] or diff[0][0] == 'p' + diff[0][1] or set(diff[0]) in VARIANTS)
            if not variant and lev(a, b) <= 2:
                p, ln, who = ids[b][0]
                out.append(V('R2', p, ln, who, f'{b} ~ {a}'))
    return out


@rule('R3')
def r_orphan(c):
    if not c.explore_repo:
        return []
    ids = result_ids(c)
    names = {d['full'] for p, d in public_src(c)}
    out = []
    for fn in ('collections.toml', 'results.toml', 'rates.toml', 'books.toml', 'facets.toml',
               'algorithms.toml'):
        f = c.explore_repo / fn
        if not f.exists():
            continue
        t = f.read_text()
        for m in re.finditer(r'results\s*=\s*\[([^\]]*)\]', t):
            for r in re.findall(r'"([^"]+)"|\'([^\']+)\'', m.group(1)):
                r = r[0] or r[1]
                if r not in ids:
                    out.append(V('R3', 'explore/' + fn, 0, r, 'result id'))
        for m in re.finditer(r"^(?:theorem|algorithm_definition|sketch_definition)\s*=\s*'''([^']+)'''", t, re.M):
            if m.group(1) not in names:
                out.append(V('R3', 'explore/' + fn, 0, m.group(1), 'declaration'))
        # algorithms.toml's bootstrap `definitions` lists name declarations
        defs = re.finditer(r'^\s*definitions\s*=\s*\[([^\]]*)\]', t, re.M) if fn == 'algorithms.toml' else ()
        for m in defs:
            for r in re.findall(r'"([^"]+)"', m.group(1)):
                if r not in names:
                    out.append(V('R3', 'explore/' + fn, 0, r, 'declaration'))
    return out


# ================================================================== A: algorithm tags (docstrings item 4b)
def algorithm_tag_violations(c, rid):
    """The `Algorithm:` tag problems of rule `rid`, by scripts/check_refs.py's check."""
    from check_refs import algorithm_tag_problems
    out = []
    for p, d in c.src_decls:
        if d['doc'] and 'Algorithm:' in d['doc']:
            out += [V(rid, p, d['line'], d['full'] or d['kind'], why)
                    for r, why in algorithm_tag_problems(d['doc'], d['kind']) if r == rid]
    return out


@rule('A1')
def a_format(c):
    return algorithm_tag_violations(c, 'A1')


@rule('A2')
def a_kind(c):
    return algorithm_tag_violations(c, 'A2')


@rule('A3')
def a_one(c):
    return algorithm_tag_violations(c, 'A3')


# ================================================================== G: design records
@rule('G1')
def g_deviation_fields(c):
    out = []
    lines = c.deviations.split('\n')
    for i, l in enumerate(lines):
        if not re.match(r'^## \d+\.', l):
            continue
        j = next((k for k in range(i + 1, len(lines)) if lines[k].startswith('## ')), len(lines))
        part = '\n'.join(lines[i:j])
        fields = [f.split(':')[0].split(' (')[0].strip()
                  for f in re.findall(r'^- \*\*([^*]+?)\.?\*\*', part, re.M)]
        miss = [k for k in ('Mathlib', 'NLAlib', 'Bridge', 'Why', 'Cost', 'Status')
                if not any(f.startswith(k) for f in fields)]
        if miss:
            out.append(V('G1', DEVIATIONS, i + 1, l[3:].strip()[:50], 'missing ' + ', '.join(miss)))
    return out


# ================================================================== E: programs (programs)
# E2–E4 and E9 need Lean's types and are checked by scripts/Programs.lean and scripts/Targets.lean
# (`check = "lean"`); E1 is retired (docs/design/Computation.md, F9).
COMPUTATION = 'NLAlib/Computation'
# The files that may construct `Stmt.named`: the core that defines and eliminates it, the BLAS
# kernels and the implementations.
NAMED_FILES = tuple(f'{COMPUTATION}/{f}.lean' for f in
                    ('Syntax', 'Exec', 'Subst', 'Compile', 'FirstOrder', 'BLAS', 'Dense',
                     'Sparse', 'NonInterference'))
NAMED_RE = re.compile(r'\b(?:Builder|Stmt|Computation)\.named\b|(?<![\w.])\.named\b|'
                      r'(?<![\w.])named\s+"')


@rule('E5')
def e_computation_imports(c):
    return restricted_imports(c, 'E5')


def declared_type(stmt):
    """The text after the top-level `:` of a declaration's statement, before `:=` or `where`."""
    depth, i = 0, 0
    while i < len(stmt):
        ch = stmt[i]
        if ch in '([{⦃⟨':
            depth += 1
        elif ch in ')]}⦄⟩':
            depth -= 1
        elif ch == ':' and depth == 0 and stmt[i:i + 2] != ':=':
            rest = stmt[i + 1:]
            return re.split(r':=|\bwhere\b', rest)[0]
        i += 1
    return ''


@rule('E6')
def e_semantics_home(c):
    out = []
    for p, (t, x) in c.lib_files.items():
        if p.startswith(COMPUTATION + '/'):
            continue
        for d in x['decls']:
            if d['kind'] in ('def', 'abbrev', 'instance', 'opaque', 'irreducible_def') and \
                    re.match(r'\s*(?:NLAlib\.)?(?:Computation\.)?(?:ScalarSem|Interp)\b',
                             declared_type(leansrc.strip_comments(d['stmt']))):
                out.append(V('E6', p, d['line'], d['full'] or '(instance)'))
    return out


@rule('E8')
def e_named(c):
    # A theorem may mention `named` in its statement or proof (a compile equation, say): the
    # rule is about programs, whose `named` nodes the emitter prints as calls.
    out = []
    for p, (t, x) in c.lib_files.items():
        if p in NAMED_FILES:
            continue
        proofs = {i for d in x['decls'] if d['kind'] in ('theorem', 'lemma')
                  for i in range(d['line'], d['end'] + 1)}
        for i, line in enumerate(c.code(p), 1):
            if i not in proofs and NAMED_RE.search(line):
                out.append(V('E8', p, i, '(file)', line.strip()[:80]))
    return out


# ================================================================== allowlist, baseline, main
def load_allow(path):
    if not path.exists():
        return []
    entries = tomllib.loads(path.read_text()).get('allow', [])
    for a in entries:
        if 'rule' not in a or not str(a.get('reason', '')).strip() or not ('decl' in a or 'path' in a):
            raise SystemExit(f'{path}: every [[allow]] entry has rule, decl or path, and a reason: {a}')
        if a['rule'] not in RULES:
            raise SystemExit(f'{path}: unknown rule {a["rule"]} in {a}')
    return entries


def allowed(a, v):
    return a['rule'] == v.rule and (a.get('decl') == v.decl if 'decl' in a else a['path'] == v.path)


def load_baseline(path):
    if not path.exists():
        return {}
    return json.loads(path.read_text()).get('rules', {})


def write_baseline(path, counts):
    data = {'_comment': 'Ratchet of scripts/check_rules.py (docs/contributing/checks.md §1): per error rule and file, '
                        'the violations that existed when the rule became checked. Counts may only '
                        'fall; regenerate with `python3 scripts/check_rules.py DATA.json '
                        '--update-baseline`.',
            'rules': {r: dict(sorted(f.items())) for r, f in sorted(counts.items(), key=lambda kv: rid_key(kv[0])) if f}}
    path.write_text(json.dumps(data, indent=1, ensure_ascii=False) + '\n')


def rid_key(rid):
    m = re.match(r'([A-Z]+)(\d+)', rid)
    return (m.group(1), int(m.group(2))) if m else (rid, 0)


def names_violations(c, partial):
    """N1–N18 through check_names, with its allowlist; (violations, stale entries)."""
    import check_names
    found = check_names.check(c.decls, check_names.registered_bounds(ROOT))
    allow = check_names.load_allow(ROOT / 'scripts' / 'names_allow.toml')
    ok = {(x['rule'], x['name']) for x in allow}
    flagged = {(f[0], f[1]) for f in found}
    names = {d['name'] for d in c.decls}
    out = []
    for rid, name, msg in found:
        if (rid, name) in ok:
            continue
        d = c.by_name.get(name)
        path = c.path_of(d) if d else '?'
        if rid in SPECS and d and not in_scope_path(SPECS[rid], path):
            continue
        out.append(f'{rid} {path}:{d["line"] if d else 0} {name}: {msg}')
    stale = [f'stale allowlist entry (scripts/names_allow.toml): {x["name"]} ({x["rule"]})'
             for x in allow if (x['rule'], x['name']) not in flagged
             and not (partial and x['name'] not in names)]
    return out, stale


def check_registry():
    """Every checked rule of rules.toml outside N1–N18 (scripts/check_names.py) has a check here,
    and every check has its entry."""
    missing = [r for r, sp in SPECS.items() if sp['check'] not in ('none', 'lean')
               and not r.startswith('N') and r not in RULES]
    if missing:
        raise SystemExit(f'check_rules: no check for {", ".join(missing)} ({RULES_TOML})')


check_registry()


def run(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('data', nargs='?', type=Path, help='extraction JSON (scripts/explore_data.sh)')
    ap.add_argument('--files', nargs='+', default=None, help='report and ratchet only these files')
    ap.add_argument('--only', default='', help='comma-separated rule ids')
    ap.add_argument('--warnings', action='store_true', help='print every warning')
    ap.add_argument('--warn', action='store_true', help='report, but exit 0 (warning mode)')
    ap.add_argument('--all', action='store_true', help='also print violations within the baseline')
    ap.add_argument('--partial', action='store_true', help='DATA.json covers part of the library')
    ap.add_argument('--no-names', action='store_true', help='skip the naming rules N1–N18')
    ap.add_argument('--update-baseline', action='store_true', help='rewrite the baseline (lower only)')
    ap.add_argument('--force', action='store_true', help='with --update-baseline: allow raising counts')
    ap.add_argument('--baseline', type=Path, default=BASELINE)
    ap.add_argument('--allow', type=Path, default=ALLOW)
    ap.add_argument('--explore-repo', type=Path, default=None, help="the explorer's folder, explore/ of a NLA-lib/NLA-lib.github.io checkout (R3)")
    ap.add_argument('--mathlib', type=Path, default=ROOT / '.lake/packages/mathlib/Mathlib')
    ap.add_argument('--root', type=Path, default=ROOT)
    ap.add_argument('--list', action='store_true', help='print the rules and exit')
    a = ap.parse_args(argv)
    if a.list:
        for rid in sorted(SPECS, key=rid_key):
            r = SPECS[rid]
            scope = '' if r['scope'] == 'library' else ' [' + ', '.join(r['scope']) + ']'
            print(f'{rid:4s} {r["severity"]:7s} {r["check"]:10s} {r["section"]}: {r["statement"]}{scope}')
        return 0
    data = json.loads(a.data.read_text()) if a.data else None
    c = Ctx(a.root, data, a.explore_repo, a.mathlib)
    only = {x.strip() for x in a.only.split(',') if x.strip()}
    files = None
    if a.files:
        files = set()
        for f in a.files:
            fp = Path(f).resolve()
            files.add(fp.relative_to(a.root.resolve()).as_posix() if fp.is_relative_to(a.root.resolve())
                      else f)
    ran = [rid for rid in sorted(RULES, key=rid_key)
           if (not only or rid in only) and (RULES[rid]['tier'] == 'src' or data)]

    def in_scope(rid, path):
        if files is not None and path not in files:
            return False
        if RULES[rid]['tier'] == 'x' and a.partial and path not in c.x_paths:
            return False
        return True

    allow = load_allow(a.allow)
    used_allow = set()
    found = collections.defaultdict(list)  # rid -> [V]
    for rid in ran:
        for v in RULES[rid]['fn'](c):
            hit = next((i for i, x in enumerate(allow) if allowed(x, v)), None)
            if hit is not None:
                used_allow.add(hit)
                continue
            found[rid].append(v)
    baseline = load_baseline(a.baseline)
    counts = {rid: collections.Counter(v.path for v in found[rid]) for rid in ran
              if RULES[rid]['level'] == 'error'}

    if a.update_baseline:
        if not data and any(RULES[r]['tier'] == 'x' for r in RULES):
            print('check_rules: --update-baseline needs DATA.json (the extraction rules have counts)')
            return 1
        if files or only or a.partial:
            print('check_rules: --update-baseline runs on the whole library only')
            return 1
        rises = [(rid, p, n, baseline.get(rid, {}).get(p, 0)) for rid, cnt in counts.items()
                 for p, n in cnt.items() if n > baseline.get(rid, {}).get(p, 0)]
        if rises and not a.force:
            for rid, p, n, b in rises:
                print(f'{rid} {p}: {n} violations, baseline {b}')
            print(f'check_rules: {len(rises)} counts would rise; fix them, or pass --force '
                  '(a rise needs the maintainer)')
            return 1
        new = {rid: dict(cnt) for rid, cnt in counts.items()}
        write_baseline(a.baseline, new)
        print(f'check_rules: baseline written, {sum(sum(f.values()) for f in new.values())} '
              f'violations of {sum(1 for f in new.values() if f)} rules')
        return 0

    errors, lowered, baselined = [], [], 0
    for rid, cnt in counts.items():
        base = baseline.get(rid, {})
        for p in sorted(set(cnt) | set(base)):
            if not in_scope(rid, p):
                continue
            n, b = cnt.get(p, 0), base.get(p, 0)
            vs = [v for v in found[rid] if v.path == p]
            if n > b:
                for v in vs:
                    errors.append(v.text() + (f' [{n} in this file, baseline {b}]' if b else ''))
            else:
                baselined += n
                if a.all:
                    errors_text = [v.text() + ' [baseline]' for v in vs]
                    for t in errors_text:
                        print(t)
                if n < b:
                    lowered.append(f'{rid} {p}: {n} violations, baseline {b}')
    warn = [v for rid in ran if RULES[rid]['level'] == 'warning' for v in found[rid]
            if in_scope(rid, v.path)]
    stale = [x for i, x in enumerate(allow) if i not in used_allow and x['rule'] in ran
             and files is None and not (a.partial and RULES[x['rule']]['tier'] == 'x')]
    names_out, names_stale = ([], [])
    if data and not a.no_names and (not only or any(x.startswith('N') for x in only)):
        names_out, names_stale = names_violations(c, a.partial)
        if files is not None:
            names_out = [n for n in names_out if n.split()[1].rsplit(':', 1)[0] in files]
            names_stale = []
    for t in errors:
        print(t)
    for t in names_out:
        print(t)
    if a.warnings or files is not None:
        for v in warn:
            print('warning: ' + v.text())
    for x in stale:
        print(f'stale allowlist entry (scripts/rules_allow.toml): {x["rule"]} '
              f'{x.get("decl") or x.get("path")}; it no longer matches a violation, remove it')
    for t in names_stale:
        print(t)
    if lowered:
        print('Counts below the baseline; lower it with `python3 scripts/check_rules.py DATA.json '
              '--update-baseline`:')
        for t in lowered:
            print('  ' + t)
    wcount = collections.Counter(v.rule for v in warn)
    skipped = '' if data else ' (extraction rules and N1–N18 skipped: no DATA.json)'
    nerr = len(errors) + len(names_out) + len(stale) + len(names_stale)
    print(f'check_rules: {len(ran)} rules{skipped}; {len(errors) + len(names_out)} errors, '
          f'{baselined} in the baseline, {len(warn)} warnings'
          + (' (' + ', '.join(f'{r} {n}' for r, n in sorted(wcount.items(), key=lambda kv: rid_key(kv[0])))
             + '; --warnings prints them)' if warn and not (a.warnings or files is not None) else ''))
    return 0 if a.warn else (1 if nerr else 0)


if __name__ == '__main__':
    sys.exit(run())
