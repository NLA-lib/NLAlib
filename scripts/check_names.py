#!/usr/bin/env python3
"""Check declaration names against the naming grammar of docs/contributing/naming.md (rules N1–N18).

    python3 scripts/check_names.py DATA.json [--allow scripts/names_allow.toml] [--warn]
                                   [--partial] [--only N3,N15] [--list]

DATA.json is the extraction that `scripts/explore_data.sh` writes after `lake build NLAlib`
(name, kind, module, pretty-printed signature, docstring of every public declaration). Each
violation prints as `N<k> <full name>: <message>`; the rule ids are those of docs/contributing/naming.md.
Exit status 1 when an error-severity finding is not on the allowlist, or when an allowlist entry
is stale (its declaration is gone or no longer breaks its rule). Warning-severity findings
remain visible for review; `--warn` also makes error findings non-fatal.

The checks read Lean's pretty-printed statements with `scripts/leanexpr.py`, a bracket-depth
splitter, not a Lean parser. Reliable lexical conventions are errors; semantic head, relation,
token-occurrence and power-orientation guesses are review warnings. Operation-model aliases,
notation and local lets cannot be judged reliably from pretty printing alone. The current
boundary is documented in docs/contributing/naming.md §6; the 2026-10 naming audit is historical.
An allowlist entry is never the fix for a real violation.
"""
import argparse
import json
import re
import sys
import tomllib
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from leanexpr import (head_candidates, idents, lc_first, peel, split_signature,  # noqa: E402
                      strip_parens, top_relation)

ROOT = Path(__file__).resolve().parent.parent

# The rule statements are in docs/rules/rules.toml, the single source of the rule data
# (docs/contributing/checks.md §1); here the checked naming rules N1–N18.
_RULE_DATA = [r for r in
              tomllib.loads((ROOT / 'docs' / 'rules' / 'rules.toml').read_text())['rule']
              if r['id'].startswith('N') and r['check'] != 'none']
RULES = {r['id']: r['statement'] for r in _RULE_DATA}
SEVERITY = {r['id']: r['severity'] for r in _RULE_DATA}
SCOPES = {r['id']: r.get('scope', 'library') for r in _RULE_DATA}

REL_TOKENS = {'le', 'lt', 'eq', 'ne', 'iff', 'ge', 'gt', 'nonneg', 'pos', 'mem', 'subset', 'nonpos'}
REL_NAME = {'le': {'le', 'nonneg', 'ge', 'antitone', 'monotone', 'mono', 'anti', 'subset', 'max', 'min'},
            'lt': {'lt', 'pos', 'gt'},
            'ne': {'ne', 'pos'},
            'mem': {'mem', 'subset'},
            'subset': {'subset', 'le', 'mem'},
            'notMem': {'notMem', 'not'}}
ALLOWED_FIRST_EXTRA = {'exists', 'forall', 'ae', 'not', 'abs', 'norm', 're', 'coe', 'cast', 'natCast',
                       'ofReal', 'eq', 'le', 'lt', 'tendsto', 'isBigO', 'one', 'zero', 'two'}
# N10: outputs of algorithms; an error is `exact − <alg>` (naming §3)
ALGORITHMS = ['earlyTruncatedGeneralizedNystrom', 'earlyTruncatedNystromBKI', 'earlyTruncatedRBKI',
              'earlyTruncatedRSVD', 'generalizedNystrom', 'nystromBKI', 'nystrom', 'rsvd', 'rbki',
              'sketchAndSolve', 'hutchpp', 'girardHutchinson', 'cgIterate', 'pcgIterate', 'gmresIterate',
              'pminresIterate', 'minresIterate', 'lanczosFA', 'luLower', 'luUpper']
# N10: what may follow `<alg>_sub_`: a second approximation, or membership (`x_k - x_0 ∈ K`)
ALG_SUB_OK = {'truncatedSVD', 'mem'}
# N7
QUALITY = {'sharp', 'improved', 'tight', 'v2', 'strong', 'aux', 'main', 'key', 'thm', 'lemma',
           'hmt', 'tw', 'halko', 'tropp', 'webber', 'epperly', 'musco', 'woodruff', 'clarkson', 'meyer',
           'martinsson', 'paper', 'eq1', 'eq2', 'new', 'old', 'alt', 'prime'}
# N18: predicates whose hypothesis, as the first explicit argument, puts a theorem in their namespace
DOT_PREDICATES = {'IsHermitian': 'Matrix.IsHermitian', 'PosSemidef': 'Matrix.PosSemidef',
                  'PosDef': 'Matrix.PosDef', 'IsSVD': 'NLAlib.IsSVD',
                  'HasOrthonormalCols': 'NLAlib.HasOrthonormalCols'}
# N11: kind suffixes of named bounds (docs/constants.toml)
BOUND_SUFFIXES = ('Constant', 'Factor', 'Tail', 'Bound', 'Ratio', 'Dim')
# N4: function tokens written as notation in statements
SYMBOL_OF = {'conjTranspose': 'ᴴ', 'mulVec': '*ᵥ', 'dotProduct': '⬝ᵥ', 'kronecker': 'kroneckerMap',
             'integral': '∫', 'sqrt': '√', 'transpose': 'ᵀ', 'hadamard': '⊙', 'exp': 'exp',
             'variance': 'Var[', 'condExp': ' | ', 'rpow': ' ^ ', 'branch': 'ifThenElse'}
EXTRA_FUNC_TOKENS = {'frobNorm', 'specNorm', 'pinv', 'trace', 'det', 'rank', 'eigenvalue',
                     'singularValues', 'conjTranspose', 'quadForm', 'cfc', 'charpoly', 'submatrix',
                     'diagonal', 'fromBlocks', 'kronecker', 'dotProduct', 'mulVec', 'variance',
                     'integral', 'exp', 'log', 'sqrt', 'rpow', 'spectrum', 'condExp', 'mgf', 'transpose',
                     'hadamard', 'adjugate'}
UPPER_TOKENS_OK = {'T', 'U', 'X', 'C', 'Icc', 'Ico', 'Ioo', 'Ioc', 'Ici', 'Iic', 'Ioi', 'Iio', 'Gamma',
                   'I', 'L', 'R', 'Q', 'P'}


# ------------------------------------------------------------------ records
def record(d):
    e = dict(d)
    parts = e['name'].split('.')
    if parts[0] == 'NLAlib':
        parts = parts[1:]
    e['short'] = parts[-1]
    e['ns'] = '.'.join(parts[:-1])
    e['tok'] = e['short'].split('_')
    e['topic'] = e['module'].split('.')[1] if e['module'].count('.') else ''
    b, c = split_signature(e['signature'])
    e['binders'], e['concl'] = b, c
    e['core'], e['layers'] = peel(c)
    e['rel'] = top_relation(e['core'])
    e['doc'] = e.get('doc') or ''
    return e


def concl_part(tokens):
    """Tokens before the first `of` (the conclusion part of a name)."""
    return tokens[:tokens.index('of')] if 'of' in tokens else tokens


def hyp_part(tokens):
    return tokens[tokens.index('of') + 1:] if 'of' in tokens else []


def binder_text(e, explicit_only=False):
    return ' '.join(t for br, t in e['binders'] if br == '(' or not explicit_only)


def stat_prefix(e):
    t = e['tok']
    i = 2 if t[:2] == ['exists', 'forall'] else 0
    return t[i] if i < len(t) else ''


def is_asymptotic(e):
    return e['short'].startswith('exists_forall_') and 'Asymptotic:' in e['doc']


# ------------------------------------------------------------------ tails
def classify_tail(e):
    """(form, event, subject_has_token) for `μ(.real) {ω | P} ≤/=/< δ`, else None.
    form: 'real' | 'measure'; event: ge gt le lt both_le both_lt not_scalar not_loewner not_and
    not_pred not_other exists eq mem other."""
    r = e['rel']
    if not r or r[1] not in ('le', 'lt', 'eq'):
        return None
    lhs = strip_parens(r[0])
    m = re.match(r"^(\(?[μνκP][₀-₉']*\)?(?: \w+)?)(\.real)? \{(.*)\}$", lhs)
    if not m:
        return None
    form = 'real' if m.group(2) else 'measure'
    body = m.group(3)
    if '⫽' not in body:
        return None
    var, pred = body.split('⫽', 1)
    var = var.strip().split(':')[0].strip()
    pred = strip_parens(pred.strip())
    if pred.startswith('¬'):
        inner = strip_parens(pred[1:].strip())
        if inner.startswith('∀'):
            return form, 'not_forall', None
        ir = top_relation(inner)
        if ir and ir[1] in ('le', 'lt'):
            loewner = bool(re.search(r'• 1\b|\* \(.*\)ᴴ|ᴴ \*|smul', ir[0] + ' ' + ir[2])) and \
                not re.search(r'Norm|‖|singularValues|eigenvalue|trace|quadForm|\|', ir[0] + ir[2])
            return form, 'not_loewner' if loewner else 'not_scalar', None
        if ir and ir[1] == 'and':
            return form, 'not_and', None
        if ir is None and re.match(r'^[A-Z]\w*', inner):
            return form, 'not_pred', None
        return form, 'not_other', None
    if pred.startswith('∃'):
        return form, 'exists', None
    pr = top_relation(pred)
    if not pr:
        return form, 'other', None
    vrx = r"(?<![\w'])" + re.escape(var) + r"(?![\w'])"
    lhs_has = re.search(vrx, pr[0]) is not None
    rhs_has = re.search(vrx, pr[2]) is not None
    rel = pr[1]
    if rel in ('le', 'lt'):
        if lhs_has and rhs_has:
            return form, 'both_' + rel, None
        side = pr[2] if rhs_has and not lhs_has else pr[0]
        subj_var = 'VAR' in head_candidates(side) and not (head_candidates(side) - {'VAR', 'VAR_COE'})
        if rhs_has and not lhs_has:
            return form, {'le': 'ge', 'lt': 'gt'}[rel], not subj_var
        return form, rel, not subj_var
    return form, rel, None


def name_event(e):
    """(event token, number of relation tokens after the prefix) from the name, or None."""
    t = concl_part(e['tok'])
    pre = stat_prefix(e)
    if pre not in ('measure', 'measureReal'):
        return None
    rest = t[t.index(pre) + 1:]
    if rest and rest[0] in ('not', 'exists'):
        return rest[0], sum(1 for x in rest if x in ('le', 'lt', 'ge', 'gt', 'eq', 'mem', 'ne'))
    rels = [x for x in rest if x in ('le', 'lt', 'ge', 'gt', 'eq', 'mem', 'ne')]
    return (rels[0] if rels else None), len(rels)


# ------------------------------------------------------------------ asymptotic derivation
def derived_asymptotic(tgt):
    """CONTRIBUTING N17: `exists_forall_` + the explicit conclusion (up to its main relation for
    `integral_`/`variance_` names, RHS-shape tokens dropped) + `of_singularGapRatio_pos` for a
    gapped bound + the explicit hypotheses minus the size threshold."""
    t = tgt['tok']
    cp, hp = concl_part(t), hyp_part(t)
    idx = max((i for i, x in enumerate(cp) if x in ('le', 'lt', 'eq', 'gt', 'ge')), default=None)
    gap = idx is not None and 'singularGapRatio' in cp[idx + 1:]
    head = cp[:idx + 1] if idx is not None and stat_prefix(tgt) in ('integral', 'variance') else cp
    hyps = '_'.join(hp)
    hyps = re.sub(r'(^|_)of_[A-Za-z]+?Dim_le$', '', 'of_' + hyps if hyps else '')
    hyps = re.sub(r'(^|_)of_le_card$', '', hyps)
    parts = ['exists_forall', '_'.join(head)]
    if gap:
        parts.append('of_singularGapRatio_pos')
    if hyps:
        parts.append(hyps.lstrip('_'))
    return '_'.join(p for p in parts if p)


def dot_namespace(e):
    """The namespace N18 asks for: that of the predicate of the first explicit argument, if it is one
    of DOT_PREDICATES."""
    first = next((t for br, t in e['binders'] if br == '('), None)
    if first is None:
        return None
    m = re.match(r"^[\w'₀-₉]+ : (.+)$", first.strip())
    if not m:
        return None
    ty = m.group(1).strip()
    pm = re.match(r"^\(?[\w'₀-₉ᴴ]+(?: [^()]*)?\)?\.(IsHermitian|PosSemidef|PosDef)$", ty) or \
        re.match(r'^(IsSVD|HasOrthonormalCols)\b', ty)
    return DOT_PREDICATES[pm.group(1)] if pm else None


# ------------------------------------------------------------------ the checks
def occurs_as_notation(token, text):
    """Recognize an identifier's notation, with numeral boundaries for zero."""
    if token == 'zero' and re.search(r'(?<![\w])0(?![\w])', text):
        return True
    return bool(SYMBOL_OF.get(token) and SYMBOL_OF[token] in text)


def check(decls, registered=()):
    """Yield (rule, full name, message) for every violation."""
    D = [record(d) for d in decls]
    by_name = {e['name']: e for e in D}
    lib_defs = {e['short'] for e in D if e['kind'] in ('def', 'abbrev')}
    func_tokens = {d for d in lib_defs if len(d) > 3 and d[0].islower()} | EXTRA_FUNC_TOKENS
    thms = [e for e in D if e['kind'] == 'theorem']
    out = []

    def bad(rule, e, msg):
        scope = SCOPES[rule]
        module = e['module'].replace('.', '/')
        if isinstance(scope, list) and not any(
                module == prefix or module.startswith(prefix + '/') for prefix in scope):
            return
        out.append((rule, e['name'], msg))

    # N1 case
    for e in D:
        s, k = e['short'], e['kind']
        if k == 'theorem':
            up = [x for x in e['tok'] if x[:1].isupper() and x not in UPPER_TOKENS_OK]
            if up:
                bad('N1', e, 'theorem names are snake_case of lowerCamel tokens; UpperCamel token(s) '
                    + ', '.join(f'`{x}`' for x in up))
        elif k in ('def', 'abbrev'):
            ty = re.sub(r'\s+', ' ', e['concl']).strip()
            # Lean generates parser/attribute declaration names from syntax, including
            # punctuation and underscores. Their result type distinguishes these from
            # ordinary public data definitions; no namespace is exempted.
            parser_decl = bool(re.fullmatch(r'(?:Lean\.)?(?:Trailing)?ParserDescr', ty))
            returns_prop = bool(re.search(r'(?<![\w])Prop$', ty))
            # Universe expressions need not be a single identifier: Type (max u v).
            returns_type = bool(re.search(r'(?:^|→ |\) )(?:Type|Sort)(?:\s.*)?$', ty))
            if parser_decl:
                continue
            if '_' in s.strip('_'):
                bad('N1', e, 'a definition name has no `_`')
            elif not returns_prop and not returns_type and s[:1].isupper():
                bad('N1', e, 'a data-valued definition is lowerCamelCase')
            # Predicate components and verb APIs use lowerCamelCase (admissible,
            # contracts, inBlock), while standalone predicates use UpperCamelCase.
            # The proposition-valued result alone cannot distinguish those roles.
        elif k in ('structure', 'class') and s[:1].islower():
            bad('N1', e, 'a structure or class is UpperCamelCase')

    for e in thms:
        t, cp, hp = e['tok'], concl_part(e['tok']), hyp_part(e['tok'])
        r = e['rel']
        asym = is_asymptotic(e)

        # N5 synonyms (the spellings of naming §3)
        if 'intrinsicDim' in t:
            bad('N5', e, '`intrinsicDim` is spelt `intrinsicDimension`')
        if 'gram' in t and 'gram' not in idents(e['signature']):
            bad('N5', e, '`gram` is Mathlib\'s `Matrix.gram`; `Aᴴ * A` is `conjTranspose_mul_self`, '
                '`A * Aᴴ` is `mul_conjTranspose_self`')
        if re.search(r'(^|_)fromBlocks_diagonal(_|$)', e['short']) and 'diagonal' not in idents(e['concl']):
            bad('N5', e, '`fromBlocks A 0 0 B` is `fromBlocks_zero₁₂_zero₂₁`; Mathlib\'s '
                '`fromBlocks_diagonal` has diagonal blocks')
        if re.search(r'(^|_)(range|ker)_mulVecLin(_|$)', e['short']):
            bad('N5', e, 'the column space is `range`, the kernel `ker`, without `mulVecLin`')

        # N6 powers after their argument: `sq_f` anywhere in the conclusion part; `pow_f`, `rpow_f`
        # before the first relation (on the right a power of a compound base may lead)
        first_rel = next((i for i, x in enumerate(cp) if x in REL_TOKENS), len(cp))
        for i, x in enumerate(cp[:-1]):
            if x in ('sq', 'pow', 'rpow') and cp[i + 1] in lib_defs and \
                    not (cp[i + 1] == 'zero' and occurs_as_notation('zero', e['concl'])) and \
                    (x == 'sq' or (i < first_rel and cp[0] != 'tendsto')):
                bad('N6', e, f'`{x}_{cp[i + 1]}`: a power follows its argument '
                    f'(`{cp[i + 1]}_…_{x}`)')
                break

        # N7 quality and source words
        q = [x for x in t if x.lower() in QUALITY]
        if q:
            bad('N7', e, 'quality or source word ' + ', '.join(f'`{x}`' for x in q))

        # N10 errors are exact − computed
        for i, x in enumerate(cp[:-1]):
            if x in ALGORITHMS and cp[i + 1] == 'sub' and i + 2 < len(cp) and cp[i + 2] not in ALG_SUB_OK:
                bad('N10', e, f'`{x}_sub_{cp[i + 2]}`: an error is written `exact − computed`, '
                    f'named `…_sub_{x}`')
                break

        # N9 laws
        if stat_prefix(e) in ('integral', 'variance', 'measureReal', 'measure', 'integrable'):
            bt = binder_text(e, True)
            laws = set(re.findall(r'HasLaw (?:\([^()]*(?:\([^()]*\)[^()]*)*\)|\S+) \(?([a-z]\w*)', bt))
            if laws and not any(re.search(r'(^|_)' + law + r'(_|$)', e['short']) for law in laws):
                bad('N9', e, 'a `HasLaw` hypothesis is named `_of_hasLaw_<law>` ('
                    + ', '.join(sorted(laws)) + ')')

        if not r or r[1] in ('and', 'or') or asym:
            continue
        rel = r[1]
        lhs_c = head_candidates(r[0])
        rhs_c = head_candidates(r[2])
        if rel == 'iff':
            inner = top_relation(r[0])
            if inner and inner[1] in ('le', 'lt', 'ne', 'eq'):
                lhs_c = head_candidates(inner[0])
                if lhs_c & {'zero'}:
                    lhs_c = lhs_c | head_candidates(inner[2])

        # N3 relation token
        ok = True
        if rel in REL_NAME and rel != 'iff' and not set(cp) & REL_NAME[rel]:
            ok = False
        if rel == 'eq' and 'eq' not in cp and set(cp) & {'le', 'lt'} and 'iff' not in cp:
            ok = False
        if rel in ('le', 'lt') and 'eq' in cp and not set(cp) & {'le', 'lt', 'nonneg', 'pos', 'ge', 'gt'}:
            ok = False
        if not ok:
            where = ' (it comes after `_of_`)' if set(hp) & REL_NAME.get(rel, {rel}) else ''
            bad('N3', e, f'the conclusion is `{rel}`; its token is missing before the first `_of_`{where}')

        # N2 first token
        first = cp[0] if cp else ''
        ok = (
            (e['layers'] and e['layers'][0] in ('exists', 'existsUnique', 'ae', 'forall'))
            or 'VAR' in lhs_c or 'VAR_COE' in lhs_c
            or (first in ('measure', 'measureReal') and lhs_c & {'measure', 'measureReal'})
            or (lhs_c & {'injective', 'surjective', 'bijective', 'monotone', 'antitone', 'strictMono'}
                and lhs_c & set(cp))
            or (lhs_c & {'zero'} and ('VAR' in rhs_c or first in rhs_c))
            or first in lhs_c or first in ALLOWED_FIRST_EXTRA
            or (rel in ('le', 'lt') and first in rhs_c and set(cp) & {'nonneg', 'pos', 'ge', 'gt'})
            or first.lower() in {x.lower() for x in lhs_c}
        )
        if not ok:
            # Mathlib reads `Measure.map f ν` and `ν.map f` from the measure (`gaussianReal_map_add_const`)
            mm = re.match(r'^Measure\.map (?:\([^()]*(?:\([^()]*\)[^()]*)*\)|\S+) (.+)$', strip_parens(r[0]))
            if mm and first in head_candidates(mm.group(1)):
                ok = True
        if not ok:
            bad('N2', e, f'first token `{first}`; the conclusion starts with '
                + ', '.join(f'`{x}`' for x in sorted(lhs_c - {'VAR', 'VAR_COE'})[:4]))

        # N4 function tokens present
        concl_ids = idents(e['concl'])
        bind = binder_text(e)
        bind_ids = idents(bind) | concl_ids
        miss = [x for x in cp if x in func_tokens and x not in concl_ids
                and not occurs_as_notation(x, e['concl'])]
        miss += ['of_' + x for x in hp if x in func_tokens and x not in bind_ids
                 and not occurs_as_notation(x, bind)]
        if miss:
            bad('N4', e, 'name token(s) not in the statement: ' + ', '.join(f'`{x}`' for x in miss))

        # N13 statistics
        if lhs_c & {'integral'} and not e['ns'] and not e['short'].startswith('exists') \
                and stat_prefix(e) != 'integral':
            bad('N13', e, 'an expectation `∫ … ∂μ` on the left is named `integral_…`')
        if lhs_c & {'variance'} and stat_prefix(e) != 'variance':
            bad('N13', e, 'a variance `Var[…]` on the left is named `variance_…`')
        if lhs_c & {'integral'}:
            mi = re.match(r'^∫ \(?[^,]*\)?, (.*) ∂\S+$', strip_parens(r[0]))
            integrand = (mi.group(1) if mi else '').strip()
            if re.match(r'^(frobNorm|specNorm|nuclearNorm|schattenNorm \S+|\S+\.matrixNorm|‖)', integrand):
                rel_i = next((i for i, x in enumerate(cp) if x in REL_TOKENS), len(cp))
                has_sq, name_sq = bool(re.search(r'\^ 2$', integrand)), 'sq' in cp[:rel_i]
                if has_sq != name_sq:
                    bad('N13', e, 'the mean square `∫ ‖·‖ ^ 2` has `_sq` before the relation, '
                        'the mean `∫ ‖·‖` has none')

        # N14, N15 tails
        ct = classify_tail(e)
        if ct:
            form, ev, subj_tok = ct
            pre = stat_prefix(e)
            want = 'measureReal' if form == 'real' else 'measure'
            if pre in ('measure', 'measureReal') and pre != want:
                bad('N14', e, f'the statement is `{"μ.real" if form == "real" else "μ"} {{…}}`, '
                    f'so the prefix is `{want}_`')
            ne = name_event(e)
            if ne is not None:
                tok, nrel = ne
                if ev == 'not_scalar' or ev == 'not_forall':
                    bad('N15', e, 'a scalar event is written positively, `{ω | b < X ω}` '
                        '(`X_gt`), or `{ω | ∃ i, b < X ω i}`; `¬` only for Loewner, `∧` and predicates')
                elif ev in ('ge', 'gt', 'le', 'lt'):
                    if tok in ('le', 'lt') and ev in ('ge', 'gt'):
                        bad('N15', e, f'the event is `b {"≤" if ev == "ge" else "<"} X ω`: name the '
                            f'subject first, `X_{ev}`')
                    elif nrel < 2:
                        bad('N15', e, 'a tail name has the event relation and the tail relation')
                    elif tok != ev and subj_tok is not False:
                        bad('N15', e, f'the event is `{ev}` but the name says `{tok}`')
                elif ev in ('not_loewner', 'not_and', 'not_pred') and tok != 'not':
                    bad('N15', e, 'a negated Loewner, conjunction or predicate event is named `not_…`')
                elif ev == 'exists' and tok != 'exists':
                    bad('N15', e, 'an event `∃ …` is named `exists_…`')

    # N18 dot notation (statements §2)
    for e in thms:
        ns = dot_namespace(e)
        # only for a root name: an interface namespace (N9) or another predicate's namespace stands
        if ns and not e['ns'] and not e['short'].startswith('exists_forall_'):
            bad('N18', e, f'the first explicit argument is a `{ns.split(".")[-1]}` hypothesis, so the '
                f'theorem is `{ns}.{e["short"]}` (dot notation)')

    # N17 asymptotic forms
    for e in thms:
        if not is_asymptotic(e):
            continue
        m = re.search(r'Asymptotic:\s*`?([\w.₀-₉\']+)`?', e['doc'])
        tgt = m and (by_name.get(m.group(1)) or by_name.get('NLAlib.' + m.group(1)))
        if not tgt:
            continue  # scripts/check_refs.py reports unknown targets
        want = derived_asymptotic(tgt)
        if e['short'] != want:
            bad('N17', e, f'the asymptotic form of `{tgt["short"]}` is named `{want}`')
        if e['ns']:
            bad('N17', e, 'an asymptotic form is in the root namespace')

    # N11, N16 named bounds
    for e in D:
        if e['name'] not in registered:
            continue
        if re.search(r'(Rows|Size|Samples)$', e['short']):
            bad('N16', e, 'a sample size is named `<sketch><property>Dim`')
        elif not e['short'].endswith(BOUND_SUFFIXES):
            bad('N11', e, 'a named bound ends in ' + ', '.join(f'`{x}`' for x in BOUND_SUFFIXES))
    return out


# ------------------------------------------------------------------ allowlist and main
def load_allow(path):
    if not path.exists():
        return []
    data = tomllib.loads(path.read_text())
    entries = data.get('allow', [])
    for a in entries:
        if not {'name', 'rule', 'reason'} <= a.keys() or not a['reason'].strip():
            raise SystemExit(f'{path}: every [[allow]] entry has name, rule and a reason: {a}')
        if a['rule'] not in RULES:
            raise SystemExit(f'{path}: unknown rule {a["rule"]} for {a["name"]}')
    return entries


def registered_bounds(root):
    p = root / 'docs' / 'constants.toml'
    if not p.exists():
        return set()
    return {c['name'] for c in tomllib.loads(p.read_text()).get('constant', [])}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('data', type=Path)
    ap.add_argument('--allow', type=Path, default=ROOT / 'scripts' / 'names_allow.toml')
    ap.add_argument('--warn', action='store_true', help='report, but exit 0')
    ap.add_argument('--only', default='', help='comma-separated rule ids')
    ap.add_argument('--partial', action='store_true',
                    help='the extraction covers part of the library: an allowlisted name it does not '
                         'declare is not stale')
    ap.add_argument('--list', action='store_true', help='print the rules and exit')
    a = ap.parse_args(argv)
    if a.list:
        for k, v in RULES.items():
            print(f'{k}: {v}')
        return 0
    decls = json.loads(a.data.read_text())['decls']
    allow = load_allow(a.allow)
    found = check(decls, registered_bounds(ROOT))
    only = {x.strip() for x in a.only.split(',') if x.strip()}
    if only:
        found = [f for f in found if f[0] in only]
        allow = [x for x in allow if x['rule'] in only]
    allowed = {(x['rule'], x['name']) for x in allow}
    names = {d['name'] for d in decls}
    unallowed = [f for f in found if (f[0], f[1]) not in allowed]
    errors = [f for f in unallowed if SEVERITY[f[0]] == 'error']
    warnings = [f for f in unallowed if SEVERITY[f[0]] == 'warning']
    flagged = {(f[0], f[1]) for f in found}
    stale = [x for x in allow if (x['rule'], x['name']) not in flagged
             and not (a.partial and x['name'] not in names)]
    for rule, name, msg in errors:
        print(f'{rule} {name}: {msg}')
    for rule, name, msg in warnings:
        print(f'warning: {rule} {name}: {msg}')
    for x in stale:
        why = 'is not declared' if x['name'] not in names else f'no longer breaks {x["rule"]}'
        print(f'stale allowlist entry: {x["name"]} ({x["rule"]}) {why}; remove it')
    total = len(errors) + len(stale)
    print(f'check_names: {len(decls)} declarations, {len(errors)} violations, '
          f'{len(found) - len(unallowed)} allowlisted, {len(warnings)} review warnings, '
          f'{len(stale)} stale allowlist entries'
          + (' (warning mode)' if a.warn and total else ''))
    return 0 if a.warn or not total else 1


if __name__ == '__main__':
    sys.exit(main())
