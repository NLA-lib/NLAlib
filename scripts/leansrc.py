"""Textual parser for NLAlib Lean sources (column-0 commands, Mathlib style), used by
`scripts/check_rules.py`. It is not a Lean parser: it relies on the file template of docs/contributing/layout.md §2
(declarations, docstrings and commands start in column 0).

parse(text) -> dict with
  header      : the leading /- ... -/ block (str or None)
  has_module  : `module` keyword line present
  imports     : [(line, public?, module)]
  moddocs     : [(line, text)]               /-! ... -/ blocks
  commands    : [(line, text)]               other column-0 commands (set_option, open, attribute, ...)
  decls       : [dict(kind, name, full, private, attrs, line, doc, doc_line, stmt, stmt_end, end)]
Lines are 1-based. `end` is the last line before the next column-0 item.
"""
import re

KINDS = ("theorem", "lemma", "def", "irreducible_def", "structure", "abbrev", "instance",
         "class", "inductive", "alias", "opaque", "axiom", "example")
MODS = ("private", "protected", "noncomputable", "nonrec", "public", "partial", "unsafe")
DECL = re.compile(r"^((?:@\[[^\]]*\]\s*)*)((?:(?:%s)\s+)*)(%s)\b\s*([^\s:({\[⦃]*)" %
                  ("|".join(MODS), "|".join(KINDS)))


def strip_comments(code):
    """Remove `--` comments and block comments (incl. docstrings), keep line structure."""
    out, i, n, depth = [], 0, len(code), 0
    while i < n:
        if code.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and code.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        c = code[i]
        if depth:
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if code.startswith("--", i):
            j = code.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
            continue
        out.append(c)
        i += 1
    return "".join(out)


def _stmt_end(lines, start):
    """Locate the declaration body, skipping assignments in type-level `let`s.

    This remains a textual scan: bracket nesting and top-level let assignments are
    enough for the supported declaration layout. Comments and quoted text cannot
    supply assignment tokens.
    """
    depth = 0
    pending_lets = 0
    token = re.compile(r"\blet\b|:=|[()\[\]{}⦃⦄⟨⟩]|\bwhere\b|\|")
    for k in range(start, min(len(lines), start + 200)):
        text = re.sub(r'"(?:\\.|[^"\\])*"|«[^»]*»', ' ', lines[k])
        for m in token.finditer(text):
            value = m.group()
            if value in "([{⦃⟨":
                depth += 1
            elif value in ")]}⦄⟩":
                depth -= 1
            elif depth <= 0:
                if value == "let":
                    pending_lets += 1
                elif value == ":=":
                    if pending_lets:
                        pending_lets -= 1
                    else:
                        return k
                elif value == "where" and not text[m.end():].strip():
                    return k
                elif value == "|" and k > start and not text[:m.start()].strip():
                    return k
    return start


def parse(text):
    lines = text.split("\n")
    scan_lines = strip_comments(text).split("\n")
    res = {"header": None, "has_module": False, "imports": [], "moddocs": [], "commands": [],
           "decls": [], "lines": lines}
    i = 0
    if lines and lines[0].startswith("/-") and not lines[0].startswith(("/-!", "/--")):
        j = next((k for k in range(len(lines)) if "-/" in lines[k]), 0)
        res["header"] = "\n".join(lines[:j + 1])
        i = j + 1
    namespaces = []
    pending_doc = None
    pending_attrs = ""
    starts = []  # line indices of column-0 items, to compute ends
    while i < len(lines):
        line = lines[i]
        if not line or line[0] in " \t":
            i += 1
            continue
        if line.startswith("/-!") or line.startswith("/--") or (line.startswith("/-")):
            j = i
            while "-/" not in (lines[j][3:] if j == i else lines[j]):
                j += 1
                if j >= len(lines):
                    break
            block = "\n".join(lines[i:j + 1])
            if line.startswith("/-!"):
                res["moddocs"].append((i + 1, block))
                starts.append(i)
            elif line.startswith("/--"):
                pending_doc = (i + 1, block)
                starts.append(i)
            i = j + 1
            continue
        starts.append(i)
        if line.strip() == "module":
            res["has_module"] = True
        elif m := re.match(r"^(public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", line):
            res["imports"].append((i + 1, bool(m.group(1)), m.group(2)))
        elif m := re.match(r"^namespace\s+(\S+)", line):
            namespaces.append(m.group(1))
        elif m := re.match(r"^end\s+(\S+)\s*$", line):
            if namespaces and namespaces[-1] == m.group(1):
                namespaces.pop()
        elif re.match(r"^@\[[^\]]*\]\s*$", line):
            pending_attrs += line
            i += 1
            continue
        elif m := DECL.match(line):
            attrs = pending_attrs + (m.group(1) or "")
            kind = m.group(3)
            name = m.group(4)
            name_line = False
            if not name and kind not in ("instance", "example") and i + 1 < len(lines):
                name = (re.match(r"\s*([^\s:({\[]+)", lines[i + 1]) or [None, ""])[1]
                name_line = bool(name)
            full = name[7:] if name.startswith("_root_.") else ".".join(namespaces + [name]) \
                if name else None
            se = _stmt_end(scan_lines, i)
            res["decls"].append({
                "kind": kind, "name": name, "full": full, "private": "private" in m.group(2),
                "attrs": attrs, "line": i + 1, "doc": pending_doc[1] if pending_doc else None,
                "doc_line": pending_doc[0] if pending_doc else None,
                "stmt": "\n".join(lines[i:se + 1]), "stmt_end": se + 1,
                "namespaces": list(namespaces), "idx": len(starts) - 1})
            if name_line:  # `theorem` alone, the name on the next line (possibly in column 0)
                i += 1
        else:
            res["commands"].append((i + 1, line))
        pending_doc = None
        pending_attrs = ""
        i += 1
    # ends: next column-0 start after the declaration
    for d in res["decls"]:
        nxt = [s for s in starts if s > d["line"] - 1]
        end = (nxt[0] if nxt else len(lines))
        while end - 1 > d["line"] - 1 and not lines[end - 1].strip():
            end -= 1
        d["end"] = end
    return res


def math_spans(doc):
    """[(display?, text)] of $…$ and $$…$$ spans, skipping backtick code and HTML comments."""
    s = re.sub(r"<!--.*?-->", " ", doc, flags=re.S)
    s = re.sub(r"```.*?```", " ", s, flags=re.S)
    s = re.sub(r"`[^`\n]*`", " ", s)
    s = s.replace(r"\$", "  ")
    out = []
    for m in re.finditer(r"\$\$(.+?)\$\$|\$([^$]+?)\$", s, flags=re.S):
        out.append((m.group(1) is not None, m.group(1) if m.group(1) is not None else m.group(2)))
    return out


def prose(doc):
    """Docstring text with math, code and comments blanked."""
    s = re.sub(r"<!--.*?-->", " ", doc, flags=re.S)
    s = re.sub(r"`[^`\n]*`", " CODE ", s)
    s = re.sub(r"\$\$.+?\$\$|\$[^$]+?\$", " MATH ", s, flags=re.S)
    return s
