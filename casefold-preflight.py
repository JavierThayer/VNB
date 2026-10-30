#!/usr/bin/env python3
"""casefold-preflight.py FILE.scm [FILE.scm ...]

MIT Scheme and the VNB reader fold symbols to lower case, so two identifiers that differ only
by case are ONE identifier.  This tool lists every such pair in a Scheme file:

  * SCHEME BINDERS: names introduced by define (variable, procedure, parameters), lambda /
    named-lambda parameters, let / let* / letrec / letrec* / fluid-let / named-let / do binders.
  * STATEMENT SYMBOLS: symbols inside quoted data within an (sp ...) or (make-wff ...) form.

Three levels:
  SCOPE  a binder introduced while a case-variant binder is lexically visible (it SHADOWS it:
         (let* ((z ...) (Z (list '- z u))) ...) makes the second binding replace the first), or a
         reference whose spelling resolves to a case-variant binder.  This is how every collision
         of the week bit.  Exit status 1 when any is found.
  TOP    a local binder shadowing a top-level define of another spelling (harmless unless the
         top-level one is meant inside that scope; then a SCOPE reference hit appears too).
  FORM   two spellings in the same top-level form, in disjoint scopes (harmless today, one
         rename away from a SCOPE hit).
  file   two spellings in different top-level forms (one symbol, usually harmless).
Statement symbols are paired within one sp / make-wff form only (FORM level): inside a quoted
statement the two spellings ARE one variable.

The file is read with an s-expression tokenizer that honours strings, character literals,
line comments (;), block comments (#| ... |#, nested) and datum comments (#;), so a name inside
a string or a comment is never reported.
Integrator tooling (Python); it changes nothing.
"""
import sys
from collections import defaultdict

DELIMS = set('()[]";\'`,')
WS = set(' \t\r\n\f')


class Sym:
    __slots__ = ('name', 'line')

    def __init__(self, name, line):
        self.name, self.line = name, line


class Node(list):
    """A parsed list; .line is the line of its opening paren, .quoted marks a quote prefix."""
    line = 0
    prefix = None


def tokenize(text):
    i, n, line = 0, len(text), 1
    toks = []
    while i < n:
        ch = text[i]
        if ch == '\n':
            line += 1; i += 1; continue
        if ch in WS:
            i += 1; continue
        if ch == ';':
            while i < n and text[i] != '\n':
                i += 1
            continue
        if ch == '#' and i + 1 < n and text[i + 1] == '|':
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith('|#', i):
                    depth -= 1; i += 2
                elif text.startswith('#|', i):
                    depth += 1; i += 2
                else:
                    if text[i] == '\n':
                        line += 1
                    i += 1
            continue
        if ch == '#' and i + 1 < n and text[i + 1] == ';':
            toks.append(('DATUMCOMMENT', None, line)); i += 2; continue
        if ch == '#' and i + 1 < n and text[i + 1] == '\\':
            j = i + 3
            while j < n and text[j] not in WS and text[j] not in '()[]':
                j += 1
            toks.append(('ATOM', None, line)); i = j; continue
        if ch == '"':
            j = i + 1
            while j < n and text[j] != '"':
                if text[j] == '\\':
                    j += 1
                elif text[j] == '\n':
                    line += 1
                j += 1
            toks.append(('ATOM', None, line)); i = j + 1; continue
        if ch in '([':
            toks.append(('OPEN', None, line)); i += 1; continue
        if ch == '#' and i + 1 < n and text[i + 1] == '(':
            toks.append(('OPEN', None, line)); i += 2; continue
        if ch in ')]':
            toks.append(('CLOSE', None, line)); i += 1; continue
        if ch in "'`":
            toks.append(('QUOTE', ch, line)); i += 1; continue
        if ch == ',':
            if i + 1 < n and text[i + 1] == '@':
                toks.append(('QUOTE', ',@', line)); i += 2
            else:
                toks.append(('QUOTE', ',', line)); i += 1
            continue
        j = i
        if ch == '|':
            j = i + 1
            while j < n and text[j] != '|':
                j += 1
            toks.append(('ATOM', None, line)); i = j + 1; continue
        while j < n and text[j] not in WS and text[j] not in DELIMS and text[j] not in ')]([':
            j += 1
        toks.append(('SYM', text[i:j], line)); i = j
    return toks


def parse(toks):
    pos = 0

    def datum():
        nonlocal pos
        kind, val, line = toks[pos]
        pos += 1
        if kind == 'OPEN':
            node = Node(); node.line = line
            while pos < len(toks) and toks[pos][0] != 'CLOSE':
                d = datum()
                if d is not None:
                    node.append(d)
            pos += 1
            return node
        if kind == 'QUOTE':
            inner = datum()
            q = Node(); q.line = line; q.prefix = val
            q.append(Sym('quote' if val == "'" else 'quasiquote' if val == '`' else 'unquote', line))
            q.append(inner)
            return q
        if kind == 'DATUMCOMMENT':
            datum()                      # skip the next datum
            return None
        if kind == 'SYM':
            return Sym(val, line)
        if kind == 'CLOSE':
            return None
        return None                      # ATOM: strings, chars

    forms = []
    while pos < len(toks):
        d = datum()
        if d is not None:
            forms.append(d)
    return forms


def is_name(s):
    if not isinstance(s, Sym):
        return False
    t = s.name
    if t == '.' or not any(c.isalpha() for c in t):
        return False
    try:
        float(t.replace('/', 'e0').rstrip('e0') or 'x')
        return False
    except ValueError:
        pass
    return t.lower() != t.upper()


def head(node):
    return node[0].name.lower() if isinstance(node, Node) and node and isinstance(node[0], Sym) else None


def collect(forms):
    binders = []                         # (name, line, form_index)
    stmt = []                            # (name, line, form_index, statement_id)

    def params(p, fi):
        if isinstance(p, Sym):
            if is_name(p):
                binders.append((p.name, p.line, fi))
        elif isinstance(p, Node):
            for x in p:
                params(x, fi)

    def quoted_syms(x, fi, sid):
        if isinstance(x, Sym):
            if is_name(x):
                stmt.append((x.name, x.line, fi, sid))
        elif isinstance(x, Node):
            for y in x:
                quoted_syms(y, fi, sid)

    def walk(x, fi, sid, in_quote):
        if not isinstance(x, Node):
            return
        h = head(x)
        if h in ('quote', 'quasiquote') and len(x) > 1:
            if sid is not None:
                quoted_syms(x[1], fi, sid)
            if h == 'quasiquote':
                walk(x[1], fi, sid, True)
            return
        if in_quote and h != 'unquote':
            for y in x:
                walk(y, fi, sid, True)
            return
        if h in ('sp', 'make-wff') and sid is None:
            sid = (fi, x.line)
        if h == 'define' and len(x) > 1:
            params(x[1], fi)
        elif h in ('lambda', 'named-lambda') and len(x) > 1:
            params(x[1], fi)
        elif h in ('let', 'let*', 'letrec', 'letrec*', 'fluid-let', 'let-values', 'let*-values') and len(x) > 1:
            k = 1
            if isinstance(x[1], Sym):            # named let
                params(x[1], fi); k = 2
            if len(x) > k and isinstance(x[k], Node):
                for b in x[k]:
                    if isinstance(b, Node) and b:
                        params(b[0], fi)
        elif h == 'do' and len(x) > 1 and isinstance(x[1], Node):
            for b in x[1]:
                if isinstance(b, Node) and b:
                    params(b[0], fi)
        for y in x:
            walk(y, fi, sid, False)

    for fi, f in enumerate(forms):
        walk(f, fi, None, False)
    return binders, stmt


def scoped(forms):
    """Walk with lexical scope.  Report a binder introduced while a case-variant spelling is
    visible (shadowing), and a reference whose spelling resolves to a case-variant binder."""
    hits = []                                    # (line, message)
    info = []                                    # local shadowing a top-level define
    seen = set()

    def note(line, msg):
        if (line, msg) not in seen:
            seen.add((line, msg)); hits.append((line, msg))

    def bind(env, s, top=False):
        if not is_name(s):
            return
        k = s.name.lower()
        if k in env and env[k][0] != s.name:
            if env[k][2] and not top:
                info.append((s.line, "local %s shadows the top-level %s (line %d); harmless unless %s is meant inside"
                             % (s.name, env[k][0], env[k][1], env[k][0])))
            else:
                note(s.line, "binder %s %s %s (bound at line %d)"
                     % (s.name, "REDEFINES" if top else "shadows", env[k][0], env[k][1]))
        env[k] = (s.name, s.line, top)

    def bind_params(env, p):
        if isinstance(p, Sym):
            bind(env, p)
        elif isinstance(p, Node):
            for x in p:
                bind_params(env, x)

    def prescan_defines(body, env, top=False):
        for x in body:
            if isinstance(x, Node) and head(x) == 'define' and len(x) > 1:
                n = x[1][0] if isinstance(x[1], Node) and x[1] else x[1]
                bind(env, n, top)

    def ev(x, env):
        if isinstance(x, Sym):
            if is_name(x):
                k = x.name.lower()
                if k in env and env[k][0] != x.name:
                    note(x.line, "reference %s resolves to %s (bound at line %d)" % (x.name, env[k][0], env[k][1]))
            return
        if not isinstance(x, Node) or not x:
            return
        h = head(x)
        if h in ('quote', 'quasiquote'):
            return
        if h == 'define' and len(x) > 1:
            if isinstance(x[1], Node) and x[1]:
                inner = dict(env)
                bind_params(inner, Node(x[1][1:]))
                prescan_defines(x[2:], inner)
                for y in x[2:]:
                    ev(y, inner)
            else:
                for y in x[2:]:
                    ev(y, env)
            return
        if h in ('lambda', 'named-lambda') and len(x) > 1:
            inner = dict(env)
            bind_params(inner, x[1] if h == 'lambda' else Node(x[1][1:]) if isinstance(x[1], Node) else x[1])
            prescan_defines(x[2:], inner)
            for y in x[2:]:
                ev(y, inner)
            return
        if h in ('let', 'let*', 'letrec', 'letrec*', 'fluid-let') and len(x) > 1:
            k = 1
            inner = dict(env)
            if isinstance(x[1], Sym):
                bind(inner, x[1]); k = 2
            bs = x[k] if len(x) > k and isinstance(x[k], Node) else Node()
            if h == 'let*':
                for b in bs:
                    if isinstance(b, Node) and b:
                        for y in b[1:]:
                            ev(y, inner)
                        bind_params(inner, b[0])
            elif h in ('letrec', 'letrec*'):
                for b in bs:
                    if isinstance(b, Node) and b:
                        bind_params(inner, b[0])
                for b in bs:
                    if isinstance(b, Node) and b:
                        for y in b[1:]:
                            ev(y, inner)
            else:
                for b in bs:
                    if isinstance(b, Node) and b:
                        for y in b[1:]:
                            ev(y, env)
                for b in bs:
                    if isinstance(b, Node) and b:
                        bind_params(inner, b[0])
            prescan_defines(x[k + 1:], inner)
            for y in x[k + 1:]:
                ev(y, inner)
            return
        for y in x:
            ev(y, env)

    top = {}
    prescan_defines(forms, top, True)
    for f in forms:
        ev(f, top)
    return sorted(hits), sorted(set(info))


def report(path):
    text = open(path, encoding='utf-8', errors='replace').read()
    forms = parse(tokenize(text))
    binders, stmt = collect(forms)
    out, high = [], 0

    def pairs(items, kind, group_key):
        nonlocal high
        groups = defaultdict(lambda: defaultdict(list))
        for it in items:
            groups[it[0].lower()][it[0]].append(it)
        for key in sorted(groups):
            spell = groups[key]
            if len(spell) < 2:
                continue
            names = sorted(spell)
            for i in range(len(names)):
                for j in range(i + 1, len(names)):
                    a, b = spell[names[i]], spell[names[j]]
                    shared = {group_key(x) for x in a} & {group_key(y) for y in b}
                    level = 'HIGH' if shared else 'low'
                    if shared:
                        high += 1
                    la = ','.join(str(x[1]) for x in sorted(set(a), key=lambda t: t[1])[:6])
                    lb = ','.join(str(y[1]) for y in sorted(set(b), key=lambda t: t[1])[:6])
                    out.append((0 if shared else 1, '%-4s %-9s %s (lines %s)  vs  %s (lines %s)%s' % (
                        level, kind, names[i], la, names[j], lb,
                        '' if not shared else '  same form at line %s' % min(
                            x[1] for x in a if group_key(x) in shared))))

    pairs(binders, 'binder', lambda t: t[2])
    pairs(stmt, 'statement', lambda t: t[3])
    out.sort()
    sc, info = scoped(forms)
    print('== %s: %d SCOPE, %d TOP, %d FORM, %d file' % (path, len(sc), len(info), high, len(out) - high))
    for line, msg in sc:
        print('  SCOPE line %d: %s' % (line, msg))
    for line, msg in info:
        print('  TOP   line %d: %s' % (line, msg))
    for _, line in out:
        print('  ' + line.replace('HIGH', 'FORM').replace('low ', 'file'))
    return len(sc)


def main(argv):
    if len(argv) < 2:
        print(__doc__); return 2
    total = 0
    for p in argv[1:]:
        total += report(p)
    return 1 if total else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
