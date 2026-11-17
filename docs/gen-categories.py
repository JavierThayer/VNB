#!/usr/bin/env python3
r"""Generate the manual's categories listing (app-categories-generated.tex) from the
prover-generated reference/CATEGORIES.md.

CATEGORIES.md is written on every prover load by (write-categories-md) in
interactive.scm: the default category of every structure (its arrows, how they are
defined, the status of the three category laws), the categories declared beside a
structure with declare-category!, and the inclusions between categories, found by
the shape of the theorems.  This converter renders the same three parts as LaTeX:
a table of the default categories, a paragraph per declared category with its
defining equivalence verbatim, and the list of inclusions.

Names are shown as STORED (lower-case): VNB folds case.

Run:   python3 docs/gen-categories.py
Emits: docs/app-categories-generated.tex   (\input by ch-defs.tex)
"""
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SRC  = os.path.join(ROOT, "reference", "CATEGORIES.md")
OUT  = os.path.join(HERE, "app-categories-generated.tex")

def esc(s):
    for a, b in [('\\', r'\textbackslash{}'), ('&', r'\&'), ('%', r'\%'),
                 ('$', r'\$'), ('#', r'\#'), ('_', r'\_'), ('{', r'\{'),
                 ('}', r'\}'), ('~', r'\textasciitilde{}'), ('^', r'\textasciicircum{}'),
                 ('<', r'\textless{}'), ('>', r'\textgreater{}')]:
        s = s.replace(a, b)
    return s

def tt(s):
    """\texttt that may break after a hyphen, comma or slash: the names here are long."""
    t = esc(s)
    for c in ('-', ',', '/'):
        t = t.replace(c, c + r'\allowbreak{}')
    return r'\texttt{%s}' % t

def inline(md):
    """Markdown inline -> LaTeX: `code` becomes \texttt, [text](url) its text, the rest escaped."""
    md = re.sub(r'\[([^\]]+)\]\([^)]*\)', r'\1', md)
    out, i = [], 0
    for m in re.finditer(r'`([^`]*)`', md):
        out.append(esc(md[i:m.start()]))
        out.append(tt(m.group(1)))
        i = m.end()
    out.append(esc(md[i:]))
    txt = ''.join(out).replace(' -- ', ' --- ')
    # *emphasis* (the source links read "*Declared in* ...")
    return re.sub(r'\*([^*]+)\*', r'\\emph{\1}', txt)

def section(md, heading):
    m = re.search(r'^## %s\n(.*?)(?=^## |\Z)' % re.escape(heading), md, re.S | re.M)
    return m.group(1) if m else ''

def render_defaults(body):
    rows = []
    for line in body.splitlines():
        if not line.startswith('| `'): continue
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        if len(cells) != 7: continue
        rows.append(cells)
    o = [r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.22\linewidth}>{\raggedright\arraybackslash}p{0.30\linewidth}>{\raggedright\arraybackslash}p{0.20\linewidth}>{\raggedright\arraybackslash}p{0.18\linewidth}@{}}',
         r'\toprule', r'structure & arrows & defined & laws \\', r'\midrule', r'\endhead']
    for st, arrows, how, hs, idl, comp, inset in rows:
        laws = []
        for lab, cell in (('id', idl), ('compose', comp), ('in-set', inset)):
            status = cell.split(' -- ')[-1] if ' -- ' in cell else cell
            laws.append((lab, status))
        if all(s == 'proven' for _, s in laws):
            lawtxt = 'proven'
        else:
            lawtxt = '; '.join('%s: %s' % (l, s) for l, s in laws)
        how = how.replace('declared by `declare-hom!`', 'by `declare-hom!`')
        how = how.replace('generated from the slot list', 'generated')
        how = re.sub(r'refinement of `([^`]+)`: its parent.s arrows', r'refinement of `\1`', how)
        o.append(r'%s & %s & %s & %s \\' % (inline(st), inline(arrows), inline(how), esc(lawtxt)))
    o += [r'\bottomrule', r'\end{longtable}']
    return '\n'.join(o)


# A definition is one long line in CATEGORIES.md; set verbatim it runs off the page.  Lay it
# out: a quantifier puts its body on the next lines, indented; a connective at depth 0 starts
# each operand on a line of its own; an application too long for a line puts one argument per
# line.  Only blanks are added -- the formula's text is unchanged.
WIDTH = 66

def _split_top(s, sep):
    parts, depth, i, start = [], 0, 0, 0
    while i < len(s):
        c = s[i]
        if c in '([': depth += 1
        elif c in ')]': depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            parts.append(s[start:i]); i += len(sep); start = i; continue
        i += 1
    parts.append(s[start:])
    return parts

def _close(s, k):
    # index of the bracket closing the one opened at s[k]
    depth = 0
    for i in range(k, len(s)):
        if s[i] in '([': depth += 1
        elif s[i] in ')]':
            depth -= 1
            if depth == 0: return i
    return -1

def layout(s, ind=0):
    s = s.strip()
    pad = ' ' * ind
    if ind + len(s) <= WIDTH:
        return [pad + s]
    for conn in (' iff ', ' implies ', ' or ', ' and '):
        parts = _split_top(s, conn)
        if len(parts) > 1:
            out = layout(parts[0], ind)
            for q in parts[1:]:
                sub = layout(q, ind + len(conn) - 1)
                sub[0] = pad + conn.strip() + ' ' + sub[0].lstrip()
                out += sub
            return out
    m = re.match(r'(forall|forsome)\(\[', s)
    if m:
        k = s.index('[')
        e = _close(s, k)
        if e > 0 and s[e+1:e+3] == ', ' and s.endswith(')') and _close(s, len(m.group(1))) == len(s) - 1:
            out = [pad + s[:e+2].rstrip()]
            body = layout(s[e+3:-1], ind + 2)
            body[-1] += ')'
            return out + body
    if s.startswith('(') and _close(s, 0) == len(s) - 1:
        inner = layout(s[1:-1], ind + 1)
        inner[0] = pad + '(' + inner[0][ind + 1:]
        inner[-1] += ')'
        return inner
    m = re.match(r'[^\s(\[]+\(', s)
    if m and _close(s, m.end() - 1) == len(s) - 1:
        args = _split_top(s[m.end():-1], ', ')
        out = [pad + s[:m.end()]]
        for j, a in enumerate(args):
            sub = layout(a, ind + 2)
            sub[-1] += (',' if j < len(args) - 1 else ')')
            out += sub
        return out
    return [pad + s]

def render_declared(body):
    o = []
    blocks = re.split(r'^### ', body, flags=re.M)
    for b in blocks[1:]:
        lines = b.splitlines()
        head = lines[0].strip()
        m = re.match(r'`([^`]+)`, a category on `([^`]+)`', head)
        title = ('%s, on %s' % (m.group(1), m.group(2))) if m else head
        o.append(r'\paragraph{%s}' % tt(title))
        rest = '\n'.join(lines[1:])
        code = re.search(r'```\n(.*?)\n```', rest, re.S)
        prose = re.sub(r'```\n.*?\n```', '', rest, flags=re.S)
        for para in [p.strip() for p in prose.split('\n\n') if p.strip()]:
            if para.startswith('Definition ('):
                o.append(inline(para))
                if code:
                    o.append(r'\begin{VNBsnip}')
                    o.append('\n'.join(layout(code.group(1))))
                    o.append(r'\end{VNBsnip}')
            else:
                o.append(inline(para))
            o.append('')
    return '\n'.join(o)

def render_inclusions(body):
    items = [l[2:].strip() for l in body.splitlines() if l.startswith('- ')]
    if not items: return 'None.'
    o = [r'\begin{itemize}']
    for it in items:
        m = re.match(r'`([^`]+)` \(([^)]*)\): `(.*)`$', it)
        if m:
            o.append(r'\item %s (%s): %s' % (tt(m.group(1)), esc(m.group(2)), tt(m.group(3))))
        else:
            o.append(r'\item ' + inline(it))
    o.append(r'\end{itemize}')
    return '\n'.join(o)

def main():
    md = open(SRC, encoding='utf-8').read()
    o = ['%% AUTO-GENERATED by docs/gen-categories.py from reference/CATEGORIES.md -- do not edit.',
         '%% Regenerate:  python3 docs/gen-categories.py   (after a prover load refreshes CATEGORIES.md)',
         '',
         '% the long identifiers break only with loose spacing; \\sloppy, scoped to this file',
         r'\begingroup\sloppy',
         r'\subsubsection{The default categories}',
         'One per structure with a morphism predicate.  The laws column reads ``proven\'\' when '
         'the identity law, the composition law and the sethood of the hom-set are all proven theorems; '
         'otherwise it names the law and its status.',
         '',
         render_defaults(section(md, 'Default categories')),
         '',
         r'\subsubsection{The declared categories}',
         '',
         render_declared(section(md, 'Declared categories')),
         r'\subsubsection{Inclusions}',
         r'Theorems of the form $P(a, b, f) \Rightarrow Q(a, b, f)$ for two arrow predicates, or '
         r'$H_1(a, b) \subseteq H_2(a, b)$ for two hom-sets, found by shape.',
         '',
         render_inclusions(section(md, 'Inclusions')),
         r'\par\endgroup',
         '']
    open(OUT, 'w', encoding='utf-8').write('\n'.join(o))
    n_def = len([l for l in section(md, 'Default categories').splitlines() if l.startswith('| `')])
    n_cat = section(md, 'Declared categories').count('\n### ')
    print('wrote %s  (%d default categories, %d declared)' % (os.path.relpath(OUT, ROOT), n_def, n_cat))

if __name__ == '__main__':
    main()
