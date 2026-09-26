#!/usr/bin/env python3
r"""Generate the manual's tactic reference (app-tactics-generated.tex) from the
prover-generated reference/TACTICS.md.

TACTICS.md is emitted from the live `*tactic-help*` registry on every prover load
(tactics-help.scm), so it is always current -- it carries the real short-form
names, signatures, trust `kind`s, and the full per-tactic help.  This converter
renders it to a self-contained LaTeX reference: one ENTRY per tactic (signature,
kind, one-line summary, "when useful", and the full explanation), grouped as in
the source.  The manual is thereby the reference on its own -- it does not send
the reader to the browser TACTICS.md for the prose.

Each entry also carries a "uses" line: every kernel operation the command can cause to
be recorded.  That is not in the registry -- it is measured, by reading the source of the
command and of every procedure it calls -- so it comes from the kernel map, through
gen-tactic-uses.py, which composes it from reference/kernel-map-static.sexp.  An entry
for a command the measurement does not cover simply has no such line.

Run:   python3 docs/gen-tactics-ref.py
Emits: docs/app-tactics-generated.tex   (\input by ch-proofs.tex)
"""
import os, re, importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SRC  = os.path.join(ROOT, "reference", "TACTICS.md")
OUT  = os.path.join(HERE, "app-tactics-generated.tex")


def _load_uses():
    """(command -> [operation]), and the widest reach, from gen-tactic-uses.py.
    The module's file name is not an identifier, so it is loaded by path."""
    spec = importlib.util.spec_from_file_location(
        "gen_tactic_uses", os.path.join(HERE, "gen-tactic-uses.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    rows, widest = mod.tactic_uses()
    return {name: ops for name, ops, _ in rows}, len(widest)


USES, USES_WIDEST = _load_uses()

SKIP_GROUPS = {"Entering arguments", "Tactic kinds (trust taxonomy)"}

def esc(s):
    """LaTeX-escape prose. Backtick and apostrophe are LEFT AS-IS: they are safe
    in LaTeX text (render as quotes) and the source uses `x' Lisp-style quoting
    that renders correctly. Markdown code spans `x` thus become quoted rather
    than typewritten -- a deliberate, compile-safe simplification."""
    out = []
    for c in s:
        out.append({'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$',
                    '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}',
                    '~': r'\textasciitilde{}', '^': r'\textasciicircum{}'}.get(c, c))
    return re.sub(r'"([^"]*)"', r"``\1''", ''.join(out))   # straight -> LaTeX double quotes

def esctt(s):
    r"""Escape for \texttt (code)."""
    return esc(s)

CODE_INDENT = re.compile(r'^\s{4,}\S')   # a blurb line that is indented example code

# makeindex and LaTeX each have their own special characters, and VNB names hit
# both: `warrant!' ends in ! (makeindex's subentry separator), `card-star(a_)'
# contains _ (LaTeX math-mode shift).  An index entry is  sortkey@printedform ,
# so the two halves need DIFFERENT escaping -- the sort key is plain text
# makeindex compares, the printed form is LaTeX it typesets.
_IDX_CTRL = '!@|"'                       # makeindex control characters
_TEX_ESC = {'\\': '\\textbackslash{}', '{': '\\{', '}': '\\}', '$': '\\$',
            '&': '\\&', '#': '\\#', '^': '\\^{}', '_': '\\_',
            '%': '\\%', '~': '\\~{}'}

def _idx_quote(s):                       # protect makeindex's own metacharacters
    return ''.join(('"' + c) if c in _IDX_CTRL else c for c in s)

def idx(name, note=''):
    key = _idx_quote(name)                                   # sorts on the bare name
    shown = _idx_quote(''.join(_TEX_ESC.get(c, c) for c in name))
    tail = (' (%s)' % note) if note else ''
    return '\\index{%s@\\texttt{%s}%s}' % (key, shown, tail)


def parse(md):
    """Return [(group_title, [entry, ...]), ...] where entry is a dict with keys
    sig, kind, short, when, long (long is a list of raw lines)."""
    lines = md.splitlines()
    groups, cur_group, cur_entries = [], None, []
    i, n = 0, len(lines)
    def flush():
        if cur_group and cur_entries:
            groups.append((cur_group, list(cur_entries)))
    while i < n:
        line = lines[i]
        m2 = re.match(r'^## (.+?)\s*$', line)
        if m2:
            flush()
            title = m2.group(1)
            cur_group = None if title in SKIP_GROUPS else title
            cur_entries = []
            i += 1
            continue
        m3 = re.match(r'^### (.+?)\s*$', line)
        if m3 and cur_group is not None:
            name = m3.group(1)
            j = i + 1
            block = []
            while j < n and not re.match(r'^#{2,3} ', lines[j]):
                block.append(lines[j]); j += 1
            entry = classify(name, block)
            cur_entries.append(entry)
            i = j
            continue
        i += 1
    flush()
    return groups

def classify(name, block):
    """Split an entry block into sig / kind / short / when / long-lines."""
    sig, kind, short, when = name, '', '', ''
    kind_idx = when_idx = short_idx = uses_idx = None
    for k, bl in enumerate(block):
        if re.match(r'^    \S', bl) and sig == name:
            sig = bl.strip()
        elif bl.startswith('*Kind:*'):
            km = re.search(r'`([^`]+)`', bl)
            if km: kind = km.group(1)
            kind_idx = k
        elif bl.startswith('*When useful:*'):
            when = bl[len('*When useful:*'):].strip()
            when_idx = k
        elif bl.startswith('*Uses:*'):
            # TACTICS.md carries the same measured line; it is regenerated here
            # from the kernel map, so the source line is noted and dropped rather
            # than falling through into the explanation as prose.
            uses_idx = k
        elif bl.strip() and not bl.startswith('*') and not re.match(r'^    ', bl) and not short:
            short = bl.strip()
            short_idx = k
    # the long explanation is everything after the LAST of the field lines -- the
    # short summary, then Kind, Uses and When useful, in whatever order the source
    # emits them -- so that a field line never falls through into the prose.
    found = [i for i in (short_idx, kind_idx, uses_idx, when_idx) if i is not None]
    start = max(found) if found else None
    long_lines = block[start + 1:] if start is not None else []
    # trim leading / trailing blank lines
    while long_lines and not long_lines[0].strip(): long_lines.pop(0)
    while long_lines and not long_lines[-1].strip(): long_lines.pop()
    return dict(name=name, sig=sig, kind=kind, short=short, when=when, long=long_lines)

def render_long(lines):
    """Render the long-explanation lines: prose paragraphs (blank-line separated),
    with indented example blocks passed through verbatim."""
    o, para = [], []
    def flush_prose():
        if para:
            o.append(esc(' '.join(x.strip() for x in para)))
            o.append('')
            para.clear()
    i, n = 0, len(lines)
    while i < n:
        ln = lines[i]
        if not ln.strip():
            flush_prose(); i += 1; continue
        if CODE_INDENT.match(ln):
            flush_prose()
            code = []
            while i < n and (CODE_INDENT.match(lines[i]) or not lines[i].strip()):
                # keep code lines; stop the run at a blank followed by non-code
                if not lines[i].strip():
                    if i + 1 < n and not CODE_INDENT.match(lines[i + 1]):
                        break
                    code.append('')
                else:
                    code.append(lines[i].rstrip())
                i += 1
            while code and not code[-1].strip(): code.pop()
            o.append('\\begin{VNBsnip}')      # fancyvrb: true verbatim, handles ~ < & # etc.
            o.extend(code)
            o.append('\\end{VNBsnip}')
            o.append('')
        else:
            para.append(ln); i += 1
    flush_prose()
    return o

def uses_line(name):
    """The measured `Uses' line for one entry, already LaTeX, or '' if the kernel
    map does not cover the command."""
    ops = USES.get(name)
    if ops is None:
        return ''
    if not ops:
        return 'no kernel operation: it records no inference.'
    if len(ops) == USES_WIDEST:
        return 'every one of the %d kernel operations.' % USES_WIDEST
    return ' '.join('\\texttt{%s}' % esc(op) for op in ops) + '.'


def render(groups):
    o = []
    o.append('%% AUTO-GENERATED by docs/gen-tactics-ref.py from reference/TACTICS.md -- do not edit.')
    o.append('%% Regenerate:  python3 docs/gen-tactics-ref.py   (after a prover load refreshes TACTICS.md)')
    o.append('')
    o.append('\\DeclareRobustCommand{\\tactkind}[1]{{\\footnotesize\\textsc{#1}}}')
    o.append('')
    o.append('Every tactic is tagged with a \\emph{kind} grounded in the '
             '\\texttt{dg-apply-rule!} tag it emits, so the trusted base is legible: '
             '\\texttt{rule} is a single primitive kernel inference (the fixed trusted '
             'base); \\texttt{oracle} is a trusted decision procedure run as a black box; '
             '\\texttt{composite} only chains kernel rules, adding no new inference; '
             '\\texttt{meta} performs no deduction (session, search, navigation).  A '
             'proof\'s trust surface is exactly its \\texttt{rule} steps plus whichever '
             '\\texttt{oracle}s and asserted premises it cites.\n')
    o.append('The same reference is available at the REPL with \\texttt{(tactics \'name)} '
             'and in the browser file \\texttt{reference/TACTICS.md}; all three are '
             'generated from one registry, so they never disagree.\n')
    o.append('An entry\'s \\emph{Uses} line names every kernel operation the command\'s own '
             'code can cause to be recorded, those recorded by the procedures it calls '
             'included. It is the bound on what the command can do, whether or not any proof '
             'in the library exercises it, and it is measured by reading the source rather '
             'than declared alongside the command. One further set is common to every command '
             'and is stated once instead of in every entry: the hook that runs after any '
             'command which changed the proof, to close the definedness sequents an '
             'instantiation left owed. Section~\\ref{sec:command-uses} tabulates the same '
             'figures for every command at once.\n')
    for title, entries in groups:
        o.append('\\subsection*{%s}' % esc(title))
        o.append('')
        for e in entries:
            # ragged heading so a long signature wraps at its spaces instead of
            # overfilling; kind trails inline in small caps.
            o.append('\\par\\smallskip{\\raggedright\\noindent\\texttt{%s}%s%s\\par}\\nobreak'
                     % (esctt(e['sig']),
                        ('\\quad\\tactkind{%s}' % esc(e['kind'])) if e['kind'] else '',
                        idx(e['name'], 'tactic')))
            if e['short']:
                o.append('\\noindent %s\\par' % esc(e['short']))
            u = uses_line(e['name'])
            if u:
                o.append('\\noindent\\textit{Uses:} %s\\par' % u)
            if e['when']:
                o.append('\\noindent\\textit{When useful:} %s\\par' % esc(e['when']))
            if e['long']:
                o.append('')
                o.extend(render_long(e['long']))
        o.append('')
    return '\n'.join(o)

def main():
    with open(SRC, encoding='utf-8') as f:
        md = f.read()
    groups = parse(md)
    with open(OUT, 'w', encoding='utf-8') as o:
        o.write(render(groups) + '\n')
    ntac = sum(len(e) for _, e in groups)
    print('wrote %s  (%d groups, %d tactics)'
          % (os.path.relpath(OUT, ROOT), len(groups), ntac))

if __name__ == '__main__':
    main()
