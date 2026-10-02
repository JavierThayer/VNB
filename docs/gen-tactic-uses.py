#!/usr/bin/env python3
r"""gen-tactic-uses.py -- emit the per-command "uses" list: for every proof command,
the kernel operations it can cause to be recorded.

    docs/app-tactic-uses-generated.tex   \VNBtacticusestable, \VNBtacticusescount
    reference/TACTIC-USES.md             the same table as a reference page
    tactic-uses-data.scm                 the same table as Scheme data, read by
                                         tactics-help.scm so that reference/TACTICS.md
                                         carries a "uses" line inside each entry

SOURCE, read here and written by no hand:

  reference/kernel-map-static.sexp   the static half of the kernel map, written by
                                     kernel-map-static.scm.  Its `kernel' section gives,
                                     for each kernel entry point, the operations it may
                                     record; its `tactics' section gives, for each proof
                                     command, the entry points reachable from the
                                     command's own code.  Composing the two gives the
                                     operations a command can reach.  The file carries
                                     its own regeneration instructions in its header.

  tactics-help.scm                   *tactic-kind*, the command registry, for the kind
                                     column and as a fallback: a command the kernel map
                                     does not list is still listed here, with the
                                     operations of its own `emits' field, and marked.

A command that records nothing -- navigation, search, session -- gets an empty list.

This module is also imported by gen-tactics-ref.py, which puts the same line inside each
entry of the manual's tactic reference; `tactic_uses()' is the entry point for that.
"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SEXP = os.path.join(ROOT, "reference", "kernel-map-static.sexp")
KIND = os.path.join(ROOT, "tactics-help.scm")
TEX  = os.path.join(HERE, "app-tactic-uses-generated.tex")
MD   = os.path.join(ROOT, "reference", "TACTIC-USES.md")
SCM  = os.path.join(ROOT, "tactic-uses-data.scm")


# ---------------------------------------------------------------- the S-expression reader
_TOKEN = re.compile(r'''"(?:[^"\\]|\\.)*"|;[^\n]*|[()]|[^\s()";]+''')


def read_sexp(path):
    """The first datum of a Scheme data file: lists, strings, numbers, symbols.
    Comments are skipped, as the Scheme reader skips them."""
    with open(path, encoding="utf-8") as f:
        text = f.read()
    toks = [t for t in _TOKEN.findall(text) if not t.startswith(";")]
    pos = 0

    def atom(t):
        if t.startswith('"'):
            return t[1:-1]
        try:
            return int(t)
        except ValueError:
            pass
        try:
            return float(t)
        except ValueError:
            pass
        return t                       # a symbol, kept as its printed name

    def datum():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t == "(":
            out = []
            while toks[pos] != ")":
                out.append(datum())
            pos += 1
            return out
        if t == ")":
            raise SyntaxError("unbalanced ) in " + path)
        return atom(t)

    if not toks:
        sys.exit("gen-tactic-uses: %s is empty" % path)
    return datum()


def section(data, name):
    for entry in data:
        if isinstance(entry, list) and entry and entry[0] == name:
            return entry[1]
    sys.exit("gen-tactic-uses: no `%s' section in %s" % (name, SEXP))


# ---------------------------------------------------------------- the two inputs
def read_kernel_map():
    """(entry point -> [operation]), (command -> [entry point]), plus the counts."""
    if not os.path.exists(SEXP):
        sys.exit("gen-tactic-uses: %s is missing.  Its header says how to regenerate it."
                 % os.path.relpath(SEXP, ROOT))
    data = read_sexp(SEXP)
    entry_ops = {e[0]: list(e[2]) for e in section(data, "kernel")}
    cmd_entries = {t[0]: list(t[1]) for t in section(data, "tactics")}
    if len(entry_ops) < 40 or len(cmd_entries) < 60:
        sys.exit("gen-tactic-uses: the kernel map gave %d entry points and %d commands"
                 % (len(entry_ops), len(cmd_entries)))
    return entry_ops, cmd_entries


def read_tactic_kind():
    """(command -> [operation]) from *tactic-kind* in tactics-help.scm, in registry order.
    An entry is (name kind emits); emits is #f, one symbol, or a list of symbols."""
    src = open(KIND).read()
    a = src.index("(define *tactic-kind*")
    b = src.index("(define (tactic-kind-of", a)
    block = re.sub(r";[^\n]*", "", src[a:b])          # drop comments
    out = []
    for m in re.finditer(r"\(([a-z0-9!*+-]+)\s+(meta|rule|oracle|composite)\s+(#f|[a-z0-9-]+|\([^()]*\))\)",
                         block):
        name, _, emits = m.group(1), m.group(2), m.group(3)
        if emits == "#f":
            ops = []
        elif emits.startswith("("):
            ops = emits.strip("()").split()
        else:
            ops = [emits]
        out.append((name, ops))
    if len(out) < 60:
        sys.exit("gen-tactic-uses: only %d entries parsed from *tactic-kind*" % len(out))
    return out


# ---------------------------------------------------------------- the composition
def tactic_uses():
    """[(command, [operation], from_registry)], sorted by command, plus the widest set.

    Returns (rows, widest).  `widest' is the largest set any command reaches: the
    commands that run a procedure handed to them, or replay a recorded one, reach
    exactly it, and printing it out for each of them would be pages of one list."""
    entry_ops, cmd_entries = read_kernel_map()
    kinds = read_tactic_kind()

    unknown = sorted({e for es in cmd_entries.values() for e in es if e not in entry_ops})
    if unknown:
        print("*** WARNING: the kernel map's command table names entry points its entry-point "
              "table does not list: " + ", ".join(unknown))

    rows, seen = [], set()
    for name, ops in kinds:
        seen.add(name)
        if name in cmd_entries:
            used = sorted({op for e in cmd_entries[name] for op in entry_ops.get(e, [])})
            rows.append((name, used, False))
        else:
            rows.append((name, sorted(set(ops)), True))
    for name in sorted(cmd_entries):
        if name not in seen:
            used = sorted({op for e in cmd_entries[name] for op in entry_ops.get(e, [])})
            rows.append((name, used, False))
    rows.sort(key=lambda r: r[0])
    widest = max((set(u) for _, u, m in rows if not m), key=len)
    return rows, widest


def render(used, widest):
    """The 'uses' list, or a phrase when it is the widest set."""
    if not used:
        return None
    if set(used) == widest:
        return "ALL"
    return used


def tex_esc(s):
    return s.replace("_", r"\_").replace("&", r"\&").replace("#", r"\#")


def main():
    rows, widest = tactic_uses()
    from_registry = [n for n, u, m in rows if m and u]

    # ------------------------------------------------------------ LaTeX
    lines = ["%% GENERATED by gen-tactic-uses.py from reference/kernel-map-static.sexp and",
             "%% tactics-help.scm (*tactic-kind*).  Do not edit.",
             r"\newcommand{\VNBtacticusescount}{%d}" % len(rows),
             r"\newcommand{\VNBtacticusesmax}{%d}" % len(widest),
             r"\newcommand{\VNBtacticusestable}{%",
             r"\begin{longtable}{@{}p{0.17\textwidth}p{0.79\textwidth}@{}}",
             r"\toprule",
             r"command & operations it can reach \\",
             r"\midrule",
             r"\endfirsthead",
             r"\toprule",
             r"command & operations it can reach \\",
             r"\midrule",
             r"\endhead"]
    for name, used, marked in rows:
        r = render(used, widest)
        if r is None:
            cell = "none"
        elif r == "ALL":
            cell = r"\emph{all %d reachable operations}" % len(widest)
        else:
            cell = " ".join(r"\texttt{%s}" % tex_esc(op) for op in r)
        if marked and used:
            cell += r" \textsuperscript{r}"
        lines.append(r"\texttt{%s} & %s\\" % (tex_esc(name), cell))
    lines += [r"\bottomrule",
              r"\end{longtable}",
              r"\noindent\footnotesize \textsuperscript{r}: read from the command registry rather",
              r"than from the kernel map, which predates the command.\normalsize}"]
    open(TEX, "w").write("\n".join(lines) + "\n")

    # ------------------------------------------------------------ Markdown
    md = ["# What each proof command can reach", "",
          "A proof command changes the deduction graph only by calling kernel operations.",
          "The operations listed against a command are the bound on what it can do: every",
          "operation recorded by any kernel procedure reachable from the command's own code,",
          "whether or not the library exercises it.  A command listed as `none` records nothing;",
          "those are the navigation, search and session commands.", "",
          "The list is composed from the two halves of *Kernel map*: which operations each",
          "kernel entry point records, and which entry points each command reaches.  Entries",
          "marked [r] come from the command registry (`*tactic-kind*`) instead, because the",
          "kernel map predates the command.", "",
          "One further set is common to every command and is stated once, in *Kernel map*,",
          "rather than repeated in every row: the hook that runs after any command which",
          "changed the proof, to close the definedness sequents an instantiation left owed.", "",
          "| command | operations it can reach |", "|---|---|"]
    for name, used, marked in rows:
        r = render(used, widest)
        if r is None:
            cell = "none"
        elif r == "ALL":
            cell = "*all %d reachable operations*" % len(widest)
        else:
            cell = " ".join("`%s`" % op for op in r)
        if marked and used:
            cell += " [r]"
        md.append("| `%s` | %s |" % (name, cell))
    md.append("")
    open(MD, "w").write("\n".join(md) + "\n")

    # ------------------------------------------------------------ Scheme data
    scm = [";;; tactic-uses-data.scm -- GENERATED by docs/gen-tactic-uses.py from",
           ";;; reference/kernel-map-static.sexp.  Do not edit.",
           ";;;",
           ";;; One entry per proof command: the kernel operations the command can cause",
           ";;; to be recorded, measured by reading the source of the command and of every",
           ";;; procedure it reaches.  tactics-help.scm reads this file if it is there and",
           ";;; prints the list inside each entry of reference/TACTICS.md; without it the",
           ";;; entries simply carry no `Uses' line.",
           ";;;",
           ";;; Regenerate:  python3 docs/gen-tactic-uses.py   (or `make -C docs gen')",
           ";;; after re-running the two kernel-map instruments; their own headers say how.",
           "",
           "("]
    for name, used, _ in rows:
        scm.append("  (%s%s)" % (name, "".join(" " + op for op in used)))
    scm += [")", ""]
    # Write ONLY on change: this file is in the tree and `prover --band-if-fresh' compares
    # the band's mtime against every .scm, so an unchanged rewrite (every `make' in docs/)
    # made the band read stale and refused the suite (2026-10-02).
    new_scm = "\n".join(scm) + "\n"
    if not (os.path.exists(SCM) and open(SCM).read() == new_scm):
        open(SCM, "w").write(new_scm)

    n_ops = len({op for _, u, _ in rows for op in u})
    print("gen-tactic-uses: %d commands (%d from the kernel map, %d from the registry); "
          "%d operations, widest reach %d"
          % (len(rows), len(rows) - sum(1 for _, _, m in rows if m), len(from_registry),
             n_ops, len(widest)))
    if from_registry:
        print("gen-tactic-uses: not in the kernel map's command table: "
              + ", ".join(sorted(from_registry)))


if __name__ == "__main__":
    main()
