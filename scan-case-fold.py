#!/usr/bin/env python3
"""Source-level scanner for case-fold capture bugs in VNB .scm files.

MIT Scheme case-folds symbols at read time, so two mixed-case names
that lower-case to the same string become the SAME symbol after read.
When a binder (FORALL, FORSOME, SEP, ...) introduces a name X whose
lowercase clashes with another name in scope (outer binder or a free
reference in the body), capture happens silently and the formula
means something other than what was written.

This scanner parses .scm files case-sensitively, tracks binder scopes,
and flags every such collision.

Usage:
    python3 scan-case-fold.py             # scan whole prover tree
    python3 scan-case-fold.py file ...    # scan listed files
"""

import sys
import os
from dataclasses import dataclass

BINDERS_ONE = {'FORALL', 'FORSOME', 'IOTA', 'VNB-LAMBDA'}
BINDERS_SEP = {'SEP': 3, 'COMP': 2, 'BIG-UNION': 3}  # body starts at this idx


def tokenize(src):
    """List of (text, line). ; comments stripped. Strings preserved-as-blank."""
    out = []
    line = 1
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c == '\n':
            line += 1
            i += 1
        elif c == ';':
            while i < n and src[i] != '\n':
                i += 1
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                if src[j] == '\\' and j + 1 < n:
                    j += 2
                else:
                    if src[j] == '\n':
                        line += 1
                    j += 1
            i = j + 1 if j < n else n
        elif c.isspace():
            i += 1
        elif c in '()':
            out.append((c, line))
            i += 1
        elif c == "'":
            out.append(("'", line))
            i += 1
        elif c == '`':
            out.append(("`", line))
            i += 1
        elif c == ',':
            # ,@ or ,
            if i + 1 < n and src[i+1] == '@':
                out.append((",@", line))
                i += 2
            else:
                out.append((",", line))
                i += 1
        else:
            j = i
            while j < n and src[j] not in '()\'`, \t\n;"':
                j += 1
            out.append((src[i:j], line))
            i = j
    return out


def parse(tokens, i):
    if i >= len(tokens):
        return None, i
    text, line = tokens[i]
    if text == '(':
        items = []
        i += 1
        while i < len(tokens) and tokens[i][0] != ')':
            item, i = parse(tokens, i)
            if item is not None:
                items.append(item)
        return items, i + 1
    if text == ')':
        return None, i + 1
    if text in ("'", "`"):
        item, i = parse(tokens, i + 1)
        return [(text, line), item], i
    if text in (',', ',@'):
        item, i = parse(tokens, i + 1)
        return [(text, line), item], i
    return (text, line), i + 1


def parse_all(tokens):
    forms = []
    i = 0
    while i < len(tokens):
        form, i = parse(tokens, i)
        if form is not None:
            forms.append(form)
    return forms


def is_atom(x):
    return isinstance(x, tuple) and len(x) == 2 and isinstance(x[0], str)


def is_list(x):
    return isinstance(x, list)


def collect_symbols(form, out):
    """Append every (text, line) atom found in argument positions of form.

    Head positions are skipped: per VNB semantics, free-vars doesn't track
    symbols in head position and subst-free doesn't enter them, so a name
    appearing as the operator of a compound form can never be captured by
    an outer binder.  Recurses into compound heads to handle cases like
    ((D s) x y) where the head (D s) itself has an arg position.
    """
    if is_atom(form):
        out.append(form)
        return
    if not is_list(form) or not form:
        return
    head = form[0]
    # Unwrap quote/backquote/unquote so the wrapped form is scanned as code.
    if is_atom(head) and head[0] in ("'", "`", ",", ",@"):
        if len(form) >= 2:
            collect_symbols(form[1], out)
        return
    # Recurse into a compound head's arg positions, but don't collect the head
    # atom itself.
    if is_list(head):
        collect_symbols(head, out)
    # Args: all in arg position, collect.
    for child in form[1:]:
        collect_symbols(child, out)


def scan(form, scope, hits):
    """Walk form. scope = {bound_name_text: line}. Append (line, kind, binder, bound, other, other_line) to hits."""
    if not is_list(form) or not form:
        return
    head = form[0]
    if is_atom(head):
        head_text, head_line = head
        head_upper = head_text.upper()

        # Unwrap quote/backquote/unquote: descend into the wrapped form treating it as code.
        if head_text in ("'", "`"):
            if len(form) >= 2:
                scan(form[1], scope, hits)
            return
        if head_text in (',', ',@'):
            if len(form) >= 2:
                scan(form[1], scope, hits)
            return

        if head_upper in BINDERS_ONE and len(form) >= 3:
            var = form[1]
            if is_atom(var):
                var_text, var_line = var
                # collisions in current scope
                for outer_name, outer_line in scope.items():
                    if outer_name.lower() == var_text.lower() and outer_name != var_text:
                        hits.append((var_line, 'shadow', head_upper, var_text, outer_name, outer_line))
                # collisions with free references in body
                body_syms = []
                for child in form[2:]:
                    collect_symbols(child, body_syms)
                seen = set()
                for sym_text, sym_line in body_syms:
                    if sym_text == var_text:
                        continue
                    if sym_text.lower() != var_text.lower():
                        continue
                    key = (sym_text, sym_line)
                    if key in seen:
                        continue
                    seen.add(key)
                    hits.append((var_line, 'capture', head_upper, var_text, sym_text, sym_line))
                new_scope = dict(scope)
                new_scope[var_text] = var_line
                for child in form[2:]:
                    scan(child, new_scope, hits)
                return

        if head_upper in BINDERS_SEP:
            body_pos = BINDERS_SEP[head_upper]
            if len(form) > body_pos:
                var = form[1]
                if is_atom(var):
                    var_text, var_line = var
                    for j in range(2, body_pos):
                        scan(form[j], scope, hits)
                    for outer_name, outer_line in scope.items():
                        if outer_name.lower() == var_text.lower() and outer_name != var_text:
                            hits.append((var_line, 'shadow', head_upper, var_text, outer_name, outer_line))
                    body_syms = []
                    for j in range(body_pos, len(form)):
                        collect_symbols(form[j], body_syms)
                    seen = set()
                    for sym_text, sym_line in body_syms:
                        if sym_text == var_text:
                            continue
                        if sym_text.lower() != var_text.lower():
                            continue
                        key = (sym_text, sym_line)
                        if key in seen:
                            continue
                        seen.add(key)
                        hits.append((var_line, 'capture', head_upper, var_text, sym_text, sym_line))
                    new_scope = dict(scope)
                    new_scope[var_text] = var_line
                    for j in range(body_pos, len(form)):
                        scan(form[j], new_scope, hits)
                    return
    # generic recursion
    for child in form:
        scan(child, scope, hits)


def gather_files(roots):
    out = []
    for root in roots:
        if os.path.isfile(root):
            out.append(root)
            continue
        for dirpath, dirnames, fnames in os.walk(root):
            for f in fnames:
                if not f.endswith('.scm'):
                    continue
                if f.startswith('scratch'):
                    continue
                out.append(os.path.join(dirpath, f))
    return sorted(out)


def main():
    if len(sys.argv) > 1:
        files = gather_files(sys.argv[1:])
    else:
        files = gather_files(['/home/ubuntu/prover'])

    grand = []
    for f in files:
        with open(f) as fh:
            src = fh.read()
        toks = tokenize(src)
        forms = parse_all(toks)
        hits = []
        for form in forms:
            scan(form, {}, hits)
        if hits:
            grand.append((f, hits))

    total = 0
    for f, hits in grand:
        print(f"\n=== {f} ===")
        for h in hits:
            line, kind, binder, bound, other, other_line = h
            if kind == 'shadow':
                print(f"  line {line}: SHADOW  ({binder} {bound} ...) re-binds outer "
                      f"{other!r} (line {other_line}) -- case-folds equal")
            else:
                print(f"  line {line}: CAPTURE ({binder} {bound} ...) body mentions "
                      f"{other!r} (line {other_line}) -- case-folds equal")
            total += 1

    print(f"\n{total} potential issues across {len(grand)} files")


if __name__ == '__main__':
    main()
