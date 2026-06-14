#!/usr/bin/env python3
"""Build one self-contained, cross-linked reference.html from the generated
reference/*.md files (plus the structure graph embedded as inline SVG).

What it does, in plain terms:
  * Reads the markdown reference docs the prover writes on load (THEOREMS.md,
    STRUCTURE-INDEX.md, PSS.md, ...).
  * Converts each to HTML (a small markdown subset: headings, lists, indented
    code blocks, `inline code`, **bold**, links).
  * Cross-links: every backticked name that is a known structure / theorem /
    definition / PSS entry becomes a hyperlink to its canonical entry, so you
    can click `card-singleton` anywhere and jump to where it's stated.
  * Embeds the structure graph (dot -Tsvg) at the top of the Structures part;
    clicking a graph node jumps to that structure's section.
  * Emits a sticky left navigation pane listing every doc.
  * Writes everything into a single reference.html -- open in any browser.

Regenerate after a library change (the .md files refresh on prover load):
    python3 reference/build-reference-html.py
"""
import os, re, html, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DOT  = os.path.join(HERE, "structure-graph.dot")
OUT  = os.path.join(HERE, "reference.html")

# Ordered: reading-oriented first, retrieval indexes last.  (title, filename)
# STRUCTURE-INDEX precedes STRUCTURES so it claims the canonical structure ids.
DOCS = [
    ("Library map",        "LIBRARY.md"),
    ("Structures",         "STRUCTURE-INDEX.md"),
    ("Structure notes",    "STRUCTURES.md"),
    ("Theorems & axioms",  "THEOREMS.md"),
    ("Definitions",        "DEFINITIONS.md"),
    ("Functors",           "FUNCTORS.md"),
    ("Proof Support Set",  "PSS.md"),
    ("By operator",        "BY-OPERATOR.md"),
    ("Macete index",       "MACETE-INDEX.md"),
    ("Fingerprint index",  "FINGERPRINT-INDEX.md"),
    ("Proof debt",         "PROOF-DEBT.md"),
    ("Tactics",            "TACTICS.md"),
]

def esc(s):
    return html.escape(s, quote=True)

# --- collect the canonical name -> anchor map -------------------------------
# Priority structure > theorem > definition > pss; first writer wins so the
# anchor we link to is the one actually emitted at the entry's home doc.

def read(fname):
    p = os.path.join(HERE, fname)
    return open(p, encoding="utf-8").read() if os.path.exists(p) else ""

def structure_names():
    # canonical structure set = node names in the graph .dot
    names = set()
    for line in read("structure-graph.dot").splitlines():
        m = re.match(r'\s*"([^"]+)"\s+\[tooltip=', line)
        if m:
            names.add(m.group(1))
    return names

def theorem_names():
    names = []
    for line in read("THEOREMS.md").splitlines():
        m = re.match(r'\s*-\s+`([^`]+)`', line)
        if m:
            names.append(m.group(1))
    return names

def heading3_names(fname):
    names = []
    for line in read(fname).splitlines():
        m = re.match(r'###\s+(.+?)\s*$', line)
        if m:
            names.append(m.group(1).strip("`").strip())
    return names

STRUCTS = structure_names()
THMS    = set(theorem_names())
DEFS    = set(heading3_names("DEFINITIONS.md"))
PSS     = set(heading3_names("PSS.md"))

def anchor_for(name):
    if name in STRUCTS: return name          # bare; matches graph node URLs
    if name in THMS:    return "t-" + name
    if name in DEFS:    return "d-" + name
    if name in PSS:     return "p-" + name
    return None

# --- inline markdown --------------------------------------------------------

def linkify_code(name):
    a = anchor_for(name)
    inner = f"<code>{esc(name)}</code>"
    return f'<a class="x" href="#{esc(a)}">{inner}</a>' if a else inner

def inline(text):
    """Render inline markdown of one already-newline-free string."""
    # 1. protect code spans (and cross-link them) with placeholders
    spans = []
    def stash(htmlfrag):
        spans.append(htmlfrag)
        return f"\x00{len(spans)-1}\x00"
    text = re.sub(r"`([^`]+)`", lambda m: stash(linkify_code(m.group(1))), text)
    # 2. protect explicit markdown links [text](href)
    text = re.sub(r"\[([^\]]+)\]\(([^)]+)\)",
                  lambda m: stash(f'<a href="{esc(m.group(2))}">{esc(m.group(1))}</a>'),
                  text)
    # 3. escape everything else
    text = esc(text)
    # 4. emphasis.  **bold** first so single-* doesn't nibble it.  Single-*
    #    is adjacency-aware: an opening '*' must be followed by non-space and a
    #    closing '*' preceded by non-space, so spaced multiplication " * " in
    #    statements is never treated as emphasis.  '_' stays targeted to the
    #    warrant tag (statements contain trailing-underscore vars like n_).
    text = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"_(\[warrant:[^\]]*\])_", r"<em>\1</em>", text)
    text = re.sub(r"\*(\S|\S[^*]*?\S)\*", r"<em>\1</em>", text)
    # 5. restore placeholders
    text = re.sub(r"\x00(\d+)\x00", lambda m: spans[int(m.group(1))], text)
    return text

def inline_stmt(text):
    """Render a formal statement verbatim: escape only, plus the trailing
    warrant tag.  NO emphasis -- statements legitimately contain bare `*`
    (e.g. the structure `rr+*`), which star-emphasis would mangle."""
    t = esc(text)
    return re.sub(r"_(\[warrant:[^\]]*\])_", r'<em>\1</em>', t)

# --- block markdown ---------------------------------------------------------

def slug(s):
    s = s.strip().strip("`").strip().lower()
    s = re.sub(r"[^a-z0-9+*<>=/.-]+", "-", s).strip("-")
    return s or "x"

def md_to_html(text, docid, used_ids):
    """Convert a markdown doc to HTML.  docid namespaces generic headings;
    structure/def/pss headings get their canonical ids instead."""
    out = []
    # Drop the prover's explicit empty anchors (e.g. <a id="field"></a>): our
    # generated heading ids already provide those targets, and passing the raw
    # tag through would both show as literal text and duplicate the id.
    text = re.sub(r'<a id="[^"]*"></a>', "", text)
    lines = text.split("\n")
    i, n = 0, len(lines)

    def claim(idbase):
        cid, k = idbase, 2
        while cid in used_ids:
            cid = f"{idbase}-{k}"; k += 1
        used_ids.add(cid)
        return cid

    def heading_id(level, raw):
        name = raw.strip().strip("`").strip()
        if name in STRUCTS:                       return claim(name)
        if docid == "DEFINITIONS" and level == 3: return claim("d-" + name)
        if docid == "PSS"         and level == 3: return claim("p-" + name)
        return claim(f"{docid}__{slug(raw)}")

    while i < n:
        line = lines[i]
        stripped = line.strip()

        if not stripped:
            i += 1; continue

        # heading
        m = re.match(r"(#{1,6})\s+(.*)$", line)
        if m:
            level = len(m.group(1)); raw = m.group(2).strip()
            hid = heading_id(level, raw)
            tag = f"h{min(level+1, 6)}"   # shift down: doc gets <h2> as top
            out.append(f'<{tag} id="{esc(hid)}">{inline(raw)}</{tag}>')
            i += 1; continue

        # horizontal rule
        if re.match(r"^-{3,}\s*$", line):
            out.append("<hr>"); i += 1; continue

        # indented code block (4+ spaces, not a list item): the statements
        if re.match(r"^ {4,}\S", line) and not re.match(r"^\s*-\s", line):
            buf = []
            while i < n and (not lines[i].strip() or re.match(r"^ {4,}", lines[i])):
                if not lines[i].strip() and not (i+1 < n and re.match(r"^ {4,}", lines[i+1])):
                    break
                buf.append(lines[i][4:] if lines[i].startswith("    ") else lines[i])
                i += 1
            out.append(f"<pre>{esc(chr(10).join(buf).rstrip())}</pre>")
            continue

        # list (supports nesting by indent; continuation lines append to item)
        if re.match(r"^(\s*)-\s+", line):
            items = []   # [level, html, id_or_None]
            while i < n:
                lm = re.match(r"^(\s*)-\s+(.*)$", lines[i])
                if lm:
                    lvl = len(lm.group(1)) // 2
                    raw = lm.group(2)
                    itid = None
                    # A catalog entry `name` U+2014 statement: render the name as
                    # plain code and the statement verbatim (no emphasis -- it may
                    # contain bare `*`).  THEOREMS.md is the canonical theorem
                    # home, so its entries also get the `t-<name>` cross-link id.
                    stmt = re.match(r"`([^`]+)`\s*—\s*(.*)$", raw)
                    if stmt:
                        name, body = stmt.group(1), stmt.group(2)
                        # Fold mechanical -rev mirrors into their base entry,
                        # like the fingerprint index: drop the standalone -rev,
                        # tag the base (±), but keep a t-<name>-rev anchor on the
                        # base so existing cross-links still resolve.
                        if docid == "THEOREMS" and name.endswith("-rev") \
                                and name[:-4] in THMS:
                            i += 1
                            continue
                        extra = marker = ""
                        if docid == "THEOREMS" and name in THMS:
                            itid = claim("t-" + name)
                            if name + "-rev" in THMS:
                                extra  = f'<a id="t-{esc(name)}-rev"></a>'
                                marker = (' <span class="pm" title="reverse'
                                          ' (-rev) mirror folded in">(±)</span>')
                            inner = extra + f"<code>{esc(name)}</code>{marker} — " \
                                    + inline_stmt(body)
                        elif stmt:
                            inner = f"<code>{esc(name)}</code> — " + inline_stmt(body)
                    else:
                        inner = inline(raw)
                    items.append([lvl, inner, itid])
                    i += 1
                elif lines[i].strip() and not re.match(r"(#{1,6})\s", lines[i]) \
                        and not re.match(r"^-{3,}\s*$", lines[i]) and items:
                    # continuation of previous item
                    items[-1][1] += " " + inline(lines[i].strip())
                    i += 1
                else:
                    break
            out.append(render_list(items))
            continue

        # paragraph: gather consecutive plain lines
        buf = []
        while i < n and lines[i].strip() and not re.match(r"(#{1,6})\s", lines[i]) \
                and not re.match(r"^-{3,}\s*$", lines[i]) \
                and not re.match(r"^(\s*)-\s+", lines[i]) \
                and not re.match(r"^ {4,}\S", lines[i]):
            buf.append(lines[i].strip()); i += 1
        out.append(f"<p>{inline(' '.join(buf))}</p>")

    return "\n".join(out)

def render_list(items):
    """items: list of [level, inner_html, id_or_None] -> nested <ul>."""
    html_out = []
    stack = []   # current open levels
    for lvl, inner, itid in items:
        while len(stack) > lvl + 1:
            html_out.append("</ul>"); stack.pop()
        while len(stack) < lvl + 1:
            html_out.append("<ul>"); stack.append(True)
        attr = f' id="{esc(itid)}"' if itid else ""
        html_out.append(f"<li{attr}>{inner}</li>")
    html_out.extend("</ul>" for _ in stack)
    return "".join(html_out)

# --- structure graph embed --------------------------------------------------

def graph_svg():
    if not os.path.exists(DOT):
        return ""
    try:
        svg = subprocess.run(["dot", "-Tsvg", DOT],
                             capture_output=True, text=True, check=True).stdout
    except Exception as e:
        print("warning: dot failed, embedding no graph:", e, file=sys.stderr)
        return ""
    svg = svg[svg.index("<svg"):]
    svg = svg.replace('structure-graph.html#views', '#STRUCTURE-INDEX__top')
    svg = svg.replace("structure-graph.html#", "#")   # node URLs -> in-page
    return f'<div class="graph">{svg}</div>'

# --- assemble ---------------------------------------------------------------

CSS = """
 body { font-family: Helvetica, Arial, sans-serif; color:#1a2a3a; margin:0; }
 #wrap { display:flex; align-items:flex-start; }
 nav { position:sticky; top:0; align-self:flex-start; min-width:13rem;
       height:100vh; overflow:auto; padding:1.2rem 1rem; background:#f5f8fc;
       border-right:1px solid #dde6f0; box-sizing:border-box; }
 nav h1 { font-size:1rem; margin:.2rem 0 1rem; color:#2a4a6a; }
 nav a { display:block; padding:.18rem .3rem; color:#33536f; text-decoration:none;
         border-radius:4px; font-size:.92rem; }
 nav a:hover { background:#e3edf8; }
 /* min-width:0 lets this flex child shrink below its content's intrinsic
    width; without it a wide <pre> formula forces main past the viewport and
    the off-page text can't be reached by the scrollbar. */
 main { padding:1.5rem 2.4rem; max-width:62rem; min-width:0; flex:1 1 auto; }
 h2 { color:#2a4a6a; border-bottom:2px solid #e3edf8; padding-bottom:.2rem;
      margin-top:2.4rem; }
 h3,h4,h5,h6 { color:#365b7d; margin:.9rem 0 .25rem; }
 :target { background:#fff4e0; box-shadow:-.5rem 0 0 #fff4e0, .3rem 0 0 #fff4e0; }
 [id] { scroll-margin-top: .6rem; }
 code { background:#f2f6fb; padding:0 .25rem; border-radius:3px;
        font-family: ui-monospace, Menlo, Consolas, monospace; font-size:.92em;
        overflow-wrap:anywhere; }
 /* wrap long formulas instead of overflowing -- they stay readable without
    any horizontal scrolling; pre-wrap keeps the original spacing. */
 pre { background:#f7f9fc; border:1px solid #e6edf6; border-radius:6px;
       padding:.6rem .8rem; font-size:.86rem;
       white-space:pre-wrap; overflow-wrap:anywhere; }
 li, p { overflow-wrap:anywhere; }
 a.x { text-decoration:none; }
 a.x:hover code { background:#dbe9fb; }
 .pm { color:#9aa7b4; font-size:.85em; cursor:help; }
 ul { margin:.3rem 0; }
 li { margin:.12rem 0; }
 hr { border:0; border-top:1px solid #e6edf6; margin:1.2rem 0; }
 .graph { overflow:auto; border:1px solid #ddd; border-radius:8px;
          padding:1rem; margin:.6rem 0 1.4rem; }
 svg a { cursor:pointer; }
 .lead { color:#667; }
"""

def build():
    used_ids = set()
    nav, body = [], []
    nav.append('<h1>VNB reference</h1>')
    svg_block = graph_svg()
    for title, fname in DOCS:
        text = read(fname)
        if not text:
            continue
        secid = fname.replace(".md", "")          # e.g. THEOREMS, STRUCTURE-INDEX
        used_ids.add(secid)
        nav.append(f'<a href="#{esc(secid)}">{esc(title)}</a>')
        # an extra empty anchor so the graph's #STRUCTURE-INDEX__top resolves
        top_anchor = f'<span id="{esc(secid)}__top"></span>' if secid == "STRUCTURE-INDEX" else ""
        body.append(f'<section><h2 id="{esc(secid)}">{esc(title)}'
                    f' <span class="lead">&mdash; {esc(fname)}</span></h2>{top_anchor}')
        if secid == "STRUCTURE-INDEX" and svg_block:
            body.append(svg_block)
        body.append(md_to_html(text, secid, used_ids))
        body.append("</section>")

    doc = f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>VNB library reference</title>
<style>{CSS}</style></head><body>
<div id="wrap">
<nav>{''.join(nav)}</nav>
<main>{''.join(body)}</main>
</div></body></html>
"""
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(doc)
    ndocs = sum(1 for _, fn in DOCS if read(fn))
    print(f"wrote {OUT}  ({ndocs} docs, {len(STRUCTS)} structures, "
          f"{len(THMS)} theorem ids, {len(DEFS)} defs, {len(PSS)} pss)")

if __name__ == "__main__":
    build()
