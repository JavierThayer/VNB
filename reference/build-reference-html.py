#!/usr/bin/env python3
"""Build the browser library reference from the generated reference/*.md files.

Each reference doc becomes its OWN standalone page (THEOREMS.html,
STRUCTURE-INDEX.html, PSS.html, ...), and reference.html is a styled hub that
links to them all.  Every page carries the same left sidebar (so you can hop
between docs), and every backticked name that names a known structure / theorem
/ definition / PSS entry becomes a hyperlink to its canonical entry -- across
pages when needed (e.g. `card-singleton` on the Theorems page links into
STRUCTURE-INDEX.html).

What it does, in plain terms:
  * Reads the markdown reference docs the prover writes on load.
  * Converts each to HTML (a small markdown subset: headings, lists, indented
    code blocks, `inline code`, **bold**, links).
  * Cross-links backticked names to their canonical entry's page + anchor.
  * Emits one self-contained HTML page per doc, plus reference.html (the hub).

Regenerate after a library change (the .md files refresh on prover load):
    python3 reference/build-reference-html.py
"""
import os, re, html, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT  = os.path.join(HERE, "reference.html")

# Ordered: reading-oriented first, retrieval indexes last.
# (title, filename, blurb).  STRUCTURE-INDEX precedes STRUCTURES so it claims
# the canonical structure ids.  The blurb is shown on the hub cards and as the
# sidebar tooltip.
DOCS = [
    ("Library map",        "LIBRARY.md",          "the lay of the land — where everything lives"),
    ("Structures",         "STRUCTURE-INDEX.md",  "every structure: slots, laws, views"),
    ("Structure notes",    "STRUCTURES.md",       "prose notes on the structure hierarchy"),
    ("Theorems & axioms",  "THEOREMS.md",         "the full installed catalog"),
    ("Definitions",        "DEFINITIONS.md",      "term & predicate definitions"),
    ("Functoids",          "FUNCTORS.md",         "structure-to-structure constructions"),
    ("Proof Support Set",  "PSS.md",              "theorems excused from the VNB test, accepted on a warrant"),
    ("By operator",        "BY-OPERATOR.md",      "results indexed by the operator they mention"),
    ("Macete index",       "MACETE-INDEX.md",     "rewrite macetes, grouped"),
    ("Fingerprint index",  "FINGERPRINT-INDEX.md","results bucketed by conclusion skeleton"),
    ("Proof debt",         "PROOF-DEBT.md",       "what each proof rests on (asserted base)"),
    ("Tactics",            "TACTICS.md",          "interactive proof commands, each with a one-line gloss"),
]

# secid (filename without .md) -> output page filename.
def page_of(secid):
    return secid + ".html"

def esc(s):
    return html.escape(s, quote=True)

# --- collect the canonical name -> (page, anchor) map -----------------------
# Priority structure > theorem > definition > pss; the anchor we link to is the
# one actually emitted at the entry's home doc/page.

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

# Home page (page, anchor) for each linkable name.
def target_for(name):
    if name in STRUCTS: return (page_of("STRUCTURE-INDEX"), name)          # bare; matches graph node URLs
    if name in THMS:    return (page_of("THEOREMS"),        "t-" + name)
    if name in DEFS:    return (page_of("DEFINITIONS"),     "d-" + name)
    if name in PSS:     return (page_of("PSS"),             "p-" + name)
    return None

# The page currently being rendered -- so a same-page link stays a bare #anchor
# (no reload) while cross-page links carry the file.
CURRENT_PAGE = None

# --- inline markdown --------------------------------------------------------

def linkify_code(name):
    t = target_for(name)
    inner = f"<code>{esc(name)}</code>"
    if not t:
        return inner
    page, anchor = t
    href = f"#{esc(anchor)}" if page == CURRENT_PAGE else f"{esc(page)}#{esc(anchor)}"
    return f'<a class="x" href="{href}">{inner}</a>'

def inline(text):
    """Render inline markdown of one already-newline-free string."""
    # 1. protect code spans (and cross-link them) with placeholders.  Remember
    #    each span's raw code text, so an explicit link whose label IS a code
    #    span (step 2) can use the bare <code> rather than nesting the span's
    #    own auto-link inside it.
    spans = []
    code_at = {}
    def stash(htmlfrag, code=None):
        spans.append(htmlfrag)
        if code is not None:
            code_at[len(spans) - 1] = code
        return f"\x00{len(spans)-1}\x00"
    text = re.sub(r"`([^`]+)`",
                  lambda m: stash(linkify_code(m.group(1)), code=m.group(1)), text)
    # 2. protect explicit markdown links [text](href).  If the label is exactly
    #    one code-span placeholder, the span would already be an auto-link to
    #    (usually) the same anchor -- so render the bare <code> inside this
    #    explicit link instead of nesting <a> in <a> (invalid, and it showed as
    #    a stray placeholder before).
    def linksub(m):
        label, href = m.group(1), m.group(2)
        mm = re.fullmatch(r"\x00(\d+)\x00", label)
        if mm and int(mm.group(1)) in code_at:
            label = f"<code>{esc(code_at[int(mm.group(1))])}</code>"
        else:
            label = esc(label)
        return stash(f'<a class="x" href="{esc(href)}">{label}</a>')
    text = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", linksub, text)
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
    # 5. restore placeholders.  Loop until stable: a code span nested inside a
    #    markdown link (e.g. [`cc-ring`](#cc-ring)) leaves a placeholder INSIDE
    #    another placeholder's stashed HTML, and re.sub is single-pass -- so one
    #    substitution would expose, but not expand, the inner one.
    while "\x00" in text:
        new = re.sub(r"\x00(\d+)\x00", lambda m: spans[int(m.group(1))], text)
        if new == text:           # an unmatched NUL we can't resolve; bail
            break
        text = new
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
            tag = f"h{min(level+1, 6)}"   # shift down: doc title is the page <h1>
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

# --- shared chrome ----------------------------------------------------------

CSS = """
 :root { --ink:#1a2a3a; --accent:#2a4a6a; --accent2:#3f7fb0; --rule:#dde6f0;
         --bg:#eef3f9; --panel:#f5f8fc; }
 * { box-sizing:border-box; }
 body { font-family: Helvetica, Arial, sans-serif; color:var(--ink); margin:0;
        background:#fff; }
 #wrap { display:flex; align-items:flex-start; }
 nav { position:sticky; top:0; align-self:flex-start; min-width:14rem; width:14rem;
       height:100vh; overflow:auto; padding:1.2rem 1rem; background:var(--panel);
       border-right:1px solid var(--rule); box-sizing:border-box; }
 nav .home { font-size:1.05rem; font-weight:600; color:var(--accent);
             text-decoration:none; display:block; margin:.1rem 0 1rem; }
 nav .home:hover { text-decoration:underline; }
 nav a.doc { display:block; padding:.28rem .5rem; color:#33536f; text-decoration:none;
             border-radius:5px; font-size:.92rem; line-height:1.3; }
 nav a.doc:hover { background:#e3edf8; }
 nav a.doc.active { background:var(--accent); color:#fff; font-weight:600; }
 nav .extra { display:block; margin-top:1.2rem; padding-top:.8rem;
              border-top:1px solid var(--rule); }
 /* min-width:0 lets this flex child shrink below its content's intrinsic
    width; without it a wide <pre> formula forces main past the viewport. */
 main { padding:1.6rem 2.4rem 3rem; max-width:62rem; min-width:0; flex:1 1 auto; }
 h1.page { color:var(--accent); font-size:1.9rem; margin:.2rem 0 .1rem;
           background:linear-gradient(95deg,#2a4a6a 0%,#3f7fb0 60%,#b06a00 100%);
           -webkit-background-clip:text; background-clip:text; color:transparent; }
 .page-sub { color:#667; margin:.1rem 0 1.6rem; font-size:1.02rem; }
 h2 { color:var(--accent); border-bottom:2px solid #e3edf8; padding-bottom:.2rem;
      margin-top:2.2rem; }
 h3,h4,h5,h6 { color:#365b7d; margin:.9rem 0 .25rem; }
 :target { background:#fff4e0; box-shadow:-.5rem 0 0 #fff4e0, .3rem 0 0 #fff4e0; }
 [id] { scroll-margin-top: .6rem; }
 code { background:#f2f6fb; padding:0 .25rem; border-radius:3px;
        font-family: ui-monospace, Menlo, Consolas, monospace; font-size:.92em;
        overflow-wrap:anywhere; }
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
 .lead { color:#667; }
 /* hub */
 .hub main { max-width:54rem; }
 .hub-grid { display:grid; grid-template-columns:repeat(auto-fit,minmax(15rem,1fr));
             gap:.9rem; margin:1.4rem 0; }
 a.card { display:block; background:#fff; border:1px solid var(--rule);
          border-radius:10px; padding:.9rem 1.1rem; text-decoration:none;
          color:inherit; transition:border-color .12s, box-shadow .12s; }
 a.card:hover { border-color:var(--accent2);
                box-shadow:0 2px 10px rgba(42,74,106,.10); }
 a.card .t { color:var(--accent); font-weight:600; font-size:1.05rem; }
 a.card .b { color:#667; font-size:.9rem; margin-top:.2rem; line-height:1.4; }
"""

def sidebar(active_secid):
    """The left nav, shared by every page.  ACTIVE_SECID is highlighted (None on
    the hub).  A 'Reference home' link tops it; the structure graph sits below."""
    parts = ['<a class="home" href="reference.html">&#8962; VNB reference</a>']
    for title, fname, _ in DOCS:
        if not read(fname):
            continue
        secid = fname[:-3]
        cls = "doc active" if secid == active_secid else "doc"
        parts.append(f'<a class="{cls}" href="{esc(page_of(secid))}">{esc(title)}</a>')
    parts.append('<a class="doc extra" href="structure-graph.html">Structure graph &#8599;</a>')
    return "".join(parts)

def page_html(title, sub, active_secid, body, body_class=""):
    cls = f' class="{body_class}"' if body_class else ""
    return f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>{esc(title)} &mdash; VNB reference</title>
<style>{CSS}</style></head><body{cls}>
<div id="wrap">
<nav>{sidebar(active_secid)}</nav>
<main>{body}</main>
</div></body></html>
"""

# --- assemble ---------------------------------------------------------------

def build():
    global CURRENT_PAGE
    written = []

    # one standalone page per doc
    for title, fname, blurb in DOCS:
        text = read(fname)
        if not text:
            continue
        secid = fname[:-3]                        # e.g. THEOREMS, STRUCTURE-INDEX
        page = page_of(secid)
        CURRENT_PAGE = page
        used_ids = set()
        body = [f'<h1 class="page">{esc(title)}</h1>',
                f'<p class="page-sub">{esc(blurb)} '
                f'<span class="lead">&mdash; {esc(fname)}</span></p>']
        if secid == "STRUCTURE-INDEX":
            body.append('<p class="lead">See the clickable '
                        '<a href="structure-graph.html">structure graph</a> '
                        '&mdash; refines &amp; view-as relations, with every node a link.</p>')
        body.append(md_to_html(text, secid, used_ids))
        with open(os.path.join(HERE, page), "w", encoding="utf-8") as f:
            f.write(page_html(title, blurb, secid, "\n".join(body)))
        written.append(page)

    # the hub: reference.html
    CURRENT_PAGE = "reference.html"
    cards = []
    for title, fname, blurb in DOCS:
        if not read(fname):
            continue
        secid = fname[:-3]
        cards.append(f'<a class="card" href="{esc(page_of(secid))}">'
                     f'<div class="t">{esc(title)}</div>'
                     f'<div class="b">{esc(blurb)}</div></a>')
    cards.append('<a class="card" href="structure-graph.html">'
                 '<div class="t">Structure graph &#8599;</div>'
                 '<div class="b">refines &amp; view-as relations, every node clickable</div></a>')
    hub_body = (f'<h1 class="page">VNB library reference</h1>'
                f'<p class="page-sub">The installed library, one page per index. '
                f'Every backticked name links to where it is stated.</p>'
                f'<div class="hub-grid">{"".join(cards)}</div>')
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(page_html("VNB library reference", "", None, hub_body, body_class="hub"))

    print(f"wrote {OUT} (hub) + {len(written)} doc pages: {', '.join(written)}")
    print(f"  ({len(STRUCTS)} structures, {len(THMS)} theorem ids, "
          f"{len(DEFS)} defs, {len(PSS)} pss)")

if __name__ == "__main__":
    build()
