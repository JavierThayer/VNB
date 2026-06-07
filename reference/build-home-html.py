#!/usr/bin/env python3
"""Build the VNB browser landing page (home.html).

A front door rendered in HTML.  Two kinds of link:
  * Reference links go to other HTML pages (reference.html, structure-graph.html)
    -- ordinary in-browser navigation.
  * Workbench links poke Emacs: each is a fire-and-forget fetch to a tiny
    localhost listener the launcher runs (http://127.0.0.1:PORT/do?fn=NAME).
    Emacs dispatches NAME through a fixed whitelist and raises its frame, so
    the actual proving (Focus workspace, REPL, scratch) happens in Emacs as
    before -- the browser is only the lobby.

Usage:  python3 build-home-html.py [PORT]      (PORT default 8973)
The launcher passes the port it actually listens on, so the two stay in sync.
"""
import os, sys, html

HERE = os.path.dirname(os.path.abspath(__file__))
OUT  = os.path.join(HERE, "home.html")
PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8973

def esc(s): return html.escape(s, quote=True)

# Reference reading -- all in the browser.  (label, href, blurb).  The #ANCHORS
# are reference.html's per-doc sections (build-reference-html.py: secid = the
# .md filename).  These cover what used to be the Emacs "Show X" home items.
REF_LINKS = [
    ("Library",           "reference.html",                  "everything cross-linked — start here"),
    ("Structures",        "reference.html#STRUCTURE-INDEX",  "every structure: slots, laws, views"),
    ("Theorems & axioms", "reference.html#THEOREMS",         "the full installed catalog"),
    ("Definitions",       "reference.html#DEFINITIONS",      "term & predicate definitions"),
    ("Proof Support Set", "reference.html#PSS",              "results accepted as warranted support"),
    ("Fingerprint Index", "reference.html#FINGERPRINT-INDEX","results bucketed by conclusion skeleton"),
    ("Structure Graph",   "structure-graph.html",            "refines & view-as relations, clickable"),
]
# Workbench: (heading, [(label, fn-name, blurb), ...]).  Emacs is ONLY for work
# the user actually performs -- starting/continuing proofs, scratch, building.
# Each fn-name MUST have a matching entry in vnb--home-actions (vnb-launch.el);
# keep the two in sync by hand.  No "Open Workspace": the browser IS the home
# page, so there is no separate Emacs landing page to bounce to.
WORKBENCH = [
    ("Prove", [
        ("Start Proof",    "start-proof",    "edit the goal in a buffer, then begin in the Focus workspace"),
        ("Continue Proof", "continue-proof", "return to the proof in progress (Focus workspace)"),
        ("Scratch",        "scratch",        "Lisp-interaction sheet: C-j sends a sexp/region to the prover"),
    ]),
    ("Build", [
        ("Build Formula",  "build-formula",  "parse and validate a formula"),
        ("Build Structure","build-structure","define a new structure (saved to file)"),
        ("Calculator",     "calculator",     "work out an arithmetic expression"),
    ]),
    ("Session", [
        ("Examples",     "examples",     "step through worked example proofs"),
        ("Save Session", "save-session", "this session's proofs as one re-loadable script"),
    ]),
]

CSS = """
 body { font-family: Helvetica, Arial, sans-serif; color:#1a2a3a;
        background:#eef3f9; margin:0; padding:3rem 1rem; }
 main { max-width:46rem; margin:0 auto; }
 h1 { color:#2a4a6a; font-size:1.6rem; margin:.2rem 0; }
 .sub { color:#667; margin:.2rem 0 2rem; }
 h2 { color:#365b7d; font-size:1.05rem; margin:1.8rem 0 .6rem;
      border-bottom:2px solid #dde6f0; padding-bottom:.2rem; }
 .card { display:block; background:#fff; border:1px solid #dde6f0;
         border-radius:10px; padding:.8rem 1rem; margin:.5rem 0;
         text-decoration:none; color:inherit; transition:box-shadow .12s; }
 .card:hover { box-shadow:0 2px 10px rgba(40,80,140,.15); border-color:#bcd0e8; }
 .card .t { font-weight:600; color:#2a4a6a; }
 .card .b { color:#667; font-size:.9rem; margin-top:.1rem; }
 .emacs .t::after { content:" \\2192 Emacs"; color:#b06a00; font-weight:400;
                    font-size:.82rem; }
 #flash { position:fixed; top:1rem; right:1rem; background:#2a4a6a; color:#fff;
          padding:.5rem .9rem; border-radius:6px; opacity:0; transition:opacity .2s;
          font-size:.9rem; }
 #flash.show { opacity:.95; }
"""

JS = f"""
 const PORT = {PORT};
 function flash(msg) {{
   const f = document.getElementById('flash');
   f.textContent = msg; f.classList.add('show');
   setTimeout(() => f.classList.remove('show'), 1400);
 }}
 function poke(ev, fn, label) {{
   ev.preventDefault();
   fetch('http://127.0.0.1:' + PORT + '/do?fn=' + encodeURIComponent(fn),
         {{mode:'no-cors'}})
     .then(() => flash('\\u2192 ' + label + ' (see Emacs)'))
     .catch(() => flash('Emacs listener not reachable — start it from the launcher'));
 }}
"""

def ref_card(label, href, blurb):
    return (f'<a class="card" href="{esc(href)}">'
            f'<div class="t">{esc(label)}</div>'
            f'<div class="b">{esc(blurb)}</div></a>')

def emacs_card(label, fn, blurb):
    return (f'<a class="card emacs" href="#" '
            f'onclick="poke(event, \'{esc(fn)}\', \'{esc(label)}\')">'
            f'<div class="t">{esc(label)}</div>'
            f'<div class="b">{esc(blurb)}</div></a>')

def build():
    refs = "".join(ref_card(*r) for r in REF_LINKS)
    work_sections = []
    n_work = 0
    for heading, items in WORKBENCH:
        cards = "".join(emacs_card(*e) for e in items)
        n_work += len(items)
        work_sections.append(
            f'<h2>{esc(heading)} <span class="sub" style="font-size:.85rem">'
            f'(opens in Emacs)</span></h2>\n{cards}')
    works = "\n".join(work_sections)
    doc = f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>VNB Math Assistant</title>
<style>{CSS}</style></head><body>
<div id="flash"></div>
<main>
<h1>VNB Math Assistant</h1>
<p class="sub">The home page. Reference reading happens here in the browser; proving happens in Emacs.</p>
<h2>Reference</h2>
{refs}
{works}
</main>
<script>{JS}</script>
</body></html>
"""
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(doc)
    print(f"wrote {OUT}  (port {PORT}, {len(REF_LINKS)} reference + {n_work} workbench links)")

if __name__ == "__main__":
    build()
